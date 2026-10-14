{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Default
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Default where

import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Error

import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Cluster
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Permute
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Intrinsic (Intrinsic(..))
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.Foreign

import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.RMW
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation

import Control.Monad

type CG f = forall target op env idxEnv. (CompileForeignExp target, Intrinsic target) => Args env f -> IdxArgs idxEnv f -> (LoopDepth, OpCodeGen target op env idxEnv)
type CGLoop f = forall target op env idxEnv. (CompileForeignExp target, Intrinsic target) => FlatOp op env idxEnv -> Args env f -> IdxArgs idxEnv f -> (LoopDepth, OpCodeGen target op env idxEnv)

data FoldOrScan = IsFold | IsScan deriving Eq
data ScanInclusiveness = ScanInclusive | ScanExclusive deriving Eq

defaultCodeGenGenerate :: CG (Fun' (sh -> t) -> Out sh t -> ())
defaultCodeGenGenerate (ArgFun fun :>: array :>: _) (_ :>: IdxArgIdx depth idxs :>: _) =
  ( depth
  , OpCodeGenSingle $ \envs -> do
    let idxs' = envsPrjIndices idxs envs
    r <- app1 (llvmOfFun1 (compileArrayInstrEnvs envs) fun) idxs'
    writeArray' envs array idxs r
  )
defaultCodeGenGenerate _ _ = internalError "Missing index for argument of generate"

defaultCodeGenMap :: CG (Fun' (a -> b) -> In sh a -> Out sh b -> ())
defaultCodeGenMap (ArgFun fun :>: input :>: output :>: _) (_ :>: IdxArgIdx depth idxs :>: _) =
  ( depth
  , OpCodeGenSingle $ \envs -> do
    x <- readArray' envs input idxs
    r <- app1 (llvmOfFun1 (compileArrayInstrEnvs envs) fun) x
    writeArray' envs output idxs r
  )
defaultCodeGenMap _ _ = internalError "Missing index for argument of map"

defaultCodeGenBackpermute :: CG (Fun' (sh' -> sh) -> In sh t -> Out sh' t -> ())
defaultCodeGenBackpermute (_ :>: input :>: output :>: _) (_ :>: IdxArgIdx depth inputIdx :>: IdxArgIdx _ outputIdx :>: _) =
  ( depth
  , OpCodeGenSingle $ \envs -> do
    -- Note that the index transformation (the function in the first argument)
    -- is already executed and part of the idxEnv. The index transformation is
    -- thus now given by 'inputIdx' and 'outputIdx'.
    x <- readArray' envs input inputIdx
    writeArray' envs output outputIdx x
  )
defaultCodeGenBackpermute _ _ = internalError "Missing index for argument of backpermute"

defaultCodeGenPermute
  :: (CompileForeignExp target, Intrinsic target, f ~ (Fun' (e -> e -> e) -> Mut sh' e -> In sh (PrimMaybe (sh', e)) -> ()))
  => Int
  -> (Operands Word64 -> CodeGen target () -> CodeGen target ())
  -> Args env f -> IdxArgs idxEnv f -> (LoopDepth, OpCodeGen target op env idxEnv)
defaultCodeGenPermute lockArraySize atomically (ArgFun combineFun :>: output :>: source :>: _) (_ :>: _ :>: IdxArgIdx depth sourceIdx :>: _) =
  -- To perform atomic updates to values in output, we may use locks. Instead
  -- of having one lock per entry in output, we use a fixed-size array of
  -- locks, with size lockArraySize. We map an index in values to the index of
  -- a lock using a hash function. We use the pointer of the first array in
  -- output as a seed in the hash function, to make conflicts between multiple
  -- permute operations (that execute concurrently) less likely.
  --
  -- We use the pointer of the first output buffer
  -- together with the index of the hash function,
  -- as:
  -- hash(ptr + i)
  -- This reduces the chance of collisions between multiple concurrent
  -- permutes, as each permute will have a different ptr, as they cannot write
  -- to the same buffer concurrently.
  -- Note that we use ptr + i instead of ptr + i * sizeof(..) for simplicity.
  -- Given that ptr + i * sizeof(..) will not overlap between concurrent
  -- permutes, ptr + i will also not overlap as sizeof(..) >= 1.
  ( depth
  , OpCodeGenSingle $ \envs -> do
    -- project element onto the destination array and (atomically) update
    x' <- readArray' envs source sourceIdx
    A.when (A.isJust x') $ do
      let idxx = A.fromJust x'
      let idx = A.fst idxx
      let x = A.snd idxx
      let sh' = envsPrjParameters (shapeExpVars shr sh) envs
      j <- intOfIndex shr sh' idx

      -- Choose a synchronisation strategy:
      -- (1) Atomic RMW (atomic-fetch-and-something) or atomic store (when combineFun = const)
      -- (2) Atomic Compare-and-swap loop
      -- (3) Locks
      -- For option 1, check if combineFun corresponds to a RMW operation
      combineRMW <- detectRMW combineFun `guard'` (\(tp, rmw, _) -> liftCodeGen $ supportsAtomicRMW tp rmw)
      -- For option 2, check if the values are singular and if the target supports CAS on these values
      combineCAS <- detectCAS combineFun `guard'` (\tp -> liftCodeGen $ supportsAtomicCAS $ scalarTypeSize tp)
      -- Option 3 is always possible.
      -- Branch on these options
      if
        -- Option 1
        | Just (tp, rmw, fun) <- combineRMW -> do
          z <- app1 (llvmOfFun1 (compileArrayInstrEnvs envs) fun) x
          (ptr, alias) <- singleArrayPtr TypeInt tp envs output j
          -- Pointer cast is safe, since detectRMW checks the alignment of the value
          let ptr' = ptrCast (ScalarPrimType tp) ptr
          case rmw of
            Exchange -> do
              _ <- instrMD' (AtomicStore tp ptr' (op tp z) Monotonic) (bufferMetadata' alias)
              return ()
            _
              | SingleScalarType (NumSingleType numTp) <- tp -> do
                _ <- instrMD' (AtomicRMW numTp NonVolatile rmw ptr' (op tp z) (CrossThread, AcquireRelease)) (bufferMetadata' alias)
                return ()
              | otherwise -> internalError "AtomicRMW only supports num types"

        -- Option 2
        | Just tp <- combineCAS -> do
          (ptr, alias) <- singleArrayPtr TypeInt tp envs output j
          -- Pointer cast is safe, since detectCAS checks the alignment of the value
          let ptr' = ptrCast (ScalarPrimType tp) ptr
          atomicCasLoop tp
            (\y -> app2 (llvmOfFun2 (compileArrayInstrEnvs envs) combineFun) x y)
            ptr'
            alias

        -- Option 3
        | otherwise -> do
          -- Convert 'j' to the index of the lock.
          -- As commented above, we compute the hash of ptr + j,
          -- where ptr is the pointer of the first buffer in the output, bitcasted to an int,
          -- and j is the index in the array (where the permute is writing to).
          seed <- firstArrayPtr envs output
          i <- A.add numType seed j
          i' <- A.fromIntegral TypeInt (IntegralNumType TypeWord64) i
          h <- A.hash i'
          lockIdx <- A.rem TypeWord64 h $ A.liftWord64 $ Prelude.fromIntegral lockArraySize

          atomically lockIdx $ do
            y <- readArray TypeInt envs output j
            r <- app2 (llvmOfFun2 (compileArrayInstrEnvs envs) combineFun) x y
            writeArray TypeInt envs output j r
  )
  where
    ArgArray _ (ArrayR shr _) sh _ = output

    guard' :: Maybe a -> (a -> CodeGen target Bool) -> CodeGen target (Maybe a)
    guard' Nothing _ = return Nothing
    guard' (Just a) cond = do
      c <- cond a
      return $ if c then Just a else Nothing

defaultCodeGenPermute _ _ _ _ = internalError "Missing index for argument of permute"

defaultCodeGenPermuteUnique
  :: CG (Mut sh' e -> In sh (PrimMaybe (sh', e)) -> ())
defaultCodeGenPermuteUnique (output :>: source :>: _) (_ :>: IdxArgIdx depth sourceIdx :>: _) =
  ( depth
  , OpCodeGenSingle $ \envs -> do
    -- project element onto the destination array and update
    x' <- readArray' envs source sourceIdx
    A.when (A.isJust x') $ do
      let idxx = A.fromJust x'
      let idx = A.fst idxx
      let x = A.snd idxx
      let sh' = envsPrjParameters (shapeExpVars shr sh) envs
      j <- intOfIndex shr sh' idx
      -- Under the assumption that all indices (j) are unique,
      -- this is not a race condition.
      writeArray TypeInt envs output j x
  )
  where
    ArgArray _ (ArrayR shr _) sh _ = output
defaultCodeGenPermuteUnique _ _ = internalError "Missing index for argument of permute"

defaultCodeGenFold
  :: CGLoop (Fun' (e -> e -> e) -> Exp' e -> In (sh, Int) e -> Out sh e -> ())
defaultCodeGenFold flatOp (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _) (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx depth outputIdx :>: _) =
  ( depth
  , OpCodeGenLoop
    flatOp
    PeelNot
    (\envs -> do
      var <- tupleAlloca tp
      seed' <- llvmOfExp (compileArrayInstrEnvs envs) seed
      tupleStore tp var seed'
      return var
    )
    (\var envs -> do
      x <- readArray' envs input inputIdx
      accum <- tupleLoad tp var
      new <-
        if envsDescending envs then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
      tupleStore tp var new
    )
    (\var envs -> do
      value <- tupleLoad tp var
      writeArray' envs output outputIdx value
    )
  )
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
defaultCodeGenFold _ _ _ = internalError "Missing index for argument of fold"

defaultCodeGenFold1
  :: CGLoop (Fun' (e -> e -> e) -> In (sh, Int) e -> Out sh e -> ())
defaultCodeGenFold1 flatOp (ArgFun fun :>: input :>: output :>: _) (_ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx depth outputIdx :>: _) =
  -- TODO: Try to find an identity value, and convert to NFold
  ( depth
  , OpCodeGenLoop
    flatOp
    PeelGuaranteed
    (\_ -> tupleAlloca tp)
    (\var envs -> do
      x <- readArray' envs input inputIdx
      -- Note: if the loop peeling is applied (separating the first iteration
      -- of the loop), then this code will be executed twice. envsIsFirst envs
      -- will then either be a constant True, or a constant False.
      -- ifThenElse' (opposed to the version with a prime) will then generate
      -- code for only one branch, and thus also without conditional jumps.
      new <- A.ifThenElse' (tp, envsIsFirst envs)
        ( do
          return x
        )
        ( do
          accum <- tupleLoad tp var
          if envsDescending envs then
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
          else
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
        )
      tupleStore tp var new
    )
    (\var envs -> do
      value <- tupleLoad tp var
      writeArray' envs output outputIdx value
    )
  )
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
defaultCodeGenFold1 _ _ _ = internalError "Missing index for argument of fold1"

defaultCodeGenScan1 :: Direction -> CGLoop (Fun' (e -> e -> e) -> In (sh, Int) e -> Out (sh, Int) e -> ())
defaultCodeGenScan1 dir flatOp (ArgFun fun :>: input :>: output :>: _) (_ :>: IdxArgIdx depth inputIdx :>: IdxArgIdx _ outputIdx :>: _) =
  -- TODO: Try to find an identity value to prevent loop peeling / the conditional in the body of the loop.
  -- Ideally we add a PostScan as primitive, such that we can convert a scan1 into a postscan
  ( depth - 1
  , OpCodeGenLoop
    flatOp
    PeelConditional
    (\_ -> tupleAlloca tp)
    (\var envs -> do
      x <- readArray' envs input inputIdx
      new <- A.ifThenElse' (tp, envsIsFirst envs)
        ( do
          return x
        )
        ( do
          accum <- tupleLoad tp var
          if envsDescending envs then do
            when (dir /= RightToLeft) $ internalError "Wrong direction in scan1"
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
          else do
            when (dir /= LeftToRight) $ internalError "Wrong direction in scan1"
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
        )
      tupleStore tp var new
      writeArray' envs output outputIdx new
    )
    (\_ _ -> return ())
  )
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
defaultCodeGenScan1 _ _ _ _ = internalError "Missing index for argument of scan1"

defaultCodeGenScan' :: Direction -> CGLoop (Fun' (e -> e -> e) -> Exp' e -> In (sh, Int) e -> Out (sh, Int) e -> Out sh e -> ())
defaultCodeGenScan' dir flatOp
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: foldOutput :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: IdxArgIdx depth foldOutputIdx :>: _) =
  ( depth
  , OpCodeGenLoop
    flatOp
    PeelNot
    (\envs -> do
      var <- tupleAlloca tp
      seed' <- llvmOfExp (compileArrayInstrEnvs envs) seed
      tupleStore tp var seed'
      return var
    )
    (\var envs -> do
      accum <- tupleLoad tp var
      writeArray' envs output outputIdx accum
      x <- readArray' envs input inputIdx
      new <-
        if envsDescending envs then do
          when (dir /= RightToLeft) $ internalError "Wrong direction in scan'"
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
        else do
          when (dir /= LeftToRight) $ internalError "Wrong direction in scan'"
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
      tupleStore tp var new
    )
    (\var envs -> do
      value <- tupleLoad tp var
      writeArray' envs foldOutput foldOutputIdx value
    )
  )
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
defaultCodeGenScan' _ _ _ _ = internalError "Missing index for argument of scan'"

defaultCodeGenScan :: Direction -> CGLoop (Fun' (e -> e -> e) -> Exp' e -> In (sh, Int) e -> Out (sh, Int) e -> ())
defaultCodeGenScan LeftToRight flatOp
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx depth inputIdx :>: _ :>: _) =
  ( depth - 1
  , OpCodeGenLoop
    flatOp
    PeelNot
    (\envs -> do
      var <- tupleAlloca tp
      seed' <- llvmOfExp (compileArrayInstrEnvs envs) seed
      tupleStore tp var seed'
      return var
    )
    (\var envs -> do
      when (envsDescending envs) $ internalError "Wrong direction in scan"
      accum <- tupleLoad tp var
      writeArray' envs output inputIdx accum
      x <- readArray' envs input inputIdx
      new <-
        if envsDescending envs then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
      tupleStore tp var new
    )
    (\var envs -> do
      value <- tupleLoad tp var
      let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
      writeArrayAt' envs output rowIdx n' value
    )
  )
  where
    ArgArray _ (ArrayR _ tp) inputSh _ = input
    n = case inputSh of
      TupRpair _ (TupRsingle n') -> n'
      _ -> internalError "Shape impossible"
    rowIdx = case inputIdx of
      TupRpair i _ -> i
      _ -> internalError "Shape impossible"
defaultCodeGenScan RightToLeft flatOp
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx depth inputIdx :>: _ :>: _) =
  ( depth - 1
  , OpCodeGenLoop
    flatOp
    PeelNot
    (\envs -> do
      var <- tupleAlloca tp
      seed' <- llvmOfExp (compileArrayInstrEnvs envs) seed
      tupleStore tp var seed'
      let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
      writeArrayAt' envs output rowIdx n' seed'
      return var
    )
    (\var envs -> do
      unless (envsDescending envs) $ internalError "Wrong direction in scan"
      accum <- tupleLoad tp var
      x <- readArray' envs input inputIdx
      new <-
        if envsDescending envs then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
      tupleStore tp var new
      writeArray' envs output inputIdx new
    )
    (\_ _ -> return ())
  )
  where
    ArgArray _ (ArrayR _ tp) inputSh _ = input
    n = case inputSh of
      TupRpair _ (TupRsingle n') -> n'
      _ -> internalError "Shape impossible"
    rowIdx = case inputIdx of
      TupRpair i _ -> i
      _ -> internalError "Shape impossible"
defaultCodeGenScan _ _ _ _ = internalError "Missing index for argument of scan"
