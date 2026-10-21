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

module Data.Array.Accelerate.LLVM.CodeGen.Default (
  FoldOrScan(..), ScanInclusiveness(..),
  -- Sequential code generation
  defaultCodeGenGenerate,
  defaultCodeGenMap,
  defaultCodeGenBackpermute,
  defaultCodeGenPermute,
  defaultCodeGenPermuteUnique,
  defaultCodeGenFold,
  defaultCodeGenFold1,
  defaultCodeGenScan1,
  defaultCodeGenScan',
  defaultCodeGenScan,
  -- Parallel code generation
  defaultParCodeGenScan1,
  defaultParCodeGenScan',
  defaultParCodeGenScan,
  defaultParCodeGenFold,
  defaultParCodeGenFold1,
  FoldScanCodeGen(..), ParCodeGenFoldCommutative, ParCodeGenChainedScan,
  -- Utilities for implementing chained scans
  ChainedScanKernelMemory, ChainedScanKernelMemorySlot,
  chainedScanKernelMemory, chainedScanKernelMemorySlot,
  chainedScanInit, chainedScanLookback, chainedScanFinish,
  chainedScanDescriptorIdxTag, chainedScanGetDescriptorSlot,
  combineInDirection, flagAggregate, flagPrefix
) where

import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Analysis.Exp
import Data.Array.Accelerate.Error

import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import qualified Data.Array.Accelerate.LLVM.CodeGen.Constant as A
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Cluster
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Permute
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Intrinsic (Intrinsic(..))
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop            as Loop
import Data.Array.Accelerate.LLVM.Foreign

import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.RMW
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.GetElementPtr
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation

import Control.Monad
import Data.Maybe

type CG f = forall target op env idxEnv. (CompileForeignExp target, Intrinsic target) => Args env f -> IdxArgs idxEnv f -> (LoopDepth, OpCodeGen target op env idxEnv)
type CGLoop f = forall target op env idxEnv. (CompileForeignExp target, Intrinsic target) => FlatOp op env idxEnv -> Args env f -> IdxArgs idxEnv f -> (LoopDepth, OpCodeGen target op env idxEnv)
type CGPar target analysis f = forall env idxEnv. (CompileForeignExp target, Intrinsic target) => Bool -> Args env f -> IdxArgs idxEnv f -> Maybe (Exists (ParLoopCodeGen target analysis env idxEnv))

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

-- Parallel code generation for folds and scans

defaultParCodeGenScan1
  :: FoldScanCodeGen target analysis
  -> CGPar target analysis
      (Fun' (e -> e -> e) -> In (sh, Int) e -> Out (sh, Int) e -> ())
defaultParCodeGenScan1 scanCode descending
    (ArgFun fun :>: input :>: output :>: _)
    (_ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _)
  = Just $ parCodeGenFoldOrScan scanCode descending IsScan ScanInclusive fun Nothing input inputIdx
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
    (\_ _ -> return ())
defaultParCodeGenScan1 _ _ _ _ = internalError "Missing index for argument of scan1"

defaultParCodeGenScan'
  :: FoldScanCodeGen target analysis
  -> CGPar target analysis
      (Fun' (e -> e -> e) -> Exp' e -> In (sh, Int) e -> Out (sh, Int) e -> Out sh e -> ())
defaultParCodeGenScan' scanCode descending
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: foldOutput :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: IdxArgIdx _ foldOutputIdx :>: _)
  = Just $ parCodeGenFoldOrScan scanCode descending IsScan ScanExclusive fun (Just seed) input inputIdx
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
    (\envs result -> writeArray' envs foldOutput foldOutputIdx result)
defaultParCodeGenScan' _ _ _ _ = internalError "Missing index for argument of scan'"

defaultParCodeGenScan
  :: FoldScanCodeGen target analysis
  -> CGPar target analysis
      (Fun' (e -> e -> e) -> Exp' e -> In (sh, Int) e -> Out (sh, Int) e -> ())
defaultParCodeGenScan scanCode descending
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: _ :>: _)
  | descending = -- Right-to-left
    Just $ parCodeGenFoldOrScan scanCode descending IsScan ScanInclusive fun (Just seed) input inputIdx
      (\envs result -> do
        let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
        writeArrayAt' envs output rowIdx n' result
      )
      (\envs result -> writeArray' envs output inputIdx result)
      (\_ _ -> return ())
  | otherwise = -- Left-to-right
      Just $ parCodeGenFoldOrScan scanCode descending IsScan ScanExclusive fun (Just seed) input inputIdx
        (\_ _ -> return ())
        (\envs result -> writeArray' envs output inputIdx result)
        (\envs result -> do
          let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
          writeArrayAt' envs output rowIdx n' result
        )
  where
    ArgArray _ _ inputSh _ = input
    n = case inputSh of
      TupRpair _ (TupRsingle n') -> n'
      _ -> internalError "Shape impossible"
    rowIdx = case inputIdx of
      TupRpair i _ -> i
      _ -> internalError "Shape impossible"
defaultParCodeGenScan _ _ _ _ = internalError "Missing index for argument of scan"

defaultParCodeGenFold
  :: FoldScanCodeGen target analysis
  -> CGPar target analysis
      (Fun' (e -> e -> e) -> Exp' e -> In (sh, Int) e -> Out sh e -> ())
defaultParCodeGenFold scanCode descending
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _)
  = Just $ parCodeGenFoldOrScan scanCode descending IsFold ScanInclusive fun (Just seed) input inputIdx
    (\_ _ -> return ())
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
defaultParCodeGenFold _ _ _ _ = internalError "Missing index for argument of fold"

defaultParCodeGenFold1
  :: FoldScanCodeGen target analysis
  -> CGPar target analysis
      (Fun' (e -> e -> e) -> In (sh, Int) e -> Out sh e -> ())
defaultParCodeGenFold1 scanCode descending
    (ArgFun fun :>: input :>: output :>: _)
    (_ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _)
  = Just $ parCodeGenFoldOrScan scanCode descending IsFold ScanInclusive fun Nothing input inputIdx
    (\_ _ -> return ())
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
defaultParCodeGenFold1 _ _ _ _ = internalError "Missing index for argument of fold1"

data FoldScanCodeGen target analysis = FoldScanCodeGen
  (forall env idxEnv sh e. ParCodeGenFoldCommutative target analysis env idxEnv sh e)
  (forall env idxEnv sh e. ParCodeGenChainedScan target analysis env idxEnv sh e)

parCodeGenFoldOrScan
  :: forall target analysis env idxEnv sh e.
     FoldScanCodeGen target analysis
  -> Bool
  -> FoldOrScan
  -> ScanInclusiveness
  -> Fun env (e -> e -> e)
  -> Maybe (Exp env e) -- Seed. Optional for inclusive scans, required for exclusive scans
  -> Arg env (In (sh, Int) e)
  -> ExpVars idxEnv (sh, Int)
  -- Code after evaluating the seed
  -- Must be 'return ()' if the seed is Nothing or foldOrScan = IsFold
  -> (Envs env idxEnv -> Operands e -> CodeGen target ())
  -- Code in a tile loop, to handle one item of the output
  -- Must be 'return ()' if foldOrScan = IsFold
  -> (Envs env idxEnv -> Operands e -> CodeGen target ())
  -- Code after the parallel loop
  -> (Envs env idxEnv -> Operands e -> CodeGen target ())
  -> Exists (ParLoopCodeGen target analysis env idxEnv)
parCodeGenFoldOrScan (FoldScanCodeGen foldCode scanCode) descending foldOrScan inclusiveness fun mSeed input inputIdx codeSeed codeElement codeEnd
  -- Note that the body of this function uses seed instead of mSeed. When no
  -- seed is given, this function will try to find an identity value and use
  -- that as seed to simplify the generated code. To use this new value, we
  -- must use seed instead of mSeed.

  -- Commutative folds have a special code path
  | IsFold <- foldOrScan
  , Just s <- seed
  , Just i <- identity
  = foldCode descending tp fun s i (\envs -> readArray' envs input inputIdx) codeEnd
  -- Non-commutative folds or any scan
  | otherwise
  = scanCode descending foldOrScan inclusiveness tp fun seed identity (\envs -> readArray' envs input inputIdx) codeSeed codeElement codeEnd
  where
    -- Find an identity value
    identity
      -- seed is commonly the identity value
      | Just s <- mSeed
      , if descending then isRightIdentity fun s else isLeftIdentity fun s
      = Just s
      -- Use a simple heuristic to guess an identity value
      | Just v <- if descending then findRightIdentity fun else findLeftIdentity fun
      = Just $ mkConstant tp v
      -- No identity could be found
      | otherwise
      = Nothing

    -- If no seed is given, use identity value as seed (when available)
    seed
      | isJust mSeed = mSeed
      | otherwise = identity

    ArgArray _ (ArrayR _ tp) _ _ = input

type ParCodeGenChainedScan target analysis env idxEnv sh e
  =  Bool -- descending
  -> FoldOrScan -- this code path for chained scans is also used for non-commutative folds
  -> ScanInclusiveness
  -> TypeR e
  -> Fun env (e -> e -> e)
  -> Maybe (Exp env e) -- Seed. Optional for inclusive scans, required for exclusive scans
  -> Maybe (Exp env e) -- Identity value of the combination function. Optional, but beneficial for performance
  -- Read an element from the input. Needs to be called from within a tile
  -- loop, and returns the input value for that iteration of the tile loop.
  -> (Envs env idxEnv -> CodeGen target (Operands e))
  -- Code after evaluating the seed
  -- Must be 'return ()' if the seed is Nothing
  -> (Envs env idxEnv -> Operands e -> CodeGen target ())
  -- Code in a tile loop, to handle one item of the output
  -> (Envs env idxEnv -> Operands e -> CodeGen target ())
  -- Code after the parallel loop
  -> (Envs env idxEnv -> Operands e -> CodeGen target ())
  -> Exists (ParLoopCodeGen target analysis env idxEnv)

type ParCodeGenFoldCommutative target analysis env idxEnv sh e
  =  Bool -- descending
  -> TypeR e
  -> Fun env (e -> e -> e) -- Must be commutative
  -- TODO: Can we make this work without an identity value? (I.e. make the seed and identity a Maybe, like we do for scans)
  -> Exp env e -- Seed. Optional for inclusive scans, required for exclusive scans
  -> Exp env e -- Identity value of the combination function. Optional, but beneficial for performance
  -- Read an element from the input. Needs to be called from within a tile
  -- loop, and returns the input value for that iteration of the tile loop.
  -> (Envs env idxEnv -> CodeGen target (Operands e))
  -- Code after the parallel loop
  -> (Envs env idxEnv -> Operands e -> CodeGen target ())
  -> Exists (ParLoopCodeGen target analysis env idxEnv)

type ChainedScanKernelMemory e = SizedArray (Struct (BufferEltR (ChainedScanKernelMemorySlot e)))
type ChainedScanKernelMemorySlot e = ((Word8, e), e)

chainedScanKernelMemory :: Int -> TypeR e -> PrimType (ChainedScanKernelMemory e)
chainedScanKernelMemory descriptorsLength tp =
  ArrayPrimType (fromIntegral descriptorsLength) $
    StructPrimType False $ bufferEltsR $ chainedScanKernelMemorySlot tp

chainedScanKernelMemorySlot :: TypeR e -> TypeR (ChainedScanKernelMemorySlot e)
chainedScanKernelMemorySlot tp = TupRsingle scalarTypeWord8 `TupRpair` tp `TupRpair` tp

-- | Initialize kernel memory for a chained scan.
-- Note that this function is sequential, and GPU backends should use a
-- parallel variant of this function (ideally).
-- Caller of this function should still write the seed to memory manually.
-- This function returns a pointer to that location
chainedScanInit
  :: Int
  -> TypeR e
  -> Operand (Ptr (Struct (ChainedScanKernelMemory e)))
  -> CodeGen target (TupR Operand (Distribute Ptr (BufferEltR e)))
chainedScanInit descriptorsLength tp ptr = do
  -- Initialize all flags (but the first) to flagInit
  Loop.imapFromStepTo [] (A.liftInt 1) (A.liftInt 1) (A.liftInt descriptorsLength) $ \i -> do
    (flagPtr, _, _) <- chainedScanGetDescriptorSlot descriptorsLength tp ptr i
    -- Initialize with 0xFF:
    -- Tag is stored in 7 most significant bits, and 0xFE is the tag
    -- before 0 (with wrap around).
    -- The state is stored in the least significant bit, and 1 denotes
    -- that that tile is finished (flagPrefix).
    _ <- instrMD' (Store NonVolatile flagPtr (A.integral TypeWord8 0xFF) Nothing) (bufferMetadata' Nothing)
    return ()

  -- Tile i starts look-back at index i, and writes result to index i+1.
  -- When available, the seed is thus written to index 0 here.
  -- Always set first flag to 'prefix available', to let look-back of first
  -- tile succeed (with garbage value; that value is not used since
  -- combineInDirection checks whether a seed is given.)
  (flagPtr, _, valuePtrs) <- chainedScanGetDescriptorSlot descriptorsLength tp ptr $ A.liftInt 0
  -- tag = 0, tag | flagPrefix = flagPrefix, so
  -- we can write flagPrefix directly.
  _ <- instrMD' (Store NonVolatile flagPtr flagPrefix Nothing) (bufferMetadata' Nothing)
  return valuePtrs

-- | Concludes a chained scan by returning the total reduced value
chainedScanFinish
  :: Envs env idxEnv
  -> Int
  -> TypeR e
  -> Operand (Ptr (Struct (ChainedScanKernelMemory e)))
  -> CodeGen target (Operands e)
chainedScanFinish envs descriptorsLength tp ptr = do
  let tileCount
        | envsLoopDepth envs /= 0 = internalError "Parallel scan should be 1-dimensional here"
        | (_, tc) : _ <- envsTileSizeCount envs = tc
        | otherwise = internalError "envsTileSizeCount should not be empty during codegen of parallel scan"

  (descIdx, _) <- chainedScanDescriptorIdxTag descriptorsLength tileCount
  (_, _, valuePtrs) <- chainedScanGetDescriptorSlot descriptorsLength tp ptr descIdx
  tupleLoad tp valuePtrs

chainedScanLookback
  :: (CompileForeignExp target, Intrinsic target)
  => Envs env idxEnv
  -> CodeGen target (Operand Word32) -- Acquire number of threads (or thread groups in case of GPUs)
  -> Int
  -> TypeR e
  -> Operand (Ptr (Struct (ChainedScanKernelMemory e)))
  -> Operand (Ptr Int)
  -> TupR Operand (Distribute Ptr (BufferEltR e))
  -> Fun env (e -> e -> e)
  -> Maybe (Exp env e) -- Seed
  -> Maybe (Exp env e) -- Identity
  -> Operands e -- Reduced value of current tile
  -> CodeGen target (Operands e, Operands e) -- Exclusive, inclusive prefix of this tile
chainedScanLookback envs getThreadCount descriptorsLength tp ptr lookbackIndex lookbackValue fun seed identity local = do
  -- Before sharing our aggregate, check if we can already write to this
  -- slot in the cyclic buffer in 'ptr'.
  --
  -- To ensure overwrites of values that are still needed, we let tile i
  -- synchronize with tile i - S, where
  -- S = max(buffer_length - 2*max_threads + 1, 1)
  -- (assuming buffer_length >= 2)
  -- Tile i must wait with sharing its aggregate until tile i - S has
  -- flag 'prefix available'.
  -- Note that this description was written for CPUs, but it extends to GPUs
  -- by replacing 'thread' with 'threadgroup' (since a threadgroup is the unit
  -- that handles one tile at a time).
  --
  -- For the correctness of this protocol, we need the following lemma:
  -- The look-back of tile k goes no further than tile k - max_threads.
  -- Sketch of proof: each time the thread of tile k finds flag
  -- 'aggregate available', it goes to the previous tile. Since the look-
  -- back and the threads producing the aggregates go in different
  -- directions, the thread of tile k sees at most one 'aggregate
  -- available' per other thread, thus at most max_threads-1 in total.
  -- The look-back will thus not go further back than tile
  -- k - max_threads.
  --
  -- We demonstrate the correctness of this protocol separately for S>1
  -- and S=1. First, assume S > 1.
  -- By the definition of S, S = buffer_length - 2 * max_threads + 1
  -- Assume tile k is not ready yet. Tiles k - max_threads to k must not
  -- be overwritten yet in the cyclic buffer, i.e. tile indices
  -- k - max_threads + buffer_length and larger may not write yet.
  -- This protocol blocks tile k + S from writing at this point,
  -- but later tiles (eg k + S + 1) can already share their aggregate.
  -- Since two threads are blocked at this point (the thread handling
  -- tile k and the thread for tile k + S), at most max_threads-2 threads
  -- may write an aggregate to tiles k+S+1 to k+S+max_threads-2
  -- (inclusive). Tiles whose index is at least k+S+max_threads-1 will
  -- not start yet, when tile k is not ready.
  -- We thus have to ensure that:
  -- k + S + max_threads - 1 <= k - max_threads + buffer_length
  -- We know S = buffer_length - 2 * max_threads + 1,
  -- and by adding 'k + max_threads - 1' to both sides and rearranging,
  -- we get:
  -- k + S + max_threads - 1 <= k - max_threads + buffer_length
  --
  -- Now assume S = 1.
  -- The scan now essentially behaves like a regular chained scan,
  -- without decoupled look-back: the "look-back" of tile i only starts
  -- when tile i-1 is completed, and the look-back will thus directly
  -- succeed.
  --
  -- Note that we get no benefits of the decoupled look-back when S=1,
  -- but we can this way still have a correct scan when the program runs
  -- on more threads than anticipated. The buffer_length should be chosen
  -- to be at least 3 times the expected maximum number of threads.
  -- However, since this is set at compile-time and the number of threads
  -- follows at run-time, we have to make an estimation here. By the
  -- design of this protocol, the estimation will not influence
  -- correctness, but will only influence the performance.

  -- Compute the 'S' from above
  syncDistance <- do
    threads <- getThreadCount
    threads' <- A.fromIntegral TypeWord32 numType $ OP_Word32 threads
    threads2 <- A.mul numType threads' $ A.liftInt 2
    sub <- A.sub numType (A.liftInt descriptorsLength) threads2
    plusOne <- A.add numType sub $ A.liftInt 1
    A.max singleType plusOne $ A.liftInt 1

  -- Synchronize with previous tile by waiting on its prefix
  syncIndex <-
    A.sub numType (envsTileIndex envs) syncDistance
      >>= A.add numType (A.liftInt 1)
  -- Note: we check for 'greater than zero' instead of 'greater than or
  -- equal to zero'.
  -- Index zero is initialized with the seed (if a seed is available),
  -- and ignored otherwise. The first tile writes to index 1, since tile
  -- i writes to descriptor i+1 (and starts look-back at index i).
  A.when (A.gt singleType syncIndex $ A.liftInt 0) $ do
    _ <- Loop.while [] TupRunit
      (\_ -> do
        (prevDescIdx, prevTag) <- chainedScanDescriptorIdxTag descriptorsLength syncIndex
        (prevFlagPtr, _, _) <- chainedScanGetDescriptorSlot descriptorsLength tp ptr prevDescIdx

        flag <- instrMD (AtomicLoad scalarType prevFlagPtr Acquire) (bufferMetadata' Nothing)
        flagPrefix' <- A.bor TypeWord8 prevTag $ OP_Word8 flagPrefix
        -- Block while this tile has no prefix
        A.neq singleType flag flagPrefix'
      )
      (\_ -> return OP_Unit)
      OP_Unit
    return ()

  -- Perform regular work for look-back

  -- Share our aggregate
  nextTileIdx <- A.add numType (envsTileIndex envs) (A.liftInt 1)
  (thisDescIdx, thisTag) <- chainedScanDescriptorIdxTag descriptorsLength nextTileIdx
  (thisFlagPtr, thisAggregatePtrs, thisPrefixPtrs) <- chainedScanGetDescriptorSlot descriptorsLength tp ptr thisDescIdx
  tupleStore tp thisAggregatePtrs local
  OP_Word8 newFlag <- A.bor TypeWord8 thisTag $ OP_Word8 flagAggregate
  _ <- instrMD' (AtomicStore scalarType thisFlagPtr newFlag Release) (bufferMetadata' Nothing)

  -- Initialize look-back
  _ <- instr' $ Store NonVolatile lookbackIndex (op scalarTypeInt $ envsTileIndex envs) Nothing
  case identity of
    Nothing -> return ()
    Just identity' -> do
      value <- llvmOfExp (compileArrayInstrEnvs envs) identity'
      tupleStore tp lookbackValue value

  -- Decoupled look-back
  _ <- Loop.while [] TupRunit
    (\_ -> do
      idx <- instr $ Load NonVolatile lookbackIndex Nothing
      (prevDescIdx, prevTag) <- chainedScanDescriptorIdxTag descriptorsLength idx
      (prevFlagPtr, prevAggregatePtrs, prevPrefixPtrs) <- chainedScanGetDescriptorSlot descriptorsLength tp ptr prevDescIdx

      flag <- instrMD (AtomicLoad scalarType prevFlagPtr Acquire) (bufferMetadata' Nothing)

      flagAggregate' <- A.bor TypeWord8 prevTag $ OP_Word8 flagAggregate
      flagPrefix' <- A.bor TypeWord8 prevTag $ OP_Word8 flagPrefix

      hasAggregate <- A.eq singleType flag flagAggregate'
      hasPrefix <- A.eq singleType flag flagPrefix'
      
      _ <- A.ifThenElse (TupRunit, A.lor hasAggregate hasPrefix)
        (do
          value <- A.ifThenElse (tp, return hasPrefix)
            (tupleLoad tp prevPrefixPtrs) (tupleLoad tp prevAggregatePtrs)
          current <- tupleLoad tp lookbackValue

          isFirst <- A.eq singleType idx $ envsTileIndex envs

          new <- combineInDirection envs tp fun identity isFirst True current value
          tupleStore tp lookbackValue new

          -- Increment lookbackIndex
          -- Note that this will only be used when hasAggregate = true;
          -- when hasPrefix = true the loop will exit and this value will
          -- not be used.
          OP_Int idx' <- A.sub numType idx $ A.liftInt 1
          _ <- instr $ Store NonVolatile lookbackIndex idx' Nothing

          return OP_Unit
        )
        ( return OP_Unit ) -- TODO: sleep?

      A.lnot hasPrefix
    )
    (\_ -> return OP_Unit)
    OP_Unit
  exclusivePrefix <- tupleLoad tp lookbackValue

  isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
  -- Add local value to exclusive prefix to compute inclusive prefix
  inclusivePrefix <- combineInDirection envs tp fun seed isFirstTile False exclusivePrefix local

  tupleStore tp thisPrefixPtrs inclusivePrefix
  OP_Word8 newFlag' <- A.bor TypeWord8 thisTag $ OP_Word8 flagPrefix
  _ <- instrMD' (AtomicStore scalarType thisFlagPtr newFlag' Release) (bufferMetadata' Nothing)
  return (exclusivePrefix, inclusivePrefix)


chainedScanDescriptorIdxTag :: Int -> Operands Int -> CodeGen target (Operands Int, Operands Word8)
chainedScanDescriptorIdxTag descriptorsLength tileIdx = do
  descIdx <- A.rem TypeInt tileIdx (A.liftInt descriptorsLength)
  tag <- A.quot TypeInt tileIdx (A.liftInt descriptorsLength) >>= A.mul numType (A.liftInt 2)
  tag8 <- A.fromIntegral TypeInt (numType @Word8) tag
  return (descIdx, tag8)

chainedScanGetDescriptorSlot
  :: Int
  -> TypeR e
  -> Operand (Ptr (Struct (ChainedScanKernelMemory e)))
  -> Operands Int
  -> CodeGen target
      ( Operand (Ptr Word8)
      , TupR Operand (Distribute Ptr (BufferEltR e))
      , TupR Operand (Distribute Ptr (BufferEltR e)))
chainedScanGetDescriptorSlot descriptorsLength tp ptr (OP_Int i) = do
  slot <- instr' $ GetElementPtr $
    GEP ptr (A.num numType 0 :: Operand Int32) $
    GEPStruct (chainedScanKernelMemory descriptorsLength tp) TupleIdxSelf $
    GEPArray i GEPEmpty
  ptrs <- tuplePtrs (chainedScanKernelMemorySlot tp) slot
  case ptrs of
    TupRsingle flag `TupRpair` valueAggregate `TupRpair` valuePrefix -> return (flag, valueAggregate, valuePrefix)
    _ -> internalError "Pair impossible"

-- initial: the initial value of the accumulator ('a'). This function
--   checks whether this is Just or Nothing to know whether the variable
--   was initialized or not.
-- isFirst: whether this is the first iteration. When isFirst is true and
--   initial Nothing, this function will not use the value in 'a' and
--   directly return 'b'. Otherwise it will combine 'a' and 'b'.
-- reversed: whether the direction should be reversed (ie fun should be flipped)
combineInDirection :: (CompileForeignExp target, Intrinsic target) => Envs env idxEnv -> TypeR e -> Fun env (e -> e -> e) -> Maybe a -> Operands Bool -> Bool -> Operands e -> Operands e -> CodeGen target (Operands e)
combineInDirection envs tp fun initial isFirst reversed a b
  | isJust initial = do
    if envsDescending envs /= reversed then
      app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) b a
    else
      app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) a b
  | otherwise =
    A.ifThenElse' (tp, isFirst)
      ( return b )
      ( do
        if envsDescending envs /= reversed then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) b a
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) a b
      )

flagAggregate, flagPrefix :: Operand Word8
flagAggregate = A.scalar scalarTypeWord8 0
flagPrefix = A.scalar scalarTypeWord8 1
