{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
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
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Error

import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Cluster
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Sugar (app1, IROpenFun2 (app2))
import Data.Array.Accelerate.LLVM.Foreign

import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Instruction

import Data.Maybe
import Control.Monad

type CG f = forall target op env idxEnv. CompileForeignExp target => Args env f -> IdxArgs idxEnv f -> (LoopDepth, OpCodeGen target op env idxEnv)
type CGLoop f = forall target op env idxEnv. CompileForeignExp target => FlatOp op env idxEnv -> Args env f -> IdxArgs idxEnv f -> (LoopDepth, OpCodeGen target op env idxEnv)

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
  :: (CompileForeignExp target, f ~ (Fun' (e -> e -> e) -> Mut sh' e -> In sh (PrimMaybe (sh', e)) -> ()))
  => (Envs env idxEnv -> Operand Int -> Operands sh' -> CodeGen target () -> CodeGen target ())
  -> Args env f -> IdxArgs idxEnv f -> (LoopDepth, OpCodeGen target op env idxEnv)
defaultCodeGenPermute atomically (ArgFun combineFun :>: output :>: source :>: _) (_ :>: _ :>: IdxArgIdx depth sourceIdx :>: _) =
  ( depth
  , OpCodeGenSingle $ \envs -> do
    -- project element onto the destination array and (atomically) update
    x' <- readArray' envs source sourceIdx
    A.when (A.isJust x') $ do
      let idxx = A.fromJust x'
      let idx = A.fst idxx
      let x = A.snd idxx
      let sh' = envsPrjParameters (shapeExpVars shr sh) envs
      OP_Int j <- intOfIndex shr sh' idx
      atomically envs j idx $ do
        y <- readArray TypeInt envs output (OP_Int j)
        r <- app2 (llvmOfFun2 (compileArrayInstrEnvs envs) combineFun) x y
        writeArray TypeInt envs output (OP_Int j) r
  )
  where
    ArgArray _ (ArrayR shr _) sh _ = output
defaultCodeGenPermute _ _ _ = internalError "Missing index for argument of permute"

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
