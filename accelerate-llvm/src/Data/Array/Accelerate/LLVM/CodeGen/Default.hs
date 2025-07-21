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

type CG f = forall target op env idxEnv. CompileForeignExp target => Args env f -> IdxArgs idxEnv f -> (LoopDepth, OpCodeGen target op env idxEnv)

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
