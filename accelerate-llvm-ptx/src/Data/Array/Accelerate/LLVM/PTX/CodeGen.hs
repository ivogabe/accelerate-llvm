{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen (

  codegen,
  KernelMetadata,

) where

-- accelerate

import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (shapeRFromRank, shapeType, rank)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Partitioned as P hiding (combine)
import Data.Array.Accelerate.Analysis.Exp
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment hiding ( Empty )
import Data.Array.Accelerate.LLVM.CodeGen.Cluster
import Data.Array.Accelerate.LLVM.CodeGen.Default
import Data.Array.Accelerate.LLVM.PTX.Operation
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Intrinsic ()
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Permute
import Data.Array.Accelerate.LLVM.PTX.Foreign
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Maybe

import LLVM.AST.Type.Module
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.RMW
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified LLVM.AST.Type.Function as LLVM
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Sugar (app1, IROpenFun2 (app2))
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
-- import Data.Array.Accelerate.LLVM.PTX.CodeGen.Permute (atomically)
import Data.Array.Accelerate.AST.LeftHandSide (Exists (Exists))
import Control.Monad
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop as Loop
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import qualified Text.LLVM as LP

codegen :: String
        -> Env AccessGroundR env
        -> Clustered PTXOp args
        -> Args env args
        -> LLVM PTX
           ( Int -- The size of the kernel data, shared by all threads working on this kernel.
           , Module (KernelType env))
codegen name env cluster args
 | flat@(FlatCluster shr idxLHS sizes dirs localR localLHS flatOps) <- toFlatClustered cluster args
 , parallelDepth <- flatClusterIndependentLoopDepth flat
 , Exists parallelShr <- shapeRFromRank parallelDepth
 , Refl <- marshalFunResultUnit env =
  codeGenKernel name (LLVM.Lam kernelDataRawType "kernel_data" . bindArgs) $ do
    extractEnv
    if parallelDepth == 0 && rank shr /= 0 then do
      internalError "TODO: Implement parallel collective operations on one-dimensional arrays"
    else if parallelDepth /= rank shr then do
      internalError "TODO: Implement parallel collective operations on multi-dimensional arrays"
    else do
      -- Parallelise over all independent dimensions
      let (envs, loops) = initEnv gamma shr idxLHS sizes dirs localR localLHS
      let parSizes = parallelIterSize parallelShr loops
      parSize <- shapeSize parallelShr parSizes

      imapFromTo (A.liftInt 0) parSize $ \linearIdx -> do
        idx <- indexOfInt parallelShr parSizes linearIdx
        let envs' = envs{
            envsLoopDepth = parallelDepth,
            envsIdx =
              foldr (\(o, i) -> Env.partialUpdate o i) (envsIdx envs)
              $ zip (shapeOperandsToList parallelShr idx) (map (\(i, _, _) -> i) loops),
            -- Independent operations should not depend on envsIsFirst.
            envsIsFirst = OP_Bool $ boolean False,
            envsDescending = False
          }
        genSequential envs' (drop parallelDepth loops) $ opCodeGens opCodeGen flatOps

      return_

    return 0 -- We don't use kernel data yet
  where
    (bindArgs, extractEnv, gamma) = bindEnvArgs @PTX env
    kernelDataRawType :: PrimType (Ptr (SizedArray Word))
    kernelDataRawType = PtrPrimType (ArrayPrimType 0 primType) defaultAddrSpace

opCodeGen :: FlatOp PTXOp env idxEnv -> (LoopDepth, OpCodeGen PTX PTXOp env idxEnv)
opCodeGen (FlatOp PTXGenerate args idxArgs) = defaultCodeGenGenerate args idxArgs
opCodeGen (FlatOp PTXMap args idxArgs) = defaultCodeGenMap args idxArgs
opCodeGen (FlatOp PTXBackpermute args idxArgs) = defaultCodeGenBackpermute args idxArgs
opCodeGen (FlatOp PTXPermute
    (combineFun :>: output :>: locks :>: source :>: _)
    (i1 :>: i2 :>: _ :>: i3 :>: _)) =
  defaultCodeGenPermute
    (\envs j _ -> atomically envs locks $ OP_Int j)
    (combineFun :>: output :>: source :>: ArgsNil)
    (i1 :>: i2 :>: i3 :>: ArgsNil)
opCodeGen (FlatOp PTXPermute' args idxArgs) = defaultCodeGenPermuteUnique args idxArgs
