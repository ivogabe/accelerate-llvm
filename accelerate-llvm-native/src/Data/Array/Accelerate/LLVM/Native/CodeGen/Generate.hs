{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen.Generate
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Generate
  where

import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Partitioned

import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.Compile.Cache

import Data.Array.Accelerate.LLVM.Native.Target                     ( Native )
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop

import LLVM.AST.Type.Representation
import Data.Array.Accelerate.LLVM.CodeGen.IR
import LLVM.AST.Type.Function                                       as LLVM
import LLVM.AST.Type.Global
import LLVM.AST.Type.Name                                      as LLVM
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Constant
import LLVM.AST.Type.Module

import Data.Typeable

-- Construct a new array by applying a function to each index. Each thread
-- processes multiple adjacent elements.
--
-- mkGenerate
--     :: forall genv sh e.
--        UID
--     -> Label
--     -> Env AccessGroundR genv
--     -> Arg genv (Out sh e)
--     -> Arg genv (Fun' (sh -> e))
--     -> LLVM Native (Module (KernelType genv))
-- mkGenerate uid name env array@(ArgArray _ (ArrayR shr _) sh _) (ArgFun fun)
--   = codeGenFunction uid "generate" (LLVM.Lam argTp "arg") $ do
--       extractEnv
--       let sh' = aprjParameters (shapeExpVars shr sh) gamma
--       workstealChunked shr workstealIndex workstealActiveThreads sh' $ \ix i -> do
--         r <- app1 (llvmOfFun1 fun gamma) ix
--         writeArray TypeInt gamma array i r
--   where
--     (argTp, extractEnv, workstealIndex, workstealActiveThreads, gamma) = bindHeaderEnv env
