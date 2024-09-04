{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Execute.Kernel
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Execute.Kernel where

import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Array.Unique
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.LLVM.CodeGen.Environment       ( MarshalArg, marshalScalarArg )
import Data.Array.Accelerate.LLVM.Native.Kernel
import Data.Array.Accelerate.LLVM.Native.Execute.Marshal
import Data.Primitive.Vec

import Foreign.Ptr
import Foreign.ForeignPtr
import GHC.ForeignPtr
import Foreign.Marshal.Alloc
import Foreign.Storable
import Data.Typeable

foreign import ccall "dynamic"  
  callKernelPtr :: FunPtr (Ptr () -> IO Bool) -> Ptr () -> IO Bool

data KernelCall env where
  KernelCall :: !(FunPtr (KernelType env)) -> !(ForeignPtr ()) -> KernelCall env

-- Executes a kernel. Returns True if all work has definitely been finished.
-- There may be multiple threads that return true. It is guaranteed that at
-- least one thread returns True.
--
callKernel :: FunPtr (KernelType env) -> (ForeignPtr ()) -> IO Bool
callKernel funPtr foreignPtr =
  withForeignPtr foreignPtr $ \argPtr ->
      callKernelPtr (castFunPtr funPtr) (castPtr argPtr)
