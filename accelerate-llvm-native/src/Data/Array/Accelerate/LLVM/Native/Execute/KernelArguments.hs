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
-- Module      : Data.Array.Accelerate.LLVM.Native.Execute.KernelArguments
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Execute.KernelArguments (prepareKernel, touchKernel) where

import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Array.Unique
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Lifetime
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.LLVM.CodeGen.Environment       ( MarshalArg, marshalScalarArg )
import Data.Array.Accelerate.LLVM.Native.Kernel
import Data.Array.Accelerate.LLVM.Native.Execute.Environment
import Data.Array.Accelerate.LLVM.Native.Execute.Kernel
import Data.Array.Accelerate.LLVM.Native.Execute.Marshal
import Data.Primitive.Vec

import Foreign.Ptr
import Foreign.ForeignPtr
import GHC.ForeignPtr
import Foreign.Marshal.Alloc
import Foreign.Storable
import Data.Typeable

prepareKernel :: forall env f. NativeEnv env -> NativeKernelMetadata f -> KernelFun NativeKernel f -> SArgs env f -> IO (Exists KernelCall)
prepareKernel env (NativeKernelMetadata envSize) fun args = do
  -- Allocate memory to store the header and the arguments to the function.
  -- The header takes 2 cache lines and the env take 'envSize' bytes.
  -- Align by 2 cache lines.
  --
  -- TODO: Should we add padding to the header to store it in 2 cache lines, or is 1 sufficient?
  -- Currently we pad it to 2 cache lines.
  --
  foreignPtr :: ForeignPtr () <- mallocPlainForeignPtrAlignedBytes (cacheLineSize * 2 + envSize) (cacheLineSize * 2)

  withForeignPtr foreignPtr $ \argPtr -> do
    -- putStrLn "Trying to launch kernel"

    -- Initialise 'worksteal index' to 0
    poke (castPtr argPtr) (0 :: Int32)

    -- Initialise 'active threads' to 0
    pokeElemOff (castPtr argPtr) 1 (0 :: Int32)

    let
      go :: forall kenv f'. Int -> OpenKernelFun NativeKernel kenv f' -> SArgs env f' -> IO (Exists KernelCall)
      go cursor (KernelFunBody (NativeKernel funLifetime _ _ _)) ArgsNil
        | cursor == cacheLineSize * 2 + envSize =
          return $ Exists $ KernelCall @kenv (unsafeGetValue funLifetime) foreignPtr
        | otherwise = internalError "Cursor and size do not match. prepareKernel and sizeOfEnv might be inconsistent."
      go cursor (KernelFunLam argR fun') (arg :>: args') = do
        let (align, size) = alignmentAndSizeOfArgument argR
        let aligned = makeAligned cursor align
        let ptr = plusPtr argPtr aligned
        unsafeWriteArg env argR ptr arg
        go (aligned + size) fun' args'

    go (cacheLineSize * 2) fun args

touchKernel :: forall env f. NativeEnv env -> KernelFun NativeKernel f -> SArgs env f -> IO ()
touchKernel env = go
  where
    go :: OpenKernelFun NativeKernel kenv f' -> SArgs env f' -> IO ()
    go (KernelFunBody (NativeKernel funLifetime _ _ _)) ArgsNil = touchLifetime funLifetime
    go (KernelFunLam argR fun) (arg :>: args) = do
      touchArg env argR arg
      go fun args

touchArg :: NativeEnv env -> KernelArgR t s -> SArg env t -> IO ()
touchArg env (KernelArgRbuffer _ _) (SArgBuffer _ var) = 
  let Buffer _ ua = prj (varIdx var) env
  in touchUniqueArray ua
touchArg _ _ _ = return ()

-- Writes the value of an argument to the arguments struct.
-- This operation is unsafe, as we write the pointer in case of a buffer
-- argument, and that pointer may be deallocated when this arguments struct
-- is used. The same issue can occur with the pointer to the function stored in
-- the KernelCall. To prevent that, one must call 'touchKernel' after working
-- with the KernelCall. That assures that all needed objects remain live.
--
unsafeWriteArg :: NativeEnv env -> KernelArgR t s -> Ptr (MarshalArg s) -> SArg env t -> IO ()
unsafeWriteArg env (KernelArgRbuffer _ _) ptr (SArgBuffer _ var) = do
  let Buffer _ ua = prj (varIdx var) env
  poke ptr (unsafeUniqueArrayPtr ua)
unsafeWriteArg env (KernelArgRscalar tp'@(SingleScalarType tp)) ptr (SArgScalar var)
  | SingleDict <- singleDict tp
  , Refl <- marshalScalarArg (SingleScalarType tp) = do
    let value = prjGroundVar (Var (GroundRscalar tp') (varIdx var)) env
    poke ptr value
unsafeWriteArg env (KernelArgRscalar (VectorScalarType (VectorType _ (tp :: SingleType u)))) ptr (SArgScalar var)
  | SingleDict <- singleDict tp = do
    let
      ptr' :: Ptr u
      ptr' = castPtr ptr
      value = prj (varIdx var) env
      go :: Int -> [u] -> IO ()
      go _ [] = return ()
      go i (v:vs) = do
        pokeElemOff ptr' i v
        go (i + 1) vs
    go 0 $ listOfVec value

cacheLineSize :: Int
cacheLineSize = 64
