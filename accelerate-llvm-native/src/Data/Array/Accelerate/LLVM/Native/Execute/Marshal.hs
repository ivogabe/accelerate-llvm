{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Execute.Marshal
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Execute.Marshal
  ( sizeOfEnv, alignmentAndSizeOfArgument, makeAligned )
  where

-- accelerate
import Data.Array.Accelerate.Array.Unique
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.Type

-- libraries
import Data.Primitive.Vec
import Data.Bits
import Foreign.Ptr
import Foreign.Storable
import qualified Foreign.LibFFI                                 as FFI

marshalInt :: Int -> FFI.Arg
marshalInt = $( case finiteBitSize (undefined::Int) of
                    32 -> [| FFI.argInt32 . fromIntegral |]
                    64 -> [| FFI.argInt64 . fromIntegral |]
                    _  -> error "I don't know what architecture I am" )

marshalBuffer :: Buffer t -> FFI.Arg
marshalBuffer (Buffer _ ua) = FFI.argPtr $ unsafeUniqueArrayPtr ua

sizeOfEnv :: KernelFun kernel f -> Int
sizeOfEnv = sizeOfEnv' 0

sizeOfEnv' :: Int -> OpenKernelFun kernel env f -> Int
sizeOfEnv' cursor (KernelFunLam argR fun)
  | (align, size) <- alignmentAndSizeOfArgument argR
  = sizeOfEnv' (makeAligned cursor align + size) fun
sizeOfEnv' cursor (KernelFunBody _) = cursor

alignmentAndSizeOfArgument :: forall s t. KernelArgR s t -> (Int, Int)
alignmentAndSizeOfArgument = \case
  KernelArgRbuffer _ _ -> go @(Ptr ())
  KernelArgRscalar (SingleScalarType tp)
    | SingleDict <- singleDict tp -> go @t
  KernelArgRscalar (VectorScalarType (VectorType n (tp :: SingleType u)))
    | SingleDict <- singleDict tp
    , (align, size) <- go @u
    -> (nextPowerOfTwo $ n * align, n * size)
  where
    go :: forall a. Storable a => (Int, Int)
    go = (alignment (undefined :: a), sizeOf (undefined :: a))

makeAligned :: Int -> Int -> Int
makeAligned cursor align = cursor + m
  where
    m = -cursor `mod` align

-- Rounds a number up to the next power of 2
nextPowerOfTwo :: Int -> Int
nextPowerOfTwo x = 1 `shiftL` (finiteBitSize (0 :: Int) - countLeadingZeros (x - 1))
