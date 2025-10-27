-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.Link.Object
-- Copyright   : [2017..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.Link.Object
  where

import Data.Array.Accelerate.Lifetime
import Data.ByteString.Short.Char8                                  ( ShortByteString, unpack )
import Data.List
import Formatting
import qualified Foreign.CUDA.Driver                                as CUDA

data KernelObject = KernelObject
  { kernelObjName            :: {-# UNPACK #-} !ShortByteString
  , kernelObjFun             :: {-# UNPACK #-} !CUDA.Fun
  , kernelObjSharedMemBytes  :: {-# UNPACK #-} !Int
  , kernelObjThreadBlockSize :: {-# UNPACK #-} !Int
  , kernelObjThreadBlocks    :: (Int -> Int)
  }

-- | Object code consists of executable code in the device address space
--
type ObjectCode = Lifetime CUDA.Module

