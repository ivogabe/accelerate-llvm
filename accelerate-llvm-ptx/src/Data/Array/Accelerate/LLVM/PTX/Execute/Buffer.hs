{-# LANGUAGE OverloadedStrings #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.Execute.Buffer
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.Execute.Buffer where

import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Lifetime

import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.PTX.Target                        ( PTX(..) )
import Data.Array.Accelerate.LLVM.PTX.Execute.Stream
import Data.Array.Accelerate.LLVM.PTX.Execute.Par

import Foreign.CUDA.Driver.Error
import qualified Foreign.CUDA.Ptr                                   as CUDA
import qualified Foreign.CUDA.Driver                                as CUDA
import qualified Foreign.CUDA.Driver.Stream                         as CUDA

import Control.Exception
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Text.Lazy.Builder
import Formatting
import Foreign.Ptr
import Foreign.ForeignPtr

data PTXBuffer t = PTXBuffer !Int !(Lifetime (CUDA.DevicePtr t))

mallocDevice :: ScalarType t -> Int -> Par (PTXBuffer t)
mallocDevice tp size = do
  let byteSize = bytesElt (TupRsingle tp) * size
  array <- liftIO $ CUDA.mallocArray byteSize
  lifetime <- liftIO $ newLifetime $ CUDA.castDevPtr (array :: CUDA.DevicePtr Word8)
  liftIO $ addFinalizer lifetime $ CUDA.free array
  return $ PTXBuffer size lifetime

copyToDevice :: ScalarType t -> Buffer t -> Par (PTXBuffer t)
copyToDevice tp buffer@(Buffer hostPtr) = do
  byteSize <- liftIO $ withForeignPtr hostPtr (memoryByteSize . castPtr)
  devicePtr <- liftIO (CUDA.mallocArray $ fromIntegral byteSize)
  stream <- asks ptxStream
  hostPtr1 <- liftIO $ withForeignPtr hostPtr (return . castPtr)
  hostPtr2 <- liftIO $ CUDA.registerArray [] (fromIntegral byteSize) hostPtr1
  liftIO $ CUDA.pokeArrayAsync (fromIntegral byteSize) hostPtr2 devicePtr (Just stream)

  -- Call 'CUDA.unregisterArray hostPtr2' when we next block (sync CPU with GPU)
  cleanUpUnregisterHostPtr hostPtr2
  -- Same for touchForeignPtr hostPtr
  cleanUpTouchForeignPtr hostPtr

  lifetime <- liftIO $ newLifetime $ CUDA.castDevPtr (devicePtr :: CUDA.DevicePtr Word8)
  liftIO $ addFinalizer lifetime $ CUDA.free devicePtr
  let size = fromIntegral byteSize `div` bytesElt (TupRsingle tp)
  return $ PTXBuffer size lifetime

copyToHost :: ScalarType t -> PTXBuffer t -> Par (Buffer t)
copyToHost tp (PTXBuffer size lifetime) = do
  let devicePtr1 = unsafeGetValue lifetime
  let devicePtr2 = CUDA.castDevPtr devicePtr1 :: CUDA.DevicePtr Word8
  let byteSize = bytesElt (TupRsingle tp) * size
  buffer@(Buffer hostPtr) <- unsafeFreezeBuffer <$> liftIO (newBuffer tp size)
  hostPtr1 <- liftIO $ withForeignPtr hostPtr (return . castPtr)
  hostPtr2 <- liftIO $ CUDA.registerArray [] (fromIntegral byteSize) hostPtr1
  stream <- asks ptxStream
  liftIO $ CUDA.peekArrayAsync (fromIntegral byteSize) devicePtr2 hostPtr2 (Just stream)

  -- Call 'CUDA.unregisterArray hostPtr2' when we next block (sync CPU with GPU)
  cleanUpUnregisterHostPtr hostPtr2
  -- Same for touchForeignPtr hostPtr
  cleanUpTouchForeignPtr hostPtr
  -- And touchLifetime lifetime
  cleanUpTouchLifetime lifetime

  return buffer

readFromDevice :: ScalarType t -> PTXBuffer t -> Int -> Par t
readFromDevice tp (PTXBuffer size lifetime) idx
  | idx >= size || idx < 0 = boundsError "Index outside of bounds, when evaluating a host-side expression (for instance a condition in an array-level if-then-else or the size of an array)"
  | ScalarDict <- scalarDict tp = do
    let devicePtr1 = unsafeGetValue lifetime `CUDA.advanceDevPtr` idx
    let devicePtr2 = CUDA.castDevPtr devicePtr1 :: CUDA.DevicePtr Word8
    let byteSize = bytesElt (TupRsingle tp)
    buffer@(Buffer hostPtr) <- unsafeFreezeBuffer <$> liftIO (newBuffer tp size)
    hostPtr1 <- liftIO $ withForeignPtr hostPtr (return . castPtr)
    hostPtr2 <- liftIO $ CUDA.registerArray [] (fromIntegral byteSize) hostPtr1
    stream <- asks ptxStream
    liftIO $ CUDA.peekArrayAsync (fromIntegral byteSize) devicePtr2 hostPtr2 (Just stream)

    block

    liftIO $ CUDA.unregisterArray hostPtr2
    liftIO $ touchForeignPtr hostPtr
    liftIO $ touchLifetime lifetime

    return $! indexBuffer tp buffer 0
