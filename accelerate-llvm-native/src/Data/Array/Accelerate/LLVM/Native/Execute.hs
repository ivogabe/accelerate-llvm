{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE ViewPatterns             #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Execute
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Execute (

) where

import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.AST.Execute
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Analysis.Hash.Schedule.Uniform
import Data.Array.Accelerate.Interpreter                ( evalExp, EvalArrayInstr(..) )
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Lifetime
import Data.Array.Accelerate.LLVM.Native.Kernel
import Data.Array.Accelerate.LLVM.Native.Link.Schedule

import Control.Exception
import Data.String
import Data.Int
import Data.Word
import Data.IORef
import Data.Typeable
import Data.Maybe
import Text.Read (readMaybe)
import Language.Haskell.TH.Syntax
import qualified Crypto.Hash.XKCP as Hash
import Control.Concurrent
import Foreign.Ptr
import Foreign.StablePtr
import Foreign.ForeignPtr
import Foreign.Storable
import GHC.Conc
import System.IO
import System.IO.Unsafe ( unsafePerformIO )
import LLVM.AST.Type.Representation
import System.Environment

instance Execute UniformScheduleFun NativeKernel where
  data Linked UniformScheduleFun NativeKernel t = NativeLinked !(NativeProgram) !(UniformScheduleFun NativeKernel () t)

  linkAfunSchedule schedule =
    NativeLinked
      (linkSchedule (hashUniformScheduleFun schedule) schedule)
      schedule
  executeAfunSchedule _ (NativeLinked (NativeProgram fun size lifetimes imports offset) schedule)
    | not rtsSupportsBoundThreads = error
      $ "\nCannot run Accelerate programs without GHC's multi-threaded runtime\n\n"
      ++ "In your .cabal file, add -threaded to ghc-options in the section of your executable:\n"
      ++ "  ghc-options: -threaded\n\n"
      ++ "For more information, see:\nhttps://downloads.haskell.org/ghc/latest/docs/users_guide/phases.html#ghc-flag-threaded \n"
    | otherwise = prepareProgram schedule start final
    where
      start :: IO (Ptr Int8, Int)
      start = do
        -- Create an MVar, which the C runtime will fill when the program is finished.
        -- The Haskell side will keep the program function and kernels alive until the
        -- MVar is filled, by performing a touchLifetime on all lifetimes
        -- when the MVar is filled.
        -- This happens in 'destructWhen' from a separate thread.
        destructorMVar <- newEmptyMVar
        sp <- newStablePtrPrimMVar destructorMVar
        forkIO $ destructWhen destructorMVar (Exists fun : lifetimes)
        -- Allocate space for the program imports, arguments and local state
        program <- runtimeProgramAlloc (fromIntegral size) (castPtr $ unsafeGetPtrFromLifetimeFunPtr fun) sp
        -- Initialize the struct with the imports
        imports program
        -- 'prepareProgram' will initialize struct with the arguments of the function
        return (program, offset)
      final :: Ptr Int8 -> IO ()
      final program = do
        -- All imports and arguments are placed in the struct, we can start the program
        runtimeSchedule defaultRuntimeWorkers program 0
        runtimeProgramRelease program

destructWhen :: MVar () -> [Exists Lifetime] -> IO ()
destructWhen mvar list = do
  readMVar mvar
  mapM_ (\(Exists l) -> touchLifetime l) list

prepareProgram
  :: UniformScheduleFun NativeKernel env f
  -> IO (Ptr Int8, Int)
  -> (Ptr Int8 -> IO ())
  -> IOFun f
prepareProgram (Slam lhs f) accum final =
  \x -> prepareProgram f (accum >>= write lhs x) final
  where
    write :: BLeftHandSide s env env' -> s -> (Ptr Int8, Int) -> IO (Ptr Int8, Int)
    write (LeftHandSideWildcard _) _ ptrCursor = return ptrCursor
    write (LeftHandSideSingle (BaseRground _)) _ _ = internalError "Ground inputs not allowed. These should be passed in a Ref"
    -- An input value
    write (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle (BaseRref tp)) (Signal mvar, Ref ioref) (ptr, cursor) = do
      poke (plusPtr ptr cursor1) (0 :: Word)
      case tp of
        -- Intialize reference count of Ref with 1.
        -- Number is shifted by one bit.
        -- The last bit denotes that this is an unfilled Ref,
        -- hence we get 0b11 = 3.
        -- See: [reference counting for Ref]
        GroundRbuffer _ -> do
          poke (plusPtr ptr cursor2) (3 :: Word)
        _ -> return ()
      -- In a separate thread, wait on the MVar and resolve the signal
      runtimeProgramRetain ptr
      _ <- forkIO $ do
        readMVar mvar
        value <- readIORef ioref
        pokeGround tp (plusPtr ptr cursor2) value
        runtimeSignalResolve defaultRuntimeWorkers (plusPtr ptr cursor1)
        runtimeProgramRelease ptr
      return (ptr, cursor2 + sz)
      where
        cursor1 = makeAligned cursor (sizeOf (0 :: Int))
        cursor2 = makeAligned (cursor1 + sizeOf (0 :: Int)) a
        (sz, a) = groundSizeAlignment tp
    -- An output value
    write (LeftHandSideSingle BaseRsignalResolver `LeftHandSidePair` LeftHandSideSingle (BaseRrefWrite tp)) (SignalResolver mvar, OutputRef ioref) (ptr, cursor) = do
      localMVar <- newEmptyMVar
      sp <- newStablePtrPrimMVar localMVar
      poke (plusPtr ptr cursor1) sp
      runtimeProgramRetain ptr
      case tp of
        -- Intialize reference count of OutputRef with 1.
        -- Number is shifted by one bit.
        -- See: [reference counting for Ref]
        GroundRbuffer _ -> do
          poke (plusPtr ptr cursor2) (2 :: Word)
        _ -> return ()
      _ <- forkIO $ do
        readMVar localMVar
        value <- peekGround tp (plusPtr ptr cursor2)
        writeIORef ioref value
        runtimeProgramRelease ptr
        putMVar mvar ()
      return (ptr, cursor2 + sz)
      where
        cursor1 = makeAligned cursor (sizeOf (0 :: Int))
        cursor2 = makeAligned (cursor1 + sizeOf (0 :: Int)) a
        (sz, a) = groundSizeAlignment tp
    write (LeftHandSidePair l1 l2) (v1, v2) ptrCursor = do
      ptrCursor1 <- write l1 v1 ptrCursor
      write l2 v2 ptrCursor1
    write _ _ _ = internalError "Unexpected LeftHandSide. Does the program have a Signal without Ref, SignalResolver without RefWrite, or the other way around?"
prepareProgram (Sbody _) accum final = do
  (ptr, _) <- accum
  final ptr

pokeGround :: GroundR a -> Ptr Int8 -> a -> IO ()
pokeGround (GroundRbuffer _) dest (Buffer fp) =
  withForeignPtr fp $ \ptr ->
    runtimeRefWriteBuffer (castPtr dest) (castPtr ptr)
pokeGround (GroundRscalar (SingleScalarType tp)) dest value
  | SingleDict <- singleDict tp = do
    poke (castPtr dest) value
pokeGround (GroundRscalar (VectorScalarType _)) _ _ = internalError "Not yet supported: VectorScalarType as input to an Acc function"

peekGround :: GroundR a -> Ptr Int8 -> IO a
peekGround (GroundRbuffer _) dest = do
  ptr <- peek $ castPtr dest
  bufferFromPtr ptr
peekGround (GroundRscalar (SingleScalarType tp)) dest
  | SingleDict <- singleDict tp = do
    peek $ castPtr dest
peekGround (GroundRscalar (VectorScalarType _)) _ = internalError "Not yet supported: VectorScalarType as output to an Acc function"

groundSizeAlignment :: GroundR a -> (Int, Int)
groundSizeAlignment (GroundRbuffer _) = (sizeOf (0 :: Int), sizeOf (0 :: Int))
groundSizeAlignment (GroundRscalar (SingleScalarType tp)) = (s, s)
  where s = bytesElt $ TupRsingle $ SingleScalarType tp
groundSizeAlignment (GroundRscalar (VectorScalarType (VectorType n tp))) = (n * s, s)
  where s = bytesElt $ TupRsingle $ SingleScalarType tp

{-# NOINLINE defaultRuntimeWorkers #-}
defaultRuntimeWorkers :: Ptr Int8
defaultRuntimeWorkers = unsafePerformIO $ threadCount >>= runtimeStartWorkers

foreign import ccall unsafe "accelerate_start_workers" runtimeStartWorkers :: Word64 -> IO (Ptr Int8)
foreign import ccall unsafe "accelerate_signal_resolve" runtimeSignalResolve :: Ptr Int8 -> Ptr Int8 -> IO ()
foreign import ccall unsafe "accelerate_program_alloc" runtimeProgramAlloc :: Word64 -> Ptr Int8 -> StablePtr PrimMVar -> IO (Ptr Int8)
foreign import ccall unsafe "accelerate_program_retain" runtimeProgramRetain :: Ptr Int8 -> IO ()
foreign import ccall unsafe "accelerate_program_release" runtimeProgramRelease :: Ptr Int8 -> IO ()
foreign import ccall unsafe "accelerate_schedule" runtimeSchedule :: Ptr Int8 -> Ptr Int8 -> Word32 -> IO ()
foreign import ccall unsafe "accelerate_ref_write_buffer" runtimeRefWriteBuffer :: Ptr (Ptr Int8) -> Ptr Int8 -> IO ()

threadCount :: IO Word64
threadCount = do
  nproc <- getNumProcessors
  menv  <- (readMaybe =<<) <$> lookupEnv "ACCELERATE_LLVM_NATIVE_THREADS"

  return $ fromIntegral $ fromMaybe nproc menv
