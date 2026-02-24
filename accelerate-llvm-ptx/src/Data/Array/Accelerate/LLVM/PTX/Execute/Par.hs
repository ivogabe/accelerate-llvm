{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.Execute.Par
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.Execute.Par (
  Par, evalPar, ptxStream, liftPar, spawnPar, block,
  cleanUpTouchLifetime, cleanUpTouchForeignPtr, cleanUpUnregisterHostPtr,
) where

import Data.Array.Accelerate.Lifetime

import Data.Array.Accelerate.LLVM.State

import Data.Array.Accelerate.LLVM.PTX.State
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Array.Accelerate.LLVM.PTX.Execute.Stream                ( Stream )
import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Event       as Event
import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Stream      as Stream

import qualified Foreign.CUDA.Driver.Stream                         as CUDA
import qualified Foreign.CUDA.Ptr                                   as CUDA
import qualified Foreign.CUDA.Driver                                as CUDA

import Foreign.ForeignPtr

import Control.Monad.Reader
import Control.Monad.State
import Control.Concurrent

newtype Par a = Par { runPar :: ReaderT Stream (StateT [CleanUp] (LLVM PTX)) a }
    deriving ( Functor, Applicative, Monad, MonadIO, MonadReader Stream, MonadState [CleanUp] )

-- CleanUp to be executed after the Par monad synchronises the CPU and GPU (via block)
data CleanUp where
  TouchLifetime :: Lifetime t -> CleanUp
  TouchForeignPtr :: ForeignPtr t -> CleanUp
  Unregister :: CUDA.HostPtr t -> CleanUp

-- | Evaluate a parallel computation
--
{-# INLINE evalPar #-}
evalPar :: Par a -> LLVM PTX a
evalPar p = do
  stream <- Stream.create
  result <- evalStateT (runReaderT (runPar (p <* block)) stream) []
  Stream.destroy stream
  return result

ptxStream :: Stream -> Stream
ptxStream = id

liftPar :: LLVM PTX a -> Par a
liftPar = Par . lift . lift

spawnPar :: Par () -> Par ()
spawnPar spawned = do
  target <- liftPar $ asks llvmTarget
  stream <- asks ptxStream
  event <- liftPar $ Event.waypoint stream
  _ <- liftIO $ forkIO $ evalPTX target $ evalPar $ do
    spawnedStream <- asks ptxStream
    liftIO $ Event.after event spawnedStream
    spawned
  return ()

cleanUpTouchLifetime :: Lifetime t -> Par ()
cleanUpTouchLifetime lifetime =
  modify' (TouchLifetime lifetime :)

cleanUpTouchForeignPtr :: ForeignPtr t -> Par ()
cleanUpTouchForeignPtr ptr =
  modify' (TouchForeignPtr ptr :)

cleanUpUnregisterHostPtr :: CUDA.HostPtr t -> Par ()
cleanUpUnregisterHostPtr hostPtr =
  modify' (Unregister hostPtr :)

runCleanUp :: Par ()
runCleanUp = do
  list <- get
  put []
  -- Run oldest clean up instruction first
  liftIO $ forM_ (reverse list) $ \case
    TouchLifetime lifetime -> touchLifetime lifetime
    TouchForeignPtr ptr -> touchForeignPtr ptr
    Unregister hostPtr -> void $ CUDA.unregisterArray hostPtr

-- Synchronises the CPU with the GPU. Blocks execution on the CPU until all
-- operations submitted to the GPU, from this Par instance, have been completed.
block :: Par ()
block = do
  stream <- ask
  liftIO $ CUDA.block stream
  runCleanUp

-- Implementation
-- --------------


{-instance Async PTX where
  type FutureR PTX = Future

  newtype Par PTX a = Par { runPar :: ReaderT ParState (LLVM PTX) a }
    deriving ( Functor, Applicative, Monad, MonadIO )

  {-# INLINEABLE new     #-}
  {-# INLINEABLE newFull #-}
  new       = Future <$> liftIO (newIORef (Empty (return ())))
  newFull v = Future <$> liftIO (newIORef (Full v))

  {-# INLINEABLE spawn #-}
  spawn m = do
    s' <- liftPar Stream.create
    r  <- localParState (const (s', Nothing)) m
    liftIO (Stream.destroy s')
    return r

  {-# INLINEABLE fork #-}
  fork m = do
    s' <- liftPar (Stream.create)
    () <- localParState (const (s', Nothing)) m
    liftIO (Stream.destroy s')

  -- When we call 'put' the actual work may not have been evaluated yet; get
  -- a new event in the current execution stream and once that is filled we can
  -- transition the IVar to Full.
  --
  {-# INLINEABLE put #-}
  put (Future ref) v = do
    stream <- asksParState ptxStream
    kernel <- asksParState ptxKernel
    event  <- liftPar (Event.waypoint stream)
    ready  <- liftIO  (Event.query event)
    let cleanupK = case kernel of
                     Just k -> touchLifetime k
                     Nothing -> return ()
    liftIO . atomicModifyIORef' ref $ \case
      Empty cleanup -> if ready then (Full v, ())
                                else (Pending event (cleanup >> cleanupK) v, ())
      _     -> internalError "multiple put"

  -- Get the value of Future. Since the actual cross-stream synchronisation
  -- happens on the device, we should never have to block/reschedule the main
  -- thread waiting on a value; if we get an empty IVar at this point, something
  -- has gone wrong.
  --
  {-# INLINEABLE get #-}
  get (Future ref) = do
    stream <- asksParState ptxStream
    liftIO  $ do
      ivar <- readIORef ref
      case ivar of
        Full v            -> return v
        Pending event cleanup v -> do
          ready <- Event.query event
          if ready
            then do
              writeIORef ref (Full v)
              cleanup
            else
              Event.after event stream
          return v
        Empty _         -> internalError "blocked on an IVar"

  {-# INLINEABLE block #-}
  block = liftIO . wait

  {-# INLINE liftPar #-}
  liftPar = Par . lift


-- | Block the calling _host_ thread until the value offered by the future is
-- available.
--
{-# INLINEABLE wait #-}
wait :: Future a -> IO a
wait (Future ref) = do
  ivar <- readIORef ref
  case ivar of
    Full v            -> return v
    Pending event cleanup v -> do
      Event.block event
      writeIORef ref (Full v)
      cleanup
      return v
    Empty _         -> internalError "blocked on an IVar"
-}

{-
{-# INLINEABLE putCleanup #-}
putCleanup :: HasCallStack => FutureR PTX a -> IO () -> a -> Par PTX ()
putCleanup (Future ref) cleanup v = do
  stream <- asksParState ptxStream
  kernel <- asksParState ptxKernel
  event  <- liftPar (Event.waypoint stream)
  ready  <- liftIO  (Event.query event)
  let cleanupK = case kernel of
                   Just k -> touchLifetime k
                   Nothing -> return ()
  liftIO . atomicModifyIORef' ref $ \case
    Empty cleanup2 -> if ready then (Full v, ())
                               else (Pending event (cleanup2 >> cleanup >> cleanupK) v, ())
    _     -> internalError "multiple put"

{-# INLINEABLE addCleanup #-}
addCleanup :: HasCallStack => FutureR PTX a -> IO () -> Par PTX ()
addCleanup (Future ref) cleanup = liftIO $ do
  toRunNow <- atomicModifyIORef' ref $ \case
    Full v -> (Full v, cleanup)
    Pending event cleanup2 v -> (Pending event (cleanup2 >> cleanup) v, return ())
    Empty cleanup2 -> (Empty (cleanup2 >> cleanup), return ())
  toRunNow
-}
