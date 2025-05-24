{-# LANGUAGE FlexibleInstances          #-}
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
  Par, evalPar, ptxStream, liftPar, spawnPar
) where

import Data.Array.Accelerate.LLVM.State

import Data.Array.Accelerate.LLVM.PTX.State
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Array.Accelerate.LLVM.PTX.Execute.Stream                ( Stream )
import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Event       as Event
import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Stream      as Stream

import Control.Monad.Reader
import Control.Monad.State
import Control.Concurrent

newtype Par a = Par { runPar :: ReaderT Stream (LLVM PTX) a }
    deriving ( Functor, Applicative, Monad, MonadIO, MonadReader Stream, MonadState PTX )

-- | Evaluate a parallel computation
--
{-# INLINE evalPar #-}
evalPar :: Par a -> LLVM PTX a
evalPar p =
  Stream.withStream $ \s -> runReaderT (runPar p) s

ptxStream :: Stream -> Stream
ptxStream = id

liftPar :: LLVM PTX a -> Par a
liftPar = Par . lift

spawnPar :: Par () -> Par ()
spawnPar spawned = do
  target <- gets llvmTarget
  stream <- asks ptxStream
  event <- liftPar $ Event.waypoint stream
  _ <- liftIO $ forkIO $ evalPTX target $ evalPar $ do
    spawnedStream <- asks ptxStream
    liftIO $ Event.after event spawnedStream
    spawned
  return ()

-- Implementation
-- --------------


{-instance Async PTX where
  type FutureR PTX = Future

  newtype Par PTX a = Par { runPar :: ReaderT ParState (LLVM PTX) a }
    deriving ( Functor, Applicative, Monad, MonadIO, MonadReader ParState, MonadState PTX )

  {-# INLINEABLE new     #-}
  {-# INLINEABLE newFull #-}
  new       = Future <$> liftIO (newIORef Empty)
  newFull v = Future <$> liftIO (newIORef (Full v))

  {-# INLINEABLE spawn #-}
  spawn m = do
    s' <- liftPar Stream.create
    r  <- local (const (s', Nothing)) m
    liftIO (Stream.destroy s')
    return r

  {-# INLINEABLE fork #-}
  fork m = do
    s' <- liftPar (Stream.create)
    () <- local (const (s', Nothing)) m
    liftIO (Stream.destroy s')

  -- When we call 'put' the actual work may not have been evaluated yet; get
  -- a new event in the current execution stream and once that is filled we can
  -- transition the IVar to Full.
  --
  {-# INLINEABLE put #-}
  put (Future ref) v = do
    stream <- asks ptxStream
    kernel <- asks ptxKernel
    event  <- liftPar (Event.waypoint stream)
    ready  <- liftIO  (Event.query event)
    liftIO . modifyIORef' ref $ \case
      Empty -> if ready then Full v
                        else Pending event kernel v
      _     -> internalError "multiple put"

  -- Get the value of Future. Since the actual cross-stream synchronisation
  -- happens on the device, we should never have to block/reschedule the main
  -- thread waiting on a value; if we get an empty IVar at this point, something
  -- has gone wrong.
  --
  {-# INLINEABLE get #-}
  get (Future ref) = do
    stream <- asks ptxStream
    liftIO  $ do
      ivar <- readIORef ref
      case ivar of
        Full v            -> return v
        Pending event k v -> do
          ready <- Event.query event
          if ready
            then do
              writeIORef ref (Full v)
              case k of
                Just f  -> touchLifetime f
                Nothing -> return ()
            else
              Event.after event stream
          return v
        Empty           -> internalError "blocked on an IVar"

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
    Pending event k v -> do
      Event.block event
      writeIORef ref (Full v)
      case k of
        Just f  -> touchLifetime f
        Nothing -> return ()
      return v
    Empty           -> internalError "blocked on an IVar"
-}
