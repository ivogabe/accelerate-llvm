{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.Execute.Environment
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.Execute.Environment (

  module Data.Array.Accelerate.AST.Environment,
  module Data.Array.Accelerate.LLVM.PTX.Execute.Environment,

) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Error

import Data.Array.Accelerate.LLVM.PTX.Execute.Buffer
import Data.Array.Accelerate.LLVM.PTX.Execute.Par
import Data.Array.Accelerate.LLVM.PTX.Execute.Event (Event)
import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Event as Event

import Data.IORef
import Control.Concurrent.MVar
import Control.Monad.Reader

type Gamma = Env Value

data Value t where
  ValueScalar
    :: !(ScalarType t) -> !t -> Value t
  ValueBuffer
    :: !(PTXBuffer t) -> Value (Buffer t)
  ValueSignal
    :: !PTXSignal -> Value Signal
  ValueSignalResolver
    :: !PTXSignal -> Value SignalResolver
  -- Note that a Ref could just become an IORef, but instead we make it an MVar
  -- here. If a Ref were an IORef, then we would need to call CUDA.block each
  -- time we read from a reference, which may potentially limit the amount of
  -- task parallelism. By using an MVar, each Ref already performs the
  -- host-side synchronisations, and we use signals (and their Events) mostly
  -- for the device-side synchronisations. At some points we will still need to
  -- use CUDA.block, but at least we do that less frequently.
  ValueRef
    :: !(MVar (Value t)) -> Value (Ref t)
  ValueOutputRef
    :: !(MVar (Value t)) -> Value (OutputRef t)

instance Distributes Value where
  reprIsSingle (ValueScalar tp _) = reprIsSingle tp
  reprIsSingle (ValueBuffer _) = Refl
  reprIsSingle (ValueSignal _) = Refl
  reprIsSingle (ValueSignalResolver _) = Refl
  reprIsSingle (ValueRef _) = Refl
  reprIsSingle (ValueOutputRef _) = Refl

  pairImpossible (ValueScalar tp _) = pairImpossible tp
  unitImpossible (ValueScalar tp _) = unitImpossible tp

-- TODO: Use manual reference counting, instead of Lifetimes with destructors?
-- We should then first make reference counting explicit in UniformSchedule,
-- since we would otherwise need to duplicate that logic in all backends.
-- Applies to PTXSignal and PTXBuffer
newtype PTXSignal = PTXSignal Event

baseToValues :: BasesR t -> t -> Par (Distribute Value t)
-- Unit
baseToValues TupRunit _ = return ()
-- Scalar input argument
baseToValues (TupRsingle BaseRsignal `TupRpair` TupRsingle (BaseRref (GroundRscalar tp))) (Signal mvar, Ref input) = do
  event <- liftPar Event.create
  ref <- liftIO $ newEmptyMVar

  -- Asynchronously wait on the signal, and fill the ptx signal / event and reference when ready.
  spawnPar $ do
    liftIO $ readMVar mvar
    value <- liftIO $ readIORef input
    liftIO $ putMVar ref $ ValueScalar tp value
    stream <- asks ptxStream
    liftIO $ Event.record event stream

  return (ValueSignal $ PTXSignal event, ValueRef ref)
-- Buffer input argument
baseToValues (TupRsingle BaseRsignal `TupRpair` TupRsingle (BaseRref (GroundRbuffer tp))) (Signal mvar, Ref input) = do
  event <- liftPar Event.create
  ref <- liftIO $ newEmptyMVar

  -- Asynchronously wait on the signal, and fill the ptx signal / event and reference when ready.
  spawnPar $ do
    liftIO $ readMVar mvar
    buffer <- liftIO $ readIORef input
    ptxBuffer <- copyToDevice tp buffer
    liftIO $ putMVar ref $ ValueBuffer ptxBuffer
    stream <- asks ptxStream
    liftIO $ Event.record event stream

  return (ValueSignal $ PTXSignal event, ValueRef ref)
-- Scalar output argument
baseToValues (TupRsingle BaseRsignalResolver `TupRpair` TupRsingle (BaseRrefWrite (GroundRscalar _))) (SignalResolver mvar, OutputRef output) = do
  event <- liftPar Event.create
  ref <- liftIO $ newEmptyMVar

  spawnPar $ do
    stream <- asks ptxStream
    liftIO $ Event.after event stream
    block
    v <- liftIO $ readMVar ref
    let value = case v of
          ValueScalar _ x -> x
          _ -> internalError "Scalar impossible"
    liftIO $ writeIORef output value
    liftIO $ putMVar mvar ()

  return (ValueSignalResolver $ PTXSignal event, ValueOutputRef ref)
-- Buffer output argument
baseToValues (TupRsingle BaseRsignalResolver `TupRpair` TupRsingle (BaseRrefWrite (GroundRbuffer tp))) (SignalResolver mvar, OutputRef output) = do
  event <- liftPar Event.create
  ref <- liftIO $ newEmptyMVar

  spawnPar $ do
    stream <- asks ptxStream
    liftIO $ Event.after event stream
    block
    b <- liftIO $ readMVar ref
    let ptxBuffer = case b of
          ValueBuffer x -> x
          _ -> internalError "Buffer impossible"
    buffer <- copyToHost tp ptxBuffer
    liftIO $ writeIORef output buffer
    liftIO $ putMVar mvar ()

  return (ValueSignalResolver $ PTXSignal event, ValueOutputRef ref)
-- Pair
baseToValues (TupRpair t1 t2) (v1, v2) = do
  x1 <- baseToValues t1 v1
  x2 <- baseToValues t2 v2
  return (x1, x2)
baseToValues _ _ = internalError "Unexpected types in the input or output of an Acc function"
