{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE CPP                  #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UnboxedTuples        #-}
{-# LANGUAGE UndecidableInstances #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Execute.Sleep
-- Copyright   : [2018..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Execute.Environment
  ( module Data.Array.Accelerate.AST.Environment
  , NativeEnv, Values(..), ValueR, Value(..), ValuesIOFun
  , prj, prjVars, prjGroundVar, values, groundValue
  , push
  ) where

import Data.Array.Accelerate.AST.Environment hiding ( Val, prj, push )
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.LLVM.Native.Execute.Scheduler
import Unsafe.Coerce
import System.IO.Unsafe
import Control.Concurrent
import Control.Concurrent.MVar

type family ValueR e where
  ValueR Signal         = NativeSignal
  ValueR SignalResolver = NativeSignal
  ValueR e              = e

newtype Value e = Value (ValueR e)

data Values e where
  ValuesUnit   :: Values ()
  ValuesPair   :: !(Values a) -> !(Values b) -> Values (a, b)
  ValuesSingle :: !(Value e) -> Values e

type NativeEnv = Env Value

type family ValuesIOFun f where
  ValuesIOFun (a -> b) = Values a -> ValuesIOFun b
  ValuesIOFun t        = IO t

prj :: Idx env t -> NativeEnv env -> ValueR t
prj idx env
  | Value e <- prj' idx env = e

prjVars :: Vars s env t -> NativeEnv env -> Values t
prjVars TupRunit         _   = ValuesUnit
prjVars (TupRpair v1 v2) env = prjVars v1 env `ValuesPair` prjVars v2 env
prjVars (TupRsingle var) env = ValuesSingle $ Value $ prj (varIdx var) env

-- For ground types, 'Value t ~ t'
prjGroundVar :: GroundVar env t -> NativeEnv env -> t
prjGroundVar (Var _ idx) env = unsafeCoerce $ prj idx env

values :: Workers -> BasesR t -> t -> Values t
values workers (TupRpair t1 t2) (v1, v2) = values workers t1 v1 `ValuesPair` values workers t2 v2
values workers TupRunit         ()       = ValuesUnit
values workers (TupRsingle tp)  v        = case tp of
  -- For ground types, 'Value t ~ t'
  BaseRground _   -> ValuesSingle $ Value $ unsafeCoerce v
  BaseRref _      -> ValuesSingle $ Value v
  BaseRrefWrite _ -> ValuesSingle $ Value v
  BaseRsignal
    | Signal mvar <- v -> unsafePerformIO $ do
      signal <- newSignal
      _ <- forkIO (readMVar mvar >> resolveSignal workers signal) -- NIET DEZE
      return $ ValuesSingle $ Value signal
  BaseRsignalResolver
    | SignalResolver mvar <- v -> unsafePerformIO $ do
      signal <- newSignal
      scheduleAfter workers [signal] $ Job $ \_ -> putMVar mvar ()
      return $ ValuesSingle $ Value signal

-- For ground types, 'Value t ~ t'
groundValue :: GroundR t -> t -> Value t
groundValue _ v = Value $ unsafeCoerce v

push :: NativeEnv env -> (LeftHandSide s t env env', Values t) -> NativeEnv env'
push env (LeftHandSideWildcard _, _)              = env
push env (LeftHandSideSingle _  , ValuesSingle a) = env `Push` a
push env (LeftHandSidePair l1 l2, ValuesPair a b) = push env (l1, a) `push` (l2, b)
push _ _ = internalError "Tuple mismatch"
