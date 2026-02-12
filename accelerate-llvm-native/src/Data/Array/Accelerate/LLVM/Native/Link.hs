{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Link
-- Copyright   : [2017..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Link (

  module Data.Array.Accelerate.LLVM.Native.Link,
  {-ExecutableR(..),-} FunctionTable(..), Function, ObjectCode,

) where

import Data.Array.Accelerate.Lifetime

import Data.Array.Accelerate.LLVM.State

import Data.Array.Accelerate.LLVM.Native.Target
import Data.Array.Accelerate.LLVM.Native.Compile

import Data.Array.Accelerate.LLVM.Native.Link.Cache
import Data.Array.Accelerate.LLVM.Native.Link.Object
import Data.Array.Accelerate.LLVM.Native.Link.Runtime

import Control.Monad.Reader
import Prelude                                                      hiding ( lookup )
import Foreign.Ptr
import Data.Coerce (coerce)

-- | Link to the generated shared object file, creating function pointers for
-- every kernel's entry point.
--
link :: ObjectR f -> LLVM Native (Lifetime (FunPtr f))
link (ObjectR uid nm _ so) = do
  cache <- asks linkCache
  fun <- liftIO $ dlsym uid cache (loadSharedObject nm so)
  return $! castLifetimeFunPtr fun

castLifetimeFunPtr :: Lifetime (FunPtr f) -> Lifetime (FunPtr g)
castLifetimeFunPtr = coerce
