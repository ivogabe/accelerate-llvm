{-# OPTIONS_GHC -Wno-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.Foreign
-- Copyright   : [2016..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.Foreign (

  -- Foreign functions
  ForeignAcc(..), ForeignAfun, ForeignArg,
  ForeignExp(..),

  -- useful re-exports
  LLVM,
  PTX(..),
  module Data.Array.Accelerate.LLVM.Foreign

) where

import qualified Data.Array.Accelerate.Sugar.Foreign                as S

import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.CodeGen.Sugar

import Data.Array.Accelerate.LLVM.Foreign
import Data.Array.Accelerate.LLVM.PTX.Operation
import Data.Array.Accelerate.LLVM.PTX.Target

import Data.Typeable


instance CompileForeignExp PTX where
  {- foreignAcc (ff :: asm (a -> b))
    | Just Refl        <- eqT @asm @ForeignAcc
    , ForeignAcc _ asm <- ff = Just asm
    | otherwise              = Nothing -}

  foreignExp (ff :: asm (x -> y))
    | Just Refl        <- eqT @asm @ForeignExp
    , ForeignExp _ asm <- ff = Just asm
    | otherwise              = Nothing

{- instance S.Foreign ForeignAcc where
  strForeign (ForeignAcc s _) = s -}

instance S.Foreign ForeignExp where
  strForeign (ForeignExp s _) = s


-- Foreign functions in the PTX backend.
--
{- data ForeignAcc f where
  ForeignAcc :: String
             -> (a -> Par PTX (Future b))
             -> ForeignAcc (a -> b) -}

-- Foreign expressions in the PTX backend.
--
data ForeignExp f where
  ForeignExp :: String
             -> IRFun1 PTX (x -> y)
             -> ForeignExp (x -> y)
