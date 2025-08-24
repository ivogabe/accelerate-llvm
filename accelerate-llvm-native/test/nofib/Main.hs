-- |
-- Module      : nofib-llvm-native
-- Copyright   : [2017..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
--
-- Portability : non-portable (GHC extensions)
{-# LANGUAGE TypeApplications #-}
module Main where

import Data.Array.Accelerate.Test.NoFib
import Data.Array.Accelerate.LLVM.Native

main :: IO ()
main = nofib runN
