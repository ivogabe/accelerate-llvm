{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Target
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Target (

  module Data.Array.Accelerate.LLVM.Target,
  module Data.Array.Accelerate.LLVM.Native.Target,
  nativeTargetTriple,
  nativeCPUName,

) where

-- accelerate
import Data.Array.Accelerate.LLVM.Native.Link.Cache                 ( LinkCache )
import Data.Array.Accelerate.LLVM.Target                            ( Target(..) )
import Data.Array.Accelerate.LLVM.CodeGen.Intrinsic
import Data.Array.Accelerate.LLVM.CodeGen.Exp                       ( trap )


import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic (liftInt)
-- standard library
import Data.ByteString                                              ( ByteString )
import Data.ByteString.Short                                        ( ShortByteString )
import System.IO.Unsafe
import Data.Array.Accelerate.LLVM.Target.ClangInfo
import Data.Text                                                    ( Text, unpack )
import Data.Array.Accelerate.LLVM.CodeGen.Monad                     ( CodeGen )
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop               ( putString, putInt, putchar, fflush, exit )

-- | Native machine code JIT execution target
--
data Native = Native
  { linkCache     :: !LinkCache
  }

instance Target Native where
  targetTriple     = Just nativeTargetTriple
  targetDataLayout = Nothing  -- LLVM will fill it in just fine for CPU targets

instance Intrinsic Native where
  trapWithMessage msg = do
    _ <- putString ((unpack msg) ++ "\n")
    -- _ <- putInt (liftInt 65)
    -- _ <- putchar (liftInt 65)
    _ <- fflush
    exit 1
    -- trap
