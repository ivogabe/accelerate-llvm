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
import qualified System.Info                                        as Info
import System.IO.Unsafe
import Data.Array.Accelerate.LLVM.Target.ClangInfo
import Data.Text                                                    ( Text, unpack )
import Data.Array.Accelerate.LLVM.CodeGen.Monad                     ( CodeGen )
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop               ( putString, abort )

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
    _ <- putString (unpack msg ++ "\n")

    -- On Windows calling putString and llvm.trap consecutively causes
    -- the program to hang in an infinite loop, repeatedly printing newline characters.
    -- So instead of using llvm.trap, we call the abort function from the C standard library.
    -- This is also what llvm.trap would be lowered to if the target does not have a trap instruction.
    -- See: https://llvm.org/docs/LangRef.html#llvm-trap-intrinsic
    if Info.os == "mingw32"
      then abort
      else trap

