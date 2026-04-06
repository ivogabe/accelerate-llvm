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
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Profile

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic (liftInt)
-- standard library
import Data.ByteString                                              ( ByteString )
import Data.ByteString.Short                                        ( ShortByteString )
import qualified System.Info                                        as Info
import System.IO.Unsafe
import Data.Array.Accelerate.LLVM.Target.ClangInfo
import Data.Text                                                    ( Text, unpack )
import Data.Array.Accelerate.LLVM.CodeGen.Monad                     ( CodeGen )
import Control.Monad                                                ( void )

import LLVM.AST.Type.Representation
import LLVM.AST.Type.Name
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Function

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
    printString (unpack msg)
    _ <- fflush

    -- On Windows calling puts and llvm.trap consecutively causes
    -- the program to hang in an infinite loop, repeatedly printing newline characters.
    -- So instead of using llvm.trap, we call the abort function from the C standard library.
    -- This is also what llvm.trap would be lowered to if the target does not have a trap instruction.
    -- See: https://llvm.org/docs/LangRef.html#llvm-trap-intrinsic
    --
    -- TODO: This was tested when we used 'puts', but now we use 'printf' (via putString).
    -- We should test this again.
    if Info.os == "mingw32"
      then abort
      else trap

printf :: IsPrim a => String -> Operand a -> CodeGen Native ()
printf format val = do
  (nm, l) <- global_string format
  let strPtr = ConstantOperand $ derefGlobalString l nm
  call (lamUnnamed primType $ VarLams $ Body (PrimType $ primType @Int32) Nothing (Label "printf"))
       (ArgumentsCons strPtr []
         $ ArgumentsCons val []
           ArgumentsNil)
       []
  return ()

putInt :: Operands Int -> CodeGen Native ()
putInt x = void $ printf "%d" (op TypeInt x)

putchar :: Operands Int32 -> CodeGen Native ()
putchar x = void $
  call (lamUnnamed primType $ Body (PrimType $ primType @Int32) Nothing (Label "putchar"))
       (ArgumentsCons (op TypeInt32 x) [] ArgumentsNil) []

printString :: String -> CodeGen Native ()
printString "" = return ()
printString [c] = putchar $ liftInt32 $ Prelude.fromIntegral $ fromEnum c
printString msg = do
  (nm, l) <- global_string msg
  let strPtr = ConstantOperand $ derefGlobalString l nm
  _ <- printf "%s" strPtr
  return ()

fflush :: CodeGen Native (Operands Int)
fflush = call (lamUnnamed primType $ Body (PrimType primType) Nothing (Label "fflush"))
              (ArgumentsCons (op TypeWord64 (liftWord64 0)) [] ArgumentsNil)
              []

abort :: CodeGen Native ()
abort = void $ call (Body VoidType Nothing (Label "abort"))
                    ArgumentsNil
                    []

