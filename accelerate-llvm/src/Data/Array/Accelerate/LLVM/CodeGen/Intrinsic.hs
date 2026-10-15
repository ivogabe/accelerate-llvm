{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Intrinsic
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Intrinsic (

  Intrinsic(..)

) where

import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Elt

-- accelerate-llvm
import LLVM.AST.Type.Name
import LLVM.AST.Type.Instruction.RMW
import Data.Array.Accelerate.LLVM.State
import {-# SOURCE #-} Data.Array.Accelerate.LLVM.CodeGen.Monad  ( CodeGen )

-- libraries
import Data.Monoid
import Data.ByteString.Short                                    ( ShortByteString )
import Data.HashMap.Strict                                      ( HashMap )
import qualified Data.HashMap.Strict                            as HashMap
import Prelude                                                  as P
import Data.Text                                                ( Text )

-- | During code generation we need to know the name of functions implementing
-- certain intrinsic maths operations. Depending on the backend, these functions
-- may not be implemented using the standard C math library.
--
-- This class allows a backend to provide a mapping from the C math library
-- function name to the name of the function which should be called instead. The
-- default implementation maps to the llvm intrinsic. For example:
--
--   sqrtf      -> llvm.sqrt.f32
--   sqrt       -> llvm.sqrt.f64
--
class Intrinsic arch where
  intrinsicForTarget :: HashMap ShortByteString Label
  intrinsicForTarget = llvmIntrinsic

  trapWithMessage :: Text -> CodeGen arch ()
  trapWithMessage _ = return ()

  supportsAtomicCAS :: Int -> LLVM arch Bool

  supportsAtomicRMW :: ScalarType e -> RMWOperation -> LLVM arch Bool
  -- We can overapproximate the set of supported RMW operations by checking if
  -- CAS is supported on the size of the elements. LLVM will convert any
  -- unsupported RMWs to a CAS loop, so it is fine to emit RMW operations if we
  -- know the fallback will be possible.
  --
  -- See https://llvm.org/docs/Atomics.html, for instance on X86:
  -- atomicrmw xchg uses XCHG, atomicrmw add and atomicrmw sub use XADD, and
  -- all other atomicrmw operations generate a loop with LOCK CMPXCHG.
  --
  -- If this is not desired for a certain backend, this behavior can be
  -- overwritten.
  supportsAtomicRMW tp _ = supportsAtomicCAS (scalarTypeSize tp)

llvmIntrinsic :: HashMap ShortByteString Label
llvmIntrinsic =
  let floating base rest
          = (base,        Label ("llvm." <> base <> ".f64"))
          : (base <> "f", Label ("llvm." <> base <> ".f32"))
          : (base <> "l", Label ("llvm." <> base <> ".f128"))
          : rest
  in
  HashMap.fromList $ foldr floating []
    [ "sqrt"
    , "powi"
    , "sin"
    , "cos"
    , "pow"
    , "exp"
    , "exp2"
    , "log"
    , "log10"
    , "log2"
    , "fma"
    , "fabs"
    , "copysign"
    , "floor"
    , "ceil"
    , "trunc"
    , "rint"
    , "nearbyint"
    , "round"
    ]

