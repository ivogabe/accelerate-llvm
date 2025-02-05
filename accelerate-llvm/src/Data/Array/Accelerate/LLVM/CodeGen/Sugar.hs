{-# LANGUAGE GADTs           #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies    #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Sugar
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Sugar (

  IRExp, MIRExp, IRFun1, IRFun2,
  IROpenExp, IROpenFun1(..), IROpenFun2(..),

  IRBuffer(..), IRBufferScope(..)

) where

import Data.Array.Accelerate.Array.Buffer
import LLVM.AST.Type.AddrSpace
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Operand
import Foreign.Ptr

import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad


-- Scalar expressions
-- ------------------

-- | LLVM IR is in single static assignment, so we need to be able to generate
-- fresh names for each application of a scalar function or expression.
--
type IRExp     arch     t = IROpenExp arch () t
type MIRExp    arch     t = Maybe (IRExp arch t)
type IROpenExp arch env t = CodeGen arch (Operands t)

type IRFun1 arch t = IROpenFun1 arch () t
type IRFun2 arch t = IROpenFun2 arch () t

data IROpenFun1 arch env t where
  IRFun1 :: { app1 :: Operands a -> IROpenExp arch (env,a) b }
         -> IROpenFun1 arch env (a -> b)

data IROpenFun2 arch env t where
  IRFun2 :: { app2 :: Operands a -> Operands b -> IROpenExp arch ((env,a),b) c }
         -> IROpenFun2 arch env (a -> b -> c)


-- Arrays
-- ------

data IRBuffer e
  = IRBuffer
      -- The pointer to the value or values of the buffer
      (Operand (Ptr (ScalarArrayDataR e)))
      AddrSpace
      Volatility
      -- The scope of this pointer: whether it refers to a single value (of a
      -- fused-away buffer), a tile (a block of a fused-away buffer in a kernel
      -- containing a chained scan) or a regular manifest array.
      IRBufferScope

data IRBufferScope
  -- The pointer of the buffer refers to a single value.
  -- This is used for an buffer that is fused away.
  -- The pointer should not be incremented, before reading or writing to this
  -- buffer.
  = IRBufferScopeSingle
  -- The pointer of the buffer refers to a fixed size chunk of memory,
  -- corresponding to a tile loop. This is used to store data between different
  -- tile loops, when generating the code for a kernel containing scans.
  -- The pointer should be incremented by the iteration variable of the tile
  -- loop.
  | IRBufferScopeTile
  -- The pointer of the buffer refers to the start of the array.
  -- This is used for manifest arrays (that are not fused away).
  -- The pointer should be incremented by the (absolute) linear index of the
  -- element.
  | IRBufferScopeArray
