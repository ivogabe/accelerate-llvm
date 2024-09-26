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

  IRBuffer(..),

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

-- DVB: cute, but completely irrelevant the way I have Native set up currently
data IRBuffer e
  = IRBuffer
      -- If the buffer is not fused away, then a pointer to the buffer, its
      -- address space and volatility are stored.
      --
      (Maybe (Operand (Ptr (ScalarArrayDataR e)), AddrSpace, Volatility))
      -- If the buffer is fused away, then it is replaced by a local variable.
      -- In case of diagonal fusion, the buffer does exist but later reads to
      -- the buffer are replaced by a local variable. That variable is stored
      -- here. Note that we here assume that reads and writes to this buffer
      -- are all to the same index. Fusion should assure that this property
      -- holds.
      --
      (Maybe (Operand e))


