{-# LANGUAGE GADTs #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Constant
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Constant (

  constant, scalar, single, vector, num, integral, floating, boolean,
  undef, undefs,

) where


import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type

import LLVM.AST.Type.Constant
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation

import Data.Primitive.Vec


-- | A constant value
--
constant :: TypeR a -> a -> Operands a
constant TupRunit         ()    = OP_Unit
constant (TupRpair ta tb) (a,b) = OP_Pair (constant ta a) (constant tb b)
constant (TupRsingle t)   a     = ir t (scalar t a)

scalar :: ScalarType a -> a -> Operand a
scalar t = ConstantOperand . ScalarConstant t

single :: SingleType a -> a -> Operand a
single t = scalar (SingleScalarType t)

vector :: VectorType (Vec n a) -> (Vec n a) -> Operand (Vec n a)
vector t = scalar (VectorScalarType t)

num :: NumType a -> a -> Operand a
num t = single (NumSingleType t)

integral :: IntegralType a -> a -> Operand a
integral t = num (IntegralNumType t)

floating :: FloatingType a -> a -> Operand a
floating t = num (FloatingNumType t)

boolean :: Bool -> Operand Bool
boolean = ConstantOperand . BooleanConstant


-- | The string 'undef' can be used anywhere a constant is expected, and
-- indicates that the program is well defined no matter what value is used.
--
-- <http://llvm.org/docs/LangRef.html#undefined-values>
--
undef :: ScalarType a -> Operand a
undef t = ConstantOperand (UndefConstant (PrimType (ScalarPrimType t)))

undefs :: TypeR a -> Operands a
undefs TupRunit = OP_Unit
undefs (TupRsingle ty) = ir ty $ undef ty
undefs (TupRpair l r) = OP_Pair (undefs l) (undefs r)
