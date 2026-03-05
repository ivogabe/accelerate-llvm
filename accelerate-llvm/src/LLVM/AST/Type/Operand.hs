{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : LLVM.AST.Type.Operand
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module LLVM.AST.Type.Operand (

  Operand(..),
  ptrCast,

) where

import LLVM.AST.Type.Constant
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Name
import LLVM.AST.Type.Representation

import Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.LLVM.Internal.LLVMPretty     as LLVM


-- | An 'Operand' is roughly anything that is an argument to an 'Instruction'
--
data Operand a where
  LocalReference  :: Type a -> Name a -> Operand a
  ConstantOperand :: Constant a -> Operand a


-- | Convert to llvm-pretty
--
instance Downcast (Operand a) (LLVM.Typed LLVM.Value) where
  downcast (LocalReference t n) = LLVM.Typed (downcast t) (LLVM.ValIdent (nameToPrettyI n))
  downcast (ConstantOperand c)  = downcast c

instance TypeOf Operand where
  typeOf (LocalReference t _) = t
  typeOf (ConstantOperand c)  = typeOf c

-- | Casts the pointee type of a pointer operand.
-- This is possible without generating instructions, as LLVM switched to an
-- untyped pointer type, i.e. the pointee type is not given in the pointer
-- type any more. In our internal LLVM language we do keep those pointee types
-- for additional type safety, and this function should be used carefully.
--
-- If LLVM ever returns to strongly typed pointers, we should place this
-- function in the CodeGen monad and add a BitCast / PtrCast instruction.
ptrCast :: PrimType b -> Operand (Ptr a) -> Operand (Ptr b)
ptrCast tp (LocalReference (PrimType (PtrPrimType _ addrspace)) name) = LocalReference (PrimType (PtrPrimType tp addrspace)) $ castName name
ptrCast _ (LocalReference _ _) = internalError "Ptr impossible"
ptrCast tp (ConstantOperand c) = ConstantOperand $ case c of
  UndefConstant (PrimType (PtrPrimType _ addrspace)) -> UndefConstant $ PrimType $ PtrPrimType tp addrspace
  UndefConstant _ -> internalError "Ptr impossible"
  NullPtrConstant (PrimType (PtrPrimType _ addrspace)) -> NullPtrConstant $ PrimType $ PtrPrimType tp addrspace
  NullPtrConstant _ -> internalError "Ptr impossible"
  ScalarConstant _ _ -> internalError "Ptr impossible"
  ConstantGetElementPtr _ -> internalError "ptrCast not yet supported for ConstantGetElementPtr"
  GlobalReference (PrimType (PtrPrimType _ addrspace)) name -> GlobalReference (PrimType (PtrPrimType tp addrspace)) $ castName name
  GlobalReference _ _ -> internalError "Ptr impossible"
