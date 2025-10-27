{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : LLVM.AST.Type.Function
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module LLVM.AST.Type.Function
  where

import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Name
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation
import LLVM.AST.Type.InlineAssembly

-- import qualified LLVM.AST.Attribute                                 as LLVM
-- import qualified LLVM.AST.Global                                    as LLVM
-- import qualified LLVM.AST.Instruction                               as LLVM
import qualified Text.LLVM                                          as LLVM

import Data.Typeable

data Callable
  = CallAssembly InlineAssembly
  | CallGlobal Label
  | CallLocal Label

-- | Attributes for the function call instruction
--
data FunctionAttribute
  = NoReturn
  | NoUnwind
  | ReadOnly
  | ReadNone
  | AlwaysInline
  | NoDuplicate
  | Convergent
  | InaccessibleMemOnly

-- | Tail call kind for function call instruction
--
data TailCall
  = Tail
  | NoTail
  | MustTail

-- | Parameters for functions
--
data Parameter a where
  Parameter :: PrimType a -> Name a -> Parameter a

-- | Attribute groups are groups of attributes that are referenced by
-- objects within the IR. To use an attribute group, an object must
-- reference its GroupID.
--
data GroupID = GroupID !Word


-- | Functions are arguments to the 'call' instruction; either global
-- functions or inline assembly.
--
data Function kind t where
  Body :: Result r ~ r => Type r -> Maybe TailCall -> kind -> Function kind r
  Lam  :: PrimType a -> Name a -> Function kind t -> Function kind (a -> t)

lamUnnamed :: PrimType a -> Function kind t -> Function kind (a -> t)
lamUnnamed tp = Lam tp (UnName 0)

instance Downcast FunctionAttribute LLVM.FunAttr where
  downcast NoReturn            = LLVM.Noreturn
  downcast NoUnwind            = LLVM.Nounwind
  downcast ReadOnly            = LLVM.Readonly
  downcast ReadNone            = LLVM.Readnone
  downcast AlwaysInline        = LLVM.Alwaysinline
  downcast NoDuplicate         = LLVM.Noduplicate
  downcast Convergent          = LLVM.Convergent
  downcast InaccessibleMemOnly = LLVM.InaccessibleMemOnly

instance Downcast (Parameter a) (LLVM.Typed LLVM.Ident) where
  -- TODO attributes! llvm-pretty doesn't seem to support them, but we put
  -- [NoAlias, NoCapture] on pointer types.
  -- TODO: Should check if these parameters are necessary (by benchmarking the old backend with llvm-hs), and if so, should send a PR to llvm-pretty
  downcast (Parameter t n) = LLVM.Typed (downcast t) (nameToPrettyI n)

instance Downcast TailCall Bool where
  downcast Tail     = True
  downcast NoTail   = False
  downcast MustTail = error "TODO MustTail"

-- instance Downcast GroupID LLVM.GroupID where
--   downcast (GroupID n) = LLVM.GroupID n

type family Result t where
  Result (s -> t) = Result t
  Result t        = t

scalarTypeIsResult :: ScalarType r -> r :~: Result r
scalarTypeIsResult (VectorScalarType _) = Refl
scalarTypeIsResult (SingleScalarType (NumSingleType tp)) = case tp of
  IntegralNumType t -> integralTypeIsResult t
  FloatingNumType t -> floatingTypeIsResult t

integralTypeIsResult :: IntegralType r -> r :~: Result r
integralTypeIsResult = \case
  TypeInt    -> Refl
  TypeInt8   -> Refl
  TypeInt16  -> Refl
  TypeInt32  -> Refl
  TypeInt64  -> Refl
  TypeWord   -> Refl
  TypeWord8  -> Refl
  TypeWord16 -> Refl
  TypeWord32 -> Refl
  TypeWord64 -> Refl

floatingTypeIsResult :: FloatingType r -> r :~: Result r
floatingTypeIsResult = \case
  TypeHalf   -> Refl
  TypeFloat  -> Refl
  TypeDouble -> Refl

-- Empty data type since llvm-pretty doesn't support parameter attributes yet
data ParameterAttribute

data Arguments f where
  ArgumentsCons :: Operand a -> [ParameterAttribute] -> Arguments f -> Arguments (a -> f)
  ArgumentsNil  :: Result f ~ f => Arguments f

functionBody :: Function kind t -> kind
functionBody (Lam _ _ f) = functionBody f
functionBody (Body _ _ b) = b
