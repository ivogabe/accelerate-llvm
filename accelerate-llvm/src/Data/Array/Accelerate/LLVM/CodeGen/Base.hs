{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Base
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Base (

  -- References
  Name(..),
  local, global,

  -- Functions & parameters
  call, call', callLocal,
  bindScalars, MarshalScalars, bindWorkRange,

  shapeOperandsToList,

) where

import LLVM.AST.Type.Constant
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Function                                       as LLVMType
import LLVM.AST.Type.Global
import LLVM.AST.Type.InlineAssembly
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Name
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation

import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.Representation.Array                   ( Array, ArrayR(..) )
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type

import qualified Text.LLVM                                          as LP

import Data.Monoid
import Data.String
import Data.Typeable
import Text.Printf
import qualified Data.IntMap                                        as IM
import Prelude                                                      as P


-- References
-- ----------

local :: TypeR a -> Name a -> Operands a
local  tp n = travTypeToOperands tp (\t i -> LocalReference (PrimType (ScalarPrimType t)) (rename n i))

global :: TypeR a -> Name a -> Operands a
global tp n = travTypeToOperands tp (\t i -> ConstantOperand (GlobalReference (PrimType (ScalarPrimType t)) (rename n i)))


-- Generating names for things
-- ---------------------------

-- | Names of array data components
--
arrayName :: Name (Array sh e) -> Int -> Name e'        -- for the i-th component of the ArrayData
arrayName (Name n)   i = Name (n <> fromString (printf   ".ad%d"   i))
arrayName (UnName n) i = Name (     fromString (printf "%d.ad%d" n i))

-- | Names of shape components
--
shapeName :: Name (Array sh e) -> Int -> Name sh'       -- for the i-th component of the shape structure
shapeName (Name n)   i = Name (n <> fromString (printf   ".sh%d"   i))
shapeName (UnName n) i = Name (     fromString (printf "%d.sh%d" n i))

-- | Names combined with traversing
--
rename :: Name t -> Int -> Name t'                      -- for the i-th component of the named variable
rename (Name   n) i = Name (n <> fromString (printf    "%d"   i))
rename (UnName n) i = Name (     fromString (printf "%d.%d" n i))

{-# INLINEABLE travTypeToList #-}
travTypeToList
    :: forall tp a.
       TypeR tp
    -> (forall s. ScalarType s -> Int -> a)
    -> [a]
travTypeToList tp f = snd $ go tp 0
  where
    -- DANGER: [1] must traverse in the same order as [2]
    go :: TypeR s -> Int -> (Int, [a])
    go TupRunit         i = (i,   [])
    go (TupRsingle t')  i = (i+1, [f t' i])
    go (TupRpair t2 t1) i = let (i1, r1) = go t1 i
                                (i2, r2) = go t2 i1
                            in
                            (i2, r2 ++ r1)

{-# INLINEABLE travTypeToOperands #-}
travTypeToOperands
    :: TypeR t
    -> (forall s. ScalarType s -> Int -> Operand s)
    -> Operands t
travTypeToOperands tp f = snd $ go tp 0
  where
    -- DANGER: [2] must traverse in the same order as [1]
    go :: TypeR s -> Int -> (Int, Operands s)
    go TupRunit         i = (i,   OP_Unit)
    go (TupRsingle t')  i = (i+1, ir t' $ f t' i)
    go (TupRpair t2 t1) i = let (i1, r1) = go t1 i
                                (i2, r2) = go t2 i1
                            in
                            (i2, OP_Pair r2 r1)


shapeOperandsToList :: ShapeR sh -> Operands sh -> [Operand Int]
shapeOperandsToList = \shr ops -> reverse $ go shr ops
  where
    -- Returns the individual operands in reverse order
    go :: ShapeR sh -> Operands sh -> [Operand Int]
    go ShapeRz _ = []
    go (ShapeRsnoc shr) (OP_Pair sh sz) =
      op TypeInt sz : go shr sh


-- travTypeToOperandsPtr
--     :: forall t. Elt t
--     => AddrSpace
--     -> t {- dummy -}
--     -> (forall s. ScalarType s -> Int -> Operand (Ptr s))
--     -> Operands (Ptr t)
-- travTypeToOperandsPtr as t f = snd $ go (eltType @t) 0
--   where
--     -- DANGER: [2] must traverse in the same order as [1]
--     -- go :: TypeR s -> Int -> (Int, Operands (Ptr s))
--     go :: TypeR (EltRepr s) -> Int -> (Int, Operands (EltRepr (Ptr s)))   -- TLM: ugh ):
--     go TypeRunit         i = (i,   OP_Unit)
--     go (TypeRscalar t')  i = (i+1, ir (PtrPrimType t' as) $ f t' i)
--     go (TypeRpair t2 t1) i = let (i1, r1) = go t1 i
--                                  (i2, r2) = go t2 i1
--                              in
--                              (i2, OP_Pair r2 r1)


-- Function parameters
-- -------------------

-- | Call a global function. The function declaration is inserted into the
-- symbol table.
--
call :: GlobalFunction t -> Arguments t -> [FunctionAttribute] -> CodeGen arch (Operands (Result t))
call f args attrs = do
  let decl      = (downcast f) { LP.decAttrs = downcast attrs }
      --
      go :: GlobalFunction t -> Function Callable t
      go (Body t k l) = Body t k (CallGlobal l)
      go (Lam t x l)  = Lam t x (go l)
  --
  declareExternFunc decl
  -- TODO: this only puts the attributes on the external function declaration,
  -- not on the call instruction. The original llvm-hs code also put them on
  -- the call instruction. Should compare LLVM IR / benchmark to see if this is
  -- an issue (llvm-pretty does not yet support function attributes on call
  -- instructions).
  instr (Call (go f) args)

call' :: GlobalFunction t -> Arguments t -> [FunctionAttribute] -> CodeGen arch (Operand (Result t))
call' f args attrs = do
  let decl      = (downcast f) { LP.decAttrs = downcast attrs }
      --
      go :: GlobalFunction t -> Function Callable t
      go (Body t k l) = Body t k (CallGlobal l)
      go (Lam t x l)  = Lam t x (go l)
  --
  declareExternFunc decl
  instr' (Call (go f) args)

callLocal :: Function Label t -> Arguments t -> [FunctionAttribute] -> CodeGen arch (Operand (Result t))
callLocal f args _attrs = do
  let
      --
      go :: Function Label t -> Function Callable t
      go (Body t k l) = Body t k (CallLocal l)
      go (Lam t x l)  = Lam t x (go l)
  --
  instr' (Call (go f) args)

-- | Converts a tuple of scalars to a function type
type family MarshalScalars a res where
  MarshalScalars (t, s) res = MarshalScalars t (MarshalScalars s res)
  MarshalScalars ()     res = res
  MarshalScalars t      res = t -> res

bindScalars :: String -> TypeR t -> (Result f :~: Result (MarshalScalars t f), GlobalFunctionDefinition f -> GlobalFunctionDefinition (MarshalScalars t f), Operands t)
bindScalars prefix tp = (eq, fun, operands)
  where
    (_, eq, fun, operands) = bindScalars' prefix 0 tp

bindScalars' :: forall t f. String -> Int -> TypeR t -> (Int, Result f :~: Result (MarshalScalars t f), GlobalFunctionDefinition f -> GlobalFunctionDefinition (MarshalScalars t f), Operands t)
bindScalars' prefix fresh (TupRpair t1 t2)
  | (fresh1, eq1, f1, o1) <- bindScalars' prefix fresh  t1
  , (fresh2, eq2, f2, o2) <- bindScalars' prefix fresh1 t2
  = (fresh2, case (eq1, eq2) of (Refl, Refl) -> Refl, f1 . f2, OP_Pair o1 o2)
bindScalars' prefix fresh (TupRsingle tp)
  | Refl <- marshalScalar @t @f tp = (fresh + 1, Refl, LLVMType.Lam (ScalarPrimType tp) name, ir tp operand)
    where
    operand = LocalReference (PrimType $ ScalarPrimType tp) name
    name = fromString $ prefix ++ show fresh
bindScalars' _      fresh (TupRunit) = (fresh, Refl, id, OP_Unit)

marshalScalar :: ScalarType t -> (t -> res) :~: MarshalScalars t res
-- Pattern match to prove that 't' is not () or a pair type
marshalScalar (VectorScalarType _) = Refl
marshalScalar (SingleScalarType (NumSingleType (IntegralNumType tp))) = case tp of
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
marshalScalar (SingleScalarType (NumSingleType (FloatingNumType tp))) = case tp of
  TypeHalf   -> Refl
  TypeFloat  -> Refl
  TypeDouble -> Refl

bindWorkRange
  :: ShapeR sh
  -> ( Result t :~: Result (MarshalScalars sh (MarshalScalars sh t))
     , GlobalFunctionDefinition t -> GlobalFunctionDefinition (MarshalScalars sh (MarshalScalars sh t))
     , Operands sh
     , Operands sh
     )
bindWorkRange shr
  | (eq1, funStart, opStart) <- bindScalars "ix.start." tp
  , (eq2, funEnd,   opEnd)   <- bindScalars "ix.end." tp
  = (case (eq1, eq2) of (Refl, Refl) -> Refl, funStart . funEnd, opStart, opEnd)
  where
    tp = shapeType shr
    
