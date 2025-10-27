{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ViewPatterns #-}
module LLVM.AST.Type.GetElementPtr where

import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Representation
import Data.Array.Accelerate.Representation.Type (TupleIdx, tupleIdxToInt)
import Data.Array.Accelerate.Error


-- | A @getelementptr@ instruction. The @op@ parameter is the type of operands
-- (in practice, 'LLVM.AST.Type.Operand.Operand' or
-- 'LLVM.AST.Type.Constant.Constant'). The @ptra@ and @ptrb@ type indices are
-- the input and output /pointer/ type.
--
-- The type of indices is unconstrained, which is more flexible than reality,
-- and the kind of operands must be uniform, which is /less/ flexible than
-- reality. Reality is quite cumbersome:
-- * When indexing into a structure (currently unsupported by this data type),
--   the index type must be @i32@ and its value must be constant.
-- * When indexing into an array, the index type may be any /integral/ type,
--   signed or unsigned, which are then treated as signed integers.
--
-- <https://llvm.org/docs/LangRef.html#getelementptr-instruction>
data GetElementPtr op ptra ptrb where
  GEP :: op (Ptr a)
      -> op i             -- ^ the offset to the initial pointer (counted in pointees, not in bytes)
      -> GEPIndex op a b  -- ^ field/index selection path
      -> GetElementPtr op (Ptr a) (Ptr b)

-- | A convenience pattern synonym for the common case of a full path of length 1.
pattern GEP1 :: op (Ptr a) -> op i -> GetElementPtr op (Ptr a) (Ptr a)
pattern GEP1 ptr ix <- GEP ptr ix GEPEmpty
  where GEP1 ptr ix = GEP ptr ix GEPEmpty

-- | An index sequence that goes from a 'Ptr a' to a 'Ptr b'. Note that this
-- data type is indexed with the base types of the pointers, not the pointer
-- types themselves.
data GEPIndex op a b where
  GEPEmpty  :: GEPIndex op b b

  GEPArray  :: op i              -> GEPIndex op a b -> GEPIndex op (SizedArray a) b

  -- Store a type witness of 'a', to show that 'a' is not unit or a pair.
  -- The TupleIdx to Int conversion (in tupleIdxToInt) only makes sense
  -- when we index to singular values in the struct, as these become the
  -- fields of the struct.
  GEPStruct :: PrimType a
            -> TupleIdx struct a -> GEPIndex op a b -> GEPIndex op (Struct struct) b

downcastGEPIndex
  :: (forall i. Downcast (op i) v)
  => (Int32 -> v)
  -> GEPIndex op a b
  -> PrimType a
  -> [v]
downcastGEPIndex _ GEPEmpty _ = []
downcastGEPIndex lift (GEPArray i l) (ArrayPrimType _ t) =
  downcast i : downcastGEPIndex lift l t
downcastGEPIndex lift (GEPStruct tp i l) (skipTypeAlias -> StructPrimType _ tps) =
  lift (fromIntegral $ tupleIdxToInt tps i) : downcastGEPIndex lift l tp
downcastGEPIndex _ _ _ = internalError "Array or Struct type impossible"

gepIndexOutType :: GEPIndex op a b -> PrimType a -> PrimType b
gepIndexOutType GEPEmpty t = t
gepIndexOutType (GEPArray _ l) (ArrayPrimType _ t) = gepIndexOutType l t
gepIndexOutType (GEPArray _ _) (ScalarPrimType _) = internalError "Array type impossible"
gepIndexOutType (GEPStruct t _ l) _ = gepIndexOutType l t

instance TypeOf op => TypeOf (GetElementPtr op ptra) where
  typeOf (GEP p _ path) =
    case typeOf p of
      PrimType (PtrPrimType tp addr) -> PrimType (PtrPrimType (gepIndexOutType path tp) addr)
      PrimType (ScalarPrimType _) -> internalError "Pointer type impossible"
