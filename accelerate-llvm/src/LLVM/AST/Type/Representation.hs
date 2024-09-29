{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : LLVM.AST.Type.Representation
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module LLVM.AST.Type.Representation (

  module LLVM.AST.Type.Representation,
  module Data.Array.Accelerate.Type,
  Ptr, Struct(..),
  AddrSpace(..),

) where

import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.AST.LeftHandSide

import LLVM.AST.Type.AddrSpace
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Name

import qualified LLVM.AST.Type                                      as LLVM

import Data.List
import Data.Text.Lazy.Builder
import Foreign.Ptr
import Foreign.Storable
import Formatting
import Text.Printf
import qualified Data.ByteString.Short.Char8                        as S8


-- Witnesses to observe the LLVM type hierarchy:
--
-- <http://llvm.org/docs/LangRef.html#type-system>
--
-- Type
--   * void
--   * labels & metadata
--   * function types
--   * first class types (basic types)
--      * primitive types (single value types, things that go in registers)
--          * multi (SIMD vectors of primitive types: pointer and single values)
--          * single value types
--              * int
--              * float
--              * ptr (any first-class or function type)
--      * aggregate types
--          * (static) array
--          * [opaque] structure
--
-- We actually don't want to encode this hierarchy as shown above, since it is
-- not precise enough for our purposes. For example, the `Add` instruction
-- operates on operands of integer type or vector (multi) of integer types, so
-- we would probably prefer to add multi-types as a sub-type of IntegralType,
-- FloatingType, etc.
--
-- We minimally extend Accelerate's existing type hierarchy to support the
-- features we require for code generation: void types, pointer types, and
-- simple aggregate structures (for CmpXchg).
--

data Type a where
  VoidType  :: Type ()
  PrimType  :: PrimType a -> Type a

newtype Struct a = Struct a

data PrimType a where
  BoolPrimType    ::                            PrimType Bool
  ScalarPrimType  :: ScalarType a            -> PrimType a          -- scalar value types (things in registers)
  PtrPrimType     :: PrimType a -> AddrSpace -> PrimType (Ptr a)    -- pointers (XXX: volatility?)
  ArrayPrimType   :: Word64 -> ScalarType a  -> PrimType a          -- static arrays
  StructPrimType  :: Bool -> TupR PrimType l -> PrimType (Struct l) -- aggregate structures
  NamedPrimType   :: Label -> PrimType a     -> PrimType a          -- typedef

skipTypeAlias :: PrimType a -> PrimType a
skipTypeAlias (NamedPrimType _ t) = skipTypeAlias t
skipTypeAlias t = t

-- | All types
--

class IsType a where
  type' :: Type a

instance IsType () where
  type' = VoidType

instance IsType Int where
  type' = PrimType primType

instance IsType Int8 where
  type' = PrimType primType

instance IsType Int16 where
  type' = PrimType primType

instance IsType Int32 where
  type' = PrimType primType

instance IsType Int64 where
  type' = PrimType primType

instance IsType Word where
  type' = PrimType primType

instance IsType Word8 where
  type' = PrimType primType

instance IsType Word16 where
  type' = PrimType primType

instance IsType Word32 where
  type' = PrimType primType

instance IsType Word64 where
  type' = PrimType primType

instance IsType Half where
  type' = PrimType primType

instance IsType Float where
  type' = PrimType primType

instance IsType Double where
  type' = PrimType primType

instance IsType (Ptr Int) where
  type' = PrimType primType

instance IsType (Ptr Int8) where
  type' = PrimType primType

instance IsType (Ptr Int16) where
  type' = PrimType primType

instance IsType (Ptr Int32) where
  type' = PrimType primType

instance IsType (Ptr Int64) where
  type' = PrimType primType

instance IsType (Ptr Word) where
  type' = PrimType primType

instance IsType (Ptr Word8) where
  type' = PrimType primType

instance IsType (Ptr Word16) where
  type' = PrimType primType

instance IsType (Ptr Word32) where
  type' = PrimType primType

instance IsType (Ptr Word64) where
  type' = PrimType primType

instance IsType (Ptr Float) where
  type' = PrimType primType

instance IsType (Ptr Double) where
  type' = PrimType primType

instance IsType Bool where
  type' = PrimType BoolPrimType


-- | All primitive types
--

class IsPrim a where
  primType :: PrimType a

instance IsPrim Int where
  primType = ScalarPrimType scalarType

instance IsPrim Int8 where
  primType = ScalarPrimType scalarType

instance IsPrim Int16 where
  primType = ScalarPrimType scalarType

instance IsPrim Int32 where
  primType = ScalarPrimType scalarType

instance IsPrim Int64 where
  primType = ScalarPrimType scalarType

instance IsPrim Word where
  primType = ScalarPrimType scalarType

instance IsPrim Word8 where
  primType = ScalarPrimType scalarType

instance IsPrim Word16 where
  primType = ScalarPrimType scalarType

instance IsPrim Word32 where
  primType = ScalarPrimType scalarType

instance IsPrim Word64 where
  primType = ScalarPrimType scalarType

instance IsPrim Half where
  primType = ScalarPrimType scalarType

instance IsPrim Float where
  primType = ScalarPrimType scalarType

instance IsPrim Double where
  primType = ScalarPrimType scalarType

instance IsPrim (Ptr Int) where
  primType = PtrPrimType primType defaultAddrSpace

instance IsPrim (Ptr Int8) where
  primType = PtrPrimType primType defaultAddrSpace

instance IsPrim (Ptr Int16) where
  primType = PtrPrimType primType defaultAddrSpace

instance IsPrim (Ptr Int32) where
  primType = PtrPrimType primType defaultAddrSpace

instance IsPrim (Ptr Int64) where
  primType = PtrPrimType primType defaultAddrSpace

instance IsPrim (Ptr Word) where
  primType = PtrPrimType primType defaultAddrSpace

instance IsPrim (Ptr Word8) where
  primType = PtrPrimType primType defaultAddrSpace

instance IsPrim (Ptr Word16) where
  primType = PtrPrimType primType defaultAddrSpace

instance IsPrim (Ptr Word32) where
  primType = PtrPrimType primType defaultAddrSpace

instance IsPrim (Ptr Word64) where
  primType = PtrPrimType primType defaultAddrSpace

instance IsPrim (Ptr Half) where
  primType = PtrPrimType primType defaultAddrSpace

instance IsPrim (Ptr Float) where
  primType = PtrPrimType primType defaultAddrSpace

instance IsPrim (Ptr Double) where
  primType = PtrPrimType primType defaultAddrSpace

instance IsPrim Bool where
  primType = BoolPrimType

instance Show (Type a) where
  show VoidType     = "()"
  show (PrimType t) = show t

instance Show (PrimType a) where
  show BoolPrimType                = "Bool"
  show (ScalarPrimType t)          = show t
  show (NamedPrimType (Label l) _) = S8.unpack l
  show (ArrayPrimType n t)         = printf "[%d x %s]" n (show t)
  show (StructPrimType _ t)        = printf "{ %s }" (intercalate ", " (go t))
    where
      go :: TupR PrimType t -> [String]
      go TupRunit         = []
      go (TupRsingle s)   = [show s]
      go (TupRpair ta tb) = go ta ++ go tb

  show (PtrPrimType t (AddrSpace n)) = printf "Ptr%s %s" a p
    where
      p             = show t
      a | n == 0    = ""
        | otherwise = printf "[addrspace %d]" n :: String
      -- p | PtrPrimType{} <- t  = printf "(%s)" (show t)
      --   | otherwise           = show t

formatType :: Format r (Type a -> r)
formatType = later $ \case
  VoidType   -> "()"
  PrimType t -> bformat formatPrimType t

formatPrimType :: Format r (PrimType a -> r)
formatPrimType = later $ \case
  BoolPrimType              -> "Bool"
  ScalarPrimType t          -> bformat formatScalarType t
  NamedPrimType (Label t) _ -> bformat string (S8.unpack t)
  ArrayPrimType n t         -> bformat (squared (int % " x " % formatScalarType)) n t
  StructPrimType _ t        -> bformat (braced (commaSpaceSep builder)) (go t)
    where
      go :: TupR PrimType t -> [Builder]
      go TupRunit         = []
      go (TupRsingle s)   = [bformat formatPrimType s]
      go (TupRpair ta tb) = go ta ++ go tb

  PtrPrimType t (AddrSpace 0) -> bformat ("Ptr "                        % formatPrimType) t
  PtrPrimType t (AddrSpace n) -> bformat ("Ptr[addrspace " % int % "] " % formatPrimType) n t


-- | Does the concrete type represent signed or unsigned values?
--
class IsSigned dict where
  signed   :: dict a -> Bool
  signed   = not . unsigned
  --
  unsigned :: dict a -> Bool
  unsigned = not . signed

instance IsSigned ScalarType where
  signed (SingleScalarType t) = signed t
  signed (VectorScalarType t) = signed t

instance IsSigned SingleType where
  signed (NumSingleType t)    = signed t

instance IsSigned VectorType where
  signed (VectorType _ t) = signed t

instance IsSigned BoundedType where
  signed (IntegralBoundedType t) = signed t

instance IsSigned NumType where
  signed (IntegralNumType t) = signed t
  signed (FloatingNumType t) = signed t

instance IsSigned IntegralType where
  signed = \case
    TypeInt{}     -> True
    TypeInt8{}    -> True
    TypeInt16{}   -> True
    TypeInt32{}   -> True
    TypeInt64{}   -> True
    _             -> False

instance IsSigned FloatingType where
  signed _ = True


-- | Recover the type of a container
--
class TypeOf f where
  typeOf :: f a -> Type a


-- | Convert to llvm-hs
--
instance Downcast (Type a) LLVM.Type where
  downcast VoidType     = LLVM.VoidType
  downcast (PrimType t) = downcast t

instance Downcast (PrimType a) LLVM.Type where
  downcast BoolPrimType         = LLVM.IntegerType 1
  downcast (NamedPrimType t _)  = LLVM.NamedTypeReference (downcast t)
  downcast (ScalarPrimType t)   = downcast t
#if MIN_VERSION_llvm_hs_pure(15,0,0)
  downcast (PtrPrimType _ a)    = LLVM.PointerType a
#else
  downcast (PtrPrimType t a)    = LLVM.PointerType (downcast t) a
#endif
  downcast (ArrayPrimType n t)  = LLVM.ArrayType n (downcast t)
  downcast (StructPrimType p t) = LLVM.StructureType p (go t)
    where
      go :: TupR PrimType t -> [LLVM.Type]
      go TupRunit         = []
      go (TupRsingle s)   = [downcast s]
      go (TupRpair ta tb) = go ta ++ go tb

llvmTypeToAccTypeR :: Type a -> Maybe (TypeR a)
llvmTypeToAccTypeR VoidType = Just TupRunit
llvmTypeToAccTypeR (PrimType (ScalarPrimType st)) = Just $ TupRsingle st
llvmTypeToAccTypeR _ = Nothing

primSizeAlignment :: PrimType a -> (Int, Int)
primSizeAlignment BoolPrimType = (1, 1)
primSizeAlignment (ScalarPrimType (SingleScalarType tp)) = (sz, sz)
  where sz = bytesElt $ TupRsingle $ SingleScalarType tp
primSizeAlignment (ScalarPrimType (VectorScalarType (VectorType n tp))) = (sz * n, sz)
  where sz = bytesElt $ TupRsingle $ SingleScalarType tp
primSizeAlignment (PtrPrimType _ _) = (sz, sz)
  where sz = sizeOf (undefined :: Ptr ())
primSizeAlignment (ArrayPrimType n tp) = (sz * fromIntegral n, sz)
  where sz = bytesElt (TupRsingle tp)
primSizeAlignment (StructPrimType False tup) = (makeAligned sz a, a)
  where (sz, a) = primTupSizeAlignment tup
primSizeAlignment (StructPrimType True _) = internalError "Packed structs not supported"
primSizeAlignment (NamedPrimType _ tp) = primSizeAlignment tp

primTupSizeAlignment :: TupR PrimType l -> (Int, Int)
primTupSizeAlignment = foldl f (0, 1) . flattenTupR
  where
    f :: (Int, Int) -> Exists PrimType -> (Int, Int)
    f (sz1, a1) (Exists tp) = (makeAligned sz1 a2 + sz2, max a1 a2)
      where
        (sz2, a2) = primSizeAlignment tp

makeAligned :: Int -> Int -> Int
makeAligned cursor align = cursor + m
  where
    m = (-cursor) `mod` align
