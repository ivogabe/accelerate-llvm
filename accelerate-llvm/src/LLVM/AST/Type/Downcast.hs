{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : LLVM.AST.Type.Downcast
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module LLVM.AST.Type.Downcast (

  Downcast(..),

) where

import Data.Array.Accelerate.Type
-- import qualified LLVM.AST.Type                                      as LLVM
import qualified Text.LLVM                                          as LLVM

import Data.Bits

import GHC.Stack


-- | Convert a value from our representation of the LLVM AST which uses
-- Haskell-level types, into the llvm-hs representation where types are
-- represented only at the value level.
--
-- The type-level information to generate the appropriate value-level types.
--
class Downcast typed untyped where
  downcast :: HasCallStack => typed -> untyped

instance Downcast a a' => Downcast [a] [a'] where
  downcast = map downcast

instance Downcast a a' => Downcast (Maybe a) (Maybe a') where
  downcast Nothing  = Nothing
  downcast (Just x) = Just (downcast x)

instance (Downcast a a', Downcast b b') => Downcast (a,b) (a',b') where
  downcast (a,b) = (downcast a, downcast b)

instance (Downcast a a', Downcast b b') =>  Downcast (Either a b) (Either a' b') where
  downcast (Left a)  = Left (downcast a)
  downcast (Right b) = Right (downcast b)


instance Downcast (ScalarType a) LLVM.Type where
  downcast (SingleScalarType t) = downcast t
  downcast (VectorScalarType t) = downcast t

instance Downcast (SingleType a) LLVM.Type where
  downcast (NumSingleType t) = downcast t

instance Downcast (VectorType a) LLVM.Type where
  -- Our Vec is packed, whereas LLVM's Vector includes padding.
  -- Instead of a Vec, we use an Array as that does not add padding,
  -- and aligns individual values based on the alignment of t only.
  downcast (VectorType n t)
    -- We could add a special case for power-of-two vectors,
    -- since they don't need padding anyway. However, depending on
    -- the architecture this may require more alignment, and we would need to
    -- encorporate that for instance in primSizeAlignment
    -- | popCount n == 1 = LLVM.Vector (fromIntegral n) (downcast t)
    = LLVM.Array  (fromIntegral n) (downcast t)

instance Downcast (BoundedType t) LLVM.Type where
  downcast (IntegralBoundedType t) = downcast t

instance Downcast (NumType a) LLVM.Type where
  downcast (IntegralNumType t) = downcast t
  downcast (FloatingNumType t) = downcast t

instance Downcast (IntegralType a) LLVM.Type where
  downcast TypeInt     = LLVM.PrimType (LLVM.Integer (fromIntegral (finiteBitSize (undefined :: Int))))
  downcast TypeInt8    = LLVM.PrimType (LLVM.Integer 8)
  downcast TypeInt16   = LLVM.PrimType (LLVM.Integer 16)
  downcast TypeInt32   = LLVM.PrimType (LLVM.Integer 32)
  downcast TypeInt64   = LLVM.PrimType (LLVM.Integer 64)
  downcast TypeWord    = LLVM.PrimType (LLVM.Integer (fromIntegral (finiteBitSize (undefined :: Word))))
  downcast TypeWord8   = LLVM.PrimType (LLVM.Integer 8)
  downcast TypeWord16  = LLVM.PrimType (LLVM.Integer 16)
  downcast TypeWord32  = LLVM.PrimType (LLVM.Integer 32)
  downcast TypeWord64  = LLVM.PrimType (LLVM.Integer 64)

instance Downcast (FloatingType a) LLVM.Type where
  downcast TypeHalf    = LLVM.PrimType (LLVM.FloatType LLVM.Half)
  downcast TypeFloat   = LLVM.PrimType (LLVM.FloatType LLVM.Float)
  downcast TypeDouble  = LLVM.PrimType (LLVM.FloatType LLVM.Double)

