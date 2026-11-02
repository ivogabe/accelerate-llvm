{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Profile
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Profile (

  global_string, derefGlobalString, locationDataType, source_location_data, TracySrcloc

) where

import LLVM.AST.Type.Constant
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.GetElementPtr
import LLVM.AST.Type.Name
import LLVM.AST.Type.Representation
import qualified Data.Array.Accelerate.LLVM.Internal.LLVMPretty     as LP

import Data.Array.Accelerate.LLVM.CodeGen.Monad

import Data.Array.Accelerate.Representation.Type

import Data.Char


global_string :: String -> CodeGen arch (Name (Ptr (SizedArray Word8)), Word64)
global_string str = do
  let str0  = str ++ "\0"
      l     = fromIntegral (length str0)
  --
  nm <- freshGlobalName
  _  <- declareGlobalVar $ LP.Global
    { LP.globalSym = nameToPrettyS nm
    , LP.globalAttrs = LP.GlobalAttrs
        { LP.gaLinkage = Just LP.Private
        , LP.gaVisibility = Nothing
        , LP.gaAddrSpace = LP.defaultAddrSpace
        , LP.gaConstant = True }
    , LP.globalType = LP.Array l (LP.PrimType (LP.Integer 8))
    , LP.globalValue = Just $ LP.ValArray (LP.PrimType (LP.Integer 8)) [ LP.ValInteger (toInteger (ord c)) | c <- str0 ]
    , LP.globalAlign = Nothing
    , LP.globalMetadata = mempty
    }
  return (nm, l)

-- ___tracy_source_location_data
type TracySrcloc = Struct ((((Ptr Int8, Ptr Int8), Ptr Int8), Int32), Int32)

locationDataType :: PrimType TracySrcloc
locationDataType = StructPrimType False
  $ TupRsingle primType
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle primType

derefGlobalString :: Word64 -> Name (Ptr (SizedArray Word8)) -> Constant (Ptr Word8)
derefGlobalString slen sname =
  -- Global references are _pointers_ to their values. A string is an
  -- [_ x i8], hence the global reference is an [_ x i8]*. The GEP needs
  -- to index the outer pointer (with a 0) and index the array (at index
  -- 0) to address the first i8 in the string; GEP then returns a pointer
  -- to this i8.
  ConstantGetElementPtr $ GEP
    (GlobalReference (PrimType (PtrPrimType (ArrayPrimType slen $ ScalarPrimType scalarType) defaultAddrSpace)) sname)
    (ScalarConstant scalarType 0 :: Constant Int32)
    (GEPArray (ScalarConstant scalarType 0 :: Constant Int32) GEPEmpty)


-- struct ___tracy_source_location_data
-- {
--     const char* name;
--     const char* function;
--     const char* file;
--     uint32_t line;
--     uint32_t color;
-- };
--
source_location_data :: String -> String -> String -> Int -> Word32 -> CodeGen arch (Name a)
source_location_data nm fun src line colour = do
  let i8ptr_t = LP.PtrTo (LP.PrimType (LP.Integer 8)) defaultAddrSpace
      i32_t = LP.PrimType (LP.Integer 32)
  _       <- typedef "___tracy_source_location_data" $ LP.Struct [ i8ptr_t, i8ptr_t, i8ptr_t, i32_t, i32_t ]
  (s, sl) <- global_string src
  (f, fl) <- global_string fun
  (n, nl) <- global_string nm
  let
      source     = if null src then NullPtrConstant type' else derefGlobalString sl s
      function   = if null fun then NullPtrConstant type' else derefGlobalString fl f
      name       = if null nm  then NullPtrConstant type' else derefGlobalString nl n
  --
  v <- freshGlobalName
  _ <- declareGlobalVar $ LP.Global
    { LP.globalSym = nameToPrettyS v
    , LP.globalAttrs = LP.GlobalAttrs
        { LP.gaLinkage = Just LP.Internal
        , LP.gaVisibility = Nothing
        , LP.gaAddrSpace = LP.defaultAddrSpace
        , LP.gaConstant = True }
    , LP.globalType = LP.Alias (LP.Ident "___tracy_source_location_data")
    , LP.globalValue = Just $
        LP.ValStruct
          [ downcast name
          , downcast function
          , downcast source
          , LP.Typed (LP.PrimType (LP.Integer 32)) (LP.ValInteger (toInteger line))
          , LP.Typed (LP.PrimType (LP.Integer 32)) (LP.ValInteger (toInteger colour))
          ]
    , LP.globalAlign = Just 8
    , LP.globalMetadata = mempty
    }
  return v
