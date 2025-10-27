{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : LLVM.AST.Type.Module
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module LLVM.AST.Type.Module
  where

import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Global
import qualified Text.LLVM as LP
import qualified Text.LLVM.Triple as LP

import qualified Data.Map as Map


-- | A compiled module consists of a number of global functions (kernels). The
-- module additionally includes a map from the callable function definitions to
-- the metadata for that function.
--
data Module a
  = Module { moduleName             :: String
           , moduleDataLayout       :: LP.DataLayout
           , moduleTargetTriple     :: LP.TargetTriple
           , moduleMain             :: GlobalFunctionDefinition a
           , moduleTypes            :: [LP.TypeDecl]
           , moduleGlobals          :: [LP.Global]
           , moduleDeclares         :: [LP.Declare]
           , moduleNamedMd          :: [LP.NamedMd]
           , moduleUnnamedMd        :: [LP.UnnamedMd]
           }

instance Downcast (Module t) LP.Module where
  downcast (Module _name dataLayout target main types globals decls namedMd unnamedMd) =
    LP.Module
      { LP.modSourceName = Nothing
      , LP.modTriple     = target 
      , LP.modDataLayout = dataLayout
      , LP.modTypes      = types
      , LP.modNamedMd    = namedMd
      , LP.modUnnamedMd  = unnamedMd
      , LP.modComdat     = Map.empty
      , LP.modGlobals    = globals
      , LP.modDeclares   = decls
      , LP.modDefines    = [downcast main]
      , LP.modInlineAsm  = []
      , LP.modAliases    = []
      }
