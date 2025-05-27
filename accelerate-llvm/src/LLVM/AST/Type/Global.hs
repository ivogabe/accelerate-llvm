{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : LLVM.AST.Type.Global
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module LLVM.AST.Type.Global
  where

import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Function
import LLVM.AST.Type.Name

import qualified Data.Map as Map

import qualified Text.LLVM                                          as LLVM


-- | An external global function definition.
--
type GlobalFunction t = Function Label t -- Function without implementation
type GlobalFunctionDefinition t = Function GlobalFunctionBody t -- Function with implementation

data GlobalFunctionBody = GlobalFunctionBody (Maybe LLVM.Linkage) Label [LLVM.BasicBlock]

instance Downcast (GlobalFunction t) LLVM.Declare where
  downcast f = LLVM.Declare
    { LLVM.decLinkage = Just LLVM.External
    , LLVM.decVisibility = Nothing
    , LLVM.decRetType = res
    , LLVM.decName = nm
    , LLVM.decArgs = args
    , LLVM.decVarArgs = False
    , LLVM.decAttrs = []
    , LLVM.decComdat = Nothing }
    where
      trav :: GlobalFunction t -> ([LLVM.Type], LLVM.Type, LLVM.Symbol)
      trav (Body t _ n) = ([], downcast t, labelToPrettyS n)
      trav (Lam a _ l)  = let (as, r, n) = trav l
                          in  (downcast a : as, r, n)
      --
      (args, res, nm) = trav f

instance Downcast (GlobalFunctionDefinition t) LLVM.Define where
  downcast f = LLVM.Define
    { LLVM.defLinkage = linkage'
    , LLVM.defVisibility = Nothing
    , LLVM.defRetType = res
    , LLVM.defName = nm
    , LLVM.defArgs = args
    , LLVM.defVarArgs = False
    , LLVM.defAttrs = []
    , LLVM.defSection = Nothing
    , LLVM.defGC = Nothing
    , LLVM.defBody = bs
    , LLVM.defMetadata = Map.empty
    , LLVM.defComdat = Nothing }
    where
      trav :: GlobalFunctionDefinition t -> ((Maybe LLVM.Linkage), [LLVM.Typed LLVM.Ident], LLVM.Type, LLVM.Symbol, [LLVM.BasicBlock])
      trav (Body t _ (GlobalFunctionBody linkage n blocks)) = (linkage, [], downcast t, labelToPrettyS n, blocks)
      trav (Lam t p l)
        = (linkage, LLVM.Typed (downcast t) (nameToPrettyI p) : ps, r, n, blocks)
        where (linkage, ps, r, n, blocks) = trav l
      --
      (linkage', args, res, nm, bs) = trav f
