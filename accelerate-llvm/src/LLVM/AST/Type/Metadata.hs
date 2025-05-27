{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : LLVM.AST.Type.Metadata
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module LLVM.AST.Type.Metadata
  where

import LLVM.AST.Type.Constant
import LLVM.AST.Type.Downcast

import qualified Text.LLVM                                as LLVM

import Data.ByteString.Short                              ( ShortByteString )
import qualified Data.ByteString.Short.Char8              as SBS8

type InstructionMetadata = [(String, Metadata)]
type MetadataNodeID = Int

-- | Metadata does not have a type, and is not a value.
--
-- <http://llvm.org/docs/LangRef.html#metadata>
--
data MetadataNode
  = MetadataNode ![Maybe Metadata]
  | MetadataNodeReference {-# UNPACK #-} !Int

data Metadata where
  MetadataStringOperand   :: {-# UNPACK #-} !ShortByteString -> Metadata
  MetadataConstantOperand :: !(Constant t) -> Metadata
  MetadataNodeOperand     :: !MetadataNode -> Metadata
  -- metadata of llvm-pretty
  MetadataPretty          :: LLVM.ValMd -> Metadata

-- | Convert to llvm-pretty
--
instance Downcast [Maybe Metadata] LLVM.ValMd where
  downcast mds = LLVM.ValMdNode $ map (fmap downcast) mds

instance Downcast Metadata LLVM.ValMd where
  downcast (MetadataStringOperand s)   = LLVM.ValMdString (SBS8.unpack s)
  downcast (MetadataConstantOperand o) = LLVM.ValMdValue (downcast o)
  downcast (MetadataNodeOperand n)     = downcast n
  downcast (MetadataPretty m)          = m

instance Downcast MetadataNode LLVM.ValMd where
  downcast (MetadataNode n)            = LLVM.ValMdNode (downcast n)
  downcast (MetadataNodeReference r)   = LLVM.ValMdRef r

downcastInstructionMetadata :: InstructionMetadata -> [(String, LLVM.ValMd)]
downcastInstructionMetadata = map (fmap downcast)
