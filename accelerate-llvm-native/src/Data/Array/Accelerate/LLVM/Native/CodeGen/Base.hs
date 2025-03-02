{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen.Base
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Base
  where

import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Profile
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.Compile.Cache
import Data.Array.Accelerate.LLVM.Native.Target                     ( Native )
import Data.Array.Accelerate.LLVM.Native.Foreign                    ()
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Primitive.Vec

import LLVM.AST.Type.Representation
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Name
import LLVM.AST.Type.Module
import LLVM.AST.Type.AddrSpace
import qualified LLVM.AST.Global                                    as LLVM
import qualified LLVM.AST.Type                                      as LLVM

import Data.String
import qualified Data.ByteString.Short.Char8                        as S8

-- The struct passed as argument to a call contains:
--  * work_function: ptr
--  * continuation: ptr, u32 (program, location)
--  * active_threads: u32,
--  * work_index: u64,
--  * In the future, perhaps also store a work_size: u32
-- We store the work function as a pointer to a struct, as that makes it easy
-- to separate pointers to a kernel from pointers to buffers, when compiling
-- a schedule.
type Header = (((((Ptr (Struct Int8)), Ptr Int8), Word32), Word32), Word64)

headerType :: TupR PrimType Header
headerType = TupRsingle (PtrPrimType (StructPrimType False $ TupRsingle primType) defaultAddrSpace)
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle primType

type KernelType env = Ptr (Struct ((Header, Struct (MarshalEnv env)), SizedArray Word)) -> Word64 -> Word8

bindHeaderEnv
  :: forall env. Env AccessGroundR env
  -> ( PrimType (Ptr (Struct ((Header, Struct (MarshalEnv env)), SizedArray Word)))
     , CodeGen Native ()
     , Operand (Ptr Word64) -- Pointer to work index
     , Operand (Word64) -- First work index index
     , Operand (Ptr (SizedArray Word))
     , Gamma env
     )
bindHeaderEnv env =
  ( argTp
  , do
      instr_ $ downcast $ nameIndex := GetStructElementPtr primType arg (TupleIdxLeft $ TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      instr_ $ downcast $ "env" := GetStructElementPtr envTp arg (TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      instr_ $ downcast $ nameKernelMemory := GetStructElementPtr kernelMemTp arg (TupleIdxRight TupleIdxSelf)
      extractEnv
  , LocalReference (PrimType $ PtrPrimType (ScalarPrimType scalarType) defaultAddrSpace) nameIndex
  , LocalReference type' nameFirstIndex
  , LocalReference (PrimType $ PtrPrimType kernelMemTp defaultAddrSpace) nameKernelMemory
  , gamma
  )
  where
    -- The Word array at the end is kernel memory. SEE: [Kernel Memory]
    -- Note that the array here has size 0, but it may be larger.
    -- LLVM allows this, since we only use pointer casts here and the allocation does not happen here.
    argTp = PtrPrimType (StructPrimType False (headerType `TupRpair` TupRsingle envTp `TupRpair` TupRsingle kernelMemTp)) defaultAddrSpace
    (envTp, extractEnv, gamma) = bindEnv env

    nameIndex = "workassist.index"
    nameFirstIndex = "workassist.first_index"
    nameKernelMemory = "kernel_memory"

    kernelMemTp :: PrimType (SizedArray Word)
    kernelMemTp = ArrayPrimType 0 primType

    arg = LocalReference (PrimType argTp) "arg"
