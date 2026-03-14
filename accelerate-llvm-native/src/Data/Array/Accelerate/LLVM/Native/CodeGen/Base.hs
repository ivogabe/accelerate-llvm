{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# OPTIONS_GHC -Wno-orphans     #-}
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

import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.Native.Target                     ( Native )
import Data.Array.Accelerate.LLVM.Native.Foreign                    ()
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Primitive.Vec

import LLVM.AST.Type.Representation
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Operand

import Data.String
import qualified Data.ByteString.Short.Char8                        as S8

shardAmount :: Word64
shardAmount = 128

cacheWidth :: Word64
cacheWidth = 64

-- Calculates how many values are needed to fill a cache line
class CalcValuesPerCacheLine t where
  valuesPerCacheLine :: t a -> Word64

instance CalcValuesPerCacheLine PrimType where
  valuesPerCacheLine tp = (cacheWidth + byteSize - 1) `div` byteSize    
    where byteSize = fromIntegral (fst (primSizeAlignment tp))

instance CalcValuesPerCacheLine ScalarType where
  valuesPerCacheLine tp = valuesPerCacheLine $ ScalarPrimType tp


-- The struct passed as argument to a call contains:
--  * work_function: ptr
--  * continuation: ptr, u32 (program, location)
--  * active_threads: u32,
--  * work_index: u64,
--  * In the future, perhaps also store a work_size: u32
-- We store the work function as a pointer to a struct, as that makes it easy
-- to separate pointers to a kernel from pointers to buffers, when compiling
-- a schedule.
type Header = ((((Ptr (Struct Int8), Ptr Int8), Word32), Word32), Word64)

headerType :: TupR PrimType Header
headerType = TupRsingle (PtrPrimType (StructPrimType False $ TupRsingle primType) defaultAddrSpace)
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle primType

shardIndexesTp :: PrimType (SizedArray Word64)
shardIndexesTp = ArrayPrimType (shardAmount * valuesPerCacheLine scalarTypeWord64) primType

shardSizesTp :: PrimType (SizedArray Word64)
shardSizesTp = ArrayPrimType shardAmount primType

shardStorageTp :: PrimType (Struct (SizedArray Word64, SizedArray Word64))
shardStorageTp = StructPrimType False $ TupRsingle shardIndexesTp `TupRpair` TupRsingle shardSizesTp

shardStorageSize :: Int
shardStorageSize = fst $ primSizeAlignment shardStorageTp

kernelMemTp :: PrimType (SizedArray Word)
kernelMemTp = ArrayPrimType 0 primType

type KernelType env
  -- Ptr to the kernel struct
  = Ptr (Struct ((Header, Struct (MarshalEnv env)), SizedArray Word))
  -- Ptr to the locks array (for any permutes)
  -> Ptr Word8
  -- A magic value for single-threaded initialization or finalization
  -> Word64
  -- Only in initialization, this function returns whether the kernel should run sequentially or in parallel
  -> Word8

bindHeaderEnv
  :: forall env. Env AccessGroundR env
  -> ( PrimType (Ptr (Struct ((Header, Struct (MarshalEnv env)), SizedArray Word)))
     , CodeGen Native (
    --  , Operand (Ptr (SizedArray Word64))  -- work indexes of shards
    --  , Operand (Ptr (SizedArray Word64))  -- sizes of the shards
       Operand (Ptr Word64)               -- In the case of workassist, the workassist index.
       -- In the case of sharded self scheduling, combined the next shard and amount of finished shards.
     , Operand Word64 -- Flag that specifies if the work needs to be initialized or finished
     , Gamma env
     ))
bindHeaderEnv env =
  ( argTp
  , do
      instr_ $ downcast $ nameIndex                  := GetElementPtr (gepStruct primType arg $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      instr_ $ downcast $ "env"                      := GetElementPtr (gepStruct envTp arg $ TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      extractEnv
      return (
          LocalReference (PrimType $ PtrPrimType (ScalarPrimType scalarType) defaultAddrSpace) nameIndex
        , LocalReference type' nameFlag
        -- , LocalReference (PrimType $ PtrPrimType kernelMemTp defaultAddrSpace) nameKernelMemory
        , gamma
        )
      )
  where
    -- The Word array at the end is kernel memory. SEE: [Kernel Memory]
    -- Note that the array here has size 0, but it may be larger.
    -- LLVM allows this, since we only use pointer casts here and the allocation does not happen here.
    argTp = PtrPrimType (StructPrimType False (headerType `TupRpair` TupRsingle envTp `TupRpair` TupRsingle kernelMemTp)) defaultAddrSpace
    (envTp, extractEnv, gamma) = bindEnvFromStruct env

    nameIndex = "workassist.index"
    nameFlag = "workassist.flag"

    arg = LocalReference (PrimType argTp) "arg"

data ShardConfig = WithShards (Operand (Ptr (SizedArray Word64))) (Operand (Ptr (SizedArray Word64)))
                 | NoShards

bindKernelMemory 
  :: forall env. 
     PrimType (Ptr (Struct ((Header, Struct env), SizedArray Word)))
  -> Bool 
  -> CodeGen Native (ShardConfig, Operand (Ptr (SizedArray Word)))
bindKernelMemory argTp useSharded = 
  do
    let kernelMemory' = GetElementPtr (gepStruct kernelMemTp arg $ TupleIdxRight TupleIdxSelf)
    if useSharded
      then do
        kernelMemory <- instr' kernelMemory'
        kernelMemoryWithShards <- instr' $ PtrCast (PtrPrimType memTp defaultAddrSpace) kernelMemory
        instr_ $ downcast $ nameShards := GetElementPtr (gepStruct shardIndexesTp kernelMemoryWithShards $ TupleIdxLeft $ TupleIdxLeft TupleIdxSelf)
        instr_ $ downcast $ nameShardSizes := GetElementPtr (gepStruct shardSizesTp kernelMemoryWithShards $ TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
        instr_ $ downcast $ nameKernelMemory := GetElementPtr (gepStruct kernelMemTp kernelMemoryWithShards $ TupleIdxRight TupleIdxSelf)
        return ( WithShards (LocalReference (PrimType $ PtrPrimType shardIndexesTp defaultAddrSpace) nameShards)
                           (LocalReference (PrimType $ PtrPrimType shardSizesTp defaultAddrSpace) nameShardSizes)
               , LocalReference (PrimType $ PtrPrimType kernelMemTp defaultAddrSpace) nameKernelMemory
               )
      else do
        instr_ $ downcast $ nameKernelMemory := kernelMemory'
        return (NoShards, LocalReference (PrimType $ PtrPrimType kernelMemTp defaultAddrSpace) nameKernelMemory)
  where
    arg = LocalReference (PrimType argTp) "arg"
    memTp = StructPrimType False $ TupRsingle shardIndexesTp `TupRpair` TupRsingle shardSizesTp `TupRpair` TupRsingle kernelMemTp

    nameShards = "workassist.shards"
    nameShardSizes = "workassist.shard_sizes"
    nameKernelMemory = "kernel_memory"
