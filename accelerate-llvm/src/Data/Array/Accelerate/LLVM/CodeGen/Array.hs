{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Array
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Array (

  readArray, readArray',
  writeArray, writeArray', writeArrayAt',
  readBuffer,
  writeBuffer,

  tupleAlloca, tuplePtrs, tupleStore, tupleLoad,

  intOfIndex,

  firstArrayPtr

) where

import Control.Applicative
import Prelude                                                      hiding ( read )
import Data.Bits
import Data.Typeable                                                ( (:~:)(..) )

import LLVM.AST.Type.GetElementPtr
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Metadata

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Error

import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic      as A


-- | Read a value from an array at the given index
--
{-# INLINEABLE readArray' #-}
readArray'
    :: forall int genv idxEnv m sh e arch.
       Envs genv idxEnv
    -> Arg genv (m sh e) -- m is In or Mut
    -> ExpVars idxEnv sh
    -> CodeGen arch (Operands e)
readArray' env (ArgArray _ (ArrayR shr tp) sh buffers) idx = do
  let sh' = envsPrjSh shr sh env
  let idx' = envsPrjIndices idx env
  linearIdx <- intOfIndex shr sh' idx'
  let linearIdx' = op TypeInt linearIdx
  let
    read :: forall t. TypeR t -> GroundVars genv (Buffers t) -> CodeGen arch (Operands t)
    read TupRunit         _                = return OP_Unit
    read (TupRpair t1 t2) (TupRpair b1 b2) = OP_Pair <$> read t1 b1 <*> read t2 b2
    read (TupRsingle t)   (TupRsingle buffer)
      | Refl <- reprIsSingle @ScalarType @t @Buffer t
      , irbuffer <- envsPrjBuffer buffer env
      = ir t <$> readBuffer t TypeInt irbuffer linearIdx' (Just $ op TypeInt $ envsTileLocalIndex env)
    read _ _ = internalError "Tuple mismatch"
  read tp buffers

-- | Read a value from an array at the given index
--
{-# INLINEABLE readArray #-}
readArray
    :: forall int genv idxEnv m sh e arch.
       IntegralType int
    -> Envs genv idxEnv
    -> Arg genv (m sh e) -- m is In or Mut
    -> Operands int
    -> CodeGen arch (Operands e)
readArray int envs (ArgArray _ (ArrayR _ tp) _ buffers) (op int -> ix) = read tp buffers
  where
    read :: forall t. TypeR t -> GroundVars genv (Buffers t) -> CodeGen arch (Operands t)
    read TupRunit         _                = return OP_Unit
    read (TupRpair t1 t2) (TupRpair b1 b2) = OP_Pair <$> read t1 b1 <*> read t2 b2
    read (TupRsingle t)   (TupRsingle buffer)
      | Refl <- reprIsSingle @ScalarType @t @Buffer t
      , irbuffer <- envsPrjBuffer buffer envs
      = ir t <$> readBuffer t int irbuffer ix Nothing
    read _ _ = internalError "Tuple mismatch"

readBuffer
    :: ScalarType e
    -> IntegralType int
    -> IRBuffer e
    -> Operand int
    -> Maybe (Operand Int) -- Index within a tile, if in a tile loop
    -> CodeGen arch (Operand e)
readBuffer e i (IRBuffer buffer a v IRBufferScopeArray alias) ix _ = do
  p <- getElementPtr a e i buffer ix
  load a e v p alias
readBuffer e i (IRBuffer buffer a v IRBufferScopeSingle alias) _ _ = do
  p <- getElementPtr a e TypeInt buffer (scalar scalarTypeInt 0)
  load a e v p alias
readBuffer e i (IRBuffer buffer a v IRBufferScopeTile alias) _ (Just localIx) = do
  p <- getElementPtr a e TypeInt buffer localIx
  load a e v p alias
readBuffer _ _ _ _ _ = internalError "Cannot read from buffer in Tile scope"

-- | Write a value into an array at the given index
--
{-# INLINEABLE writeArray' #-}
writeArray'
    :: forall int genv idxEnv m sh e arch.
       Envs genv idxEnv
    -> Arg genv (m sh e) -- m is Out or Mut
    -> ExpVars idxEnv sh
    -> Operands e
    -> CodeGen arch ()
writeArray' env (ArgArray _ (ArrayR shr tp) sh buffers) idx val = do
  let sh' = envsPrjSh shr sh env
  let idx' = envsPrjIndices idx env
  linearIdx <- intOfIndex shr sh' idx'
  let linearIdx' = op TypeInt linearIdx
  let
    write :: forall t. TypeR t -> GroundVars genv (Buffers t) -> Operands t -> CodeGen arch ()
    write TupRunit _ _ = return ()
    write (TupRpair t1 t2) (TupRpair b1 b2)    (OP_Pair v1 v2) = write t1 b1 v1 >> write t2 b2 v2
    write (TupRsingle t)   (TupRsingle buffer) (op t -> value)
      | Refl <- reprIsSingle @ScalarType @t @Buffer t
      , irbuffer <- envsPrjBuffer buffer env
      = writeBuffer t TypeInt irbuffer linearIdx' (Just $ op TypeInt $ envsTileLocalIndex env) value
    write _ _ _ = internalError "Tuple mismatch"
  write tp buffers val


-- | Write a value into an array at the given index
--
{-# INLINEABLE writeArrayAt' #-}
writeArrayAt'
    :: forall int genv idxEnv m sh e arch.
       Envs genv idxEnv
    -> Arg genv (m (sh, Int) e) -- m is Out or Mut
    -> ExpVars idxEnv sh
    -> Operand Int
    -> Operands e
    -> CodeGen arch ()
writeArrayAt' env (ArgArray _ (ArrayR shr tp) sh buffers) idx i val = do
  let sh' = envsPrjSh shr sh env
  let idx' = envsPrjIndices idx env
  linearIdx <- intOfIndex shr sh' (OP_Pair idx' $ OP_Int i)
  let linearIdx' = op TypeInt linearIdx
  let
    write :: forall t. TypeR t -> GroundVars genv (Buffers t) -> Operands t -> CodeGen arch ()
    write TupRunit _ _ = return ()
    write (TupRpair t1 t2) (TupRpair b1 b2)    (OP_Pair v1 v2) = write t1 b1 v1 >> write t2 b2 v2
    write (TupRsingle t)   (TupRsingle buffer) (op t -> value)
      | Refl <- reprIsSingle @ScalarType @t @Buffer t
      , irbuffer <- envsPrjBuffer buffer env
      -- Note that operations using writeArrayAt' cannot fuse,
      -- hence we can pass Nothing here.
      = writeBuffer t TypeInt irbuffer linearIdx' Nothing value
    write _ _ _ = internalError "Tuple mismatch"
  write tp buffers val


-- | Write a value into an array at the given index
--
{-# INLINEABLE writeArray #-}
writeArray
    :: forall int genv idxEnv m sh e arch.
       IntegralType int
    -> Envs genv idxEnv
    -> Arg genv (m sh e) -- m is Out or Mut
    -> Operands int
    -> Operands e
    -> CodeGen arch ()
writeArray int envs (ArgArray _ (ArrayR _ tp) _ buffers) (op int -> ix) val = write tp buffers val
  where
    write :: forall t. TypeR t -> GroundVars genv (Buffers t) -> Operands t -> CodeGen arch ()
    write TupRunit _ _ = return ()
    write (TupRpair t1 t2) (TupRpair b1 b2)    (OP_Pair v1 v2) = write t1 b1 v1 >> write t2 b2 v2
    write (TupRsingle t)   (TupRsingle buffer) (op t -> value)
      | Refl <- reprIsSingle @ScalarType @t @Buffer t
      , irbuffer <- envsPrjBuffer buffer envs
      = writeBuffer t int irbuffer ix Nothing value
    write _ _ _ = internalError "Tuple mismatch"


writeBuffer
    :: ScalarType e
    -> IntegralType int
    -> IRBuffer e
    -> Operand int
    -> Maybe (Operand Int) -- The local index within a tile, if in a tile loop
    -> Operand e
    -> CodeGen arch ()
writeBuffer e i (IRBuffer buffer a v IRBufferScopeArray alias) ix _ x = do
  p <- getElementPtr a e i buffer ix
  _ <- store a v e p x alias
  return ()
writeBuffer e i (IRBuffer buffer a v IRBufferScopeSingle alias) ix _ x = do
  p <- getElementPtr a e TypeInt buffer (scalar scalarTypeInt 0)
  _ <- store a v e p x alias
  return ()
writeBuffer e i (IRBuffer buffer a v IRBufferScopeTile alias) _ (Just localIx) x = do
  p <- getElementPtr a e TypeInt buffer localIx
  _ <- store a v e p x alias
  return ()
writeBuffer _ _ _ _ _ _ = internalError "Cannot write to buffer in Tile scope"


-- | A wrapper around the GetElementPtr instruction, which correctly
-- computes the pointer offset for non-power-of-two SIMD types
--
getElementPtr
    :: AddrSpace
    -> ScalarType e
    -> IntegralType int
    -> Operand (Ptr e)
    -> Operand int
    -> CodeGen arch (Operand (Ptr e))
getElementPtr _ _ _ arr ix = instr' $ GetElementPtr $ GEP1 arr ix


-- | A wrapper around the Load instruction.
-- This function used to be needed when we treated Vector types (Vec)
-- differently, now it directly emits a single Load instruction.
--
load :: AddrSpace
     -> ScalarType e
     -> Volatility
     -> Operand (Ptr e)
     -> Maybe (MetadataNodeID, MetadataNodeID)
     -> CodeGen arch (Operand e)
load addrspace e v p alias = instrMD' (Load e v p) (bufferMetadata' alias)


-- | A wrapper around the Store instruction.
-- This function used to be needed when we treated Vector types (Vec)
-- differently, now it directly emits a single Store instruction.
--
store :: AddrSpace
      -> Volatility
      -> ScalarType e
      -> Operand (Ptr e)
      -> Operand e
      -> Maybe (MetadataNodeID, MetadataNodeID)
      -> CodeGen arch ()
store addrspace volatility e p v alias = do
    _ <- instrMD' (Store volatility p v) (bufferMetadata' alias)
    return ()

tupleAlloca :: forall e arch. TypeR e -> CodeGen arch (TupR Operand (Distribute Ptr e))
tupleAlloca TupRunit = return TupRunit
tupleAlloca (TupRpair t1 t2) = TupRpair <$> tupleAlloca t1 <*> tupleAlloca t2
tupleAlloca (TupRsingle tp)
  | Refl <- reprIsSingle @ScalarType @e @Ptr tp
  = TupRsingle <$> hoistAlloca (ScalarPrimType tp)

tuplePtrs :: forall full arch. TypeR full -> Operand (Ptr (Struct full)) -> CodeGen arch (TupR Operand (Distribute Ptr full))
tuplePtrs tp ptr = go TupleIdxSelf tp
  where
    go :: forall e. TupleIdx full e -> TypeR e -> CodeGen arch (TupR Operand (Distribute Ptr e))
    go _ TupRunit = return TupRunit
    go tupleIdx (TupRpair t1 t2)
      = TupRpair <$> go (tupleLeft tupleIdx) t1 <*> go (tupleRight tupleIdx) t2
    go tupleIdx (TupRsingle t)
      | Refl <- reprIsSingle @ScalarType @e @Ptr t
      = TupRsingle <$> instr' (GetElementPtr $ gepStruct (ScalarPrimType t) ptr tupleIdx)

tupleStore :: forall e arch. TypeR e -> TupR Operand (Distribute Ptr e) -> Operands e -> CodeGen arch ()
tupleStore TupRunit _ _ = return ()
tupleStore (TupRpair t1 t2) (TupRpair p1 p2) (OP_Pair v1 v2) =
  tupleStore t1 p1 v1 >> tupleStore t2 p2 v2
tupleStore (TupRsingle tp) (TupRsingle ptr) value 
  | Refl <- reprIsSingle @ScalarType @e @Ptr tp = do
    _ <- instr' $ Store NonVolatile ptr $ op tp value
    return ()
tupleStore _ _ _ = internalError "Tuple mismatch"

tupleLoad :: forall e arch. TypeR e -> TupR Operand (Distribute Ptr e) -> CodeGen arch (Operands e)
tupleLoad TupRunit _ = return OP_Unit
tupleLoad (TupRpair t1 t2) (TupRpair p1 p2) = OP_Pair <$> tupleLoad t1 p1 <*> tupleLoad t2 p2
tupleLoad (TupRsingle tp) (TupRsingle ptr)
  | Refl <- reprIsSingle @ScalarType @e @Ptr tp
  = instr $ Load tp NonVolatile ptr
tupleLoad _ _ = internalError "Tuple mismatch"

-- | Convert a multidimensional array index into a linear index
--
intOfIndex :: ShapeR sh -> Operands sh -> Operands sh -> CodeGen arch (Operands Int)
intOfIndex ShapeRz OP_Unit OP_Unit
  = return $ A.liftInt 0
intOfIndex (ShapeRsnoc shr) (OP_Pair sh sz) (OP_Pair ix i)
  -- If we short-circuit the last dimension, we can avoid inserting
  -- a multiply by zero and add of the result.
  = case shr of
      ShapeRz -> return i
      _       -> do
        a <- intOfIndex shr sh ix
        b <- A.mul numType a sz
        c <- A.add numType b i
        return c

firstArrayPtr :: forall arch env idxEnv m sh e. Envs env idxEnv -> Arg env (m sh e) -> CodeGen arch (Operands Int)
firstArrayPtr envs (ArgArray _ _ _ vars) = case flattenTupR vars of
  [] -> return $ A.liftInt 0
  Exists var : _ -> case prjPartial (varIdx var) $ envsGround envs of
    Just (GroundOperandBuffer (IRBuffer ptr _ _ _ _)) ->
      instr $ PtrToInt TypeInt ptr
    _ -> internalError "Buffer not found in firstArrayPtr"
