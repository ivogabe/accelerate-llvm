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

  tupleAlloca, tupleStore, tupleLoad,

  intOfIndex

) where

import Control.Applicative
import Prelude                                                      hiding ( read )
import Data.Bits
import Data.Typeable                                                ( (:~:)(..) )

import LLVM.AST.Type.AddrSpace
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Array.Buffer                           ( ScalarArrayDataR, SingleArrayDict(..), singleArrayDict )
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
      = ir t <$> readBuffer t TypeInt irbuffer linearIdx'
    read _ _ = internalError "Tuple mismatch"
  read tp buffers

-- | Read a value from an array at the given index
--
{-# INLINEABLE readArray #-}
readArray
    :: forall int genv m sh e arch.
       IntegralType int
    -> Gamma genv
    -> Arg genv (m sh e) -- m is In or Mut
    -> Operands int
    -> CodeGen arch (Operands e)
readArray int env (ArgArray _ (ArrayR _ tp) _ buffers) (op int -> ix) = read tp buffers
  where
    read :: forall t. TypeR t -> GroundVars genv (Buffers t) -> CodeGen arch (Operands t)
    read TupRunit         _                = return OP_Unit
    read (TupRpair t1 t2) (TupRpair b1 b2) = OP_Pair <$> read t1 b1 <*> read t2 b2
    read (TupRsingle t)   (TupRsingle buffer)
      | Refl <- reprIsSingle @ScalarType @t @Buffer t
      , irbuffer <- aprjBuffer buffer env
      = ir t <$> readBuffer t int irbuffer ix
    read _ _ = internalError "Tuple mismatch"

readBuffer
    :: ScalarType e
    -> IntegralType int
    -> IRBuffer e
    -> Operand int
    -> CodeGen arch (Operand e)
readBuffer e i (IRBuffer buffer a v IRBufferScopeArray) ix = do
  p <- getElementPtr a e i buffer ix
  load a e v p
readBuffer e i (IRBuffer buffer a v IRBufferScopeSingle) _ = do
  p <- getElementPtr a e TypeInt buffer (scalar scalarTypeInt 0)
  x <- load a e v p
  return x
readBuffer _ _ _ _ = internalError "Cannot read from buffer in Tile scope"


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
      = writeBuffer t TypeInt irbuffer linearIdx' value
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
      = writeBuffer t TypeInt irbuffer linearIdx' value
    write _ _ _ = internalError "Tuple mismatch"
  write tp buffers val


-- | Write a value into an array at the given index
--
{-# INLINEABLE writeArray #-}
writeArray
    :: forall int genv m sh e arch.
       IntegralType int
    -> Gamma genv
    -> Arg genv (m sh e) -- m is Out or Mut
    -> Operands int
    -> Operands e
    -> CodeGen arch ()
writeArray int env (ArgArray _ (ArrayR _ tp) _ buffers) (op int -> ix) val = write tp buffers val
  where
    write :: forall t. TypeR t -> GroundVars genv (Buffers t) -> Operands t -> CodeGen arch ()
    write TupRunit _ _ = return ()
    write (TupRpair t1 t2) (TupRpair b1 b2)    (OP_Pair v1 v2) = write t1 b1 v1 >> write t2 b2 v2
    write (TupRsingle t)   (TupRsingle buffer) (op t -> value)
      | Refl <- reprIsSingle @ScalarType @t @Buffer t
      , irbuffer <- aprjBuffer buffer env
      = writeBuffer t int irbuffer ix value
    write _ _ _ = internalError "Tuple mismatch"


writeBuffer
    :: ScalarType e
    -> IntegralType int
    -> IRBuffer e
    -> Operand int
    -> Operand e
    -> CodeGen arch ()
writeBuffer e i (IRBuffer buffer a v IRBufferScopeArray) ix x = do
  p <- getElementPtr a e i buffer ix
  _ <- store a v e p x
  return ()
writeBuffer e i (IRBuffer buffer a v IRBufferScopeSingle) ix x = do
  p <- getElementPtr a e TypeInt buffer (scalar scalarTypeInt 0)
  _ <- store a v e p x
  return ()
writeBuffer _ _ _ _ _ = return () -- Buffer is fused away


-- | A wrapper around the GetElementPtr instruction, which correctly
-- computes the pointer offset for non-power-of-two SIMD types
--
getElementPtr
    :: AddrSpace
    -> ScalarType e
    -> IntegralType int
    -> Operand (Ptr (ScalarArrayDataR e))
    -> Operand int
    -> CodeGen arch (Operand (Ptr e))
getElementPtr _ t@(SingleScalarType tp)   _ arr ix
  | SingleArrayDict <- singleArrayDict tp = instr' $ GetElementPtr t arr [ix]
getElementPtr a t@(VectorScalarType v) i arr ix
  | VectorType n tp <- v
  , IntegralDict   <- integralDict i
  -- We do not put padding between vector elelemnts. LLVM does do that to
  -- align the elements, which is an issue for Vectors of a size which isn't
  -- a power of two. Hence we need to do more work to compute the pointer to a
  -- Vector. We treat a 'Buffer (Vec n t)' as a 'Ptr t' (as seen in the type
  -- families ScalarArrayDataR and MarshalArg).
  = if popCount n == 1
       then do
          -- The vector size is a power of two, so there is no difference in
          -- padding between our and LLVM's semantics. We cast the pointer to a
          -- pointer of vectors and then perform GetElementPointer on that.
          arr' <- instr' $ PtrCast ptrVecType arr
          instr' $ GetElementPtr t arr' [ix]
       else do
          -- 
          ix'  <- instr' $ Mul (IntegralNumType i) ix (integral i (fromIntegral n))
          p'   <- instr' $ GetElementPtr (SingleScalarType tp) arr [integral i 0, ix']
          instr' $ PtrCast ptrVecType p'
  where
    ptrVecType = PtrPrimType (ScalarPrimType (VectorScalarType v)) a


-- | A wrapper around the Load instruction, which splits non-power-of-two
-- SIMD types into a sequence of smaller reads.
--
-- Note: [Non-power-of-two loads and stores]
--
-- Splitting this operation a sequence of smaller power-of-two stores does
-- not work because those instructions may (will) violate alignment
-- restrictions, causing a general protection fault. So, we simply
-- implement those stores as a sequence of stores for each individual
-- element.
--
-- We could do runtime checks for what the pointer alignment is and perform
-- a vector store when we align on the right boundary, but I'm not sure the
-- extra complexity is worth it.
--
load :: AddrSpace
     -> ScalarType e
     -> Volatility
     -> Operand (Ptr e)
     -> CodeGen arch (Operand e)
load addrspace e v p
  | SingleScalarType{} <- e = instr' $ Load e v p
  | VectorScalarType s <- e
  , VectorType n base  <- s
  , m                  <- fromIntegral n
  = if popCount m == 1
       then instr' $ Load e v p
       else do
         p' <- instr' $ PtrCast (PtrPrimType (ScalarPrimType (SingleScalarType base)) addrspace) p
         --
         let go i w
               | i >= m    = return w
               | otherwise = do
                   q  <- instr' $ GetElementPtr (SingleScalarType base) p' [integral integralType i]
                   r  <- instr' $ Load (SingleScalarType base) v q
                   w' <- instr' $ InsertElement i w r
                   go (i+1) w'
         --
         go 0 (undef e)


-- | A wrapper around the Store instruction, which splits non-power-of-two
-- SIMD types into a sequence of smaller writes.
--
-- See: [Non-power-of-two loads and stores]
--
store :: AddrSpace
      -> Volatility
      -> ScalarType e
      -> Operand (Ptr e)
      -> Operand e
      -> CodeGen arch ()
store addrspace volatility e p v
  | SingleScalarType{} <- e = do_ $ Store volatility p v
  | VectorScalarType s <- e
  , VectorType n base  <- s
  , m                  <- fromIntegral n
  = if popCount m == 1
       then do_ $ Store volatility p v
       else do
         p' <- instr' $ PtrCast (PtrPrimType (ScalarPrimType (SingleScalarType base)) addrspace) p
         --
         let go i
               | i >= m    = return ()
               | otherwise = do
                   x <- instr' $ ExtractElement i v
                   q <- instr' $ GetElementPtr (SingleScalarType base) p' [integral integralType i]
                   _ <- instr' $ Store volatility q x
                   go (i+1)
         go 0

{--
      let
          go :: forall arch n t. SingleType t -> Int32 -> Operand (Ptr t) -> Operand (Vec n t) -> CodeGen arch ()
          go t offset ptr' val'
            | offset >= size = return ()
            | otherwise      = do
                let remaining = size - offset
                    this      = setBit 0 (finiteBitSize remaining - countLeadingZeros remaining - 1)

                    vec'      = VectorType (fromIntegral this) t
                    ptr_vec'  = PtrPrimType (ScalarPrimType (VectorScalarType vec')) addrspace

                    repack :: Int32 -> Operand (Vec m t) -> CodeGen arch (Operand (Vec m t))
                    repack j u
                      | j >= this = return u
                      | otherwise = do
                          x <- instr' $ ExtractElement (offset + j) val'
                          v <- instr' $ InsertElement j u x
                          repack (j+1) v

                if remaining == 1
                   then do
                     x <- instr' $ ExtractElement offset val'
                     _ <- instr' $ Store volatility ptr' x
                     return ()

                   else do
                     v <- repack 0 $ undef (VectorScalarType vec')
                     p <- instr' $ PtrCast ptr_vec' ptr'
                     _ <- instr' $ Store volatility p v

                     q <- instr' $ GetElementPtr ptr' [integral integralType this]
                     go t (offset + this) q val'

      ptr' <- instr' $ PtrCast (PtrPrimType (ScalarPrimType (SingleScalarType base)) addrspace) ptr
      go base 0 ptr' val

  where
    VectorType (fromIntegral -> size) base = vec
--}

tupleAlloca :: forall e arch. TypeR e -> CodeGen arch (TupR Operand (Distribute Ptr e))
tupleAlloca TupRunit = return TupRunit
tupleAlloca (TupRpair t1 t2) = TupRpair <$> tupleAlloca t1 <*> tupleAlloca t2
tupleAlloca (TupRsingle tp)
  | Refl <- reprIsSingle @ScalarType @e @Ptr tp
  = TupRsingle <$> instr' (Alloca $ ScalarPrimType tp)

tupleStore :: forall e arch. TypeR e -> TupR Operand (Distribute Ptr e) -> Operands e -> CodeGen arch ()
tupleStore TupRunit _ _ = return ()
tupleStore (TupRpair t1 t2) (TupRpair p1 p2) (OP_Pair v1 v2) =
  tupleStore t1 p1 v1 >> tupleStore t2 p2 v2
tupleStore (TupRsingle tp) (TupRsingle ptr) value 
  | Refl <- reprIsSingle @ScalarType @e @Ptr tp = do
    instr' $ Store NonVolatile ptr $ op tp value
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
