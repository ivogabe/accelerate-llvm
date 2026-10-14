{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Permute
-- Copyright   : [2016..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Permute (
  detectRMW, detectCAS,
  atomicCasLoop
) where

import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Type

import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Sugar

import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.RMW                                as RMW
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Metadata
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation

import Control.Applicative
import Data.Bits
import Data.String
import Prelude


-- | A forward permutation might be specialised to use atomic instructions to
-- perform the read-modify-write of the output array directly, rather than
-- separately acquiring a lock. This function detects RMW operations in Exp
-- code.
--
-- Specialisation for atomic operations is currently limited to direct
-- applications of the function; that is, we don't dig down underneath
-- let-bindings.
--
detectRMW
    :: forall aenv e.
       Fun aenv (e -> e -> e)
    -> Maybe ( ScalarType e, RMWOperation, Fun aenv (e -> e) )
detectRMW fun
  -- If the old value is not used (i.e. permute const) then we can just
  -- store the new value directly. Since we do not require the return value
  -- we can do this for any scalar value with a regular Store.
  -- 
  -- However, as we use an unzipped struct-of-array representation for product
  -- types, this is not possible if 'e' is a pair. Previous versions of
  -- Accelerate did allow this, with a risk for inconsistent data due to non-
  -- atomic updates. The use case for this feature was permute with non-
  -- overlapping indices, which is now served by permuteUnique.
  --
  | Lam lhs (Lam (LeftHandSideWildcard tp) (Body body)) <- fun
  , TupRsingle tp' <- tp
  , isProperlyAligned tp'
  = Just (tp', Exchange, Lam lhs $ Body body)

  -- Detect RMW operations, that may be handled by atomic-fetch-and-something.
  | Lam lhs@(LeftHandSideSingle tp@SingleScalarType{}) (Lam (LeftHandSideSingle _) (Body body)) <- fun
  -- SingleTypes are aligned to their size, no need to check isProperlyAligned
  , Just (rmw, x)         <- rmwOp body
  , Just x'               <- strengthenE latest x
  = Just (tp, rmw, Lam lhs (Body x'))

  | otherwise
  = Nothing
  where
    -- XXX: This doesn't work for newtypes because the coercion gets in the
    -- way. This should be generalised to work for product types (e.g.
    -- complex numbers) and take this factor into account as well.
    --    TLM-2019-09-27
    --
    rmwOp :: OpenExp (((),e),e) aenv e -> Maybe (RMWOperation, OpenExp (((),e),e) aenv e)
    rmwOp (PrimApp f xs)
      | PrimAdd{}  <- f = (RMW.Add,) <$> extract xs
      | PrimSub{}  <- f = (RMW.Sub,) <$> extract xs
      | PrimMin{}  <- f = (RMW.Min,) <$> extract xs
      | PrimMax{}  <- f = (RMW.Max,) <$> extract xs
      | PrimBOr{}  <- f = (RMW.Or,)  <$> extract xs
      | PrimBAnd{} <- f = (RMW.And,) <$> extract xs
      | PrimBXor{} <- f = (RMW.Xor,) <$> extract xs
    rmwOp _             = Nothing

    -- Determine which argument to a binary function was the new value being
    -- combined. This only works when the old value is used unmodified, but that
    -- is sufficient for us because otherwise it would not be suitable for the
    -- atomic update operation.
    --
    -- In the permutation function, the old value is given as the second
    -- argument, corresponding to ZeroIdx.
    --
    extract :: OpenExp (((),e),e) aenv (e,e) -> Maybe (OpenExp (((),e),e) aenv e)
    extract (Pair x y)
      | Evar (Var _ ZeroIdx) <- x = Just y
      | Evar (Var _ ZeroIdx) <- y = Just x
    extract _
      = Nothing

    -- Used with 'strengthenE' to ensure that the expression does not make use
    -- of the old value except in the combination function.
    latest :: (((),e),e) :?> ((),e)
    latest ZeroIdx      = Nothing
    latest (SuccIdx ix) = Just ix

-- | Detects whether this operation can be used in a compare-and-swap loop,
-- instead of using locks for synchronisation.
detectCAS :: Fun aenv (e -> e -> e) -> Maybe (ScalarType e)
detectCAS (Lam lhs _)
  | TupRsingle tp <- lhsToTupR lhs
  , isProperlyAligned tp = Just tp
detectCAS _ = Nothing

-- | Checks whether values of the given type are properly aligned, when stored
-- in arrays. Note that vector types may have higher alignment in arrays,
-- than the guaranteed alignment in other locations (like kernel memory or on,
-- the stack, as computed by scalarTypeAlignment).
--
-- All single types are aligned to their size.
-- Vector types are aligned to the size of their element.
-- Since buffers are aligned to 64 bytes (CACHE_LINE_SIZE in align.h),
-- vector types will be properly aligned if their size is a power of two,
-- and their total size is less than 64 bytes.
isProperlyAligned :: ScalarType e -> Bool
isProperlyAligned (SingleScalarType _) = True
isProperlyAligned (VectorScalarType (VectorType w tp)) = popCount w == 1 && singleTypeSize tp * w <= 64


-- Implementation of atomic RMW operation (e.g. (+), (-)) using atomic
-- compare-and-swap instructions, for targets which do not support the native
-- instruction at this type but do support CAS at this bit width.
--
-- > void casAdd(double *addr, double val)
-- > {
-- >     uint64_t* addr_i = reinterpret_cast<uint64_t*> addr;
-- >     uint64_t old     = *addr_i;
-- >
-- >     do {
-- >       uint64_t expected = old;
-- >       uint64_t new      = reinterpret_cast<uint64_t>(val + reinterpret_cast<double>(expected));
-- >       if (old == new) break;
-- >
-- >       uint64_t old      = atomicCAS(addr_i, expected, new);
-- >     }
-- >     while (old != expected);
-- > }
--
atomicCasLoop
  :: ScalarType e
  -> (Operands e -> CodeGen arch (Operands e))
  -> Operand (Ptr e)
  -> Maybe (MetadataNodeID, MetadataNodeID)
  -> CodeGen arch ()
atomicCasLoop tp update addr alias
  | Exists i <- intTypeOfSize (scalarTypeSize tp) = do
    let si = SingleScalarType $ NumSingleType $ IntegralNumType i
    let addr' = ptrCast (ScalarPrimType si) addr

    init' <- instrMD' (AtomicLoad si addr' Monotonic) (bufferMetadata' alias)

    spin  <- newBlock "cas.spin"
    go    <- newBlock "cas.go"
    exit  <- newBlock "cas.exit"
    old'  <- fresh  $ TupRsingle si
    top   <- br spin

    setBlock spin
    old   <- instr' $ BitCast tp (op i old')
    val   <- update $ ir tp old
    val'  <- instr' $ BitCast si (op tp val)
    same  <- A.eq (NumSingleType $ IntegralNumType i) old' (ir i val')
    -- Early exit when the newly computed value is the same as old.
    -- This may occur when the operator (update) performs min or max,
    -- and the existing value is already smaller or larger than the new value
    -- in permute.
    _ <- cbr same exit go

    setBlock go
    -- Perform the compare-and-swap
    -- TODO: We could mark this CmpXchg as weak, as it is already in a loop. That
    -- may increase performance on some systems.
    --
    -- From the LLVM language specification:
    -- If the cmpxchg operation is marked as weak then a spurious failure is
    -- permitted: the operation may not write <new> even if the comparison matched
    -- https://llvm.org/docs/LangRef.html#cmpxchg-instruction
    r     <- instrMD' (CmpXchg i NonVolatile addr' (op i old') val' (CrossThread, Monotonic) Monotonic) (bufferMetadata' alias)
    done  <- instr' $ ExtractValue primType            (TupleIdxRight TupleIdxSelf) r
    next' <- instr' $ ExtractValue (ScalarPrimType si) (TupleIdxLeft  TupleIdxSelf) r

    bot   <- cbr (OP_Bool done) exit spin
    _     <- phi' (TupRsingle si) spin old' [(ir i init',top), (ir i next',bot)]

    setBlock exit

intTypeOfSize :: Int -> Exists IntegralType
intTypeOfSize = \case
  1 -> Exists TypeWord8
  2 -> Exists TypeWord16
  4 -> Exists TypeWord32
  8 -> Exists TypeWord64
  n -> internalError $ fromString $ "No integral type of size " ++ show n
