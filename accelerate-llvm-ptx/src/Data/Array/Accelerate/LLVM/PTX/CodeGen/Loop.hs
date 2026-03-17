-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen.Loop
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen.Loop
  where

-- accelerate
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic            as A
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop        as Loop

import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.Target

import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.Volatile

-- | A standard loop where the CUDA threads cooperatively step over an index
-- space from the start to end indices. The threads stride the array in a way
-- that maintains memory coalescing.
--
-- The start and end array indices are given as natural array indexes, and the
-- thread specific indices are calculated by the loop.
--
-- > for ( int i = blockDim.x * blockIdx.x + threadIdx.x + start
-- >     ; i <  end
-- >     ; i += blockDim.x * gridDim.x )
--
-- TODO: This assumes that the starting offset retains alignment to the warp
--       boundary. This might not always be the case, so provide a version that
--       explicitly aligns reads to the warp boundary.
--
imapFromTo :: Operands Int -> Operands Int -> (Operands Int -> CodeGen PTX ()) -> CodeGen PTX ()
imapFromTo start end body = do
  step  <- A.fromIntegral integralType numType =<< gridSize
  tid   <- A.fromIntegral integralType numType =<< globalThreadIdx
  i0    <- add numType tid start
  --
  Loop.imapFromStepTo [] i0 step end body

-- Self scheduled loop, where work is distributed per thread block.
--
-- The given function is called with the same index on all threads
-- in a threadblock.
--
loopSelfScheduled
  :: Operand (Ptr Word64) -- Atomic counter
  -> Operand Word64       -- Total number of iterations
  -> (Operand Word64 -> CodeGen PTX ())
  -> CodeGen PTX ()
loopSelfScheduled counter size doWork = do
  claim    <- newBlock "selfscheduled.loop.claim"
  work     <- newBlock "selfscheduled.loop.work"
  exit     <- newBlock "selfscheduled.exit"

  _ <- br claim

  _ <- setBlock claim
  index' <- staticSharedMem scalarTypeWord64 1
  let index = ptrCast (ScalarPrimType scalarTypeWord64) index'
  -- With one thread per threadblock, claim a new tile
  __syncthreads
  perThreadBlock $ do
    claimed <- Loop.atomicAdd Monotonic counter (integral TypeWord64 1)
    _ <- instr' $ Store Volatile index claimed Nothing
    return ()
  __syncthreads

  index <- instr' $ Load Volatile index Nothing

  condition <- lt singleType (OP_Word64 index) (OP_Word64 size)
  _ <- cbr condition work exit

  _ <- setBlock work
  doWork index
  _ <- br claim

  _ <- setBlock exit
  return ()

-- | Generates a loop over a range, handled together by all threads in the
-- threadblock. The loop is split in contiguous parts assigned to warps, and
-- within a warp we use a strided loops with the warp size as stride.
--
-- This function generates two variants. It specializes the code on whether
-- the tile is full.
loopInThreadblock
  :: Bool -- Descending
  -> Bool -- Loop peeling
  -> Int -- Items per thread, if the tile is full
  -> Operand Int -- Lower bound (inclusive)
  -> Operand Int -- Upper bound (exclusive)
  -> Operand Bool -- Whether the tile is full (i.e. upper - lower == perThread * #threads in threadblock)
  -> (Operand Bool -> Operand Bool -> Maybe (Operand Int32) -> Operand Int -> Operand Int -> Operand Int -> CodeGen PTX ())
  -> CodeGen PTX ()
loopInThreadblock descending peel perThread lower upper isFull body = do
  full    <- newBlock "threadblockloop.full"
  partial <- newBlock "threadblockloop.partial"
  exit    <- newBlock "threadblockloop.exit"
  _ <- cbr (OP_Bool isFull) full partial

  _ <- setBlock full
  -- The tile is full.
  -- Local 'do' to introduce variables locally to the full-mode
  do
    warpSz' <- warpSize
    warpSz <- A.fromIntegral TypeInt32 numType warpSz'
    laneIdx <- laneId >>= A.fromIntegral TypeInt32 numType
    -- Start index for thiw warp: lower + warpSize * perThread * warpIdx
    startIdx <- do
      a <- A.mul numType warpSz (OP_Int $ integral TypeInt perThread)
      warpIdx <- warpId >>= A.fromIntegral TypeInt32 numType
      b <- A.mul numType a warpIdx
      A.add numType (OP_Int lower) b

    let ann = [Loop.LoopNonEmpty] ++ [Loop.LoopPeel | peel]

    Loop.loopWith ann descending (OP_Int $ integral TypeInt 0) (OP_Int $ integral TypeInt perThread) $ \(OP_Bool isFirstForThread) idxForThread -> do
      -- TODO: Decide whether the indices within the warp should be reversed as well, for descending loops
      offset <- A.mul numType idxForThread warpSz
      OP_Int localIdx <- A.mul numType idxForThread warpSz >>= A.add numType laneIdx
      OP_Int globalIdx <- A.add numType startIdx $ OP_Int localIdx
      body (boolean True) isFirstForThread Nothing (op TypeInt idxForThread) localIdx globalIdx

  br exit

  _ <- setBlock partial
  -- TODO: Handle final, non-full tile
  -- And TODO: Mask operations in parCodeGen

  br exit

  _ <- setBlock exit
  return ()
  