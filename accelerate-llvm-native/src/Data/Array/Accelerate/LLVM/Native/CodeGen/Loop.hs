{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications    #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Native.Loop
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Loop
  where

-- accelerate
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Shape                   hiding ( eq )

import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic      as A
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Profile
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop            as Loop

import Data.Array.Accelerate.LLVM.Native.Target                     ( Native )

import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Constant
import LLVM.AST.Type.GetElementPtr
import qualified LLVM.AST.Type.Instruction.RMW as RMW
import qualified LLVM.AST.Type.Instruction.Compare as Compare
import LLVM.AST.Type.Name
import Data.Array.Accelerate.LLVM.CodeGen.Base

import Control.Monad.Trans
import Control.Monad.State
import Data.Bits

-- | A standard 'for' loop, that steps from the start to end index executing the
-- given function at each index.
--
imapFromTo
    :: Operands Int                                   -- ^ starting index (inclusive)
    -> Operands Int                                   -- ^ final index (exclusive)
    -> (Operands Int -> CodeGen Native ())            -- ^ apply at each index
    -> CodeGen Native ()
imapFromTo start end body =
  Loop.imapFromStepTo [] start (A.liftInt 1) end body


-- | Generate a series of nested 'for' loops which iterate between the start and
-- end indices of a given hyper-rectangle. LLVM is very good at vectorising
-- these kinds of nested loops, but not so good at vectorising the flattened
-- representation utilising to/from index.
--
imapNestFromTo
    :: [Loop.LoopAnnotation]                                     -- ^ annotations for all but the innermost loop
    -> [Loop.LoopAnnotation]                                     -- ^ annotations for the innermost loop
    -> ShapeR sh
    -> Operands sh                                          -- ^ initial index (inclusive)
    -> Operands sh                                          -- ^ final index (exclusive)
    -> Operands sh                                          -- ^ total array extent
    -> (Operands sh -> Operands Int -> CodeGen Native ())   -- ^ apply at each index
    -> CodeGen Native ()
imapNestFromTo annOuter annInner shr start end extent body =
  go shr start end body'
  where
    body' ix = body ix =<< intOfIndex shr extent ix

    go :: ShapeR t -> Operands t -> Operands t -> (Operands t -> CodeGen Native ()) -> CodeGen Native ()
    go ShapeRz OP_Unit OP_Unit k
      = k OP_Unit

    go (ShapeRsnoc shr') (OP_Pair ssh ssz) (OP_Pair esh esz) k
      = go shr' ssh esh
      $ \sz      -> Loop.imapFromStepTo ann ssz (A.liftInt 1) esz
      $ \i       -> k (OP_Pair sz i)
      where
        ann = case shr' of
          ShapeRz -> annInner
          _ -> annOuter

{--
-- TLM: this version (seems to) compute the corresponding linear index as it
--      goes. We need to compare it against the above implementation to see if
--      there are any advantages.
--
imapNestFromTo'
    :: forall sh. Shape sh
    => Operands sh
    -> Operands sh
    -> Operands sh
    -> (Operands sh -> Operands Int -> CodeGen Native ())
    -> CodeGen Native ()
imapNestFromTo' start end extent body = do
  startl <- intOfIndex extent start
  void $ go (eltType @sh) start end extent (int 1) startl body'
  where
    body' :: Operands (EltRepr sh) -> Operands Int -> CodeGen Native (Operands Int)
    body' ix l = body ix l >> add numType (int 1) l

    go :: TupleType t
       -> Operands t
       -> Operands t
       -> Operands t
       -> Operands Int
       -> Operands Int
       -> (Operands t -> Operands Int -> CodeGen Native (Operands Int))
       -> CodeGen Native (Operands Int)
    go TypeRunit OP_Unit OP_Unit OP_Unit _delta l k
      = k OP_Unit l

    go (TypeRpair tsh tsz) (OP_Pair ssh ssz) (OP_Pair esh esz) (OP_Pair exh exz) delta l k
      | TypeRscalar t <- tsz
      , Just Refl     <- matchScalarType t (scalarType :: ScalarType Int)
      = do
          delta' <- mul numType delta exz
          go tsh ssh esh exh delta' l $ \sz ll -> do
            Loop.iterFromStepTo ssz (int 1) esz ll $ \i l' ->
              k (OP_Pair sz i) l'
            add numType ll delta'

    go _ _ _ _ _ _ _
      = $internalError "imapNestFromTo'" "expected shape with Int components"
--}

{--
-- | Generate a series of nested 'for' loops which iterate between the start and
-- end indices of a given hyper-rectangle. LLVM is very good at vectorising
-- these kinds of nested loops, but not so good at vectorising the flattened
-- representation utilising to/from index.
--
imapNestFromStepTo
    :: forall sh. Shape sh
    => Operands sh                                    -- ^ initial index (inclusive)
    -> Operands sh                                    -- ^ steps
    -> Operands sh                                    -- ^ final index (exclusive)
    -> Operands sh                                    -- ^ total array extent
    -> (Operands sh -> Operands Int -> CodeGen Native ())   -- ^ apply at each index
    -> CodeGen Native ()
imapNestFromStepTo start steps end extent body =
  go (eltType @sh) start steps end (body' . IR)
  where
    body' ix = body ix =<< intOfIndex extent ix

    go :: TupleType t -> Operands t -> Operands t -> Operands t -> (Operands t -> CodeGen Native ()) -> CodeGen Native ()
    go TypeRunit OP_Unit OP_Unit OP_Unit k
      = k OP_Unit

    go (TypeRpair tsh tsz) (OP_Pair ssh ssz) (OP_Pair sts stz) (OP_Pair esh esz) k
      | TypeRscalar t <- tsz
      , Just Refl     <- matchScalarType t (scalarType :: ScalarType Int)
      = go tsh ssh sts esh
      $ \sz      -> Loop.imapFromStepTo ssz stz esz
      $ \i       -> k (OP_Pair sz i)

    go _ _ _ _ _
      = $internalError "imapNestFromTo" "expected shape with Int components"
--}

-- | Iterate with an accumulator between the start and end index, executing the
-- given function at each.
--
iterFromTo
    :: TypeR a
    -> Operands Int                                       -- ^ starting index (inclusive)
    -> Operands Int                                       -- ^ final index (exclusive)
    -> Operands a                                         -- ^ initial value
    -> (Operands Int -> Operands a -> CodeGen Native (Operands a))    -- ^ apply at each index
    -> CodeGen Native (Operands a)
iterFromTo tp start end seed body =
  Loop.iterFromStepTo [] tp start (A.liftInt 1) end seed body

-- Should match with ACCELERATE_WORK_PER_THREAD_STRIDE in types.h
workPerThreadStride :: Word32
workPerThreadStride = 8

workassistLoop
    :: Operand (Ptr Word64)                 -- index into work
    -> Operand (Ptr Word64)                 -- work_per_thread
    -> Word64                               -- maximum number of tiles to claim at once. When zero, this performs self scheduling, otherwise it performs data-parallel work stealing.
    -> Operand Word32                       -- thread index
    -> Operand Word32                       -- maximum number of threads
    -> Operand Word64                       -- size of total work
    -> (Operand Bool -> Operand Word64 -> CodeGen Native ())
    -> CodeGen Native ()
workassistLoop counter workPerThread maxClaim threadIndex maxThreads size doWork = do
  entry    <- getBlock
  claim    <- newBlock "workassist.loop.claim"
  work     <- newBlock "workassist.loop.work"
  claimed  <- newBlock "workassist.all.claimed"
  exit     <- newBlock "workassist.exit"

  let index = LocalReference (type' @Word64) "block_index"
  -- Whether the thread should operate in the single threaded mode of
  -- zero-overhead parallel scans.
  let seqMode = LocalReference (type' @Bool) "sequential_mode"
  -- Expected next block index, if we continue in sequential mode
  let nextIfSeqName = "next_block_if_seq"
  let nextIfSeq = LocalReference type' nextIfSeqName

  _ <- br claim

  _ <- setBlock claim
  if maxClaim == 1 then do
    instr_ $ downcast $ "block_index" := AtomicRMW numType NonVolatile RMW.Add counter (integral TypeWord64 1) (CrossThread, Monotonic)
    condition <- A.lt singleType (OP_Word64 index) (OP_Word64 size)
    _ <- cbr condition work exit

    _ <- setBlock work
    return ()
  else do
    claimGlobal <- newBlock "workassist.loop.claim.global"
    claimGlobalGo <- newBlock "workassist.loop.claim.global.go"
    claimGlobalSuccess <- newBlock "workassist.loop.claim.global.success"
    claimSteal <- newBlock "workassist.loop.claim.steal"

    -- In workPerThread, each thread stores the range of work it has claimed,
    -- but has not started working on.
    -- We represent this range as a single Word64 by packing the start and
    -- size of the range. The 48 most significant bits are used for the
    -- start tile index, and the 16 least significant store the size.
    -- The size is treated as a *signed* integer, and may become negative
    -- when multiple threads concurrently claim (steal) work from this entry.
    -- We limit the size of a steal, to ensure the size won't wrap around
    -- (underflow) during many concurrent steals.
    --
    -- Scheduling works via three sub-procedures:
    -- 1. Claiming from our own workPerThread entry.
    -- 2. If that fails, claim work from the global counter, add that to our
    --    entry in workPerThread.
    -- 3. If that also fails, steal work from other threads by updating their
    --    workPerThread entry.

    OP_Word32 threadIndexMulStride <- A.mul numType (OP_Word32 threadIndex) $ OP_Word32 $ integral TypeWord32 workPerThreadStride
    workPerThreadSelf <- instr' $ GetElementPtr $ GEP1 workPerThread threadIndexMulStride

    -- 1. Claim from our own workPerThread entry.
    indexLocal <- do
      -- Increment the start index of the range by one,
      -- and decrement the size by one,
      -- to claim the first item (tile) of the range.
      let increment = (1 `shiftL` 16) - 1
      packed <- instr' $ AtomicRMW numType NonVolatile RMW.Add workPerThreadSelf (integral TypeWord64 increment) (CrossThread, Monotonic)

      -- Unpack the packed value
      OP_Word64 start <- A.shiftR TypeWord64 (OP_Word64 packed) (A.liftInt 16)
      let sizeMask = (1 `shiftL` 16) - 1
      size' <- A.band TypeWord64 (OP_Word64 packed) (A.liftWord64 sizeMask)
      -- Convert to signed 16 bit number
      size16 <- A.fromIntegral TypeWord64 numType size'
      OP_Int64 size <- A.fromIntegral TypeInt16 numType size16

      success <- A.gt singleType (OP_Int64 size) $ A.liftInt64 0

      _ <- cbr success work claimGlobal
      return start

    -- 2. Otherwise, claim from global counter
    indexGlobal <- do
      _ <- setBlock claimGlobal
      -- First, use a heuristic to compute how many tiles we will claim from
      -- the global counter. This is based on the current number of remaining
      -- tiles. There is a risk for a race condition here, as there is time
      -- between computing the tile size and doing the actual fetch-and-add.
      -- This race condition is not a correctness problem however; it will
      -- only impact performance when we claim too many tiles.
      -- In case this happens, other threads can still steal those tiles back,
      -- and we can thus still balance the work (although with slightly more
      -- overhead).
      -- TODO: Change volatile load to atomic load
      currentCounter <- instr' $ Load Volatile counter Nothing
      check <- A.lt singleType (OP_Word64 currentCounter) (OP_Word64 size)
      _ <- cbr check claimGlobalGo claimSteal

      -- TODO: If maxClaim is small (<= 32) we could drop this heuristic, and
      -- always claim maxClaim tiles. We could then also drop the early out
      -- via 'check'.
      -- The following code somewhat assumes that maxClaim is more than 16.
      -- (It will work, but the heuristic is essentially doing nothing
      -- and always claiming maxClaim tiles if maxClaim <= 16).

      _ <- setBlock claimGlobalGo
      OP_Word64 currentRemaining <- A.sub numType (OP_Word64 size) (OP_Word64 currentCounter)
      OP_Word64 maxThreadsMul2 <- A.fromIntegral integralType numType (OP_Word32 maxThreads) >>= A.mul numType (A.liftWord64 2)
      -- Use 'remaining / (maxThreads * 2)' as initial heuristic
      count1 <- A.quot TypeWord64 (OP_Word64 currentRemaining) (OP_Word64 maxThreadsMul2)
      -- Claim at least 16 tiles
      count2 <- A.max singleType count1 (A.liftWord64 2)
      -- Claim at most maxClaim tiles
      OP_Word64 count3 <- A.min singleType count2 (A.liftWord64 maxClaim)

      -- TODO: Maybe we should announce here that we will claim something from
      -- the global counter. This informs other threads during stealing, that
      -- more stealable work might become available soon, and that they should
      -- not exit yet.
      -- We can announce this by storing a magic value in workPerThreadSelf.
      -- This magic value will be overwritten already by the newly claimed
      -- work. However, if there is no more work to be claimed, we need to
      -- explicitely remove this announcement.

      -- Increment the global counter by count3
      index <- instr' $ AtomicRMW numType NonVolatile RMW.Add counter count3 (CrossThread, Monotonic)

      success <- A.lt singleType (OP_Word64 index) (OP_Word64 size)

      _ <- cbr success claimGlobalSuccess claimSteal

      _ <- setBlock claimGlobalSuccess
      -- Success, we claimed some blocks from the global counter.
      -- Check how many we actually claimed (since we may have claimed fewer
      -- tiles if those were the last tiles).
      maxClaimed <- A.sub numType (OP_Word64 size) (OP_Word64 index)
      claimed <- A.min singleType (OP_Word64 count3) maxClaimed
      claimedSubOne <- A.sub numType claimed $ A.liftWord64 1
      _ <- br work

      indexPlusOne <- A.add numType (OP_Word64 index) $ A.liftWord64 1
      -- Pack indexPlusOne and claimedSubOne into a word, and store that in workPerThread
      OP_Word64 packed <- A.shiftL TypeWord64 indexPlusOne (A.liftInt 16) >>= A.bor TypeWord64 claimedSubOne
      -- TODO: Change volatile store to atomic store
      _ <- instr' $ Store Volatile workPerThreadSelf packed Nothing

      return index

    -- 3. Otherwise, steal from other thread
    indexSteal <- do
      -- TODO: Steal work from other threads
      _ <- setBlock claimSteal
      _ <- br exit
      return $ integral TypeWord64 0xFFFFFFFF -- TODO

    -- Add phi node to the work block, so it will choose the correct index
    _ <- setBlock work
    _ <- phi1 work "block_index" [(indexLocal, claim), (indexGlobal, claimGlobalSuccess) {-, (indexSteal, claimSteal TODO: Is this the right block? (We problably add if-then-elses to stealing...)) -}]
    return ()

  instr_ $ downcast $ "sequential_mode" := Cmp singleType Compare.EQ index nextIfSeq
  doWork seqMode index

  nextNextIfSeq <- A.add numType (OP_Word64 nextIfSeq) (OP_Word64 $ integral TypeWord64 1)
  OP_Word64 nextNextIfSeq' <- A.select (TupRsingle scalarTypeWord64) (OP_Bool seqMode) nextNextIfSeq (OP_Word64 $ integral TypeWord64 0)

  _ <- br claim

  -- Append the phi node to the start of the 'work' block.
  -- We can only do this now, as we need to have 'nextIndex', and know the
  -- exit block of 'doWork'.
  currentBlock <- getBlock
  _ <- phi1 claim nextIfSeqName [(integral TypeWord64 0, entry), (nextNextIfSeq', currentBlock)]

  setBlock exit
  retval_ $ scalar (scalarType @Word8) 0

workassistChunked :: [Loop.LoopAnnotation] -> ShapeR sh -> Operand (Ptr Word64) -> Operand (Ptr Word64) -> Word64 -> Operand Word32 -> Operand Word32 -> sh -> Operands sh -> (Operands sh -> CodeGen Native ()) -> CodeGen Native ()
workassistChunked ann shr counter workPerThread maxClaim threadIndex maxThreads chunkSz' sh doWork = do
  let chunkSz = A.lift (shapeType shr) chunkSz'
  chunkCounts <- chunkCount shr sh chunkSz
  chunkCnt <- shapeSize shr chunkCounts
  chunkCnt' :: Operand Word64 <- instr' $ BitCast scalarType $ op TypeInt chunkCnt
  workassistLoop counter workPerThread maxClaim threadIndex maxThreads chunkCnt' $ \_ chunkLinearIndex -> do
    chunkLinearIndex' <- instr' $ BitCast scalarType chunkLinearIndex
    chunkIndex <- indexOfInt shr chunkCounts (OP_Int chunkLinearIndex')
    start <- chunkStart shr chunkSz chunkIndex
    end <- chunkEnd shr sh chunkSz start
    imapNestFromTo [] ann shr start end sh (\ix _ -> doWork ix)

chunkSizeOne :: ShapeR sh -> sh
chunkSizeOne ShapeRz = ()
chunkSizeOne (ShapeRsnoc sh) = (chunkSizeOne sh, 1)

chunkSize :: ShapeR sh -> sh
chunkSize ShapeRz = ()
chunkSize (ShapeRsnoc ShapeRz) = ((), 1024)
chunkSize (ShapeRsnoc (ShapeRsnoc ShapeRz)) = (((), 32), 32)
chunkSize (ShapeRsnoc (ShapeRsnoc (ShapeRsnoc ShapeRz))) = ((((), 8), 8), 16)
chunkSize (ShapeRsnoc (ShapeRsnoc (ShapeRsnoc (ShapeRsnoc sh)))) = ((((chunkSizeOne sh, 4), 4), 8), 8)

chunkCount :: ShapeR sh -> Operands sh -> Operands sh -> CodeGen Native (Operands sh)
chunkCount ShapeRz OP_Unit OP_Unit = return OP_Unit
chunkCount (ShapeRsnoc shr) (OP_Pair sh sz) (OP_Pair chunkSh chunkSz) = do
  counts <- chunkCount shr sh chunkSh
  
  -- Compute ceil(sz / chunkSz), as
  -- (sz + chunkSz - 1) `quot` chunkSz
  chunkszsub1 <- A.sub numType chunkSz $ A.liftInt 1
  sz' <- A.add numType sz chunkszsub1
  count <- A.quot TypeInt sz' chunkSz

  return $ OP_Pair counts count

chunkStart :: ShapeR sh -> Operands sh -> Operands sh -> CodeGen Native (Operands sh)
chunkStart ShapeRz OP_Unit OP_Unit = return OP_Unit
chunkStart (ShapeRsnoc shr) (OP_Pair chunkSh chunkSz) (OP_Pair sh sz) = do
  ixs <- chunkStart shr chunkSh sh
  ix <- A.mul numType sz chunkSz
  return $ OP_Pair ixs ix

chunkEnd
  :: ShapeR sh
  -> Operands sh -- Array size (extent)
  -> Operands sh -- Chunk size
  -> Operands sh -- Chunk start
  -> CodeGen Native (Operands sh) -- Chunk end
chunkEnd ShapeRz OP_Unit OP_Unit OP_Unit = return OP_Unit
chunkEnd (ShapeRsnoc shr) (OP_Pair sh0 sz0) (OP_Pair sh1 sz1) (OP_Pair sh2 sz2) = do
  sh3 <- chunkEnd shr sh0 sh1 sh2
  sz3 <- A.add numType sz2 sz1
  sz3' <- A.min singleType sz3 sz0
  return $ OP_Pair sh3 sz3'
