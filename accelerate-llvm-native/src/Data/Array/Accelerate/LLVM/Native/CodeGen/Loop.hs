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

import Data.Array.Accelerate.LLVM.Native.CodeGen.Base               (shardAmount, cacheWidth)
import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic                hiding ( lift )
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic      as A
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR

import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop            as Loop

import Data.Array.Accelerate.LLVM.Native.Target                     ( Native )

import LLVM.AST.Type.Representation
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.Volatile
import qualified LLVM.AST.Type.Instruction.RMW as RMW
import Control.Monad.State
import Data.Array.Accelerate.LLVM.CodeGen.Base
import LLVM.AST.Type.Function
import LLVM.AST.Type.Name
import LLVM.AST.Type.GetElementPtr


-- | A standard 'for' loop, that steps from the start to end index executing the
-- given function at each index.
--
imapFromTo
    :: Operands Int                                   -- ^ starting index (inclusive)
    -> Operands Int                                   -- ^ final index (exclusive)
    -> (Operands Int -> CodeGen Native ())            -- ^ apply at each index
    -> CodeGen Native ()
imapFromTo start end body =
  Loop.imapFromStepTo [] start (liftInt 1) end body


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
      $ \sz      -> Loop.imapFromStepTo ann ssz (liftInt 1) esz
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
  Loop.iterFromStepTo [] tp start (liftInt 1) end seed body

shardedSelfScheduling
    :: Operand (Ptr (SizedArray Word64))    -- work indexes of shards
    -> Operand (Ptr (SizedArray Word64))    -- sizes of shards
    -> Operand (Ptr Word64)                 -- combined: high 32 bits = next shard index, low 32 bits = finished shard count
    -> (Operand Bool -> Operand Word64 -> Maybe (Operand Word64) -> CodeGen Native ())
    -> CodeGen Native ()
shardedSelfScheduling shardIndexes shardSizes nextShardFinishedShards doWork = do
  entry    <- getBlock
  start    <- newBlock "workassist.shards.start"
  outer    <- newBlock "workassist.shards.outer"
  inner    <- newBlock "workassist.shards.inner"
  work     <- newBlock "workassist.shards.work"
  done     <- newBlock "workassist.shards.done"
  finish   <- newBlock "workassist.shards.done.finish"
  next     <- newBlock "workassist.shards.done.next"
  exit     <- newBlock "workassist.exit"

  -- Increment next shard by 1.
  initNextFinish <- atomicAdd Monotonic nextShardFinishedShards (integral TypeWord64 0x100000000)

  _ <- br start

  setBlock next

  -- Increment next shard by 1.
  nextInc <- atomicAdd Monotonic nextShardFinishedShards (integral TypeWord64 0x100000000)

  _ <- br start

  setBlock finish

  -- Increment next shard and finished shards by 1.
  finishInc <- atomicAdd Monotonic nextShardFinishedShards (integral TypeWord64 0x100000001)

  _ <- br start

  setBlock start

  -- Check if amount of finished shards is lower than amount of shards to continue.
  finishCount <- phi (TupRsingle scalarType) [(OP_Word64 initNextFinish, entry), (OP_Word64 nextInc, next), (OP_Word64 finishInc, finish)]
  finishCount' <- A.band TypeWord64 finishCount (A.liftWord64 0xFFFFFFFF)
  finished <- A.lt singleType finishCount' (A.liftWord64 shardAmount)

  _ <- cbr finished outer exit

  setBlock outer

  nextShard' <- A.shiftR TypeWord64 finishCount (A.liftInt 32)
  OP_Word64 shardToWorkOn <- A.rem TypeWord64 nextShard' (A.liftWord64 shardAmount)

  -- Get shard from shards array, to do this we need to multiply by cache width as every shards is on a seperate cache line.
  OP_Word64 shardIdx <- A.mul numType (A.liftWord64 (cacheWidth `div` 8)) (OP_Word64 shardToWorkOn)
  shard <- instr' $ GetElementPtr $ GEP shardIndexes (integral TypeWord64 0) $ GEPArray shardIdx GEPEmpty
  
  shardSizeIdx <- instr' $ GetElementPtr $ GEP shardSizes (integral TypeWord64 0) $ GEPArray shardToWorkOn GEPEmpty
  shardSize <- instr' $ Load scalarType NonVolatile shardSizeIdx

  _ <- br inner

  setBlock inner
  
  -- Continue working on shard until finished.
  workIdx <- atomicAdd Monotonic shard (integral TypeWord64 1)
  shardFinished <- A.lt singleType (OP_Word64 workIdx) (OP_Word64 shardSize)

  _ <- cbr shardFinished work done

  setBlock work

  -- Sequential mode needs to be false here, as it is only used in 
  -- a scan operation and this scheduler is never used for scans
  doWork (boolean False) workIdx (Just shardToWorkOn)

  _ <- br inner

  setBlock done

  -- If this thread is the one to finish the last tile, we increment the amount of finished shards.
  incrementFinished <- A.eq singleType (OP_Word64 workIdx) (OP_Word64 shardSize)

  _ <- cbr incrementFinished finish next

  setBlock exit
  retval_ $ scalar (scalarType @Word8) 0

shardedSelfSchedulingChunked 
    :: [Loop.LoopAnnotation] 
    -> ShapeR sh 
    -> Operand (Ptr (SizedArray Word64))    -- work indexes of shards
    -> Operand (Ptr (SizedArray Word64))    -- sizes of shards
    -> Operand (Ptr Word64)                 -- combined: high 32 bits = next shard index, low 32 bits = finished shard count
    -> sh 
    -> Operands sh
    -> Operands sh
    -> (Operands sh -> CodeGen Native ()) 
    -> CodeGen Native ()
shardedSelfSchedulingChunked ann shr shardIndexes shardSizes nextShardFinishedShards chunkSz' sh chunkCounts doWork = do
  let chunkSz = A.lift (shapeType shr) chunkSz'
  shardedSelfScheduling shardIndexes shardSizes nextShardFinishedShards $ \_ chunkLinearIndex shardIdx -> do
    chunkLinearIndex' <- instr' $ BitCast scalarType chunkLinearIndex
    chunkIndex <- indexOfInt shr chunkCounts (OP_Int chunkLinearIndex')
    start <- chunkStart shr chunkSz chunkIndex
    end <- chunkEnd shr sh chunkSz start
    imapNestFromTo [] ann shr start end sh (\ix _ -> doWork ix)

workassistLoop
    :: Operand (Ptr Word64)                 -- index into work
    -> Operand Word64                       -- size of total work
    -> (Operand Bool -> Operand Word64 -> CodeGen Native ())
    -> CodeGen Native ()
workassistLoop counter workSize doWork = do
  entry    <- getBlock
  work     <- newBlock "workassist.loop.work"
  exit     <- newBlock "workassist.exit"

  firstIndex <- atomicAdd Monotonic counter (integral TypeWord64 1)

  initialCondition <- lt singleType (OP_Word64 firstIndex) (OP_Word64 workSize)
  initialSeq <- eq singleType (OP_Word64 firstIndex) (liftWord64 0)
  _ <- cbr initialCondition work exit

  _ <- setBlock work
  let indexName = "block_index"
  -- Whether the thread should operate in the single threaded mode of
  -- zero-overhead parallel scans.
  let seqName = "sequential_mode"
  let seqMode = LocalReference type' seqName
  let index = LocalReference type' indexName

  doWork seqMode index

  nextIndex <- atomicAdd Monotonic counter (integral TypeWord64 1)
  condition <- lt singleType (OP_Word64 nextIndex) (OP_Word64 workSize)
  indexPlusOne <- add numType (OP_Word64 index) (liftWord64 1)
  nextSeq' <- eq singleType indexPlusOne (OP_Word64 nextIndex)
  -- Continue in sequential mode if the newly claimed block directly follows
  -- the previous block, and we were still in the sequential mode.
  nextSeq <- land nextSeq' (OP_Bool seqMode)

  -- Append the phi node to the start of the 'work' block.
  -- We can only do this now, as we need to have 'nextIndex', and know the
  -- exit block of 'doWork'.
  currentBlock <- getBlock
  _ <- phi1 work indexName [(firstIndex, entry), (nextIndex, currentBlock)]
  _ <- phi1 work seqName [(op BoolPrimType initialSeq, entry), (op BoolPrimType nextSeq, currentBlock)]

  _ <- cbr condition work exit

  setBlock exit
  retval_ $ scalar (scalarType @Word8) 0

workassistChunked 
    :: [Loop.LoopAnnotation] 
    -> ShapeR sh 
    -> Operand (Ptr Word64) 
    -> sh 
    -> Operands sh 
    -> Operands sh
    -> Operands Int
    -> (Operands sh -> CodeGen Native ()) 
    -> CodeGen Native ()
workassistChunked ann shr counter chunkSz' sh chunkCounts chunkCnt doWork = do
  let chunkSz = A.lift (shapeType shr) chunkSz'
  chunkCnt' :: Operand Word64 <- instr' $ BitCast scalarType $ op TypeInt chunkCnt
  workassistLoop counter chunkCnt' $ \_ chunkLinearIndex -> do
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
chunkSize (ShapeRsnoc (ShapeRsnoc ShapeRz)) = (((), 16), 64)
chunkSize (ShapeRsnoc (ShapeRsnoc (ShapeRsnoc sh))) = (((chunkSizeOne sh, 4), 8), 32)

chunkCount :: ShapeR sh -> Operands sh -> Operands sh -> CodeGen Native (Operands sh)
chunkCount ShapeRz OP_Unit OP_Unit = return OP_Unit
chunkCount (ShapeRsnoc shr) (OP_Pair sh sz) (OP_Pair chunkSh chunkSz) = do
  counts <- chunkCount shr sh chunkSh
  
  -- Compute ceil(sz / chunkSz), as
  -- (sz + chunkSz - 1) `quot` chunkSz
  chunkszsub1 <- sub numType chunkSz $ liftInt 1
  sz' <- add numType sz chunkszsub1
  count <- A.quot TypeInt sz' chunkSz

  return $ OP_Pair counts count

chunkStart :: ShapeR sh -> Operands sh -> Operands sh -> CodeGen Native (Operands sh)
chunkStart ShapeRz OP_Unit OP_Unit = return OP_Unit
chunkStart (ShapeRsnoc shr) (OP_Pair chunkSh chunkSz) (OP_Pair sh sz) = do
  ixs <- chunkStart shr chunkSh sh
  ix <- mul numType sz chunkSz
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
  sz3 <- add numType sz2 sz1
  sz3' <- A.min singleType sz3 sz0
  return $ OP_Pair sh3 sz3'

atomicAdd :: MemoryOrdering -> Operand (Ptr Word64) -> Operand Word64 -> CodeGen Native (Operand Word64)
atomicAdd ordering ptr increment = do
  instr' $ AtomicRMW numType NonVolatile RMW.Add ptr increment (CrossThread, ordering)

atomicLoad :: MemoryOrdering -> Operand (Ptr Word64) -> CodeGen Native (Operand Word64)
atomicLoad ordering ptr = do
  instr' $ LoadAtomic scalarType NonVolatile ptr ordering 8

---- debugging tools ----
putchar :: Operands Int -> CodeGen Native (Operands Int)
putchar x = call (lamUnnamed primType $ Body (PrimType primType) Nothing (Label "putchar")) 
                 (ArgumentsCons (op TypeInt x) [] ArgumentsNil) 
                 []
putcharA, putcharB, putcharC, putcharD, putcharE, putcharF, putcharG, putcharH :: CodeGen Native ()
putcharA = void $ putchar $ liftInt 65
putcharB = void $ putchar $ liftInt 66
putcharC = void $ putchar $ liftInt 67
putcharD = void $ putchar $ liftInt 68
putcharE = void $ putchar $ liftInt 69
putcharF = void $ putchar $ liftInt 70
putcharG = void $ putchar $ liftInt 71
putcharH = void $ putchar $ liftInt 72
