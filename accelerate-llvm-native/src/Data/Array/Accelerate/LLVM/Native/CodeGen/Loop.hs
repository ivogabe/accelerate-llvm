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

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic                as A hiding (lift)
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
import Control.Monad.Trans
import Control.Monad.State
import Data.Array.Accelerate.LLVM.CodeGen.Base
import LLVM.AST.Type.Function
import LLVM.AST.Type.Name

-- | A standard 'for' loop, that steps from the start to end index executing the
-- given function at each index.
--
imapFromTo
    :: Operands Int                                   -- ^ starting index (inclusive)
    -> Operands Int                                   -- ^ final index (exclusive)
    -> (Operands Int -> CodeGen Native ())            -- ^ apply at each index
    -> CodeGen Native ()
imapFromTo start end body =
  Loop.imapFromStepTo start (liftInt 1) end body


-- | Generate a series of nested 'for' loops which iterate between the start and
-- end indices of a given hyper-rectangle. LLVM is very good at vectorising
-- these kinds of nested loops, but not so good at vectorising the flattened
-- representation utilising to/from index.
--
imapNestFromTo
    :: ShapeR sh
    -> Operands sh                                          -- ^ initial index (inclusive)
    -> Operands sh                                          -- ^ final index (exclusive)
    -> Operands sh                                          -- ^ total array extent
    -> (Operands sh -> Operands Int -> CodeGen Native ())   -- ^ apply at each index
    -> CodeGen Native ()
imapNestFromTo shr start end extent body =
  go shr start end body'
  where
    body' ix = body ix =<< intOfIndex shr extent ix

    go :: ShapeR t -> Operands t -> Operands t -> (Operands t -> CodeGen Native ()) -> CodeGen Native ()
    go ShapeRz OP_Unit OP_Unit k
      = k OP_Unit

    go (ShapeRsnoc shr') (OP_Pair ssh ssz) (OP_Pair esh esz) k
      = go shr' ssh esh
      $ \sz      -> imapFromTo ssz esz
      $ \i       -> k (OP_Pair sz i)

loopWorkFromTo :: ShapeR sh -> Operands sh -> Operands sh -> Operands sh -> TypeR s -> (LoopWork sh (StateT (Operands s) (CodeGen Native)),StateT (Operands s) (CodeGen Native) ()) -> StateT (Operands s) (CodeGen Native) ()
loopWorkFromTo shr start end extent tys (loopwork,finish) = do
  -- linix <- lift (intOfIndex shr (flipShape shr extent) (flipShape shr start))
  let linix = liftInt 0
  loopWorkFromTo' shr start end extent linix [] tys loopwork
  finish


loopWorkFromTo' :: ShapeR sh -> Operands sh -> Operands sh -> Operands sh -> Operands Int -> [Operands Int] -> TypeR s -> LoopWork sh (StateT (Operands s) (CodeGen Native)) -> StateT (Operands s) (CodeGen Native) ()
loopWorkFromTo' ShapeRz OP_Unit OP_Unit OP_Unit _ _ _ LoopWorkZ = pure ()
loopWorkFromTo' (ShapeRsnoc shr) (OP_Pair start' start) (OP_Pair end' endMaybe) (OP_Pair extent' extent) linixprev ixs tys (LoopWorkSnoc lw foo) = do
  linix <- lift $ add numType start linixprev
  end <- lift $ A.min singleType endMaybe extent
  StateT $ \s -> ((),) <$> Loop.iter
    (TupRpair typerInt typerInt)
    tys
    (OP_Pair start linix)
    s
    (\(OP_Pair i _) -> lt singleType i end
    )
    (\(OP_Pair i l) -> OP_Pair <$> add numType (constant typerInt 1) i <*> add numType (constant typerInt 1) l)
    (\(OP_Pair i l) -> execStateT $ do
                        recurlinix <- lift $ mul numType l $ firstOrZero shr extent' -- if extent' is empty, this won't be used anyway
                        loopWorkFromTo' shr start' end' extent' recurlinix (i:ixs) tys lw
                        foo l (i : ixs)
                        )

                
firstOrZero :: ShapeR sh -> Operands sh -> Operands Int
firstOrZero ShapeRz _ = constant typerInt 0
firstOrZero ShapeRsnoc{} (OP_Pair _ i) = i
  

typerInt :: TypeR Int
typerInt = TupRsingle scalarTypeInt


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
  Loop.iterFromStepTo tp start (liftInt 1) end seed body

workassistLoop
    :: Operand (Ptr Word32)                 -- index into work
    -> Operand Word32                       -- index of the first block to work on
    -> Operand (Ptr Word64)                 -- number of threads that are working
    -> Operand Word32                       -- size of total work
    -> (Operand Word32 -> StateT (Operands s) (CodeGen Native) ())
    -> StateT (Operands s) (CodeGen Native) ()
workassistLoop counter firstIndex activitiesSlot size doWork = do
  entry    <- lift getBlock
  work     <- lift $ newBlock "workassist.loop.work"
  claimed  <- lift $ newBlock "workassist.all.claimed"
  exit     <- lift $ newBlock "workassist.exit"
  finished <- lift $ newBlock "workassist.finished"

  initialCondition <- lift $ lt singleType (OP_Word32 firstIndex) (OP_Word32 size)
  _ <- lift $ cbr initialCondition work exit

  _ <- lift $ setBlock work
  let indexName = "block_index"
  let index = LocalReference type' indexName

  doWork index

  nextIndex <- lift $ atomicAdd Monotonic counter (integral TypeWord32 1)
  condition <- lift $ lt singleType (OP_Word32 nextIndex) (OP_Word32 size)

  -- Append the phi node to the start of the 'work' block.
  -- We can only do this now, as we need to have 'nextIndex', and know the
  -- exit block of 'doWork'.
  currentBlock <- lift $ getBlock
  lift $ phi1 work indexName [(firstIndex, entry), (nextIndex, currentBlock)]

  lift $ cbr condition work exit

  lift $ setBlock exit
  {- -- Decrement activeThreads
  remaining <- lift $ atomicAdd Release activeThreads (integral TypeInt32 (-1))
  -- If 'activeThreads' was 1 (now 0), then all work is definitely done.
  -- Note that there may be multiple threads returning true here.
  -- It is guaranteed that at least one thread returns true.
  allDone <- lift $ eq singleType (OP_Int32 remaining) (liftInt32 1)
  lift $ cbr allDone exitLast finished

  lift $ setBlock exitLast
  -- Use compare-and-set to change the active-threads counter to 1:
  --  * Out of all threads that currently see an active-thread count of 0, only
  --    1 will succeed the CAS.
  --  * Given that the counter is artifically increased here, no other thread
  --    will see the counter ever drop to 0.
  -- Hence we get a unique thread to continue the computation after this kernel.
  casResult <- lift $ instr' $ CmpXchg TypeInt32 NonVolatile activeThreads (integral TypeInt32 0) (integral TypeInt32 1) (CrossThread, Monotonic) Monotonic
  last' <- lift $ instr' $ ExtractValue primType (TupleIdxRight TupleIdxSelf) casResult
  lift $ retval_ last'

  lift $ setBlock finished
  -- Work was already finished -}
  lift $ retval_ $ boolean False

  -- lift $ setBlock dummy -- without this, the previous block always returns True for some reason
  

workassistChunked :: ShapeR sh -> Operand (Ptr Word32) -> Operand Word32 -> Operand (Ptr Word64) -> Operands sh -> TypeR s -> (LoopWork sh (StateT (Operands s) (CodeGen Native)), StateT (Operands s) (CodeGen Native) ()) -> StateT (Operands s) (CodeGen Native) ()
workassistChunked shr counter firstIndex activitiesSlot sh tys loopwork = do
  chunkSz <- lift $ chunkSize' shr sh
  chunkCounts <- lift $ chunkCount shr sh chunkSz
  chunkCnt <- lift $ shapeSize shr chunkCounts
  chunkCnt' :: Operand Word32 <- lift $ instr' $ Trunc boundedType boundedType $ op TypeInt chunkCnt
  workassistLoop counter firstIndex activitiesSlot chunkCnt' $ \chunkLinearIndex -> do
    chunkLinearIndex' <- lift $ instr' $ Ext boundedType boundedType chunkLinearIndex
    chunkIndex <- lift $ indexOfInt shr chunkCounts (OP_Int chunkLinearIndex')
    start <- lift $ chunkStart shr chunkSz chunkIndex
    end <- lift $ chunkEnd shr sh chunkSz start
    -- imapNestFromTo shr start end sh doWork
    loopWorkFromTo shr start end sh tys loopwork



chunkSize' :: ShapeR sh -> Operands sh -> CodeGen Native (Operands sh)
chunkSize' ShapeRz OP_Unit = return OP_Unit
chunkSize' (ShapeRsnoc ShapeRz) (OP_Pair _ sz) = do
  sz' <- A.max singleType sz (liftInt 1)
  return $ OP_Pair OP_Unit sz'
chunkSize' (ShapeRsnoc shr) (OP_Pair sh _) = do
  sh' <- chunkSize' shr sh
  return $ OP_Pair sh' (liftInt 1)
-- chunkSize' (ShapeRsnoc shr) (OP_Pair _ sz) = OP_Pair (ones shr) sz 
--   where
--     ones :: ShapeR sh -> Operands sh
--     ones ShapeRz = OP_Unit
--     ones (ShapeRsnoc shr) = OP_Pair (ones shr) (liftInt 1)

-- chunkSize :: ShapeR sh -> Operands sh
-- chunkSize ShapeRz = OP_Unit
-- chunkSize (ShapeRsnoc shr) = OP_Pair (chunkSize shr) (liftInt 1)
-- chunkSize (ShapeRsnoc ShapeRz) = ((), 1024 * 16)
-- chunkSize (ShapeRsnoc (ShapeRsnoc ShapeRz)) = (((), 64), 64)
-- chunkSize (ShapeRsnoc (ShapeRsnoc (ShapeRsnoc ShapeRz))) = ((((), 16), 16), 32)
-- chunkSize (ShapeRsnoc (ShapeRsnoc (ShapeRsnoc (ShapeRsnoc sh)))) = ((((go sh, 8), 8), 16), 16)
  -- where
  --   go :: ShapeR sh' -> sh'
  --   go ShapeRz = ()
  --   go (ShapeRsnoc sh') = (go sh', 1)

chunkCount :: ShapeR sh -> Operands sh -> Operands sh -> CodeGen Native (Operands sh)
chunkCount ShapeRz OP_Unit OP_Unit = return OP_Unit
chunkCount (ShapeRsnoc shr) (OP_Pair sh sz) (OP_Pair chunkSh chunkSz) = do
  counts <- chunkCount shr sh chunkSh
  
  -- Compute ceil(sz / chunkSz), as
  -- (sz + chunkSz - 1) `quot` chunkSz
  chunkszsub1 <- sub numType chunkSz $ constant typerInt 1
  sz' <- add numType sz chunkszsub1
  count <- A.quot TypeInt sz' chunkSz

  return $ OP_Pair counts count

-- chunkSize :: ShapeR sh -> sh
-- chunkSize ShapeRz = ()
-- chunkSize (ShapeRsnoc ShapeRz) = ((), 1024 * 16)
-- chunkSize (ShapeRsnoc (ShapeRsnoc ShapeRz)) = (((), 64), 64)
-- chunkSize (ShapeRsnoc (ShapeRsnoc (ShapeRsnoc ShapeRz))) = ((((), 16), 16), 32)
-- chunkSize (ShapeRsnoc (ShapeRsnoc (ShapeRsnoc (ShapeRsnoc sh)))) = ((((go sh, 8), 8), 16), 16)
--   where
--     go :: ShapeR sh' -> sh'
--     go ShapeRz = ()
--     go (ShapeRsnoc sh') = (go sh', 1)

-- chunkCount :: ShapeR sh -> Operands sh -> sh -> CodeGen Native (Operands sh)
-- chunkCount ShapeRz OP_Unit () = return OP_Unit
-- chunkCount (ShapeRsnoc shr) (OP_Pair sh sz) (chunkSh, chunkSz) = do
--   counts <- chunkCount shr sh chunkSh
  
--   -- Compute ceil(sz / chunkSz), as
--   -- (sz + chunkSz - 1) `quot` chunkSz
--   sz' <- add numType sz (liftInt $ chunkSz - 1)
--   count <- A.quot TypeInt sz' $ liftInt chunkSz

--   return $ OP_Pair counts count

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

atomicAdd :: MemoryOrdering -> Operand (Ptr Word32) -> Operand Word32 -> CodeGen Native (Operand Word32)
atomicAdd ordering ptr increment = do
  instr' $ AtomicRMW numType NonVolatile RMW.Add ptr increment (CrossThread, ordering)


data LoopWork sh m where
  LoopWorkZ :: LoopWork () m
  LoopWorkSnoc :: LoopWork sh m
               -- The list contains only indices available, i.e. not the ones in even deeper nesting
               -> (Operands Int -> [Operands Int] -> m ())
               -> LoopWork (sh, Int) m


flipShape :: forall sh. ShapeR sh -> Operands sh -> Operands sh
flipShape shr = multidim shr . reverse . multidim' shr


multidim :: ShapeR sh -> [Operands Int] -> Operands sh
multidim ShapeRz [] = OP_Unit
multidim (ShapeRsnoc shr) (i:is) = OP_Pair (multidim shr is) i
multidim _ _ = error "shouldn't have trusted me"

multidim' :: ShapeR sh -> Operands sh -> [Operands Int]
multidim' ShapeRz OP_Unit = []
multidim' (ShapeRsnoc shr) (OP_Pair sh i) = i : multidim' shr sh

---- debugging tools ----
putchar :: Operands Int -> CodeGen Native (Operands Int)
putchar x = call (lamUnnamed primType $ Body (PrimType primType) Nothing (Label "putchar")) 
                 (ArgumentsCons (op TypeInt x) [] ArgumentsNil) 
                 []
putcharA, putcharB, putcharC, putcharD, putcharE, putcharF, putcharG, putcharH :: StateT s (CodeGen Native) ()
putcharA = void $ lift $ putchar $ liftInt 65
putcharB = void $ lift $ putchar $ liftInt 66
putcharC = void $ lift $ putchar $ liftInt 67
putcharD = void $ lift $ putchar $ liftInt 68
putcharE = void $ lift $ putchar $ liftInt 69
putcharF = void $ lift $ putchar $ liftInt 70
putcharG = void $ lift $ putchar $ liftInt 71
putcharH = void $ lift $ putchar $ liftInt 72

printShape :: ShapeR sh -> Operands sh -> CodeGen Native ()
printShape ShapeRz _ = void $ putchar $ liftInt $ 65+25
printShape (ShapeRsnoc shr) (OP_Pair sh sz) = do
  _ <- putchar =<< add numType (liftInt 48) sz
  printShape shr sh
