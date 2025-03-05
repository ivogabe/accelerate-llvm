{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Loop
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Loop
  where

import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import LLVM.AST.Type.Metadata

import qualified LLVM.AST.Operand as LLVM
import qualified LLVM.AST.Constant as LLVM

import Prelude                                                  hiding ( fst, snd, uncurry )
import Control.Monad
import Data.Maybe (mapMaybe)


-- | TODO: Iterate over a multidimensional index space.
--
-- Build nested loops that iterate over a hyper-rectangular index space between
-- the given coordinates. The LLVM optimiser will be able to vectorise nested
-- loops, including when we insert conversions to the corresponding linear index
-- (e.g., in order to index arrays).
--
-- iterate
--     :: Shape sh
--     => Operands sh                                    -- ^ starting index
--     -> Operands sh                                    -- ^ final index
--     -> (Operands sh -> CodeGen (Operands a))          -- ^ body of the loop
--     -> CodeGen (Operands a)
-- iterate from to body = error "CodeGen.Loop.iterate"

data LoopAnnotation
  -- | Add a vectorization instruction to the generated LLVM code. This is no
  -- guarantee that LLVM will actually vectorize it.
  = LoopVectorize
  -- | Instruct LLVM to not vectorize this loop.
  | LoopNoVectorize
  -- | Add an annotation to the generated LLVM code to inform LLVM that is
  -- should interleave iterations of the loop. This might be a good
  -- alternative, if vectorization is not possible.
  | LoopInterleave
  -- | This annotation guarantees that the loop does at least one iteration.
  | LoopNonEmpty
  -- | Hint to apply loop peeling
  -- Loop peeling is only applied via loopWith.
  -- Other loop combinators ignore this annotation.
  | LoopPeel
  deriving (Eq, Ord)

-- | Execute the given function at each index in the range
--
imapFromStepTo
    :: forall i arch. IsNum i
    => [LoopAnnotation]
    -> Operands i                                     -- ^ starting index (inclusive)
    -> Operands i                                     -- ^ step size
    -> Operands i                                     -- ^ final index (exclusive)
    -> (Operands i -> CodeGen arch ())                -- ^ loop body
    -> CodeGen arch ()
imapFromStepTo ann start step end body =
  for ann
      (TupRsingle $ SingleScalarType $ NumSingleType num) start
      (\i -> lt (NumSingleType num) i end)
      (\i -> add num i step)
      body
  where num = numType @i


-- | Execute the given function at each index in the range.
-- The indices are traversed in descending order.
--
imapReverseFromStepTo
    :: forall i arch. IsNum i
    => [LoopAnnotation]
    -> Operands i                                     -- ^ starting index (inclusive)
    -> Operands i                                     -- ^ step size
    -> Operands i                                     -- ^ final index (exclusive)
    -> (Operands i -> CodeGen arch ())                -- ^ loop body
    -> CodeGen arch ()
imapReverseFromStepTo ann start step end body = do
  end' <- sub num end step
  for ann
      (TupRsingle $ SingleScalarType $ NumSingleType num) end'
      (\i -> gte (NumSingleType num) i start)
      (\i -> sub num i step)
      body
  where num = numType @i


-- | Iterate with an accumulator between given start and end indices, executing
-- the given function at each.
--
iterFromStepTo
    :: forall i a arch. IsNum i
    => [LoopAnnotation]
    -> TypeR a
    -> Operands i                                     -- ^ starting index (inclusive)
    -> Operands i                                     -- ^ step size
    -> Operands i                                     -- ^ final index (exclusive)
    -> Operands a                                     -- ^ initial value
    -> (Operands i -> Operands a -> CodeGen arch (Operands a))    -- ^ loop body
    -> CodeGen arch (Operands a)
iterFromStepTo ann tp start step end seed body =
  iter ann
       (TupRsingle $ SingleScalarType $ NumSingleType num) tp start seed
       (\i -> lt (NumSingleType num) i end)
       (\i -> add num i step)
       body
  where num = numType @i


-- | A standard 'for' loop.
--
for :: [LoopAnnotation]
    -> TypeR i
    -> Operands i                                         -- ^ starting index
    -> (Operands i -> CodeGen arch (Operands Bool))       -- ^ loop test to keep going
    -> (Operands i -> CodeGen arch (Operands i))          -- ^ increment loop counter
    -> (Operands i -> CodeGen arch ())                    -- ^ body of the loop
    -> CodeGen arch ()
for ann tp start test incr body =
  void $ while ann tp test (\i -> body i >> incr i) start


-- | An loop with iteration count and accumulator.
--
iter :: [LoopAnnotation]
     -> TypeR i
     -> TypeR a
     -> Operands i                                                -- ^ starting index
     -> Operands a                                                -- ^ initial value
     -> (Operands i -> CodeGen arch (Operands Bool))              -- ^ index test to keep looping
     -> (Operands i -> CodeGen arch (Operands i))                 -- ^ increment loop counter
     -> (Operands i -> Operands a -> CodeGen arch (Operands a))   -- ^ loop body
     -> CodeGen arch (Operands a)
iter ann tpi tpa start seed test incr body = do
  r <- while ann (TupRpair tpi tpa)
             (test . fst)
             (\v -> do v' <- uncurry body v     -- update value and then...
                       i' <- incr (fst v)       -- ...calculate new index
                       return $ pair i' v')
             (pair start seed)
  return $ snd r


-- | A standard 'while' loop
--
while :: [LoopAnnotation]
      -> TypeR a
      -> (Operands a -> CodeGen arch (Operands Bool))
      -> (Operands a -> CodeGen arch (Operands a))
      -> Operands a
      -> CodeGen arch (Operands a)
while ann tp test body start = do
  loop <- newBlock   "while.top"
  exit <- newBlock   "while.exit"
  _    <- beginBlock "while.entry"

  -- Loop annotations
  annotations <- sequence $ mapMaybe placeAnnotation ann
  annotation <- addMetadata $ \i ->
    map (Just . MetadataNodeOperand . MetadataNodeReference) (i : annotations)

  -- Entry: generate the initial value
  top <-
    if LoopNonEmpty `elem` ann then
      -- Ivo: br would make more sense than cbr here,
      -- but using br causes LLVM to crash with a segmentation fault.
      -- I didn't investigate this further, and went for the easy fix
      -- by using cbr instead of br here.
      cbr (OP_Bool $ boolean True) loop exit
    else do
      p <- test start
      cbr p loop exit

  -- Create the critical variable that will be used to accumulate the results
  prev <- fresh tp

  -- Generate the loop body. Afterwards, we insert a phi node at the head of the
  -- instruction stream, which selects the input value depending on which edge
  -- we entered the loop from: top or bottom.
  --
  setBlock loop
  next <- body prev
  p'   <- test next
  bot  <- cbrMD p' loop exit [("llvm.loop", LLVM.MDRef annotation)]

  _    <- phi' tp loop prev [(start,top), (next,bot)]

  -- Now the loop exit
  setBlock exit
  phi tp [(start,top), (next,bot)]
  where
    placeAnnotation :: LoopAnnotation -> Maybe (CodeGen arch LLVM.MetadataNodeID)
    placeAnnotation LoopVectorize = Just $
      addMetadata (\_ -> [Just $ MetadataStringOperand "llvm.loop.vectorize.enable", Just $ MetadataConstantOperand $ LLVM.Int 1 1])
    placeAnnotation LoopNoVectorize = Just $
      addMetadata (\_ -> [Just $ MetadataStringOperand "llvm.loop.vectorize.enable", Just $ MetadataConstantOperand $ LLVM.Int 1 0])
    placeAnnotation LoopInterleave = Just $
      addMetadata (\_ -> [Just $ MetadataStringOperand "llvm.loop.interleave.count", Just $ MetadataConstantOperand $ LLVM.Int 32 32])
    placeAnnotation _ = Nothing

-- | Creates an interleaved loop.
-- Instead of creating a loop like:
-- for (i = 0; i < n; i += 1) {
--   A
--   B
--   C
-- }
-- This creates a loop of the form:
-- for (; i < n % 32; i += 1) {
--   A
--   B
--   C
-- }
-- for (i = 0; i < n; i += 32) {
--   for (j in 0 .. 32) A;
--   for (j in 0 .. 32) B;
--   for (j in 0 .. 32) C;
-- }
-- If the first iteration requires special handling (first argument),
-- we need to assure the scalar loop does at least one iteration. This is
-- assured by changing 'n % 32' to '(n + 31) % 32 + 1'.
-- This is somewhat similar to loop peeling. We do not peel just the first
-- iteration from the loop, but the first few such that the remainder is a
-- multiple of 'width'.
--
-- The benefit of this transformation is that vectorization might now be easier.
-- The interleave count should thus generally be set to the preferred SIMD width.
-- For instance, if C cannot be vectorized, we can still let LLVM vectorize A and B.
-- Futhermore, if we can manually vectorize C, we can generate special code for
-- that without the need to also manually vectorize A and B in Accelerate.
loopInterleaved
  :: forall arch.
     Bool -- Whether first iteration requires special handling
  -> Bool -- Descending
  -> Int -- Interleave count (~ SIMD width)
  -> Operands Int -- Inclusive lower bound
  -> Operands Int -- Exclusive upper bound
  -> InterleavedBody arch
  -> CodeGen arch ()
loopInterleaved firstSpecial desc width lower upper body = do
  size <- A.sub numType upper lower
  (start, end, increment, compare') <-
    if desc then do
      s <- A.sub numType upper (liftInt 1) -- Convert to inclusive bound
      e <- A.sub numType lower (liftInt 1) -- Convert to exclusive bound
      return (s, e, (-1), A.gt singleType)
    else
      return (lower, upper, 1, A.lt singleType)
  
  -- Scalar loop
  scalarLoopCount <-
    if firstSpecial then do
      a <- A.add numType size (liftInt $ width - 1)
      r <- A.rem TypeInt a (liftInt width)
      c <- A.add numType r (liftInt 1)
      -- Edge case: if the input is empty, then 'c' would now say that we need
      -- to execute 'width' iterations. In all other cases 'c' is already
      -- correct.
      A.min singleType c size
    else
      A.rem TypeInt size (liftInt width)
  scalarLoopEnd <-
    if desc then
      A.sub numType start scalarLoopCount
    else
      A.add numType start scalarLoopCount

  _ <- while [LoopNoVectorize] (TupRsingle scalarTypeInt)
    (\i -> compare' i scalarLoopEnd)
    (\i -> do
      isFirst <- A.eq singleType i start
      body False isFirst i (\_ f -> f i (liftInt 0))
      A.add numType i $ liftInt increment
    )
    start

  let (simdStart, simdEnd) = if desc then (width - 1, -1) else (0, width)

  -- After the scalar loop, we can do the bulk of the loop in steps of
  -- 'width'.
  _ <- while [] (TupRsingle scalarTypeInt)
    (\i -> compare' i end)
    (\i -> do
      let
        simdLoop :: [LoopAnnotation] -> (Operands Int -> Operands Int -> CodeGen arch ()) -> CodeGen arch ()
        simdLoop ann f = do
          _ <- while ann (TupRsingle scalarTypeInt)
            (\j -> compare' j $ liftInt simdEnd)
            (\j -> do
              i' <- A.add numType i j
              f i' j
              A.add numType j $ liftInt increment 
            )
            (liftInt simdStart)
          return ()

      body False (OP_Bool $ boolean False) i simdLoop
      A.add numType i $ liftInt $ width * increment
    )
    scalarLoopEnd
  return ()

type InterleavedBody arch
  -- | Whether this is in the interleaved/simd loop (opposed to the scalar
  -- loop, if the number of iteration doesn't divide the interleave count)
  = Bool
  -- | Whether this is the first iteration. This can only be True in the
  -- scalar loop (i.e. if the first argument is False)
  -> Operands Bool
  -- The index of the first (lowest index in case of a descending loop, highest
  -- index otherwise) element of this group (SIMD vector).
  -> Operands Int
  -- | Lifts code into an inner / SIMD loop. The function gets the global index
  -- and the index in the interleaved loop (e.g. the simd lane index)
  -> ([LoopAnnotation] -> (Operands Int -> Operands Int -> CodeGen arch ()) -> CodeGen arch ())
  -> CodeGen arch ()

loopWith
  :: [LoopAnnotation]
  -> Bool
  -> Operands Int -- Inclusive lower bound
  -> Operands Int -- Exclusive upper bound
  -> (Operands Bool -> Operands Int -> CodeGen arch ())
  -> CodeGen arch ()
loopWith ann desc lower upper body
  | LoopPeel `elem` ann = do
    blockFirst <- newBlock "while.first.iteration"
    blockEnd <- newBlock "while.end"

    _ <-
      if LoopNonEmpty `elem` ann then
        br blockFirst
      else do
        -- Check if we need to do work. The first iteration can only be executed
        -- if there is at least one value in the array.
        isEmpty <- lte singleType upper lower
        cbr isEmpty blockEnd blockFirst

    -- Generate code for the first iteration
    setBlock blockFirst
    firstIdx <- if desc then sub numType upper (liftInt 1) else return lower
    body (OP_Bool $ boolean True) firstIdx

    -- Generate a loop for the remaining iterations
    if desc then do
      imapReverseFromStepTo ann' lower (liftInt 1) firstIdx $ \idx ->
        body (OP_Bool $ boolean False) idx
    else do
      second <- add numType lower (liftInt 1)
      imapFromStepTo ann' second (liftInt 1) upper $ \idx ->
        body (OP_Bool $ boolean False) idx

    _ <- br blockEnd
    -- Control flow of the cbr on isEmpty joins here
    setBlock blockEnd
  where
    -- Remove peel and non-empty annotations, as these do no longer hold
    -- in the loop for all but the first iterations.
    ann' = filter (\a -> a /= LoopPeel && a /= LoopNonEmpty) ann

-- No loop peeling
loopWith ann False lower upper body =
  imapFromStepTo ann lower (liftInt 1) upper $ \idx -> do
    isFirst <- eq (NumSingleType numType) idx lower
    body isFirst idx
loopWith ann True lower upper body = do
  upperInclusive <- sub numType upper (liftInt 1)
  imapReverseFromStepTo ann lower (liftInt 1) upper $ \idx -> do
    isFirst <- eq (NumSingleType numType) idx upperInclusive
    body isFirst idx

data LoopPeeling
  -- Do not perform loop peeling.
  = PeelNot
  -- Do not perform loop peeling. The first iteration performs a dynamic check
  -- whether this is the first iteration. When vectorizing this loop, the first
  -- iteration should thus preferably be placed in the scalar loop.
  | PeelNotCheck
  -- Perform loop peeling, but do not assume that the loop will execute at
  -- least one iteration. The code for the first iteration should thus be
  -- placed in a conditional.
  | PeelConditional
  -- Perform loop peeling.
  -- It is guaranteed that the loop executes at least one iteration.
  | PeelGuaranteed
  deriving (Eq, Ord)

peelNot :: LoopPeeling -> LoopPeeling
peelNot PeelNot = PeelNot
peelNot _ = PeelNotCheck

loopPeelingToAnnotation :: LoopPeeling -> [LoopAnnotation]
loopPeelingToAnnotation = \case
  PeelNot         -> []
  PeelNotCheck    -> []
  PeelConditional -> [LoopPeel]
  PeelGuaranteed  -> [LoopPeel, LoopNonEmpty]
