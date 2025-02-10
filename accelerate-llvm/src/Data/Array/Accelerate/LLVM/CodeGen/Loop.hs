{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
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

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Constant

import Prelude                                                  hiding ( fst, snd, uncurry )
import Control.Monad


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


-- | Execute the given function at each index in the range
--
imapFromStepTo
    :: forall i arch. IsNum i
    => Operands i                                     -- ^ starting index (inclusive)
    -> Operands i                                     -- ^ step size
    -> Operands i                                     -- ^ final index (exclusive)
    -> (Operands i -> CodeGen arch ())                -- ^ loop body
    -> CodeGen arch ()
imapFromStepTo start step end body =
  for (TupRsingle $ SingleScalarType $ NumSingleType num) start
      (\i -> lt (NumSingleType num) i end)
      (\i -> add num i step)
      body
  where num = numType @i


-- | Execute the given function at each index in the range.
-- The indices are traversed in descending order.
--
imapReverseFromStepTo
    :: forall i arch. IsNum i
    => Operands i                                     -- ^ starting index (inclusive)
    -> Operands i                                     -- ^ step size
    -> Operands i                                     -- ^ final index (exclusive)
    -> (Operands i -> CodeGen arch ())                -- ^ loop body
    -> CodeGen arch ()
imapReverseFromStepTo start step end body = do
  end' <- sub num end step
  for (TupRsingle $ SingleScalarType $ NumSingleType num) end'
      (\i -> gte (NumSingleType num) i start)
      (\i -> sub num i step)
      body
  where num = numType @i


-- | Iterate with an accumulator between given start and end indices, executing
-- the given function at each.
--
iterFromStepTo
    :: forall i a arch. IsNum i
    => TypeR a
    -> Operands i                                     -- ^ starting index (inclusive)
    -> Operands i                                     -- ^ step size
    -> Operands i                                     -- ^ final index (exclusive)
    -> Operands a                                     -- ^ initial value
    -> (Operands i -> Operands a -> CodeGen arch (Operands a))    -- ^ loop body
    -> CodeGen arch (Operands a)
iterFromStepTo tp start step end seed body =
  iter (TupRsingle $ SingleScalarType $ NumSingleType num) tp start seed
       (\i -> lt (NumSingleType num) i end)
       (\i -> add num i step)
       body
  where num = numType @i


-- | A standard 'for' loop.
--
for :: TypeR i
    -> Operands i                                         -- ^ starting index
    -> (Operands i -> CodeGen arch (Operands Bool))       -- ^ loop test to keep going
    -> (Operands i -> CodeGen arch (Operands i))          -- ^ increment loop counter
    -> (Operands i -> CodeGen arch ())                    -- ^ body of the loop
    -> CodeGen arch ()
for tp start test incr body =
  void $ while tp test (\i -> body i >> incr i) start


-- | An loop with iteration count and accumulator.
--
iter :: TypeR i
     -> TypeR a
     -> Operands i                                                -- ^ starting index
     -> Operands a                                                -- ^ initial value
     -> (Operands i -> CodeGen arch (Operands Bool))              -- ^ index test to keep looping
     -> (Operands i -> CodeGen arch (Operands i))                 -- ^ increment loop counter
     -> (Operands i -> Operands a -> CodeGen arch (Operands a))   -- ^ loop body
     -> CodeGen arch (Operands a)
iter tpi tpa start seed test incr body = do
  r <- while (TupRpair tpi tpa)
             (test . fst)
             (\v -> do v' <- uncurry body v     -- update value and then...
                       i' <- incr (fst v)       -- ...calculate new index
                       return $ pair i' v')
             (pair start seed)
  return $ snd r


-- | A standard 'while' loop
--
while :: TypeR a
      -> (Operands a -> CodeGen arch (Operands Bool))
      -> (Operands a -> CodeGen arch (Operands a))
      -> Operands a
      -> CodeGen arch (Operands a)
while tp test body start = do
  loop <- newBlock   "while.top"
  exit <- newBlock   "while.exit"
  _    <- beginBlock "while.entry"

  -- Entry: generate the initial value
  p    <- test start
  top  <- cbr p loop exit

  -- Create the critical variable that will be used to accumulate the results
  prev <- fresh tp

  -- Generate the loop body. Afterwards, we insert a phi node at the head of the
  -- instruction stream, which selects the input value depending on which edge
  -- we entered the loop from: top or bottom.
  --
  setBlock loop
  next <- body prev
  p'   <- test next
  bot  <- cbr p' loop exit

  _    <- phi' tp loop prev [(start,top), (next,bot)]

  -- Now the loop exit
  setBlock exit
  phi tp [(start,top), (next,bot)]

loopWith
  :: LoopPeeling
  -> Bool
  -> Operands Int -- Inclusive lower bound
  -> Operands Int -- Exclusive upper bound
  -> (Operands Bool -> Operands Int -> CodeGen arch ())
  -> CodeGen arch ()
loopWith PeelNot False lower upper body =
  imapFromStepTo lower (liftInt 1) upper $ \idx -> do
    isFirst <- eq (NumSingleType numType) idx lower
    body isFirst idx
loopWith PeelNot True lower upper body = do
  upperInclusive <- sub numType upper (liftInt 1)
  imapReverseFromStepTo lower (liftInt 1) upper $ \idx -> do
    isFirst <- eq (NumSingleType numType) idx upperInclusive
    body isFirst idx
loopWith peeling desc lower upper body = do
  blockFirst <- newBlock "while.first.iteration"
  blockEnd <- newBlock "while.end"

  _ <- case peeling of
    PeelGuaranteed -> br blockFirst
    _ -> do
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
    imapReverseFromStepTo lower (liftInt 1) firstIdx $ \idx ->
      body (OP_Bool $ boolean False) idx
  else do
    second <- add numType lower (liftInt 1)
    imapFromStepTo second (liftInt 1) upper $ \idx ->
      body (OP_Bool $ boolean False) idx

  _ <- br blockEnd
  -- Control flow of the cbr on isEmpty joins here
  setBlock blockEnd

data LoopPeeling
  -- Do not perform loop peeling.
  = PeelNot
  -- Perform loop peeling, but do not assume that the loop will execute at
  -- least one iteration. The code for the first iteration should thus be
  -- placed in a conditional.
  | PeelConditional
  -- Perform loop peeling.
  -- It is guaranteed that the loop executes at least one iteration.
  | PeelGuaranteed
  deriving (Eq, Ord)

