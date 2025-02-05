{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Cluster
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Cluster
  ( OpCodeGen(..), OpCodeGens(..), opCodeGens
  , genSequential, pushIdxEnv
  )
  where

import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Partitioned

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.Foreign

import LLVM.AST.Type.Operand

import Prelude                                                  hiding ( fst, snd, uncurry )
import Control.Monad

opCodeGens
  :: CompileForeignExp target
  => (forall idxEnv'. FlatOp op env idxEnv' -> (LoopDepth, OpCodeGen target env idxEnv'))
  -> FlatOps op env idxEnv
  -> OpCodeGens target env idxEnv
opCodeGens f = \case
  FlatOpsNil -> GenNil
  FlatOpsBind d lhs expr next ->
    GenBind d lhs
      (\envs -> llvmOfOpenExp
        (compileArrayInstrEnvs envs)
        expr
        (envFromPartialLazy "Missing binding in idxEnv. Are all LoopDepths correct?" $ envsIdx envs)
      )
      $ opCodeGens f next
  FlatOpsOp flatOp next
    | (d, c) <- f flatOp
    -> GenOp d c $ opCodeGens f next

data OpCodeGens target env idxEnv where
  GenNil
    :: OpCodeGens target env idxEnv

  GenBind
    :: LoopDepth
    -> ELeftHandSide t idxEnv idxEnv'
    -> (Envs env idxEnv -> CodeGen target (Operands t))
    -> OpCodeGens target env idxEnv'
    -> OpCodeGens target env idxEnv

  GenOp
    -- The loop depth where this operation first generates some code.
    -- In case of OpCodeGenSingle, this is the depth in which this code runs.
    -- In case of OpCodeGenLoop, this is the depth *outside* of the loop that
    -- it introduces.
    :: LoopDepth
    -> OpCodeGen target env idxEnv
    -> OpCodeGens target env idxEnv
    -> OpCodeGens target env idxEnv

data OpCodeGen target env idxEnv where
  OpCodeGenSingle
    :: (Envs env idxEnv -> CodeGen target ())
    -> OpCodeGen target env idxEnv

  OpCodeGenLoop
    -- Whether this operation prefers to have the first iteration be placed outside of the loop.
    -- If this Bool is True, and the array is empty on this dimension, then the
    -- behaviour of the generated code is undefined.
    :: Bool
    -- Code before the loop
    -> (Envs env idxEnv -> CodeGen target a)
    -- Code within the loop
    -> (a -> Envs env idxEnv -> CodeGen target ())
    -- Code after the loop
    -> (a -> Envs env idxEnv -> CodeGen target ())
    -> OpCodeGen target env idxEnv

genSequential
  :: Envs env idxEnv
  -- Index variables for the loop, loop directions and loop sizes
  -> [(Idx idxEnv Int, LoopDirection Int, Operands Int)]
  -> OpCodeGens target env idxEnv
  -> CodeGen target ()
genSequential envs sizes ops = do
  let depth = envsLoopDepth envs
  -- Introduce variables for fused-away and dead arrays
  envs1 <- bindLocals depth envs

  (splitFirst, nested, after) <- genSequential' envs1 ops
  case sizes of
    -- No further nested loops
    [] -> return ()
    -- If an operation prefers the first iteration to be split of the loop,
    -- and this is the deepest loop depth (to prevent too much code duplication),
    -- split the first iteration of the loop. This is also know as loop peeling.
    [(idxIdx, dir, sz)]
      | splitFirst -> do
      -- Note that we may now assume that the loop does at least one iteration.
      -- These loops with an empty iteration size are undefined behaviour.
      --
      -- Generate code for the first iteration
      let desc = isDescending dir
      firstIdx <- if desc then sub numType sz (liftInt 1) else return (liftInt 0)
      -- Start a do-block to create a local scope
      do
        -- While not necessary for correctness, we add a new block to make it
        -- clear in the generated LLVM code that this code is the first
        -- iteration of the loop.
        _  <- beginBlock "while.first.iteration"
        let idx = firstIdx
        a <- mul numType (envsLinearIndex envs depth) sz
        linearIdx <- add numType a idx
        let envs2 = envs1{
            envsLoopDepth = depth + 1,
            envsIdx = partialUpdate (op scalarTypeInt idx) idxIdx $ envsIdx envs1,
            envsLinearIndices = envsLinearIndices envs ++ [linearIdx],
            envsIsFirst = OP_Bool $ boolean True,
            envsDescending = isDescending dir
          }
        genSequential envs2 [] nested
      -- Generate a loop for the remaining iterations
      (if desc then imapReverseFromStepTo (liftInt 0) (liftInt 1) firstIdx
               else imapFromStepTo (liftInt 1) (liftInt 1) sz)
        $ \idx -> do
          a <- mul numType (envsLinearIndex envs depth) sz
          linearIdx <- add numType a idx
          let envs2 = envs1{
              envsLoopDepth = depth + 1,
              envsIdx = partialUpdate (op scalarTypeInt idx) idxIdx $ envsIdx envs1,
              envsLinearIndices = envsLinearIndices envs ++ [linearIdx],
              envsIsFirst = OP_Bool $ boolean False,
              envsDescending = isDescending dir
            }
          genSequential envs2 [] nested
    -- Start a nested loop
    ((idxIdx, dir, sz) : szs) -> do
      (if isDescending dir then imapReverseFromStepTo else imapFromStepTo)
        (liftInt 0) (liftInt 1) sz
        $ \idx -> do
          a <- mul numType (envsLinearIndex envs depth) sz
          isFirst <-
            if isDescending dir then do
              sz' <- sub numType sz (liftInt 1)
              eq singleType idx sz'
            else
              eq singleType idx (liftInt 0)
          linearIdx <- add numType a idx
          let envs2 = envs1{
              envsLoopDepth = depth + 1,
              envsIdx = partialUpdate (op scalarTypeInt idx) idxIdx $ envsIdx envs1,
              envsLinearIndices = envsLinearIndices envs ++ [linearIdx],
              envsIsFirst = isFirst,
              envsDescending = isDescending dir
            }
          genSequential envs2 szs nested
  after
  where
    isDescending :: LoopDirection Int -> Bool
    isDescending LoopDescending = True
    isDescending _ = False

genSequential'
  :: Envs env idxEnv
  -> OpCodeGens target env idxEnv
  -> CodeGen target
    -- Whether an operation in the loop prefers the first iteration to be split of the loop
    ( Bool
    -- The code in the next loop,
    -- if there is a next loop
    , OpCodeGens target env idxEnv
    -- The code after the loop,
    -- or if there is no loop,
    -- the regular code we have to emit.
    , CodeGen target ()
    )
genSequential' envs = \case
  GenNil -> return (False, GenNil, return ())
  GenBind d lhs expr next
    | d == envsLoopDepth envs -> do
      value <- expr envs
      let envs' = envs{
          envsIdx = envsIdx envs `pushIdxEnv` (lhs, value)
        }
      (splitFirst, nested, after) <- genSequential' envs' next
      return
        -- Keep this Bind in any nested loops, to still have access to the index.
        -- This returns the already introduced Operands, and does not
        -- reevaluate the expression
        ( splitFirst
        , GenBind (d + 1) lhs (const $ return value) nested
        , after
        )
    | otherwise -> do
      let envs' = envs{
          envsIdx = partialEnvSkipLHS lhs $ envsIdx envs
        }
      (splitFirst, nested, after) <- genSequential' envs' next
      -- Add GenBind to nested loop
      return
        ( splitFirst
        , GenBind d lhs expr nested
        , after
        )
  GenOp d (OpCodeGenSingle c) next
    | d == envsLoopDepth envs -> do
      (splitFirst, nested, after) <- genSequential' envs next
      -- Add the code after the loop (and before the 'after' instructions of
      -- later operations)
      return (splitFirst, nested, c envs >> after)
  GenOp d (OpCodeGenLoop splitFirst' before within after') next
    | d == envsLoopDepth envs -> do
      a <- before envs
      (splitFirst, nested, after) <- genSequential' envs next
      return
        ( splitFirst' || splitFirst
        , GenOp (d + 1) (OpCodeGenSingle $ within a) nested
        , after' a envs >> after
        )
  -- Operation is for a deeper loop
  GenOp d c next -> do
    (splitFirst, nested, after) <- genSequential' envs next
    return
      ( splitFirst
      , GenOp d c nested
      , after
      )

pushIdxEnv :: PartialEnv Operand env -> (ELeftHandSide t env env', Operands t) -> PartialEnv Operand env'
pushIdxEnv env (LeftHandSideSingle tp , e)               = env `PPush` op tp e
pushIdxEnv env (LeftHandSideWildcard _, _)               = env
pushIdxEnv env (LeftHandSidePair l1 l2, (OP_Pair e1 e2)) = pushIdxEnv env (l1, e1) `pushIdxEnv` (l2, e2)

