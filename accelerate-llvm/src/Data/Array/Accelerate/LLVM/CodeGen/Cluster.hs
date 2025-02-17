{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
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
  -- Sequential code generation
  ( OpCodeGen(..), OpCodeGens(..), LoopPeeling(..), opCodeGens
  , genSequential
  -- Parallel code generation
  , ParCodeGens(..), ParLoopCodeGen(..)
  , parCodeGens, parCodeGenMemory, parCodeGenInitMemory, parCodeGenFinish
  , genParallel
  , ParTileLoop(..), ParTileLoops(..)
  -- Utilities
  , pushIdxEnv
  )
  where

import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Error

import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.Foreign

import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Instruction

import Data.Maybe

opCodeGens
  :: CompileForeignExp target
  => (forall idxEnv'. FlatOp op env idxEnv' -> (LoopDepth, OpCodeGen target op env idxEnv'))
  -> FlatOps op env idxEnv
  -> OpCodeGens target op env idxEnv
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

data OpCodeGens target op env idxEnv where
  GenNil
    :: OpCodeGens target op env idxEnv

  GenBind
    :: LoopDepth
    -> ELeftHandSide t idxEnv idxEnv'
    -> (Envs env idxEnv -> CodeGen target (Operands t))
    -> OpCodeGens target op env idxEnv'
    -> OpCodeGens target op env idxEnv

  GenOp
    -- The loop depth where this operation first generates some code.
    -- In case of OpCodeGenSingle, this is the depth in which this code runs.
    -- In case of OpCodeGenLoop, this is the depth *outside* of the loop that
    -- it introduces.
    :: LoopDepth
    -> OpCodeGen  target op env idxEnv
    -> OpCodeGens target op env idxEnv
    -> OpCodeGens target op env idxEnv

data OpCodeGen target op env idxEnv where
  OpCodeGenSingle
    :: (Envs env idxEnv -> CodeGen target ())
    -> OpCodeGen target op env idxEnv

  OpCodeGenLoop
    -- The FlatOp from which this was compiled.
    -- Used in parCodeGens to generate a parallel version of this loop.
    :: FlatOp op env idxEnv
    -- Whether this operation prefers to have the first iteration be placed
    -- outside of the loop, also known as loop peeling.
    -> LoopPeeling
    -- Code before the loop
    -> (Envs env idxEnv -> CodeGen target a)
    -- Code within the loop
    -> (a -> Envs env idxEnv -> CodeGen target ())
    -- Code after the loop
    -> (a -> Envs env idxEnv -> CodeGen target ())
    -> OpCodeGen target op env idxEnv

genSequential
  :: Envs env idxEnv
  -- Index variables for the loop, loop directions and loop sizes
  -> [(Idx idxEnv Int, LoopDirection Int, Operands Int)]
  -> OpCodeGens target op env idxEnv
  -> CodeGen target ()
genSequential envs sizes ops = do
  let depth = envsLoopDepth envs
  -- Introduce variables for fused-away and dead arrays
  envs1 <- bindLocals depth envs

  (peeling, nested, after) <- genSequential' envs1 ops
  case sizes of
    -- No further nested loops
    [] -> return ()
    -- Start a nested loop
    ((idxIdx, dir, sz) : szs) -> do
      -- Only perform loop peeling if there are no nested loops.
      -- Loop peeling causes code duplication, which is a larger problem if
      -- there are nested loops. Furthermore, if there are (expensive) nested
      -- loops, then the benefit of loop peeling here will be less.
      let peeling' = if null szs then peeling else PeelNot
      loopWith peeling' (isDescending dir) (A.liftInt 0) sz $ \isFirst idx -> do
        let envs2 = envs1{
            envsLoopDepth = depth + 1,
            envsIdx = partialUpdate (op scalarTypeInt idx) idxIdx $ envsIdx envs1,
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
  -> OpCodeGens target op env idxEnv
  -> CodeGen target
    -- Whether an operation in the loop prefers the first iteration to be split of the loop
    ( LoopPeeling
    -- The code in the next nested loop,
    -- if there is a deeper nested loop
    , OpCodeGens target op env idxEnv
    -- The code after the loop,
    -- or if there is no loop,
    -- the regular code we have to emit.
    , CodeGen target ()
    )
genSequential' envs = \case
  GenNil -> return (PeelNot, GenNil, return ())
  GenBind d lhs expr next
    | d == envsLoopDepth envs -> do
      value <- expr envs
      let envs' = envs{
          envsIdx = envsIdx envs `pushIdxEnv` (lhs, value)
        }
      (peel, nested, after) <- genSequential' envs' next
      return
        -- Keep this Bind in any nested loops, to still have access to the index.
        -- This returns the already introduced Operands, and does not
        -- reevaluate the expression
        ( peel
        , GenBind (d + 1) lhs (const $ return value) nested
        , after
        )
    | otherwise -> do
      let envs' = envs{
          envsIdx = partialEnvSkipLHS lhs $ envsIdx envs
        }
      (peel, nested, after) <- genSequential' envs' next
      -- Add GenBind to nested loop
      return
        ( peel
        , GenBind d lhs expr nested
        , after
        )
  GenOp d (OpCodeGenSingle c) next
    | d == envsLoopDepth envs -> do
      (peel, nested, after) <- genSequential' envs next
      -- Add the code after the loop (and before the 'after' instructions of
      -- later operations)
      return (peel, nested, c envs >> after)
  GenOp d (OpCodeGenLoop _ peel' before within after') next
    | d == envsLoopDepth envs -> do
      a <- before envs
      (peel, nested, after) <- genSequential' envs next
      return
        ( Prelude.max peel' peel
        , GenOp (d + 1) (OpCodeGenSingle $ within a) nested
        , after' a envs >> after
        )
  -- Operation is for a deeper loop
  GenOp d c next -> do
    (peel, nested, after) <- genSequential' envs next
    return
      ( peel
      , GenOp d c nested
      , after
      )

pushIdxEnv :: PartialEnv Operand env -> (ELeftHandSide t env env', Operands t) -> PartialEnv Operand env'
pushIdxEnv env (LeftHandSideSingle tp , e)               = env `PPush` op tp e
pushIdxEnv env (LeftHandSideWildcard _, _)               = env
pushIdxEnv env (LeftHandSidePair l1 l2, (OP_Pair e1 e2)) = pushIdxEnv env (l1, e1) `pushIdxEnv` (l2, e2)

parCodeGens
  :: CompileForeignExp target
  -- Generate parallel code for an operation. Only called for operations on the
  -- given loop depth, which were compiled to OpCodeGenLoop.
  => (forall idxEnv'. FlatOp op env idxEnv' -> Maybe (Exists (ParLoopCodeGen target env idxEnv')))
  -> LoopDepth
  -> OpCodeGens target op env idxEnv
  -> Maybe (Exists (ParCodeGens target op env idxEnv))
parCodeGens g depth code
  | Just (Exists parCode) <- parCodeGens' g depth code
  = Just $ Exists $ parHoistDeeperLoops parCode
  | otherwise
  = Nothing

-- Helper function for parCodeGens', such that parCodeGens can be implemented as
-- parHoistDeeperLoops after parCodeGens'
parCodeGens'
  :: CompileForeignExp target
  => (forall idxEnv'. FlatOp op env idxEnv' -> Maybe (Exists (ParLoopCodeGen target env idxEnv')))
  -> LoopDepth
  -> OpCodeGens target op env idxEnv
  -> Maybe (Exists (ParCodeGens target op env idxEnv))
parCodeGens' g depth = \case
  GenNil -> Just $ Exists ParGenNil
  GenBind d lhs expr next
    | Just (Exists next') <- parCodeGens' g depth next
    -> Just $ Exists $ ParGenBind d lhs expr next'
    | otherwise
    -> Nothing
  GenOp depth' (OpCodeGenSingle code) next -> case parCodeGens' g depth next of
    Just (Exists next')
      | depth' == depth ->
        Just $ Exists $ ParGenPar
          ( ParLoopCodeGen False TupRunit
            (\_ _ -> return ())
            (\_ _ -> return ())
            (\_ _ _ _ -> return ())
            (\_ _ _ _ -> return ())
            (\_ _ _ _ -> return ())
            (\_ _ _ -> return ())
            (\_ envs -> code envs)
            Nothing
          )
          next'
      | depth' == depth + 1 ->
        Just $ Exists $ ParGenPar
          ( ParLoopCodeGen False TupRunit
            (\_ _ -> return ())
            (\_ _ -> return ())
            (\_ _ _ _ -> return ())
            (\_ _ _ envs -> code envs)
            (\_ _ _ _ -> return ())
            (\_ _ _ -> return ())
            (\_ _ -> return ())
            Nothing
          )
          next'
      | otherwise ->
        Just $ Exists $ ParGenDeeper depth' (OpCodeGenSingle code) next'
    Nothing -> Nothing
  GenOp depth' opCode@(OpCodeGenLoop flatOp _ _ _ _) next -> case parCodeGens' g depth next of
    Just (Exists next')
      | depth' == depth -> case g flatOp of
        Just (Exists par)
          | parLoopMultipleTileLoops par
          -> Just $ Exists $ ParGenPar par $ ParGenTileLoopBoundary next'
          | otherwise
          -> Just $ Exists $ ParGenPar par next'
        Nothing -> Nothing
      | otherwise -> Just $ Exists $ ParGenDeeper depth' opCode next'
    Nothing -> Nothing

-- Hoists all ParGenDeeper to before the first ParGenTileLoopBoundary.
-- Throws an error if this is not possible
parHoistDeeperLoops :: ParCodeGens target op env idxEnv kernelMemory -> ParCodeGens target op env idxEnv kernelMemory
parHoistDeeperLoops ParGenNil = ParGenNil
parHoistDeeperLoops (ParGenBind d lhs expr next) = ParGenBind d lhs expr $ parHoistDeeperLoops next
parHoistDeeperLoops (ParGenPar par next) = ParGenPar par $ parHoistDeeperLoops next
parHoistDeeperLoops (ParGenDeeper d op next) = ParGenDeeper d op $ parHoistDeeperLoops next
parHoistDeeperLoops (ParGenTileLoopBoundary next)
  | (deeper, next') <- go next
  = foldr (uncurry ParGenDeeper) (ParGenTileLoopBoundary next') deeper
  where
    go :: ParCodeGens target op env idxEnv kernelMemory -> ([(LoopDepth, OpCodeGen target op env idxEnv)], ParCodeGens target op env idxEnv kernelMemory)
    go ParGenNil = ([], ParGenNil)
    go ParGenBind{} = internalError "Cannot hoist nested loops over a ParGenBind (binding of a backpermute)"
    go (ParGenPar par n)
      | (deeper, n') <- go n
      = (deeper, ParGenPar par n')
    go (ParGenTileLoopBoundary n)
      | (deeper, n') <- go n
      = (deeper, ParGenTileLoopBoundary n')
    go (ParGenDeeper d op n)
      | (deeper, n') <- go n
      = ((d, op) : deeper, n')

data ParCodeGens target op env idxEnv kernelMemory where
  ParGenNil
    :: ParCodeGens target op env idxEnv ()

  ParGenBind
    :: LoopDepth
    -> ELeftHandSide t idxEnv idxEnv'
    -> (Envs env idxEnv -> CodeGen target (Operands t))
    -> ParCodeGens target op env idxEnv' kernelMemory
    -> ParCodeGens target op env idxEnv kernelMemory

  ParGenPar
    :: ParLoopCodeGen target env idxEnv kernelMemory1
    -> ParCodeGens target op env idxEnv kernelMemory2
    -> ParCodeGens target op env idxEnv (Struct kernelMemory1, kernelMemory2)

  ParGenDeeper
    :: LoopDepth
    -> OpCodeGen target op env idxEnv
    -> ParCodeGens target op env idxEnv kernelMemory
    -> ParCodeGens target op env idxEnv kernelMemory

  -- This marks the end of one tile loop (and the start of the next).
  -- After a tile loop boundary, there should be no more ParGenDeepers:
  -- all nested loops should be placed in the first tile loop.
  ParGenTileLoopBoundary
    :: ParCodeGens target op env idxEnv kernelMemory
    -> ParCodeGens target op env idxEnv kernelMemory

data ParLoopCodeGen target env idxEnv kernelMemory where
  ParLoopCodeGen
    -- Whether the operation prefers loop peeling of the tile loop.
    :: Bool
    -- The type of kernel memory for this operation
    -> TupR PrimType kernelMemory
    -- Initialize kernel memory (before the start of the operation)
    -> (Operand (Ptr (Struct kernelMemory)) -> Envs env idxEnv -> CodeGen target ())
    -- Initialize a thread for the current row.
    -> (Operand (Ptr (Struct kernelMemory)) -> Envs env idxEnv -> CodeGen target a)
    -- Code before a tile loop. Bool denotes whether we generate code for the
    -- single threaded mode of zero overhead parallel scans.
    -- See https://dl.acm.org/doi/abs/10.1145/3649169.3649248
    -> (Bool -> a -> Operand (Ptr (Struct kernelMemory)) -> Envs env idxEnv -> CodeGen target ())
    -- Code within the tile loop
    -> (Bool -> a -> Operand (Ptr (Struct kernelMemory)) -> Envs env idxEnv -> CodeGen target ())
    -- Code after the tile loop
    -> (Bool -> a -> Operand (Ptr (Struct kernelMemory)) -> Envs env idxEnv -> CodeGen target ())
    -- Code when the thread stops working on this row.
    -> (a -> Operand (Ptr (Struct kernelMemory)) -> Envs env idxEnv -> CodeGen target ())
    -- Code after a row, *executed once*, by only one thread, per row
    -> (Operand (Ptr (Struct kernelMemory)) -> Envs env idxEnv -> CodeGen target ())
    -- Code in the next tile loop, and whether we want to do loop peeling in that loop.
    -> Maybe (Bool, a -> Operand (Ptr (Struct kernelMemory)) -> Envs env idxEnv -> CodeGen target ())
    -> ParLoopCodeGen target env idxEnv kernelMemory

parLoopMultipleTileLoops :: ParLoopCodeGen target env idxEnv kernelMemory -> Bool
parLoopMultipleTileLoops (ParLoopCodeGen _ _ _ _ _ _ _ _ _ nextTile) = isJust nextTile

parCodeGenMemory :: ParCodeGens target op env idxEnv kernelMemory -> TupR PrimType kernelMemory
parCodeGenMemory ParGenNil = TupRunit
parCodeGenMemory (ParGenBind _ _ _ next) = parCodeGenMemory next
parCodeGenMemory (ParGenDeeper _ _ next) = parCodeGenMemory next
parCodeGenMemory (ParGenTileLoopBoundary next) = parCodeGenMemory next
parCodeGenMemory (ParGenPar par next)
  | ParLoopCodeGen _ tp _ _ _ _ _ _ _ _ <- par
  = TupRsingle (StructPrimType False tp) `TupRpair` parCodeGenMemory next

parCodeGenInitMemory
  :: Operand (Ptr (Struct memoryFull))
  -> Envs env idxEnv
  -> TupleIdx memoryFull memory
  -> ParCodeGens target op env idxEnv memory
  -> CodeGen target ()
parCodeGenInitMemory ptr envs tupleIdx = \case
  ParGenNil -> return ()
  ParGenBind d lhs expr next
    | d == depth -> do
      value <- expr envs
      let envs' = envs{
          envsIdx = envsIdx envs `pushIdxEnv` (lhs, value)
        }
      parCodeGenInitMemory ptr envs' tupleIdx next
    | otherwise -> do
      let envs' = envs{
          envsIdx = partialEnvSkipLHS lhs $ envsIdx envs
        }
      parCodeGenInitMemory ptr envs' tupleIdx next
  ParGenDeeper _ _ next -> parCodeGenInitMemory ptr envs tupleIdx next
  ParGenTileLoopBoundary next -> parCodeGenInitMemory ptr envs tupleIdx next
  ParGenPar (ParLoopCodeGen _ tp init _ _ _ _ _ _ _) next -> do
    -- Pointer to the kernel memory of this operation
    thisPtr <- instr' $ GetStructElementPtr (StructPrimType False tp) ptr (tupleLeft tupleIdx)
    init thisPtr envs
    parCodeGenInitMemory ptr envs (tupleRight tupleIdx) next
  where
    depth = envsLoopDepth envs

parCodeGenFinish
  :: Operand (Ptr (Struct memoryFull))
  -> Envs env idxEnv
  -> TupleIdx memoryFull memory
  -> ParCodeGens target op env idxEnv memory
  -> CodeGen target ()
parCodeGenFinish ptr envs tupleIdx = \case
  ParGenNil -> return ()
  ParGenBind d lhs expr next
    | d == depth -> do
      value <- expr envs
      let envs' = envs{
          envsIdx = envsIdx envs `pushIdxEnv` (lhs, value)
        }
      parCodeGenFinish ptr envs' tupleIdx next
    | otherwise -> do
      let envs' = envs{
          envsIdx = partialEnvSkipLHS lhs $ envsIdx envs
        }
      parCodeGenFinish ptr envs' tupleIdx next
  ParGenDeeper _ _ next -> parCodeGenFinish ptr envs tupleIdx next
  ParGenTileLoopBoundary next -> parCodeGenFinish ptr envs tupleIdx next
  ParGenPar (ParLoopCodeGen _ tp _ _ _ _ _ _ finish _) next -> do
    -- Pointer to the kernel memory of this operation
    thisPtr <- instr' $ GetStructElementPtr (StructPrimType False tp) ptr (tupleLeft tupleIdx)
    finish thisPtr envs
    parCodeGenFinish ptr envs (tupleRight tupleIdx) next
  where
    depth = envsLoopDepth envs

data ParTileLoop target op env idxEnv where
  ParTileLoop ::
    { ptPeel   :: Bool
    , ptBefore :: (Envs env idxEnv -> CodeGen target ())
    , ptIn     :: OpCodeGens target op env idxEnv
    , ptAfter  :: (Envs env idxEnv -> CodeGen target ())
    } -> ParTileLoop target op env idxEnv

data ParTileLoops target op env idxEnv where
  ParTileLoops ::
    { ptFirstLoop  :: ParTileLoop target op env idxEnv
    , ptOtherLoops :: [ParTileLoop target op env idxEnv]
    -- Loop for the single threaded mode
    , ptSingleThreaded :: ParTileLoop target op env idxEnv
    -- Code when the thread stops working on this row.
    , ptExit       :: (Envs env idxEnv -> CodeGen target ())
    } -> ParTileLoops target op env idxEnv

emptyParTileLoop :: ParTileLoop target op env idxEnv
emptyParTileLoop = ParTileLoop False (\_ -> return ()) GenNil (\_ -> return ())

genParallel
  :: Operand (Ptr (Struct memoryFull))
  -> Envs env idxEnv
  -> TupleIdx memoryFull memory
  -> ParCodeGens target op env idxEnv memory
  -> CodeGen target (ParTileLoops target op env idxEnv)
genParallel ptr envs tupleIdx = \case
  ParGenNil ->
    return
      ( ParTileLoops emptyParTileLoop [] emptyParTileLoop (\_ -> return ()) )

  ParGenBind d lhs expr next
    | depth == d -> do
      value <- expr envs
      let envs' = envs{
          envsIdx = envsIdx envs `pushIdxEnv` (lhs, value)
        }
      ParTileLoops loop loops loopSeq exit <- genParallel ptr envs' tupleIdx next
      return $ ParTileLoops
          (loopExtendedEnv d lhs value loop)
          (map (loopExtendedEnv d lhs value) loops)
          (loopExtendedEnv d lhs value loopSeq)
          (withExtendedEnv lhs value exit)
    | otherwise -> do
      let envs' = envs{
            envsIdx = partialEnvSkipLHS lhs $ envsIdx envs
          }
      ParTileLoops loop loops loopSeq exit <- genParallel ptr envs' tupleIdx next
      return $ ParTileLoops
          (loopSkippedEnv d lhs expr loop)
          (map (loopSkippedEnv d lhs expr) loops)
          (loopSkippedEnv d lhs expr loopSeq)
          (withSkippedEnv lhs exit)

  ParGenPar (ParLoopCodeGen peel tp _ init before body after exit _ nextLoop) next -> do
    -- Pointer to the kernel memory of this operation
    thisPtr <- instr' $ GetStructElementPtr (StructPrimType False tp) ptr (tupleLeft tupleIdx)
    -- Initialize the thread state of this operation (type variable 'a' in ParLoopCodeGen)
    a <- init thisPtr envs
    -- Initialize later operations
    ParTileLoops loop loops loopSeq exitNext <- genParallel ptr envs (tupleRight tupleIdx) next
    -- Construct data structures describing the code generation of the tile loops
    -- Include this operation in the first tile loop
    let loop' = ParTileLoop
          (peel || ptPeel loop)
          (\e -> before False a thisPtr e >> ptBefore loop e)
          (GenOp (depth + 1) (OpCodeGenSingle $ body False a thisPtr) $ ptIn loop)
          (\e -> after False a thisPtr e >> ptAfter loop e)
    let loopSeq' = ParTileLoop
          (peel || ptPeel loopSeq)
          (\e -> before True a thisPtr e >> ptBefore loopSeq e)
          (GenOp (depth + 1) (OpCodeGenSingle $ body True a thisPtr) $ ptIn loopSeq)
          (\e -> after True a thisPtr e >> ptAfter loopSeq e)
    let exit' = \e -> exit a thisPtr e >> exitNext e
    let loops' = case nextLoop of
          Nothing -> loops
          Just (p, n) -> case loops of
            l : ls ->
              l{
                ptPeel = p || ptPeel l,
                ptIn = GenOp (depth + 1) (OpCodeGenSingle $ n a thisPtr) $ ptIn l
              } : ls
            _ -> internalError "Operations wants to emit code in next tile loop, but there is no next tile loop. Is there a ParGenTileLoopBoundary missing or misplaced?"
    return $ ParTileLoops loop' loops' loopSeq' exit'
  ParGenDeeper d opC next -> do
    ParTileLoops loop loops loopSeq exit <- genParallel ptr envs tupleIdx next
    let loop' = loop{
        ptIn = GenOp d opC $ ptIn loop
      }
    let loopSeq' = loopSeq{
        ptIn = GenOp d opC $ ptIn loop
      }
    return $ ParTileLoops loop' loops loopSeq' exit
  ParGenTileLoopBoundary next -> do
    -- Start a new empty tile loop
    ParTileLoops loop loops loopSeq exit <- genParallel ptr envs tupleIdx next
    -- loopSeq, the loop for the single threaded mode of zero overhead
    -- parallel scans, does not need multiple tile loops.
    return $ ParTileLoops emptyParTileLoop (loop : loops) loopSeq exit
  where
    depth = envsLoopDepth envs

    withSkippedEnv
      :: ELeftHandSide t idxEnv1 idxEnv2
      -> (Envs env idxEnv2 -> CodeGen target ())
      -> Envs env idxEnv1
      -> CodeGen target ()
    withSkippedEnv lhs f envs1 =
      f envs1{
          envsIdx = partialEnvSkipLHS lhs $ envsIdx envs1
        }

    loopSkippedEnv
      :: LoopDepth
      -> ELeftHandSide t idxEnv1 idxEnv2
      -> (Envs env idxEnv1 -> CodeGen target (Operands t))
      -> ParTileLoop target op env idxEnv2
      -> ParTileLoop target op env idxEnv1
    loopSkippedEnv d lhs expr (ParTileLoop peel before body after) =
      ParTileLoop peel
        (withSkippedEnv lhs before)
        (GenBind d lhs expr body)
        (withSkippedEnv lhs after)

    withExtendedEnv
      :: ELeftHandSide t idxEnv1 idxEnv2
      -> Operands t
      -> (Envs env idxEnv2 -> CodeGen target ())
      -> Envs env idxEnv1
      -> CodeGen target ()
    withExtendedEnv lhs value f envs1 =
      f envs1{
          envsIdx = envsIdx envs1 `pushIdxEnv` (lhs, value)
        }

    loopExtendedEnv
      :: LoopDepth
      -> ELeftHandSide t idxEnv1 idxEnv2
      -> Operands t
      -> ParTileLoop target op env idxEnv2
      -> ParTileLoop target op env idxEnv1
    loopExtendedEnv d lhs value (ParTileLoop peel before body after) =
      ParTileLoop peel
        (withExtendedEnv lhs value before)
        -- Keep this Bind in any nested loops, to still have access to the index.
        -- This returns the already introduced Operands, and does not
        -- reevaluate the expression
        -- (const $ return value)
        (GenBind (d + 1) lhs (\_ -> return value) body)
        (withExtendedEnv lhs value after)
