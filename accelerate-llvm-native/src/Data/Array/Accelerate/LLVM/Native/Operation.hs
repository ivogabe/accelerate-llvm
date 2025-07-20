{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Accelerate
-- Copyright   : [2014..2022] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Operation
  where

-- accelerate

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.Analysis.Hash.Operation
import Data.Array.Accelerate.Backend
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels


import Data.Array.Accelerate.AST.Environment (weakenId)
import Data.Array.Accelerate.Representation.Array (ArrayR(..))
import Data.Array.Accelerate.Trafo.Var (DeclareVars(..), declareVars)
import Data.Array.Accelerate.Representation.Ground (buffersR)
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Trafo.Operation.Substitution (aletUnique, alet, weaken)
import Data.Array.Accelerate.Representation.Shape (ShapeR (..), shapeType, rank)
import Data.Array.Accelerate.Representation.Type (TypeR, TupR (..))
import Data.Array.Accelerate.Type (scalarType, Word8, scalarTypeWord8, scalarTypeInt)
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver hiding ( var, int )
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver as ILP
import Lens.Micro
import Lens.Micro.Mtl

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Control.Monad.State.Strict
import Data.Foldable (fold)

data NativeOp t where
  NMap         :: NativeOp (Fun' (s -> t)    -> In sh s -> Out sh  t -> ())
  NBackpermute :: NativeOp (Fun' (sh' -> sh) -> In sh t -> Out sh' t -> ())
  NGenerate    :: NativeOp (Fun' (sh -> t)              -> Out sh  t -> ())
  NPermute     :: NativeOp (Fun' (e -> e -> e)
                         -> Mut sh' e
                         -> Mut sh' Word8
                         -> In sh (PrimMaybe (sh', e))
                         -> ())
  NPermute'    :: NativeOp (Mut sh' e
                         -> In sh (PrimMaybe (sh', e))
                         -> ())
  NScan        :: Direction
               -> NativeOp (Fun' (e -> e -> e)
                         -> Exp' e
                         -> In (sh, Int) e
                         -> Out (sh, Int) e
                         -> ())
  NScan1       :: Direction
               -> NativeOp (Fun' (e -> e -> e)
                         -> In (sh, Int) e
                         -> Out (sh, Int) e
                         -> ())
  NScan'       :: Direction
               -> NativeOp (Fun' (e -> e -> e)
                         -> Exp' e
                         -> In (sh, Int) e
                         -> Out (sh, Int) e
                         -> Out sh e
                         -> ())
  NFold        :: NativeOp (Fun' (e -> e -> e)
                         -> Exp' e
                         -> In (sh, Int) e
                         -> Out sh e
                         -> ())
  NFold1       :: NativeOp (Fun' (e -> e -> e)
                         -> In (sh, Int) e
                         -> Out sh e
                         -> ())

instance PrettyOp NativeOp where
  prettyOp NMap         = "map"
  prettyOp NBackpermute = "backpermute"
  prettyOp NGenerate    = "generate"
  prettyOp NPermute     = "permute"
  prettyOp NPermute'    = "permuteUnique"
  prettyOp (NScan dir) = case dir of
    LeftToRight -> "scanl"
    RightToLeft -> "scanr"
  prettyOp (NScan1 dir) = case dir of
    LeftToRight -> "scanl1"
    RightToLeft -> "scanr1"
  prettyOp (NScan' dir) = case dir of
    LeftToRight -> "scanl'"
    RightToLeft -> "scanr'"
  prettyOp NFold        = "fold"
  prettyOp NFold1       = "fold1"

instance NFData' NativeOp where
  rnf' !_ = ()

instance DesugarAcc NativeOp where
  mkMap         a b c   = Exec NMap         (a :>: b :>: c :>:       ArgsNil)
  mkBackpermute a b c   = Exec NBackpermute (a :>: b :>: c :>:       ArgsNil)
  mkGenerate    a b     = Exec NGenerate    (a :>: b :>:             ArgsNil)
  mkScan dir f (Just seed) i@(ArgArray In (ArrayR shr ty) sh buf) o
    = Exec (NScan dir) (f :>: seed :>: i :>: o :>: ArgsNil)
  mkScan dir f Nothing i@(ArgArray In (ArrayR shr ty) sh buf) o
    = Exec (NScan1 dir) (f :>: i :>: o :>: ArgsNil)
  mkScan' dir f seed i@(ArgArray In (ArrayR shr ty) sh buf) o1 o2
    = Exec (NScan' dir) (f :>: seed :>: i :>: o1 :>: o2 :>: ArgsNil)
  mkPermute     (Just a) b@(ArgArray _ (ArrayR shr _) sh _) c
    | DeclareVars lhs w lock <- declareVars $ buffersR $ TupRsingle scalarTypeWord8
    = aletUnique lhs
        (Alloc shr scalarTypeWord8 $ groundToExpVar (shapeType shr) sh)
        $ alet LeftHandSideUnit
          (Exec NGenerate ( -- TODO: The old pipeline used a 'memset 0' instead, which sounds faster...
                ArgFun (Lam (LeftHandSideWildcard (shapeType shr)) $ Body $ Const scalarTypeWord8 0)
            :>: ArgArray Out (ArrayR shr (TupRsingle scalarTypeWord8)) (weakenVars w sh) (lock weakenId)
            :>: ArgsNil))
          (Exec NPermute (
                weaken w a
            :>: weaken w b
            :>: ArgArray Mut (ArrayR shr (TupRsingle scalarTypeWord8)) (weakenVars w sh) (lock weakenId)
            :>: weaken w c
            :>: ArgsNil))
  mkPermute Nothing a b = Exec NPermute' (a :>: b :>: ArgsNil)
  mkFold a (Just seed) b c = Exec NFold (a :>: seed :>: b :>: c :>: ArgsNil)
  mkFold a Nothing b c = Exec NFold1 (a :>: b :>: c :>: ArgsNil)

instance SimplifyOperation NativeOp where
  detectCopy NMap         = detectMapCopies
  detectCopy NBackpermute = detectBackpermuteCopies
  detectCopy _            = const []

instance SLVOperation NativeOp where
  slvOperation NGenerate    = defaultSlvGenerate    NGenerate
  slvOperation NMap         = defaultSlvMap         NMap
  slvOperation NBackpermute = defaultSlvBackpermute NBackpermute
  slvOperation _ = Nothing

instance EncodeOperation NativeOp where
  encodeOperation NMap         = intHost $(hashQ ("Map" :: String))
  encodeOperation NBackpermute = intHost $(hashQ ("Backpermute" :: String))
  encodeOperation NGenerate    = intHost $(hashQ ("Generate" :: String))
  encodeOperation NPermute     = intHost $(hashQ ("Permute" :: String))
  encodeOperation NPermute'    = intHost $(hashQ ("Permute'" :: String))
  encodeOperation (NScan LeftToRight)  = intHost $(hashQ ("Scanl" :: String))
  encodeOperation (NScan RightToLeft)  = intHost $(hashQ ("Scanr" :: String))
  encodeOperation (NScan1 LeftToRight) = intHost $(hashQ ("Scanl1" :: String))
  encodeOperation (NScan1 RightToLeft) = intHost $(hashQ ("Scanr1" :: String))
  encodeOperation (NScan' LeftToRight) = intHost $(hashQ ("Scanl'" :: String))
  encodeOperation (NScan' RightToLeft) = intHost $(hashQ ("Scanr'" :: String))
  encodeOperation NFold        = intHost $(hashQ ("Fold" :: String))
  encodeOperation NFold1       = intHost $(hashQ ("Fold1" :: String))

instance SetOpIndices NativeOp where
  setOpIndices _ NGenerate _ idxArgs = Just $ Right idxArgs -- Generate has no In arrays
  setOpIndices _ NMap _ (_ :>: _ :>: IdxArgIdx d i :>: ArgsNil)
    = Just $ Right $ IdxArgNone :>: IdxArgIdx d i :>: IdxArgIdx d i :>: ArgsNil
  setOpIndices _ NMap _ _ = error "Missing indices for NMap"
  setOpIndices _ NBackpermute _ _ = Just $ Left IsBackpermute
  setOpIndices _ (NScan _) _ (_ :>: _ :>: _ :>: IdxArgIdx d i :>: ArgsNil)
    -- Annotate the input with an index.
    -- Don't annotate the output. We don't fuse over the output of a normal scan,
    -- as the output of a scan is one longer than the input.
    -- We do fuse the other scans (scan' and scan1).
    = Just $ Right $ IdxArgNone :>: IdxArgNone :>: IdxArgIdx d i :>: IdxArgNone :>: ArgsNil
  setOpIndices _ (NScan _) _ _ = error "Missing indices for NScan"
  setOpIndices _ (NScan1 _) _ (_ :>: _ :>: IdxArgIdx d i :>: ArgsNil)
    = Just $ Right $ IdxArgNone :>: IdxArgIdx d i :>: IdxArgIdx d i :>: ArgsNil
  setOpIndices _ (NScan1 _) _ _ = error "Missing indices for NScan1"
  setOpIndices _ (NScan' _) _ (_ :>: _ :>: _ :>: IdxArgIdx d i :>: o :>: ArgsNil)
    = Just $ Right $ IdxArgNone :>: IdxArgNone :>: IdxArgIdx d i :>: IdxArgIdx d i :>: o :>: ArgsNil
  setOpIndices _ (NScan' _) _ _ = error "Missing indices for NScan'"
  setOpIndices indexVar NFold _ (_ :>: _ :>: _ :>: IdxArgIdx d i :>: ArgsNil)
    | Just i' <- indexVar d
    = Just $ Right $
      IdxArgNone :>: IdxArgNone :>: IdxArgIdx (d + 1) (i `TupRpair` TupRsingle (Var scalarTypeInt i')) :>: IdxArgIdx d i :>: ArgsNil
    | otherwise
    = Nothing
  setOpIndices _ NFold _ _ = error "Missing indices for NFold"
  setOpIndices indexVar NFold1 _ (_ :>: _ :>: IdxArgIdx d i :>: ArgsNil)
    | Just i' <- indexVar d
    = Just $ Right $
      IdxArgNone :>: IdxArgIdx (d + 1) (i `TupRpair` TupRsingle (Var scalarTypeInt i')) :>: IdxArgIdx d i :>: ArgsNil
    | otherwise
    = Nothing
  setOpIndices _ NFold1 _ _ = error "Missing indices for NFold1"
  setOpIndices indexVar NPermute (_ :>: _ :>: _ :>: ArgArray _ (ArrayR shr _) _ _ :>: _) (_ :: IdxArgs idxEnv f)
    | Just i <- findIndex shr
    = Just $ Right $
      IdxArgNone :>: IdxArgNone :>: IdxArgNone :>: IdxArgIdx (rank shr) i :>: ArgsNil
    | otherwise
    = Nothing
    where
      findIndex :: ShapeR sh -> Maybe (ExpVars idxEnv sh)
      findIndex ShapeRz = Just TupRunit
      findIndex (ShapeRsnoc shr')
        | Just a <- findIndex shr'
        , Just b <- indexVar (rank shr')
        = Just $ a `TupRpair` TupRsingle (Var scalarTypeInt b)
        | otherwise = Nothing
  setOpIndices indexVar NPermute' (_ :>: ArgArray _ (ArrayR shr _) _ _ :>: _) (_ :: IdxArgs idxEnv f)
    | Just i <- findIndex shr
    = Just $ Right $
      IdxArgNone :>: IdxArgIdx (rank shr) i :>: ArgsNil
    | otherwise
    = Nothing
    where
      findIndex :: ShapeR sh -> Maybe (ExpVars idxEnv sh)
      findIndex ShapeRz = Just TupRunit
      findIndex (ShapeRsnoc shr')
        | Just a <- findIndex shr'
        , Just b <- indexVar (rank shr')
        = Just $ a `TupRpair` TupRsingle (Var scalarTypeInt b)
        | otherwise = Nothing

  getOpLoopDirections (NScan dir) _ (_ :>: _ :>: IdxArgIdx _ i :>: _)
    | _ `TupRpair` TupRsingle var <- i = [(varIdx var, dir')]
    where
      dir' = case dir of
        LeftToRight -> LoopAscending
        RightToLeft -> LoopDescending
  getOpLoopDirections (NScan1 dir) _ (_ :>: _ :>: IdxArgIdx _ i :>: _)
    | _ `TupRpair` TupRsingle var <- i = [(varIdx var, dir')]
    where
      dir' = case dir of
        LeftToRight -> LoopAscending
        RightToLeft -> LoopDescending
  getOpLoopDirections (NScan' dir) _ (_ :>: _ :>: _ :>: IdxArgIdx _ i :>: _)
    | _ `TupRpair` TupRsingle var <- i = [(varIdx var, dir')]
    where
      dir' = case dir of
        LeftToRight -> LoopAscending
        RightToLeft -> LoopDescending
  getOpLoopDirections NFold _ (_ :>: _ :>: IdxArgIdx _ i :>: _)
    | _ `TupRpair` TupRsingle var <- i = [(varIdx var, LoopMonotone)]
  getOpLoopDirections NFold1 _ (_ :>: IdxArgIdx _ i :>: _)
    | _ `TupRpair` TupRsingle var <- i = [(varIdx var, LoopMonotone)]
  getOpLoopDirections _ _ _ = []

                -- vvvv old vvv
                  -- 0 means maximal parallelism; each thread only gets 1 element, e.g. output of the first stage of 1-dimensional fold
                  -- 1 is segmented along the innermost dimension into nthreads equal parts, e.g. input of the first stage of 1-dimensional fold
                  -- 2 is one row for each thread
                  -- 3 is segmented along the second dimension, e.g. input of a fused folddim followed by first stage of 1-dimensional fold
                  -- 4 is 2 dimensions per thread, etc
                  -- note that this is about _logical_ threads; if there are less physical ones present then they will perform work stealing, so this is really the (minimum) size of each bucket in the work stealing queue
                -- ^^^^ old ^^^
-- data NativeILPVar = Dims InOut (Label Comp)
--                   | DepthPerThread InOut Label
--   deriving (Eq, Ord, Show)
-- pattern InDims, OutDims {- InDepth, OutDepth -}:: Label Comp -> Graph.Var NativeOp
-- pattern InDims   l = BackendSpecific (Dims            InArr l)
-- pattern OutDims  l = BackendSpecific (Dims           OutArr l)
-- pattern InDepth  l = BackendSpecific (DepthPerThread  InArr l)
-- pattern OutDepth l = BackendSpecific (DepthPerThread OutArr l)

-- TODO: factor out more common parts of mkGraph
-- TODO: do the TODO's in here, and also do them in the Interpreter\
-- TODO: constraints and bounds for the new variable(s)
-- TODO: remove commented out old code
instance MakesILP NativeOp where
  type BackendVar NativeOp = ()
  type BackendArg NativeOp = Int -- direction: used to separate clusters later, preventing accidental horizontal fusion of backpermutes
  defaultBA :: BackendArg NativeOp
  defaultBA = 0
  data BackendClusterArg NativeOp a = BCAN
  combineBackendClusterArg :: BackendClusterArg NativeOp (Out  sh e)
                           -> BackendClusterArg NativeOp (In   sh e)
                           -> BackendClusterArg NativeOp (Var' sh)
  combineBackendClusterArg _ _ = error "combineBackendClusterArg: Shouldn't be able to fuse."

  mkGraph :: Label Comp
          -> NativeOp args
          -> LabelledArgs env args
          -> State (BackendGraphState NativeOp env) ()
  mkGraph c@(Label i _) NBackpermute (_fun :>: L _ lIn :>: L _ lOut :>: ArgsNil) = do
    let bsIn  = getLabelArrDeps lIn
    let bsOut = getLabelArrDeps lOut
    wsIn <- use $ allWriters bsIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c)
      <> allEqual ([ILP.int i] <>  readDirs (S.map (,c) bsIn))
      <> allEqual (               writeDirs (S.map (c,) bsOut))
      {- <> ILP.var (InDir c)      .==. ILP.int i -})
    fusionILP.bounds %= (<> defaultBounds bsIn c bsOut)
    -- Different order, so no in-place paths.

  -- mkGraph l@(Label i _) NBackpermute (_ :>: L (ArgArray In (ArrayR _shrI _) _ _) (_, lIns) :>: L (ArgArray Out (ArrayR shrO _) _ _) _ :>: ArgsNil) =
  --   Graph.Info
  --     mempty
  --     (    inputConstraints l lIns
  --       <> ILP.var (InFoldSize l) .==. ILP.var (OutFoldSize l)
  --       <> ILP.var (InDir l) .==. int i
  --       <> ILP.var (InDims l) .==. ILP.var (OutDims l)
  --       <> inrankifmanifest shrO l
  --         -- .+. timesN (int 3 .+. c (OutDir l))
  --         -- When we switch to gather, like in the paper, we need to add this term.
  --         -- 4 + dir is always positive, and this is exactly why we (elsewhere) define `n` as `5+(size nodes)`
  --         -- problem: this clashes with the assumption in 'inputConstraints' and 'finalise' that orders are at most n,
  --         -- so if we want this we need to change inputConstraints and finalise
  --       )-- <> c (InDims l) .+. int (rank shrO) .==. c (OutDims l) .+. int (rank shrI))
  --     (defaultBounds l)

  mkGraph c NGenerate (_fun :>: L _ lOut :>: ArgsNil) = do
    let bsOut = getLabelArrDeps lOut
    fusionILP.constraints %= (<> allEqual (writeDirs (S.map (c,) bsOut)))
    fusionILP.bounds %= (<> defaultBounds mempty c bsOut)
    -- No input, so no in-place paths.

  -- mkGraph l NGenerate (_ :>: L (ArgArray Out (ArrayR shr _) _ _) _ :>: ArgsNil) =
  --   Graph.Info
  --     mempty
  --     (outrankifmanifest shr l)
  --     (defaultBounds l)

  mkGraph c NMap (_fun :>: L _ lIn :>: L _ lOut :>: ArgsNil) = do
    let bsIn  = getLabelArrDeps lIn
    let bsOut = getLabelArrDeps lOut
    wsIn <- use $ allWriters $ getLabelArrDeps lIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c)
      <> allEqual (readDirs (S.map (,c) bsIn) <> writeDirs (S.map (c,) bsOut))
      {- <> ILP.var (InDir c)      .==. ILP.var (OutDir c) -})
    fusionILP.bounds %= (<> defaultBounds bsIn c bsOut)
    fusionILP.inplacePaths %= (<> mkUnitInplacePaths 1 c lIn lOut)

  -- mkGraph l NMap (_ :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: _ :>: ArgsNil) =
  --   Graph.Info
  --     mempty
  --     (    inputConstraints l lIns
  --       <> ILP.var (InFoldSize l) .==. ILP.var (OutFoldSize l)
  --       <> ILP.var (InDir  l) .==. ILP.var (OutDir  l)
  --       <> ILP.var (InDims l) .==. ILP.var (OutDims l)
  --       <> inrankifmanifest shr l)
  --     (defaultBounds l)

  mkGraph c NPermute (_fun :>: L _ lTargets :>: L _ lLocks :>: L _ lIn :>: ArgsNil) = do
    let bsTargets = getLabelArrDeps lTargets
    let bsLocks   = getLabelArrDeps lLocks
    let bsIn      = getLabelArrDeps lIn
    wsTargets <- use $ allWriters bsTargets
    wsLocks   <- use $ allWriters bsLocks
    wsIn      <- use $ allWriters bsIn
    fusionILP %= (wsTargets <> wsLocks) `allBefore` c
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c)
      {- <> ILP.var (InDir  c)     .==. ILP.int (-2) -}
      {- <> ILP.var (OutDir c)     .==. ILP.int (-3) -})
    fusionILP.bounds %= (<> foldMap (equal (-2) . (`ReadDir` c)) (bsTargets <> bsLocks <> bsIn)
                         <> foldMap (equal (-3) . WriteDir c)    (bsTargets <> bsLocks))

    -- No output, so no in-place paths.

  -- mkGraph l NPermute (_ :>: L _ (_, lTargets) :>: L _ (_, lLocks) :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: ArgsNil) =
  --   Graph.Info
  --     ( mempty & infusibleEdges .~ Set.map (-?> l) (lTargets <> lLocks)) -- add infusible edges from the producers of target and lock arrays to the permute
  --     (    inputConstraints l lIns
  --       <> ILP.var (InFoldSize l) .==. ILP.var (OutFoldSize l)
  --       <> ILP.var (InDims l) .==. int (rank shr)
  --       <> ILP.var (InDir  l) .==. int (-2)
  --       <> ILP.var (OutDir l) .==. int (-3)) -- Permute cannot fuse with its consumer
  --     ( lower (-2) (InDir l)
  --     <> upper (InDir l) (-1) ) -- default lowerbound for the input, but not for the output (as we set it to -3).

  mkGraph c NPermute' (L _ lTargets :>: L _ lIn :>: ArgsNil) = do
    let bsTargets = getLabelArrDeps lTargets
    let bsIn      = getLabelArrDeps lIn
    wsTargets <- use $ allWriters bsTargets
    wsIn      <- use $ allWriters bsIn
    fusionILP %= wsTargets `allBefore` c
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c)
      {- <> ILP.var (InDir  c)     .==. ILP.int (-2) -}
      {- <> ILP.var (OutDir c)     .==. ILP.int (-3) -})
    fusionILP.bounds %= (<> foldMap (equal (-2) . (`ReadDir` c)) (bsTargets <> bsIn)
                         <> foldMap (equal (-3) . WriteDir c) bsTargets)
    -- No output, so no in-place paths.

  -- mkGraph l NPermute' (L _ (_, lTargets) :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: ArgsNil) =
  --   Graph.Info
  --     ( mempty & infusibleEdges .~ Set.map (-?> l) lTargets) -- add infusible edges from the producers of target array to the permute
  --     (    inputConstraints l lIns
  --       <> ILP.var (InFoldSize l) .==. ILP.var (OutFoldSize l)
  --       <> ILP.var (InDims l) .==. int (rank shr)
  --       <> ILP.var (InDir  l) .==. int (-2)
  --       <> ILP.var (OutDir l) .==. int (-3)) -- Permute cannot fuse with its consumer
  --     ( lower (-2) (InDir l)
  --     <> upper (InDir l) (-1) ) -- default lowerbound for the input, but not for the output (as we set it to -3).

  mkGraph c (NScan (dirToInt -> dir)) (_fun :>: _exp :>: L _ lIn :>: L _ lOut :>: ArgsNil) = do
    let bsIn  = getLabelArrDeps lIn
    let bsOut = getLabelArrDeps lOut
    wsIn <- use $ allWriters $ getLabelArrDeps lIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c)
      {- <> ILP.var (InDir  c)     .==. ILP.int dir -}
      {- <> ILP.var (OutDir c)     .==. ILP.int (-3) -})
    fusionILP.bounds %= (<> foldMap (equal dir  . (`ReadDir` c)) bsIn
                         <> foldMap (equal (-3) . WriteDir c) bsOut)
    -- Output size is one larger, so no in-place paths.

  -- mkGraph l (NScan dir) (_ :>: _ :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: L _ (_, lOut) :>: ArgsNil) =
  --   Graph.Info
  --     -- Scan cannot fuse with its consumer, as the output is one larger than the input
  --     mempty
  --     (    inputConstraints l lIns
  --       <> ILP.var (InFoldSize l) .==. ILP.var (OutFoldSize l)
  --       <> ILP.var (InDir  l) .==. int dir'
  --       <> ILP.var (OutDir l) .==. int (-3)
  --       <> ILP.var (InDims l) .==. ILP.var (OutDims l)
  --       <> ILP.var (InDims l) .==. int (rank shr))
  --     ( lower (-2) (InDir l) <> lower (-3) (OutDir l) <> lower 0 (InDims l) <> lower 0 (OutDims l) )
  --   where
  --     dir' = case dir of
  --       LeftToRight -> -2
  --       RightToLeft -> -1

  mkGraph c (NScan1 (dirToInt -> dir)) (_fun :>: L _ lIn :>: L _ lOut :>: ArgsNil) = do
    let bsIn  = getLabelArrDeps lIn
    let bsOut = getLabelArrDeps lOut
    wsIn <- use $ allWriters bsIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c)
      {- <> allEqual ([ILP.int dir] <> foldl (\e -> (:e) .  readDir . (,c)) [] bsIn
                                 <> foldl (\e -> (:e) . writeDir . (c,)) [] bsOut) -}
      {- <> ILP.var (InDir  c)     .==. ILP.int dir -}
      {- <> ILP.var (OutDir c)     .==. ILP.int dir -})
    fusionILP.bounds %= (<> foldMap (equal dir . (`ReadDir` c)) bsIn
                         <> foldMap (equal dir . WriteDir c) bsOut)
    fusionILP.inplacePaths %= (<> mkUnitInplacePaths 1 c lIn lOut)

  -- mkGraph l (NScan1 dir) (_ :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: _ :>: ArgsNil) =
  --   Graph.Info
  --     mempty
  --     (    inputConstraints l lIns
  --       <> ILP.var (InFoldSize l) .==. ILP.var (OutFoldSize l)
  --       <> ILP.var (InDir  l) .==. int dir'
  --       <> ILP.var (OutDir l) .==. int dir'
  --       <> ILP.var (InDims l) .==. ILP.var (OutDims l)
  --       <> ILP.var (InDims l) .==. int (rank shr))
  --     (defaultBounds l)
  --   where
  --     dir' = case dir of
  --       LeftToRight -> -2
  --       RightToLeft -> -1

  mkGraph c (NScan' (dirToInt -> dir)) (_fun :>: _exp :>: L _ lIn :>: L _ lOut1 :>: L _ lOut2 :>: ArgsNil) = do
    let bsIn   = getLabelArrDeps lIn
    let bsOut1 = getLabelArrDeps lOut1
    let bsOut2 = getLabelArrDeps lOut2
    wsIn <- use $ allWriters $ getLabelArrDeps lIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c)
      {- <> allEqual ([ILP.int dir] <> readDirs  (S.map (,c) bsIn)
                                 <> writeDirs (S.map (c,) bsOut1)
                                 <> writeDirs (S.map (c,) bsOut2)) -}
      {- <> ILP.var (InDir  c)     .==. ILP.int dir -}
      {- <> ILP.var (OutDir c)     .==. ILP.int dir -})
    fusionILP.bounds %= (<> foldMap (equal dir . (`ReadDir` c)) bsIn
                         <> foldMap (equal dir . WriteDir c) (bsOut1 <> bsOut2))
    fusionILP.inplacePaths %= (<> mkUnitInplacePaths 1 c lIn lOut1)

  -- mkGraph l (NScan' dir) (_ :>: _ :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: _ :>: _ :>: ArgsNil) =
  --   Graph.Info
  --     mempty
  --     (    inputConstraints l lIns
  --       <> ILP.var (InFoldSize l) .==. ILP.var (OutFoldSize l)
  --       <> ILP.var (InDir  l) .==. int dir'
  --       -- TODO: Does this give a problem for the second output of scan' (the reduced values)?
  --       -- That array is one dimension lower.
  --       <> ILP.var (OutDir l) .==. int dir'
  --       <> ILP.var (InDims l) .==. ILP.var (OutDims l)
  --       <> ILP.var (InDims l) .==. int (rank shr))
  --     (defaultBounds l)
  --   where
  --     dir' = case dir of
  --       LeftToRight -> -2
  --       RightToLeft -> -1

  mkGraph c NFold (_fun :>: _exp :>: L _ lIn :>: L _ lOut :>: ArgsNil) = do
    let bsIn  = getLabelArrDeps lIn
    let bsOut = getLabelArrDeps lOut
    wsIn <- use $ allWriters bsIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c)
      <> allEqual (readDirs (S.map (,c) bsIn) <> writeDirs (S.map (c,) bsOut))
      {- <> ILP.var (InDir  c)     .==. ILP.var (OutDir c) -})
    fusionILP.bounds %= (<> defaultBounds bsIn c bsOut)
  -- Not the same shape, so no in-place paths.

  -- mkGraph l NFold (_ :>: _ :>: L (ArgArray In (ArrayR (ShapeRsnoc shr) _) _ _) (_, lIns) :>: _ :>: ArgsNil) =
  --   Graph.Info
  --     mempty
  --     (    inputConstraints l lIns
  --       <> ILP.var (InFoldSize l) .==. int (_labelId l)
  --       <> ILP.var (InDir  l) .==. ILP.var (OutDir l)
  --       <> ILP.var (InDims l) .==. int 1 .+. ILP.var (OutDims l)
  --       -- <> foldMap (\lin -> fused lin l .==. int 1) lIns
  --       <> inrankifmanifest (ShapeRsnoc shr) l)
  --     (defaultBounds l)

  mkGraph c NFold1 (_fun :>: L _ lIn :>: L _ lOut :>: ArgsNil) = do
    let bsIn  = getLabelArrDeps lIn
    let bsOut = getLabelArrDeps lOut
    wsIn <- use $ allWriters bsIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.int (c^.labelId)
      <> allEqual (readDirs (S.map (,c) bsIn) <> writeDirs (S.map (c,) bsOut))
      {- <> ILP.var (InDir  c)     .==. ILP.var (OutDir c) -})
    fusionILP.bounds %= (<> defaultBounds bsIn c bsOut)
  -- Not the same shape, so no in-place paths.

  -- mkGraph l NFold1 (_ :>: L (ArgArray In (ArrayR (ShapeRsnoc shr) _) _ _) (_, lIns) :>: _ :>: ArgsNil) =
  --   Graph.Info
  --     mempty
  --     (    inputConstraints l lIns
  --       <> ILP.var (InFoldSize l) .==. int (_labelId l)
  --       <> ILP.var (InDir  l) .==. ILP.var (OutDir l)
  --       <> ILP.var (InDims l) .==. int 1 .+. ILP.var (OutDims l)
  --       -- <> foldMap (\lin -> fused lin l .==. int 1) lIns
  --       <> inrankifmanifest (ShapeRsnoc shr) l)
  --     (defaultBounds l)

  labelLabelledArg :: M.Map (Graph.Var NativeOp) Int -> Label Comp -> LabelledArg env a -> LabelledArgOp NativeOp env a
  labelLabelledArg vars c (L x@(ArgArray In  _ _ _) y) = LOp x y (vars M.! ReadDir  (getLabelArrDep y) c)
  labelLabelledArg vars c (L x@(ArgArray Out _ _ _) y) = LOp x y (vars M.! WriteDir c (getLabelArrDep y))
  labelLabelledArg _ _ (L x y) = LOp x y 0

  getClusterArg :: LabelledArgOp NativeOp env a -> BackendClusterArg NativeOp a
  getClusterArg LOp{} = BCAN

  -- For each label: If the output is manifest, then its direction is negative (i.e. not in a backpermuted order)
  finalize :: FusionGraph -> Constraint NativeOp
  finalize g = foldMap (\(w,b) -> timesN (manifest b) .>. ILP.var (WriteDir w b)) (g^.writeEdges)

  encodeBackendClusterArg BCAN = intHost $(hashQ ("BCAN" :: String))

inputConstraints :: Label Comp -> Labels Comp -> Constraint NativeOp
inputConstraints c = foldMap $ \wIn ->
    --             timesN (fused lIn l) .>=. ILP.var (InDims l) .-. ILP.var (OutDims lIn)
    -- <> (-1) .*. timesN (fused lIn l) .<=. ILP.var (InDims l) .-. ILP.var (OutDims lIn)
                timesN (fused (wIn, c)) .>=. ILP.var (InFoldSize c) .-. ILP.var (OutFoldSize wIn)
    <> (-1) .*. timesN (fused (wIn, c)) .<=. ILP.var (InFoldSize c) .-. ILP.var (OutFoldSize wIn)

defaultBounds :: Labels GVal -> Label Comp -> Labels GVal -> Bounds NativeOp
defaultBounds bsIn c bsOut = foldMap (lower (-2) . (`ReadDir` c)) bsIn
                          <> foldMap (lower (-2) . WriteDir c) bsOut

instance NFData' (BackendClusterArg NativeOp) where
  rnf' :: BackendClusterArg NativeOp a -> ()
  rnf' !_ = ()

instance ShrinkArg (BackendClusterArg NativeOp) where
  shrinkArg :: SubArg t t' -> BackendClusterArg NativeOp t -> BackendClusterArg NativeOp t'
  shrinkArg _ BCAN = BCAN
  deadArg :: BackendClusterArg NativeOp (Out sh e) -> BackendClusterArg NativeOp (Var' sh)
  deadArg BCAN = BCAN

shrToTypeR :: ShapeR sh -> TypeR sh
shrToTypeR ShapeRz = TupRunit
shrToTypeR (ShapeRsnoc shr) = TupRpair (shrToTypeR shr) (TupRsingle scalarType)


dirToInt :: Direction -> Int
dirToInt LeftToRight = -2
dirToInt RightToLeft = -1
