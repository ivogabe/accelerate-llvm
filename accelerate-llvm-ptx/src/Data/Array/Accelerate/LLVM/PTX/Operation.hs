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

module Data.Array.Accelerate.LLVM.PTX.Operation
  where

-- accelerate

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.Analysis.Hash.Operation
import Data.Array.Accelerate.Backend
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import Data.Array.Accelerate.Error


import qualified Data.Set as Set
import Data.Array.Accelerate.AST.Environment (weakenId, weakenEmpty, weakenSucc' )
import Data.Array.Accelerate.Representation.Array (ArrayR(..))
import Data.Array.Accelerate.Trafo.Var (DeclareVars(..), declareVars)
import Data.Array.Accelerate.Representation.Ground (buffersR)
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Trafo.Operation.Substitution (aletUnique, alet, weaken, LHS (..), mkLHS)
import Data.Array.Accelerate.Representation.Shape (ShapeR (..), shapeType, rank)
import Data.Array.Accelerate.Representation.Type (TypeR, TupR (..))
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Analysis.Match
import Data.Maybe (isJust)
import Data.Array.Accelerate.Interpreter (InOut (..))
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver hiding ( c )
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver as ILP
import Lens.Micro
import Lens.Micro.Mtl
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Desugar (desugarAlloc)

import Data.Array.Accelerate.AST.Idx (Idx(..))
import Data.Array.Accelerate.Pretty.Operation (prettyFun)
import Data.Array.Accelerate.Pretty.Exp (Val (Push))
import Unsafe.Coerce (unsafeCoerce)

import Control.Monad.State.Strict

data PTXOp t where
  PTXMap       :: PTXOp (Fun' (s -> t)    -> In sh s -> Out sh  t -> ())
  PTXBackpermute :: PTXOp (Fun' (sh' -> sh) -> In sh t -> Out sh' t -> ())
  PTXGenerate  :: PTXOp (Fun' (sh -> t)              -> Out sh  t -> ())
  PTXPermute   :: PTXOp (Fun' (e -> e -> e)
                         -> Mut sh' e
                         -> Mut sh' Word32
                         -> In sh (PrimMaybe (sh', e))
                         -> ())
  PTXPermute'  :: PTXOp (Mut sh' e
                         -> In sh (PrimMaybe (sh', e))
                         -> ())
  PTXScan      :: Direction
               -> PTXOp (Fun' (e -> e -> e)
                         -> Exp' e
                         -> In (sh, Int) e
                         -> Out (sh, Int) e
                         -> ())
  PTXScan1     :: Direction
               -> PTXOp (Fun' (e -> e -> e)
                         -> In (sh, Int) e
                         -> Out (sh, Int) e
                         -> ())
  PTXScan'     :: Direction
               -> PTXOp (Fun' (e -> e -> e)
                         -> Exp' e
                         -> In (sh, Int) e
                         -> Out (sh, Int) e
                         -> Out sh e
                         -> ())
  PTXFold      :: PTXOp (Fun' (e -> e -> e)
                         -> Exp' e
                         -> In (sh, Int) e
                         -> Out sh e
                         -> ())
  PTXFold1     :: PTXOp (Fun' (e -> e -> e)
                         -> In (sh, Int) e
                         -> Out sh e
                         -> ())

instance PrettyOp PTXOp where
  prettyOp PTXMap         = "map"
  prettyOp PTXBackpermute = "backpermute"
  prettyOp PTXGenerate    = "generate"
  prettyOp PTXPermute     = "permute"
  prettyOp PTXPermute'    = "permuteUnique"
  prettyOp (PTXScan dir) = case dir of
    LeftToRight -> "scanl"
    RightToLeft -> "scanr"
  prettyOp (PTXScan1 dir) = case dir of
    LeftToRight -> "scanl1"
    RightToLeft -> "scanr1"
  prettyOp (PTXScan' dir) = case dir of
    LeftToRight -> "scanl'"
    RightToLeft -> "scanr'"
  prettyOp PTXFold        = "fold"
  prettyOp PTXFold1       = "fold1"

instance NFData' PTXOp where
  rnf' !_ = ()

instance DesugarAcc PTXOp where
  mkMap         a b c   = Exec PTXMap         (a :>: b :>: c :>:       ArgsNil)
  mkBackpermute a b c   = Exec PTXBackpermute (a :>: b :>: c :>:       ArgsNil)
  mkGenerate    a b     = Exec PTXGenerate    (a :>: b :>:             ArgsNil)
  {- mkScan dir f (Just seed) i@(ArgArray In (ArrayR shr ty) sh buf) o
    = Exec (PTXScan dir) (f :>: seed :>: i :>: o :>: ArgsNil)
  mkScan dir f Nothing i@(ArgArray In (ArrayR shr ty) sh buf) o
    = Exec (PTXScan1 dir) (f :>: i :>: o :>: ArgsNil)
  mkScan' dir f seed i@(ArgArray In (ArrayR shr ty) sh buf) o1 o2
    = Exec (PTXScan' dir) (f :>: seed :>: i :>: o1 :>: o2 :>: ArgsNil)-}
  mkPermute     (Just a) b@(ArgArray _ (ArrayR shr _) sh _) c
    | DeclareVars lhs w lock <- declareVars $ buffersR $ TupRsingle scalarTypeWord32
    = aletUnique lhs 
        (Alloc shr scalarTypeWord32 $ groundToExpVar (shapeType shr) sh)
        $ alet LeftHandSideUnit
          (Exec PTXGenerate ( -- TODO: The old pipeline used a 'memset 0' instead, which sounds faster...
                ArgFun (Lam (LeftHandSideWildcard (shapeType shr)) $ Body $ Const scalarTypeWord32 0)
            :>: ArgArray Out (ArrayR shr (TupRsingle scalarTypeWord32)) (weakenVars w sh) (lock weakenId) 
            :>: ArgsNil))
          (Exec PTXPermute (
                weaken w a 
            :>: weaken w b 
            :>: ArgArray Mut (ArrayR shr (TupRsingle scalarTypeWord32)) (weakenVars w sh) (lock weakenId) 
            :>: weaken w c 
            :>: ArgsNil))
  mkPermute Nothing a b = Exec PTXPermute' (a :>: b :>: ArgsNil)
  {-mkFold a (Just seed) b c = Exec PTXFold (a :>: seed :>: b :>: c :>: ArgsNil)
  mkFold a Nothing b c = Exec PTXFold1 (a :>: b :>: c :>: ArgsNil) -}

instance SimplifyOperation PTXOp where
  detectCopy PTXMap         = detectMapCopies
  detectCopy PTXBackpermute = detectBackpermuteCopies
  detectCopy _              = const []

instance SLVOperation PTXOp where
  slvOperation PTXGenerate    = defaultSlvGenerate    PTXGenerate
  slvOperation PTXMap         = defaultSlvMap         PTXMap
  slvOperation PTXBackpermute = defaultSlvBackpermute PTXBackpermute
  slvOperation _ = Nothing

instance EncodeOperation PTXOp where
  encodeOperation PTXMap         = intHost $(hashQ ("Map" :: String))
  encodeOperation PTXBackpermute = intHost $(hashQ ("Backpermute" :: String))
  encodeOperation PTXGenerate    = intHost $(hashQ ("Generate" :: String))
  encodeOperation PTXPermute     = intHost $(hashQ ("Permute" :: String))
  encodeOperation PTXPermute'    = intHost $(hashQ ("Permute'" :: String))
  encodeOperation (PTXScan LeftToRight)  = intHost $(hashQ ("Scanl" :: String))
  encodeOperation (PTXScan RightToLeft)  = intHost $(hashQ ("Scanr" :: String))
  encodeOperation (PTXScan1 LeftToRight) = intHost $(hashQ ("Scanl1" :: String))
  encodeOperation (PTXScan1 RightToLeft) = intHost $(hashQ ("Scanr1" :: String))
  encodeOperation (PTXScan' LeftToRight) = intHost $(hashQ ("Scanl'" :: String))
  encodeOperation (PTXScan' RightToLeft) = intHost $(hashQ ("Scanr'" :: String))
  encodeOperation PTXFold        = intHost $(hashQ ("Fold" :: String))
  encodeOperation PTXFold1       = intHost $(hashQ ("Fold1" :: String))

instance SetOpIndices PTXOp where
  setOpIndices _ PTXGenerate _ idxArgs = Just $ Right idxArgs -- Generate has no In arrays
  setOpIndices _ PTXMap _ (_ :>: _ :>: IdxArgIdx d i :>: ArgsNil)
    = Just $ Right $ IdxArgNone :>: IdxArgIdx d i :>: IdxArgIdx d i :>: ArgsNil
  setOpIndices _ PTXMap _ _ = error "Missing indices for PTXMap"
  setOpIndices _ PTXBackpermute _ _ = Just $ Left IsBackpermute
  setOpIndices _ (PTXScan _) _ (_ :>: _ :>: _ :>: IdxArgIdx d i :>: ArgsNil)
    -- Annotate the input with an index.
    -- Don't annotate the output. We don't fuse over the output of a normal scan,
    -- as the output of a scan is one longer than the input.
    -- We do fuse the other scans (scan' and scan1).
    = Just $ Right $ IdxArgNone :>: IdxArgNone :>: IdxArgIdx d i :>: IdxArgNone :>: ArgsNil
  setOpIndices _ (PTXScan _) _ _ = error "Missing indices for PTXScan"
  setOpIndices _ (PTXScan1 _) _ (_ :>: _ :>: IdxArgIdx d i :>: ArgsNil)
    = Just $ Right $ IdxArgNone :>: IdxArgIdx d i :>: IdxArgIdx d i :>: ArgsNil
  setOpIndices _ (PTXScan1 _) _ _ = error "Missing indices for PTXScan1"
  setOpIndices _ (PTXScan' _) _ (_ :>: _ :>: _ :>: IdxArgIdx d i :>: o :>: ArgsNil)
    = Just $ Right $ IdxArgNone :>: IdxArgNone :>: IdxArgIdx d i :>: IdxArgIdx d i :>: o :>: ArgsNil
  setOpIndices _ (PTXScan' _) _ _ = error "Missing indices for PTXScan'"
  setOpIndices indexVar PTXFold _ (_ :>: _ :>: _ :>: IdxArgIdx d i :>: ArgsNil)
    | Just i' <- indexVar d
    = Just $ Right $
      IdxArgNone :>: IdxArgNone :>: IdxArgIdx (d + 1) (i `TupRpair` TupRsingle (Var scalarTypeInt i')) :>: IdxArgIdx d i :>: ArgsNil
    | otherwise
    = Nothing
  setOpIndices _ PTXFold _ _ = error "Missing indices for PTXFold"
  setOpIndices indexVar PTXFold1 _ (_ :>: _ :>: IdxArgIdx d i :>: ArgsNil)
    | Just i' <- indexVar d
    = Just $ Right $
      IdxArgNone :>: IdxArgIdx (d + 1) (i `TupRpair` TupRsingle (Var scalarTypeInt i')) :>: IdxArgIdx d i :>: ArgsNil
    | otherwise
    = Nothing
  setOpIndices _ PTXFold1 _ _ = error "Missing indices for PTXFold1"
  setOpIndices indexVar PTXPermute (_ :>: _ :>: _ :>: ArgArray _ (ArrayR shr _) _ _ :>: _) (_ :: IdxArgs idxEnv f)
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
  setOpIndices indexVar PTXPermute' (_ :>: ArgArray _ (ArrayR shr _) _ _ :>: _) (_ :: IdxArgs idxEnv f)
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

  getOpLoopDirections (PTXScan dir) _ (_ :>: _ :>: IdxArgIdx _ i :>: _)
    | _ `TupRpair` TupRsingle var <- i = [(varIdx var, dir')]
    where
      dir' = case dir of
        LeftToRight -> LoopAscending
        RightToLeft -> LoopDescending
  getOpLoopDirections (PTXScan1 dir) _ (_ :>: _ :>: IdxArgIdx _ i :>: _)
    | _ `TupRpair` TupRsingle var <- i = [(varIdx var, dir')]
    where
      dir' = case dir of
        LeftToRight -> LoopAscending
        RightToLeft -> LoopDescending
  getOpLoopDirections (PTXScan' dir) _ (_ :>: _ :>: _ :>: IdxArgIdx _ i :>: _)
    | _ `TupRpair` TupRsingle var <- i = [(varIdx var, dir')]
    where
      dir' = case dir of
        LeftToRight -> LoopAscending
        RightToLeft -> LoopDescending
  getOpLoopDirections PTXFold _ (_ :>: _ :>: IdxArgIdx _ i :>: _)
    | _ `TupRpair` TupRsingle var <- i = [(varIdx var, LoopMonotone)]
  getOpLoopDirections PTXFold1 _ (_ :>: IdxArgIdx _ i :>: _)
    | _ `TupRpair` TupRsingle var <- i = [(varIdx var, LoopMonotone)]
  getOpLoopDirections _ _ _ = []

instance MakesILP PTXOp where
  type BackendVar PTXOp = ()
  type BackendArg PTXOp = Int -- direction: used to separate clusters later, preventing accidental horizontal fusion of backpermutes
  defaultBA = 0
  data BackendClusterArg PTXOp a = BCAN

  mkGraph :: Node Comp
          -> PTXOp args
          -> LabelledArgs env args
          -> State (BackendGraphState PTXOp env) ()
  mkGraph c@(Node i _) PTXBackpermute (_fun :>: L _ lIn :>: L _ lOut :>: ArgsNil) = do
    let bsIn  = getLabelArrDeps lIn
    let bsOut = getLabelArrDeps lOut
    wsIn <- use $ allWriters bsIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c)
      <> allEqual ([ILP.int i] <>  readDirs (S.map (,c) bsIn))
      <> allEqual (               writeDirs (S.map (c,) bsOut)))
    fusionILP.bounds %= (<> defaultBounds bsIn c bsOut)
    -- Different order, so no in-place paths.

  mkGraph c PTXGenerate (_fun :>: L _ lOut :>: ArgsNil) = do
    let bsOut = getLabelArrDeps lOut
    fusionILP.constraints %= (<> allEqual (writeDirs (S.map (c,) bsOut)))
    fusionILP.bounds %= (<> defaultBounds mempty c bsOut)
    -- No input, so no in-place paths.

  mkGraph c PTXMap (L (ArgFun fun) _ :>: L _ lIn :>: L _ lOut :>: ArgsNil) = do
    let bsIn  = getLabelArrDeps lIn
    let bsOut = getLabelArrDeps lOut
    wsIn <- use $ allWriters $ getLabelArrDeps lIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c)
      <> allEqual (readDirs (S.map (,c) bsIn) <> writeDirs (S.map (c,) bsOut)))
    fusionILP.bounds %= (<> defaultBounds bsIn c bsOut)
    fusionILP.inplacePaths %= case isIdentity fun of
      Just Refl -> (<> mkUnitInplacePaths (Number nComps * Number nComps) c lIn lOut)
      _         -> (<> mkUnitInplacePaths 1 c lIn lOut)

  {- mkGraph PTXPermute (_ :>: L _ (_, lTargets) :>: L _ (_, lLocks) :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: ArgsNil) l =
    Graph.Info
      ( mempty & infusibleEdges .~ Set.map (-?> l) (lTargets <> lLocks)) -- add infusible edges from the producers of target and lock arrays to the permute
      (    inputConstraints l lIns
        <> ILP.c (InFoldSize l) .==. ILP.c (OutFoldSize l)
        <> ILP.c (InDims l) .==. int (rank shr)
        <> ILP.c (InDir  l) .==. int (-2)
        <> ILP.c (OutDir l) .==. int (-3)) -- Permute cannot fuse with its consumer
      ( lower (-2) (InDir l)
      <> upper (InDir l) (-1) ) -- default lowerbound for the input, but not for the output (as we set it to -3). -}

  mkGraph c PTXPermute (_fun :>: L _ lTargets :>: L _ lLocks :>: L _ lIn :>: ArgsNil) = do
    let bsTargets = getLabelArrDeps lTargets
    let bsLocks   = getLabelArrDeps lLocks
    let bsIn      = getLabelArrDeps lIn
    wsTargets <- use $ allWriters bsTargets
    wsLocks   <- use $ allWriters bsLocks
    wsIn      <- use $ allWriters bsIn
    fusionILP %= (wsTargets <> wsLocks <> wsIn) `allBefore` c
    fusionILP.constraints %= (
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c))
    fusionILP.bounds %= (<> foldMap (equal (-2) . (`ReadDir` c)) (bsTargets <> bsLocks <> bsIn)
                         <> foldMap (equal (-3) . WriteDir c)    (bsTargets <> bsLocks <> bsIn))

  mkGraph c PTXPermute' (L _ lTargets :>: L _ lIn :>: ArgsNil) = do
    let bsTargets = getLabelArrDeps lTargets
    let bsIn      = getLabelArrDeps lIn
    wsTargets <- use $ allWriters bsTargets
    wsIn      <- use $ allWriters bsIn
    fusionILP %= wsTargets `allBefore` c
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c))
    fusionILP.bounds %= (<> foldMap (equal (-2) . (`ReadDir` c)) (bsTargets <> bsIn)
                         <> foldMap (equal (-3) . WriteDir c) bsTargets)

  mkGraph c (PTXScan (dirToInt -> dir)) (_fun :>: _exp :>: L _ lIn :>: L _ lOut :>: ArgsNil) = do
    let bsIn  = getLabelArrDeps lIn
    let bsOut = getLabelArrDeps lOut
    wsIn <- use $ allWriters $ getLabelArrDeps lIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c))
    fusionILP.bounds %= (<> foldMap (equal dir  . (`ReadDir` c)) bsIn
                         <> foldMap (equal (-3) . WriteDir c) bsOut)
    -- Output size is one larger, so no in-place paths.

  mkGraph c (PTXScan1 (dirToInt -> dir)) (_fun :>: L _ lIn :>: L _ lOut :>: ArgsNil) = do
    let bsIn  = getLabelArrDeps lIn
    let bsOut = getLabelArrDeps lOut
    wsIn <- use $ allWriters bsIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (InFoldSize c) .==. ILP.var (OutFoldSize c))
    fusionILP.bounds %= (<> foldMap (equal dir . (`ReadDir` c)) bsIn
                         <> foldMap (equal dir . WriteDir c) bsOut)
    fusionILP.inplacePaths %= (<> mkUnitInplacePaths 1 c lIn lOut)

  mkGraph c (PTXScan' (dirToInt -> dir)) (_fun :>: _exp :>: L _ lIn :>: L _ lOut1 :>: L _ lOut2 :>: ArgsNil) = do
    let bsIn   = getLabelArrDeps lIn
    let bsOut1 = getLabelArrDeps lOut1
    let bsOut2 = getLabelArrDeps lOut2
    wsIn <- use $ allWriters $ getLabelArrDeps lIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (OutFoldSize c) .==. ILP.int (c^.nodeId))
    fusionILP.bounds %= (<> foldMap (equal dir . (`ReadDir` c)) bsIn
                         <> foldMap (equal dir . WriteDir c) (bsOut1 <> bsOut2))
    fusionILP.inplacePaths %= (<> mkUnitInplacePaths 1 c lIn lOut1)

  mkGraph c PTXFold (_fun :>: _exp :>: L _ lIn :>: L _ lOut :>: ArgsNil) = do
    let bsIn  = getLabelArrDeps lIn
    let bsOut = getLabelArrDeps lOut
    wsIn <- use $ allWriters bsIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (OutFoldSize c) .==. ILP.int (c^.nodeId)
      <> allEqual (readDirs (S.map (,c) bsIn) <> writeDirs (S.map (c,) bsOut)))
    fusionILP.bounds %= (<> defaultBounds bsIn c bsOut)
    -- Not the same shape, so no in-place paths.

  mkGraph c PTXFold1 (_fun :>: L _ lIn :>: L _ lOut :>: ArgsNil) = do
    let bsIn  = getLabelArrDeps lIn
    let bsOut = getLabelArrDeps lOut
    wsIn <- use $ allWriters bsIn
    fusionILP.constraints %= (
      <> inputConstraints c wsIn
      <> ILP.var (OutFoldSize c) .==. ILP.int (c^.nodeId)
      <> allEqual (readDirs (S.map (,c) bsIn) <> writeDirs (S.map (c,) bsOut)))
    fusionILP.bounds %= (<> defaultBounds bsIn c bsOut)
    -- Not the same shape, so no in-place paths.

  labelLabelledArg :: M.Map (Graph.Var PTXOp) Int -> Node Comp -> LabelledArg env a -> LabelledArgOp PTXOp env a
  labelLabelledArg vars c (L x@(ArgArray In  _ _ _) y) = LOp x y (vars M.! ReadDir  (getLabelArrDep y) c)
  labelLabelledArg vars c (L x@(ArgArray Out _ _ _) y) = LOp x y (vars M.! WriteDir c (getLabelArrDep y))
  labelLabelledArg _ _ (L x y) = LOp x y 0

  getClusterArg :: LabelledArgOp PTXOp env a -> BackendClusterArg PTXOp a
  getClusterArg (LOp _ _ _) = BCAN
  -- For each label: If the output is manifest, then its direction is negative (i.e. not in a backpermuted order)
  finalize g = foldMap (\(w,b) -> timesN (manifest b) .>. ILP.var (WriteDir w b)) (g^.writeEdges)

  encodeBackendClusterArg (BCAN) = intHost $(hashQ ("BCAN" :: String))

inputConstraints :: Node Comp -> Nodes Comp -> Constraint PTXOp
inputConstraints c = foldMap $ \wIn ->
                timesN (fused (wIn, c)) .>=. ILP.var (InFoldSize c) .-. ILP.var (OutFoldSize wIn)
    <> (-1) .*. timesN (fused (wIn, c)) .<=. ILP.var (InFoldSize c) .-. ILP.var (OutFoldSize wIn)

defaultBounds :: Nodes GVal -> Node Comp -> Nodes GVal -> Bounds PTXOp
defaultBounds bsIn c bsOut = foldMap (lower (-2) . (`ReadDir` c)) bsIn
                          <> foldMap (lower (-2) . WriteDir c) bsOut

instance NFData' (BackendClusterArg PTXOp) where
  rnf' !_ = ()

instance ShrinkArg (BackendClusterArg PTXOp) where
  shrinkArg _ BCAN = BCAN
  deadArg BCAN = BCAN

shrToTypeR :: ShapeR sh -> TypeR sh
shrToTypeR ShapeRz = TupRunit
shrToTypeR (ShapeRsnoc shr) = TupRpair (shrToTypeR shr) (TupRsingle scalarType)
