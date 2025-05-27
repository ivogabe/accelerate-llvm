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
import Data.Array.Accelerate.Type (scalarType, Word8, scalarTypeWord8, scalarTypeInt, singleType)
import Data.Array.Accelerate.Analysis.Match
import Data.Maybe (isJust)
import Data.Array.Accelerate.Interpreter (InOut (..))
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver hiding ( c )
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver as ILP
import Lens.Micro
import qualified Data.Map as M
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Desugar (desugarAlloc)

import Data.Array.Accelerate.AST.Idx (Idx(..))
import Data.Array.Accelerate.Pretty.Operation (prettyFun)
import Data.Array.Accelerate.Pretty.Exp (Val (Push))
import Unsafe.Coerce (unsafeCoerce)

data PTXOp t where
  -- PTXMap       :: PTXOp (Fun' (s -> t)    -> In sh s -> Out sh  t -> ())
  -- PTXBackpermute :: PTXOp (Fun' (sh' -> sh) -> In sh t -> Out sh' t -> ())
  PTXGenerate  :: PTXOp (Fun' (sh -> t)              -> Out sh  t -> ())
  {- PTXPermute   :: PTXOp (Fun' (e -> e -> e)
                         -> Mut sh' e
                         -> Mut sh' Word8
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
                         -> ()) -}

instance PrettyOp PTXOp where
  --prettyOp PTXMap         = "map"
  --prettyOp PTXBackpermute = "backpermute"
  prettyOp PTXGenerate    = "generate"
  {-prettyOp PTXPermute     = "permute"
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
  prettyOp PTXFold1       = "fold1"-}

instance NFData' PTXOp where
  rnf' !_ = ()

instance DesugarAcc PTXOp where
  -- mkMap         a b c   = Exec PTXMap         (a :>: b :>: c :>:       ArgsNil)
  -- mkBackpermute a b c   = Exec PTXBackpermute (a :>: b :>: c :>:       ArgsNil)
  mkGenerate    a b     = Exec PTXGenerate    (a :>: b :>:             ArgsNil)
  {- mkScan dir f (Just seed) i@(ArgArray In (ArrayR shr ty) sh buf) o
    = Exec (PTXScan dir) (f :>: seed :>: i :>: o :>: ArgsNil)
  mkScan dir f Nothing i@(ArgArray In (ArrayR shr ty) sh buf) o
    = Exec (PTXScan1 dir) (f :>: i :>: o :>: ArgsNil)
  mkScan' dir f seed i@(ArgArray In (ArrayR shr ty) sh buf) o1 o2
    = Exec (PTXScan' dir) (f :>: seed :>: i :>: o1 :>: o2 :>: ArgsNil)
  mkPermute     (Just a) b@(ArgArray _ (ArrayR shr _) sh _) c
    | DeclareVars lhs w lock <- declareVars $ buffersR $ TupRsingle scalarTypeWord8
    = aletUnique lhs 
        (Alloc shr scalarTypeWord8 $ groundToExpVar (shapeType shr) sh)
        $ alet LeftHandSideUnit
          (Exec PTXGenerate ( -- TODO: The old pipeline used a 'memset 0' instead, which sounds faster...
                ArgFun (Lam (LeftHandSideWildcard (shapeType shr)) $ Body $ Const scalarTypeWord8 0)
            :>: ArgArray Out (ArrayR shr (TupRsingle scalarTypeWord8)) (weakenVars w sh) (lock weakenId) 
            :>: ArgsNil))
          (Exec PTXPermute (
                weaken w a 
            :>: weaken w b 
            :>: ArgArray Mut (ArrayR shr (TupRsingle scalarTypeWord8)) (weakenVars w sh) (lock weakenId) 
            :>: weaken w c 
            :>: ArgsNil))
  mkPermute Nothing a b = Exec PTXPermute' (a :>: b :>: ArgsNil)
  mkFold a (Just seed) b c = Exec PTXFold (a :>: seed :>: b :>: c :>: ArgsNil)
  mkFold a Nothing b c = Exec PTXFold1 (a :>: b :>: c :>: ArgsNil) -}

instance SimplifyOperation PTXOp where
  -- detectCopy PTXMap         = detectMapCopies
  -- detectCopy PTXBackpermute = detectBackpermuteCopies
  detectCopy _              = const []

instance SLVOperation PTXOp where
  slvOperation PTXGenerate    = defaultSlvGenerate    PTXGenerate
  -- slvOperation PTXMap         = defaultSlvMap         PTXMap
  -- slvOperation PTXBackpermute = defaultSlvBackpermute PTXBackpermute
  slvOperation _ = Nothing

instance EncodeOperation PTXOp where
  --encodeOperation PTXMap         = intHost $(hashQ ("Map" :: String))
  --encodeOperation PTXBackpermute = intHost $(hashQ ("Backpermute" :: String))
  encodeOperation PTXGenerate    = intHost $(hashQ ("Generate" :: String))
  {-encodeOperation PTXPermute     = intHost $(hashQ ("Permute" :: String))
  encodeOperation PTXPermute'    = intHost $(hashQ ("Permute'" :: String))
  encodeOperation (PTXScan LeftToRight)  = intHost $(hashQ ("Scanl" :: String))
  encodeOperation (PTXScan RightToLeft)  = intHost $(hashQ ("Scanr" :: String))
  encodeOperation (PTXScan1 LeftToRight) = intHost $(hashQ ("Scanl1" :: String))
  encodeOperation (PTXScan1 RightToLeft) = intHost $(hashQ ("Scanr1" :: String))
  encodeOperation (PTXScan' LeftToRight) = intHost $(hashQ ("Scanl'" :: String))
  encodeOperation (PTXScan' RightToLeft) = intHost $(hashQ ("Scanr'" :: String))
  encodeOperation PTXFold        = intHost $(hashQ ("Fold" :: String))
  encodeOperation PTXFold1       = intHost $(hashQ ("Fold1" :: String))-}

instance SetOpIndices PTXOp where
  setOpIndices _ PTXGenerate _ idxArgs = Just $ Right idxArgs -- Generate has no In arrays
  {-setOpIndices _ PTXMap _ (_ :>: _ :>: IdxArgIdx d i :>: ArgsNil)
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
        | otherwise = Nothing-}

  {- getOpLoopDirections (PTXScan dir) _ (_ :>: _ :>: IdxArgIdx _ i :>: _)
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
    | _ `TupRpair` TupRsingle var <- i = [(varIdx var, LoopMonotone)] -}
  getOpLoopDirections _ _ _ = []

                -- vvvv old vvv
                  -- 0 means maximal parallelism; each thread only gets 1 element, e.g. output of the first stage of 1-dimensional fold
                  -- 1 is segmented along the innermost dimension into nthreads equal parts, e.g. input of the first stage of 1-dimensional fold
                  -- 2 is one row for each thread
                  -- 3 is segmented along the second dimension, e.g. input of a fused folddim followed by first stage of 1-dimensional fold
                  -- 4 is 2 dimensions per thread, etc
                  -- note that this is about _logical_ threads; if there are less physical ones present then they will perform work stealing, so this is really the (minimum) size of each bucket in the work stealing queue
                -- ^^^^ old ^^^
data PTXILPVar = Dims InOut Label
                  -- | DepthPerThread InOut Label
  deriving (Eq, Ord, Show)
pattern InDims, OutDims {- InDepth, OutDepth -}:: Label -> Graph.Var PTXOp
pattern InDims   l = BackendSpecific (Dims            InArr l)
pattern OutDims  l = BackendSpecific (Dims           OutArr l)
-- pattern InDepth  l = BackendSpecific (DepthPerThread  InArr l)
-- pattern OutDepth l = BackendSpecific (DepthPerThread OutArr l)

-- TODO: factor out more common parts of mkGraph
-- TODO: do the TODO's in here, and also do them in the Interpreter\
-- TODO: constraints and bounds for the new variable(s)
instance MakesILP PTXOp where
  type BackendVar PTXOp = PTXILPVar
  type BackendArg PTXOp = Int -- direction: used to separate clusters later, preventing accidental horizontal fusion of backpermutes
  defaultBA = 0
  data BackendClusterArg PTXOp a = BCAN

  {- mkGraph PTXBackpermute (_ :>: L (ArgArray In (ArrayR _shrI _) _ _) (_, lIns) :>: L (ArgArray Out (ArrayR shrO _) _ _) _ :>: ArgsNil) l@(Label i _) =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> ILP.c (InFoldSize l) .==. ILP.c (OutFoldSize l)
        <> ILP.c (InDir l) .==. int i
        <> ILP.c (InDims l) .==. ILP.c (OutDims l)
        <> inrankifmanifest shrO l
          -- .+. timesN (int 3 .+. c (OutDir l)) 
          -- When we switch to gather, like in the paper, we need to add this term.
          -- 4 + dir is always positive, and this is exactly why we (elsewhere) define `n` as `5+(size nodes)`
          -- problem: this clashes with the assumption in 'inputConstraints' and 'finalise' that orders are at most n,
          -- so if we want this we need to change inputConstraints and finalise
        )-- <> c (InDims l) .+. int (rank shrO) .==. c (OutDims l) .+. int (rank shrI))
      (defaultBounds l) -}
  mkGraph PTXGenerate (_ :>: L (ArgArray Out (ArrayR shr _) _ _) _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (outrankifmanifest shr l)
      (defaultBounds l)
  {- mkGraph PTXMap (_ :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> ILP.c (InFoldSize l) .==. ILP.c (OutFoldSize l)
        <> ILP.c (InDir  l) .==. ILP.c (OutDir  l)
        <> ILP.c (InDims l) .==. ILP.c (OutDims l)
        <> inrankifmanifest shr l)
      (defaultBounds l)
  mkGraph PTXPermute (_ :>: L _ (_, lTargets) :>: L _ (_, lLocks) :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: ArgsNil) l =
    Graph.Info
      ( mempty & infusibleEdges .~ Set.map (-?> l) (lTargets <> lLocks)) -- add infusible edges from the producers of target and lock arrays to the permute
      (    inputConstraints l lIns
        <> ILP.c (InFoldSize l) .==. ILP.c (OutFoldSize l)
        <> ILP.c (InDims l) .==. int (rank shr)
        <> ILP.c (InDir  l) .==. int (-2)
        <> ILP.c (OutDir l) .==. int (-3)) -- Permute cannot fuse with its consumer
      ( lower (-2) (InDir l)
      <> upper (InDir l) (-1) ) -- default lowerbound for the input, but not for the output (as we set it to -3). 
  mkGraph PTXPermute' (L _ (_, lTargets) :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: ArgsNil) l =
    Graph.Info
      ( mempty & infusibleEdges .~ Set.map (-?> l) lTargets) -- add infusible edges from the producers of target array to the permute
      (    inputConstraints l lIns
        <> ILP.c (InFoldSize l) .==. ILP.c (OutFoldSize l)
        <> ILP.c (InDims l) .==. int (rank shr)
        <> ILP.c (InDir  l) .==. int (-2)
        <> ILP.c (OutDir l) .==. int (-3)) -- Permute cannot fuse with its consumer
      ( lower (-2) (InDir l)
      <> upper (InDir l) (-1) ) -- default lowerbound for the input, but not for the output (as we set it to -3). 
  mkGraph (PTXScan dir) (_ :>: _ :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: L _ (_, lOut) :>: ArgsNil) l =
    Graph.Info
      -- Scan cannot fuse with its consumer, as the output is one larger than the input
      mempty
      (    inputConstraints l lIns
        <> ILP.c (InFoldSize l) .==. ILP.c (OutFoldSize l)
        <> ILP.c (InDir  l) .==. int dir'
        <> ILP.c (OutDir l) .==. int (-3)
        <> ILP.c (InDims l) .==. ILP.c (OutDims l)
        <> ILP.c (InDims l) .==. int (rank shr))
      ( lower (-2) (InDir l) <> lower (-3) (OutDir l) <> lower 0 (InDims l) <> lower 0 (OutDims l) )
    where
      dir' = case dir of
        LeftToRight -> -2
        RightToLeft -> -1
  mkGraph (PTXScan1 dir) (_ :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> ILP.c (InFoldSize l) .==. ILP.c (OutFoldSize l)
        <> ILP.c (InDir  l) .==. int dir'
        <> ILP.c (OutDir l) .==. int dir'
        <> ILP.c (InDims l) .==. ILP.c (OutDims l)
        <> ILP.c (InDims l) .==. int (rank shr))
      (defaultBounds l)
    where
      dir' = case dir of
        LeftToRight -> -2
        RightToLeft -> -1
  mkGraph (PTXScan' dir) (_ :>: _ :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: _ :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> ILP.c (InFoldSize l) .==. ILP.c (OutFoldSize l)
        <> ILP.c (InDir  l) .==. int dir'
        -- TODO: Does this give a problem for the second output of scan' (the reduced values)?
        -- That array is one dimension lower.
        <> ILP.c (OutDir l) .==. int dir'
        <> ILP.c (InDims l) .==. ILP.c (OutDims l)
        <> ILP.c (InDims l) .==. int (rank shr))
      (defaultBounds l)
    where
      dir' = case dir of
        LeftToRight -> -2
        RightToLeft -> -1
  mkGraph PTXFold (_ :>: _ :>: L (ArgArray In (ArrayR (ShapeRsnoc shr) _) _ _) (_, lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> ILP.c (InFoldSize l) .==. int (_labelId l)
        <> ILP.c (InDir  l) .==. ILP.c (OutDir l)
        <> ILP.c (InDims l) .==. int 1 .+. ILP.c (OutDims l)
        -- <> foldMap (\lin -> fused lin l .==. int 1) lIns
        <> inrankifmanifest (ShapeRsnoc shr) l)
      (defaultBounds l)
  mkGraph PTXFold1 (_ :>: L (ArgArray In (ArrayR (ShapeRsnoc shr) _) _ _) (_, lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> ILP.c (InFoldSize l) .==. int (_labelId l)
        <> ILP.c (InDir  l) .==. ILP.c (OutDir l)
        <> ILP.c (InDims l) .==. int 1 .+. ILP.c (OutDims l)
        -- <> foldMap (\lin -> fused lin l .==. int 1) lIns
        <> inrankifmanifest (ShapeRsnoc shr) l)
      (defaultBounds l) -}

  labelLabelledArg :: M.Map (Graph.Var PTXOp) Int -> Label -> LabelledArg env a -> LabelledArgOp PTXOp env a
  labelLabelledArg vars l (L x@(ArgArray In  _ _ _) y) = LOp x y (vars M.! InDir  l)
  labelLabelledArg vars l (L x@(ArgArray Out _ _ _) y) = LOp x y (vars M.! OutDir l)
  labelLabelledArg _ _ (L x y) = LOp x y 0

  getClusterArg :: LabelledArgOp PTXOp env a -> BackendClusterArg PTXOp a
  getClusterArg (LOp _ _ _) = BCAN
  -- For each label: If the output is manifest, then its direction is negative (i.e. not in a backpermuted order)
  finalize = foldMap $ \l -> timesN (manifest l) .>. ILP.c (OutDir l)

  encodeBackendClusterArg (BCAN) = intHost $(hashQ ("BCAN" :: String))

inputConstraints :: Label -> Labels -> Constraint PTXOp
inputConstraints l = foldMap $ \lIn -> 
                timesN (fused lIn l) .>=. ILP.c (InDims l) .-. ILP.c (OutDims lIn)
    <> (-1) .*. timesN (fused lIn l) .<=. ILP.c (InDims l) .-. ILP.c (OutDims lIn)
    <>          timesN (fused lIn l) .>=. ILP.c (InFoldSize l) .-. ILP.c (OutFoldSize lIn)
    <> (-1) .*. timesN (fused lIn l) .<=. ILP.c (InFoldSize l) .-. ILP.c (OutFoldSize lIn)

inrankifmanifest :: ShapeR sh -> Label -> Constraint PTXOp
inrankifmanifest shr l = ILP.int (rank shr) .+. timesN (manifest l) .>=. ILP.c (InDims l)
                      <> ILP.int (rank shr) .-. timesN (manifest l) .<=. ILP.c (InDims l)

outrankifmanifest :: ShapeR sh -> Label -> Constraint PTXOp
outrankifmanifest shr l = ILP.int (rank shr) .+. timesN (manifest l) .>=. ILP.c (OutDims l)
                       <> ILP.int (rank shr) .-. timesN (manifest l) .<=. ILP.c (OutDims l)

defaultBounds :: Label -> Bounds PTXOp
defaultBounds l = lower (-2) (InDir l) <> lower (-2) (OutDir l) <> lower 0 (InDims l) <> lower 0 (OutDims l)

instance NFData' (BackendClusterArg PTXOp) where
  rnf' !_ = ()

instance ShrinkArg (BackendClusterArg PTXOp) where
  shrinkArg _ BCAN = BCAN
  deadArg BCAN = BCAN

shrToTypeR :: ShapeR sh -> TypeR sh
shrToTypeR ShapeRz = TupRunit
shrToTypeR (ShapeRsnoc shr) = TupRpair (shrToTypeR shr) (TupRsingle scalarType)
