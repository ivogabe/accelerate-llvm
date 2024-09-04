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

module Data.Array.Accelerate.LLVM.Native.Operation
  where

-- accelerate

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.Analysis.Hash.Operation
import Data.Array.Accelerate.Backend
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import Data.Array.Accelerate.Eval


import qualified Data.Set as Set
import Data.Array.Accelerate.AST.Environment (weakenId, weakenEmpty, weakenSucc' )
import Data.Array.Accelerate.Representation.Array (ArrayR(..))
import Data.Array.Accelerate.Trafo.Var (DeclareVars(..), declareVars)
import Data.Array.Accelerate.Representation.Ground (buffersR)
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Trafo.Operation.Substitution (aletUnique, alet, weaken, LHS (..), mkLHS)
import Data.Array.Accelerate.Representation.Shape (ShapeR (..), shapeType, rank)
import Data.Array.Accelerate.Representation.Type (TypeR, TupR (..))
import Data.Array.Accelerate.Type (scalarType, Word8, scalarTypeWord8, scalarTypeInt)
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
import Prettyprinter (pretty)
import Unsafe.Coerce (unsafeCoerce)

data NativeOp t where
  NMap         :: NativeOp (Fun' (s -> t)    -> In sh s -> Out sh  t -> ())
  NBackpermute :: NativeOp (Fun' (sh' -> sh) -> In sh t -> Out sh' t -> ())
  NGenerate    :: NativeOp (Fun' (sh -> t)              -> Out sh  t -> ())
  NPermute     :: NativeOp (Fun' (e -> e -> e)
                            -> Mut sh' e
                            -> Mut sh' Word8
                            -> Fun' (sh -> PrimMaybe sh')
                            -> In sh e
                            -> ())
  -- this one covers ScanDim, ScanP1 and ScanP2. Only ScanP1's second output argument will be used for the partial reductions,
  -- the others will simply get SLV'd away.
  NScanl1      :: NativeOp (Fun' (e -> e -> e) 
                         -> In (sh, Int) e 
                         -> Out (sh, Int) e -- the local scan result
                        --  -> Out (sh, Int) e -- the local fold result
                         -> ()) -- TODO: huh? Where would we make the two outputs differ? at evalOp they are the same, and i'm not sure writeOutput has a say in the matter
  NFold1       :: NativeOp (Fun' (e -> e -> e) -- segmented, TODO: how to represent the output being 'one per thread on each row'?
                         -> In  ((), Int) e
                         -> Out ((), Int) e
                         -> ())
  NFold2       :: NativeOp (Fun' (e -> e -> e) -- sequential
                         -> In (sh, Int) e
                         -> Out sh e
                         -> ())

instance PrettyOp NativeOp where
  prettyOp NMap         = "map"
  prettyOp NBackpermute = "backpermute"
  prettyOp NGenerate    = "generate"
  prettyOp NPermute     = "permute"
  prettyOp NScanl1      = "scanl1"
  prettyOp NFold1       = "fold-1"
  prettyOp NFold2       = "fold-2"

instance NFData' NativeOp where
  rnf' !_ = ()

instance DesugarAcc NativeOp where
  mkMap         a b c   = Exec NMap         (a :>: b :>: c :>:       ArgsNil)
  mkBackpermute a b c   = Exec NBackpermute (a :>: b :>: c :>:       ArgsNil)
  mkGenerate    a b     = Exec NGenerate    (a :>: b :>:             ArgsNil)
  mkScan LeftToRight f Nothing i@(ArgArray In (ArrayR shr ty) sh buf) o
    -- If multidimensional, simply NScanl1.
    -- TODO: just always doing nscanl1 now
    -- | ShapeRsnoc (ShapeRsnoc _) <- shr
    = Exec NScanl1 (f :>: i :>: o :>: ArgsNil)
    -- | otherwise -- Otherwise, NScanl1 followed by NScanl1 on the reductions, followed by a replicate on that result and then zipWith the first result.
    -- just using nscanl1 for one dimensional for now
    -- = error "todo"
  -- right to left is conceptually easy once we already have order variables for backpermute. 
  -- Exclusive scans (changing array size) are weirder, require an extra 'cons' primitive
  mkScan _ _ _ _ _ = error "todo" 
  mkPermute     a b@(ArgArray _ (ArrayR shr _) sh _) c d
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
            :>: weaken w d 
            :>: ArgsNil))
  -- -- we desugar a Fold with seed element into a Fold1 followed by a map which prepends the seed
  -- -- copied verbatim from Interpreter; this should probably be in the shared implementation except for the part where it doesn't work on 0-size arrays
  -- -- Will need to figure out how to solve that before we ship it, as long as we keep the conditional out of the loop. 
  -- -- Potentially generating multiple versions, as we do currently? With the new fusion, that might result in an exponential amount of variations in the number of folds per cluster...
  -- -- TODO
  mkFold a@(ArgFun f) (Just (ArgExp seed)) b@(ArgArray In (ArrayR _ tp) _ _) c@(ArgArray _ arr' sh' _)
    | DeclareVars lhsTemp wTemp kTemp <- declareVars $ buffersR tp =
      aletUnique lhsTemp (desugarAlloc arr' $ fromGrounds sh') $
        alet LeftHandSideUnit
          (mkFold (weaken wTemp a) Nothing (weaken wTemp b) (ArgArray Out arr' (weakenVars wTemp sh') (kTemp weakenId))) $
          case mkLHS tp of
            LHS lhs vars ->
              mkMap
                (ArgFun $ 
                  Lam lhs $ Body $ (\f' -> apply2 tp f' (weakenThroughReindex wTemp reindexExp $ 
                    weakenE weakenEmpty seed) (expVars vars)) $ weakenThroughReindex wTemp reindexExp f)
                (ArgArray In arr' (weakenVars wTemp sh') (kTemp weakenId))
                (weaken wTemp c)
  -- mkFold (a :: Arg env (Fun' (e -> e -> e))) Nothing b@(ArgArray In arr@(ArrayR shr tp) _ _) c
  --   | DeclareVars lhsSize (wSize :: env :> env') kSize <- declareVars . typeRtoGroundsR $ TupRsingle scalarTypeInt
  --   , DeclareVars lhsTemp (wTemp :: env' :> env'') kTemp <- declareVars $ buffersR tp =
  --     let w = wTemp .> wSize in
  --     case shr of
  --       ShapeRsnoc ShapeRz -> aletUnique lhsSize (Compute $ Const scalarTypeInt 2) $ -- magic constant 2; TODO change into `size/workstealsize` rounded up
  --         let sh = TupRpair TupRunit (kSize weakenId) in
  --         aletUnique lhsTemp (desugarAlloc (ArrayR shr tp) $ fromGrounds sh) $ 
  --           let tmpArrArg :: Modifier m -> Arg env'' (m ((),Int) e)
  --               tmpArrArg m = ArgArray m arr (weakenVars wTemp sh) (kTemp weakenId)
  --           in alet LeftHandSideUnit
  --             (Exec NFold1 $ weaken w a :>: weaken w b :>: tmpArrArg Out :>: ArgsNil)
  --             (Exec NFold2 $ weaken w a :>: tmpArrArg In :>: weaken w c :>: ArgsNil)
  --       _ -> -- single-kernel multidim reduction
  --         Exec NFold2 $ a :>: b :>: c :>: ArgsNil
  mkFold a Nothing b c = Exec NFold2 (a :>: b :>: c :>: ArgsNil)

instance SimplifyOperation NativeOp where
  detectCopy _          NMap         = detectMapCopies
  detectCopy matchVars' NBackpermute = detectBackpermuteCopies matchVars'
  detectCopy _ _                     = const []

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
  encodeOperation NScanl1      = intHost $(hashQ ("Scanl1" :: String))
  encodeOperation NFold1       = intHost $(hashQ ("Fold-1" :: String))
  encodeOperation NFold2       = intHost $(hashQ ("Fold-2" :: String))

                -- vvvv old vvv
                  -- 0 means maximal parallelism; each thread only gets 1 element, e.g. output of the first stage of 1-dimensional fold
                  -- 1 is segmented along the innermost dimension into nthreads equal parts, e.g. input of the first stage of 1-dimensional fold
                  -- 2 is one row for each thread
                  -- 3 is segmented along the second dimension, e.g. input of a fused folddim followed by first stage of 1-dimensional fold
                  -- 4 is 2 dimensions per thread, etc
                  -- note that this is about _logical_ threads; if there are less physical ones present then they will perform work stealing, so this is really the (minimum) size of each bucket in the work stealing queue
                -- ^^^^ old ^^^
data NativeILPVar = Dims InOut Label
                  -- | DepthPerThread InOut Label
  deriving (Eq, Ord, Show)
pattern InDims, OutDims {- InDepth, OutDepth -}:: Label -> Graph.Var NativeOp
pattern InDims   l = BackendSpecific (Dims            InArr l)
pattern OutDims  l = BackendSpecific (Dims           OutArr l)
-- pattern InDepth  l = BackendSpecific (DepthPerThread  InArr l)
-- pattern OutDepth l = BackendSpecific (DepthPerThread OutArr l)

-- TODO: factor out more common parts of mkGraph
-- TODO: do the TODO's in here, and also do them in the Interpreter\
-- TODO: constraints and bounds for the new variable(s)
instance MakesILP NativeOp where
  type BackendVar NativeOp = NativeILPVar
  type BackendArg NativeOp = (Int, IterationDepth) -- direction, depth
  defaultBA = (0,0)
  data BackendClusterArg NativeOp a = BCAN IterationDepth

  mkGraph NBackpermute (_ :>: L (ArgArray In (ArrayR _shrI _) _ _) (_, lIns) :>: L (ArgArray Out (ArrayR shrO _) _ _) _ :>: ArgsNil) l@(Label i _) =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> ILP.c (InDir l) .==. int i
        <> ILP.c (InDims l) .==. ILP.c (OutDims l)
        <> inrankifmanifest shrO l
          -- .+. timesN (int 3 .+. c (OutDir l)) 
          -- When we switch to gather, like in the paper, we need to add this term.
          -- 4 + dir is always positive, and this is exactly why we (elsewhere) define `n` as `5+(size nodes)`
          -- problem: this clashes with the assumption in 'inputConstraints' and 'finalise' that orders are at most n,
          -- so if we want this we need to change inputConstraints and finalise
        )-- <> c (InDims l) .+. int (rank shrO) .==. c (OutDims l) .+. int (rank shrI))
      (defaultBounds l)
  mkGraph NGenerate (_ :>: L (ArgArray Out (ArrayR shr _) _ _) _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (outrankifmanifest shr l)
      (defaultBounds l)
  mkGraph NMap (_ :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> ILP.c (InDir  l) .==. ILP.c (OutDir  l)
        <> ILP.c (InDims l) .==. ILP.c (OutDims l)
        <> inrankifmanifest shr l)
      (defaultBounds l)
  mkGraph NPermute (_ :>: L _ (_, lTargets) :>: L _ (_, lLocks) :>: _ :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: ArgsNil) l =
    Graph.Info
      ( mempty & infusibleEdges .~ Set.map (-?> l) (lTargets <> lLocks)) -- add infusible edges from the producers of target and lock arrays to the permute
      (    inputConstraints l lIns
        <> ILP.c (InDims l) .==. int (rank shr)
        <> ILP.c (InDir  l) .==. int (-2)
        <> ILP.c (OutDir l) .==. int (-3)) -- Permute cannot fuse with its consumer
      ( lower (-2) (InDir l)
      <> upper (InDir l) (-1) ) -- default lowerbound for the input, but not for the output (as we set it to -3). 
  mkGraph NScanl1 (_ :>: L (ArgArray In (ArrayR shr _) _ _) (_, lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> ILP.c (InDir  l) .==. int (-2)
        <> ILP.c (OutDir l) .==. int (-2)
        <> ILP.c (InDims l) .==. ILP.c (OutDims l)
        <> ILP.c (InDims l) .==. int (rank shr))
      (defaultBounds l)
  mkGraph NFold1 (_ :>: L _ (_, lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> ILP.c (InDir   l) .==. ILP.c (OutDir l)
        -- <> ILP.c (InDims  l) .==. int 1 -- TODO redesign fold1
        -- <> ILP.c (OutDims l) .==. int 0
        )
      (defaultBounds l)
  mkGraph NFold2 (_ :>: L (ArgArray In (ArrayR (ShapeRsnoc shr) _) _ _) (_, lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> ILP.c (InDir  l) .==. ILP.c (OutDir l)
        <> ILP.c (InDims l) .==. int 1 .+. ILP.c (OutDims l)
        -- <> foldMap (\lin -> fused lin l .==. int 1) lIns
        <> inrankifmanifest (ShapeRsnoc shr) l)
      (defaultBounds l)

  labelLabelledArg :: M.Map (Graph.Var NativeOp) Int -> Label -> LabelledArg env a -> LabelledArgOp NativeOp env a
  labelLabelledArg vars l (L x@(ArgArray In  _ _ _) y) = LOp x y (vars M.! InDir  l, vars M.!  InDims l)
  labelLabelledArg vars l (L x@(ArgArray Out _ _ _) y) = LOp x y (vars M.! OutDir l, vars M.! OutDims l)
  labelLabelledArg _ _ (L x y) = LOp x y (0,0)
  getClusterArg :: LabelledArgOp NativeOp env a -> BackendClusterArg NativeOp a
  getClusterArg (LOp _ _ (_, d)) = BCAN d
  -- For each label: If the output is manifest, then its direction is negative (i.e. not in a backpermuted order)
  finalize = foldMap $ \l -> timesN (manifest l) .>. ILP.c (OutDir l)

  encodeBackendClusterArg (BCAN i) = intHost $(hashQ ("BCAN" :: String)) <> intHost i

inputConstraints :: Label -> Labels -> Constraint NativeOp
inputConstraints l = foldMap $ \lIn -> 
                timesN (fused lIn l) .>=. ILP.c (InDims l) .-. ILP.c (OutDims lIn)
    <> (-1) .*. timesN (fused lIn l) .<=. ILP.c (InDims l) .-. ILP.c (OutDims lIn)

inrankifmanifest :: ShapeR sh -> Label -> Constraint NativeOp
inrankifmanifest shr l = ILP.int (rank shr) .+. timesN (manifest l) .>=. ILP.c (InDims l)
                      <> ILP.int (rank shr) .-. timesN (manifest l) .<=. ILP.c (InDims l)

outrankifmanifest :: ShapeR sh -> Label -> Constraint NativeOp
outrankifmanifest shr l = ILP.int (rank shr) .+. timesN (manifest l) .>=. ILP.c (OutDims l)
                       <> ILP.int (rank shr) .-. timesN (manifest l) .<=. ILP.c (OutDims l)
        
        

defaultBounds :: Label -> Bounds NativeOp
defaultBounds l = lower (-2) (InDir l) <> lower (-2) (OutDir l) <> lower 0 (InDims l) <> lower 0 (OutDims l)


instance NFData' (BackendClusterArg NativeOp) where
  rnf' !_ = ()

instance ShrinkArg (BackendClusterArg NativeOp) where
  shrinkArg _ (BCAN i) = BCAN i
  deadArg (BCAN i) = BCAN i

data IndexPermutation env where
  BP :: ShapeR sh1 -> ShapeR sh2 -> Fun env (sh1 -> sh2) -> GroundVars env sh1 -> IndexPermutation env
type IterationDepth = Int
instance Show (BackendClusterArg2 NativeOp env arg) where
  show (BCAN2 i d) = "{ depth = " <> show d <> ", perm = " <> show i <> " }"
  show IsUnit = "()"
instance Show (IndexPermutation env) where
  show (BP sh1 sh2 f _) = show (rank sh1) <> "->" <> show (rank sh2) <> ": " <> show (prettyFun (infenv 0) f)
    where
      infenv i = unsafeCoerce $ infenv (i+1) `Push` (pretty $ "x"<>show i)
instance StaticClusterAnalysis NativeOp where
  data BackendClusterArg2 NativeOp env arg where
    BCAN2 :: Maybe (IndexPermutation env) -> IterationDepth -> BackendClusterArg2 NativeOp env arg -- non-array args just get ths one with '999', should make a new constructor for them
    IsUnit ::BackendClusterArg2 NativeOp env (m sh ()) -- units don't get backpermuted because they don't exist
  def (ArgArray _ (ArrayR _ TupRunit) _ TupRunit) _ _ = IsUnit
  def _ _ (BCAN i) = BCAN2 Nothing i
  unitToVar    = bcan2id
  varToUnit    = bcan2id
  valueToIn    = bcan2id
  valueToOut   = bcan2id
  inToValue    = bcan2id
  outToValue   = bcan2id
  outToSh      = bcan2id
  shToOut      = bcan2id
  shToValue    = bcan2id
  varToValue   = bcan2id
  varToSh      = bcan2id
  shToVar      = bcan2id
  shrinkOrGrow _ (ArgArray _ (ArrayR _ TupRunit) _ _) _ = IsUnit
  shrinkOrGrow _ a IsUnit = error "can't grow from unit"
  shrinkOrGrow _ _ x = bcan2id x
  addTup       = bcan2id
  inToVar = bcan2id
  -- onOp propagates the backpermute information from the outputs to the inputs of each operation
  onOp NMap (bp :>: ArgsNil) _ _ = BCAN2 Nothing undefined :>: bcan2id bp :>: bp :>: ArgsNil
  onOp NBackpermute (BCAN2 (Just bp@(BP shr1 shr2 g sh)) d :>: ArgsNil) (ArgFun f :>: ArgArray In (ArrayR shrI _) _ _ :>: ArgArray Out (ArrayR shrO _) _ _ :>: ArgsNil) _
    | Just Refl <- matchShapeR shrO shr2  = BCAN2 Nothing 999 :>: BCAN2 (Just (BP shr1 shrI (compose f g) sh)) d :>: BCAN2 (Just bp) d :>: ArgsNil
    | otherwise = error "BP shapeR doesn't match backpermute output shape"
  onOp NBackpermute (BCAN2 Nothing d           :>: ArgsNil) (ArgFun f :>: ArgArray In (ArrayR shrI _) _ _ :>: ArgArray Out (ArrayR shrO _) sh _ :>: ArgsNil) _
                                          = BCAN2 Nothing d :>: BCAN2 (Just (BP shrO shrI f sh)) d             :>: BCAN2 Nothing d           :>: ArgsNil    
  onOp NGenerate (bp :>: ArgsNil) (_:>:ArgArray Out (ArrayR shR _) _ _ :>:ArgsNil) _ = 
    bcan2id bp :>: bp :>: ArgsNil -- store the bp in the function, because there is no input array
  onOp NPermute ArgsNil (_:>:_:>:_:>:_:>:ArgArray In (ArrayR shR _) _ _ :>:ArgsNil) _ = 
    BCAN2 Nothing 999 :>: BCAN2 Nothing 999 :>: BCAN2 Nothing 999 :>: BCAN2 Nothing 999 :>: BCAN2 Nothing (rank shR) :>: ArgsNil
  onOp NFold2  (bp :>: ArgsNil) (_ :>: ArgArray In _ fs _ :>: _ :>: ArgsNil) _ = BCAN2 Nothing 999 :>: fold2bp bp (case fs of TupRpair _ x -> x) :>: bp :>: ArgsNil
  onOp NFold1  (bp :>: ArgsNil) _ _ = BCAN2 Nothing 999 :>: fold1bp bp :>: bp :>: ArgsNil
  onOp NScanl1 (bp :>: ArgsNil) _ _ = BCAN2 Nothing 999 :>: bcan2id bp :>: bp :>: ArgsNil
  pairinfo _ IsUnit IsUnit = error "can't yet"
  pairinfo a@(ArgArray m (ArrayR shr (TupRpair l r)) sh (TupRpair bufl bufr)) IsUnit x = shrinkOrGrow (ArgArray m (ArrayR shr r) sh bufr) a x
  pairinfo a@(ArgArray m (ArrayR shr (TupRpair l r)) sh (TupRpair bufl bufr)) x IsUnit = shrinkOrGrow (ArgArray m (ArrayR shr l) sh bufl) a x
  pairinfo _ x y = if bcan2id x == y then bcan2id x else 
    case (x,y) of
      -- these two cases test whether the function is id, but it's still possible that one of the arguments got backpermuted to be smaller.
      -- In that case we 'should' error here, but we can't check it
      (BCAN2 Nothing xd, BCAN2 (Just (BP _ _ yp _)) yd)
        | xd == yd
        , Just Refl <- isIdentity yp
        -> bcan2id y
      (BCAN2 (Just (BP _ _ yp _)) yd, BCAN2 Nothing xd)
        | xd == yd
        , Just Refl <- isIdentity yp
        -> bcan2id x
      _ -> error $ "pairing unequal: " <> show x <> ", " <> show y
  


bcan2id :: BackendClusterArg2 NativeOp env arg -> BackendClusterArg2 NativeOp env arg'
bcan2id (BCAN2 Nothing i) = BCAN2 Nothing i
bcan2id (BCAN2 (Just (BP a b c d)) i) = BCAN2 (Just (BP a b c d)) i
bcan2id IsUnit = unsafeCoerce IsUnit -- error "bcan2id unit"

fold1bp :: BackendClusterArg2 NativeOp env (Out sh e) -> BackendClusterArg2 NativeOp env (In sh e)
fold1bp (BCAN2 Nothing i) = BCAN2 Nothing i
fold1bp (BCAN2 (Just (BP shr1 shr2 g sh)) i) = flip BCAN2 i $ Just $ BP shr1 shr2 (error "todo: multiply the innermost (outer constructor) dimension by the workstealsize" g) undefined
fold1bp IsUnit = error "unit"

fold2bp :: BackendClusterArg2 NativeOp env (Out sh e) -> GroundVars env Int -> BackendClusterArg2 NativeOp env (In (sh,Int) e)
fold2bp (BCAN2 Nothing i) _ = BCAN2 Nothing (i+1)
fold2bp (BCAN2 (Just (BP shr1 shr2 g sh)) i) foldsize = flip BCAN2 (i+1) $ Just $ 
  BP 
    (ShapeRsnoc shr1) 
    (ShapeRsnoc shr2) 
    (case g of
      Lam lhs (Body e) -> Lam (LeftHandSidePair lhs $ LeftHandSideSingle scalarTypeInt) $ 
                            Body $ Pair (weakenE (weakenSucc' weakenId) e) (Evar $ Var scalarTypeInt ZeroIdx)
      _ -> error "function type in body or non-body below lam in sh1 -> sh2")
    (TupRpair sh foldsize)
fold2bp IsUnit _ = error "unit"

instance Eq (BackendClusterArg2 NativeOp env arg) where
  IsUnit == IsUnit = True
  x@(BCAN2 p i) == y@(BCAN2 p' i') = p == p' && i == i'
  _ == _ = False

instance Eq (IndexPermutation env) where
  (BP shr1 shr2 f _) == (BP shr1' shr2' f' _)
    | Just Refl <- matchShapeR shr1 shr1'
    , Just Refl <- matchShapeR shr2 shr2'
    = isJust $ matchOpenFun f f'
  _ == _ = False


shrToTypeR :: ShapeR sh -> TypeR sh
shrToTypeR ShapeRz = TupRunit
shrToTypeR (ShapeRsnoc shr) = TupRpair (shrToTypeR shr) (TupRsingle scalarType)
