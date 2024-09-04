{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen
-- (
--   codegen
--   )
  where

-- accelerate
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (shapeType, ShapeR(..), rank)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Partitioned as P hiding (combine)
import Data.Array.Accelerate.Eval
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.CodeGen.Environment hiding ( Empty )
import Data.Array.Accelerate.LLVM.Native.Operation
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.Target
import Data.Typeable

import LLVM.AST.Type.Module
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified LLVM.AST.Type.Function as LLVM
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.LLVM.CodeGen.Sugar (app1, IROpenFun2 (app2))
import Data.Array.Accelerate.LLVM.CodeGen.Exp (llvmOfFun1, intOfIndex, llvmOfFun2)
import Data.Array.Accelerate.Trafo.Desugar (ArrayDescriptor(..))
import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic ( when, ifThenElse, eq, fromJust, isJust, liftInt )
import Data.Array.Accelerate.Analysis.Match (matchShapeR)
import Data.Array.Accelerate.Trafo.Exp.Substitution (compose)
import Data.Array.Accelerate.LLVM.Native.CodeGen.Permute (atomically)
import Control.Monad.State (StateT(..), lift, execStateT)
import qualified Data.Map as M
import Data.ByteString.Short ( ShortByteString )
import Data.Array.Accelerate.AST.LeftHandSide (Exists (Exists), lhsToTupR)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Label)
import Data.Array.Accelerate.LLVM.CodeGen.Constant (constant)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP(..))
import Data.Coerce (coerce)
import Data.Functor.Compose
import qualified Control.Monad as Prelude
import Data.Bifunctor (Bifunctor(..))
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.IR

traceIfDebugging :: String -> a -> a
traceIfDebugging _ a = a --Debug.Trace.trace str a

codegen :: ShortByteString
        -> Env AccessGroundR env
        -> Clustered NativeOp args
        -> Args env args
        -> LLVM Native (Module (KernelType env))
codegen name env (Clustered c b) args =
  codeGenFunction name (LLVM.Lam argTp "arg") $ do
    extractEnv
    let b' = mapArgs BCAJA b
    (acc, loopsize) <- execStateT (evalCluster (toOnlyAcc c) b' args gamma ()) (mempty, LS ShapeRz OP_Unit)
    _acc' <- operandsMapToPairs acc $ \(accTypeR, toOp, fromOp) -> fmap fromOp $ flip execStateT (toOp acc) $ case loopsize of
      LS loopshr loopsh -> 
        workstealChunked loopshr workstealIndex workstealActiveThreads (flipShape loopshr loopsh) accTypeR
          (body loopshr toOp fromOp, -- the LoopWork
          StateT $ \op -> second toOp <$> runStateT (foo (liftInt 0) []) (fromOp op)) -- the action to run after the outer loop
    -- acc'' <- flip execStateT acc' $ foo (liftInt 0) []
    pure ()
    where
      ba = makeBackendArg @NativeOp args gamma c b
      (argTp, extractEnv, workstealIndex, workstealActiveThreads, gamma) = bindHeaderEnv env
      body :: ShapeR sh -> (Accumulated -> a) -> (a -> Accumulated) -> LoopWork sh (StateT a (CodeGen Native))
      body ShapeRz _ _ = LoopWorkZ
      body (ShapeRsnoc shr) toOp fromOp = LoopWorkSnoc (body shr toOp fromOp) (\i is -> StateT $ \op -> second toOp <$> runStateT (foo i is) (fromOp op))
      foo :: Operands Int -> [Operands Int] -> StateT Accumulated (CodeGen Native) ()
      foo linix ixs = do
        let d = length ixs -- TODO check: this or its inverse (i.e. totalDepth - length ixs)?
        let i = (d, linix, ixs)
        newInputs <- readInputs @_ @_ @NativeOp i args ba gamma
        outputs <- evalOps @NativeOp i c newInputs args gamma
        writeOutputs @_ @_ @NativeOp i args outputs gamma



-- We use some unsafe coerces in the context of the accumulators. 
-- Some, in this function, are very local. Others, like in evalOp, 
-- just deal with the assumption that the specific operand stored at index l indeed belongs to operation l.
operandsMapToPairs
  :: Accumulated
  -> (forall accR. ( TypeR accR
     , Accumulated -> Operands accR
     , Operands accR -> Accumulated) -> r)
  -> r
operandsMapToPairs acc k
  = case existentialStuff of
    (Exists accR, toR, fromR) -> k ( accR
                                   , unsafeUnExists . toR . map (fst.snd) . M.toList
                                   , M.fromList . zip labels . fromR . Exists)
  where
  (labels, (_, existentialStuff)) = second (second (foldr
      (\(Exists newR) (Exists accR, toR, fromR) ->
        ( Exists (TupRpair newR accR)
        , \(Exists this : rest') -> case toR rest' of Exists rest -> Exists $ OP_Pair this rest
        , \(Exists hastobepair) -> case unsafeCoerce hastobepair of OP_Pair this rest -> (Exists this, Exists newR) : fromR (Exists rest)))
      (   Exists TupRunit
        , \[] -> Exists OP_Unit
        , const [])) -- should always get "Exists OP_Unit" as argument
    . unzip)
    . unzip
    $ M.toList acc
  unsafeUnExists :: Exists f -> f a
  unsafeUnExists (Exists fa) = unsafeCoerce fa

-- type family ShapeMinus big small where
--   ShapeMinus sh () = sh
--   ShapeMinus (sh, Int) (sh', Int) = ShapeMinus sh sh'



-- TODO: we need to only consider each _in-order_ vertical argument
-- TODO: we ignore backpermute currently. Could use this function to check the outputs and vertical, and the staticclusteranalysis evalI for the inputs.
-- e.g. backpermute . fold: shape of backpermute output plus the extra dimension of fold.
-- loopsizeOutVertical :: forall args env. Cluster NativeOp args -> Gamma env -> Args env args -> Loopsizes
-- loopsizeOutVertical = undefined
-- loopsizeOutVertical (Cluster _ (Cluster' io _)) gamma args = go io args
--   where
--     go :: ClusterIO a i o -> Args env a -> Loopsizes
--     go Empty ArgsNil = LS ShapeRz OP_Unit
--     go (Input io')                     (ArgArray _ (ArrayR shr _) sh _ :>: args') = go io' args' -- $ \x -> combine x (shr, aprjParameters (unsafeToExpVars sh) gamma) k
--     go (Output _ _ _ io')              (ArgArray _ (ArrayR shr _) sh _ :>: args') = combine (go io' args') $ LS shr (aprjParameters (unsafeToExpVars sh) gamma)
--     go (Trivial io')                   (ArgArray _ (ArrayR shr _) sh _ :>: args') = combine (go io' args') $ LS shr (aprjParameters (unsafeToExpVars sh) gamma)
--     go (Vertical _ (ArrayR shr _) io') (ArgVar sh                      :>: args') = combine (go io' args') $ LS shr (aprjParameters                  sh  gamma)
--     go (MutPut io')                    (_                              :>: args') = go io' args'
--     go (ExpPut io')                    (_                              :>: args') = go io' args'
--     go (VarPut io')                    (_                              :>: args') = go io' args'
--     go (FunPut io')                    (_                              :>: args') = go io' args'
-- get the largest ShapeR, and the corresponding shape
combine :: Loopsizes -> Loopsizes -> Loopsizes
combine x@(LS a _) y@(LS b _) = if rank a > rank b then x else y



type Accumulated = M.Map Label (Exists Operands, Exists TypeR)
-- type Accumulator = (Accumulated, Block, Block)

instance EvalOp NativeOp where
  type EvalMonad NativeOp = StateT Accumulated (CodeGen Native) -- should be a ReaderT
  -- dimension and linear and multidim index. The last has 'trust me, this is the right shape' levels of type safety, but trust me. It is the right shape.
  type Index NativeOp = (Int, Operands Int, [Operands Int])
  type Embed' NativeOp = Compose Maybe Operands
  type EnvF NativeOp = GroundOperand

  embed (GroundOperandParam  x) = Compose $ Just $ ir' x
  embed (GroundOperandBuffer _) = error "does this ever happen?"

  unit = Compose $ Just OP_Unit

  -- don't need to be in the monad!
  indexsh vars gamma = pure . CJ $ aprjParameters (unsafeToExpVars vars) gamma
  indexsh' vars gamma = pure . CJ $ aprjParameters vars gamma

  subtup _ CN = CN
  subtup SubTupRskip (CJ _) = CJ OP_Unit
  subtup SubTupRkeep (CJ x) = CJ x
  subtup (SubTupRpair a b) (CJ (OP_Pair x y)) = CJ $ OP_Pair ((\(CJ z)->z) $ subtup @NativeOp a $ CJ x) ((\(CJ z)->z) $ subtup @NativeOp b $ CJ y)

  -- the scalartypes guarantee that there is always only one buffer, and that the unsafeCoerce from (Buffers e) to (Buffer e) is safe
  writeOutput tp sh (TupRsingle buf) gamma (d,i,_) = \case
    CN -> pure ()
    CJ x -> lift $ Prelude.when (sh `isAtDepth` d) $ writeBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i) (op tp x)
  writeOutput _ _ _ _ _ = error "not single"
  readInput :: forall e env sh. ScalarType e -> GroundVars env sh -> GroundVars env (Buffers e) -> Gamma env -> BackendClusterArg2 NativeOp env (In sh e) -> (Int, Operands Int, [Operands Int]) -> StateT Accumulated (CodeGen Native) (Compose Maybe Operands e)
  readInput _ _ _ _ _ (d,_,is) | d /= length is = error "fail"
  readInput tp _ (TupRsingle buf) gamma (BCAN2 Nothing d') (d,i, _)
    | d /= d' = pure CN
    | otherwise = lift $ CJ . ir tp <$> readBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i)
  readInput tp sh (TupRsingle buf) gamma (BCAN2 (Just (BP shr1 (shr2 :: ShapeR sh2) f _ls)) _) (d,_,ix)
    | Just Refl <- varsContainsThisShape sh shr2
    , shr1 `isAtDepth'` d
    = lift $ CJ . ir tp <$> do
      sh2 <- app1 (llvmOfFun1 @Native f gamma) $ multidim shr1 ix
      -- let sh' = unsafeCoerce @(GroundVars env sh) @(GroundVars env sh2) sh -- "trust me", the shapeR in the BP should match the shape of the buffer
      let sh' = aprjParameters (groundToExpVar (shapeType shr2) sh) gamma
      i <- intOfIndex shr2 sh' sh2
      readBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i)
    | otherwise = pure CN
  readInput _ _ (TupRsingle _) _ _ (_,_,_) = error "here"
  -- assuming no bp, and I'll just make a read at every depth?
    -- lift $ CJ . ir tp <$> readBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i)
    -- second attempt, the above segfaults: never read instead
    -- pure CN
    -- also segfaults :(
    {- weird: this implies that a is a `IsUnit`, but it happens on Int
    error $ show tp <> case buf of
    TupRsingle _ -> "single"
    TupRpair _ _ -> "pair"
    TupRunit -> "unit" -}
  readInput _ _ _ _ _ _ = error "not single"

  evalOp  :: (Int, Operands Int, [Operands Int])
          -> Label
          -> NativeOp args
          -> Gamma env
          -> BackendArgEnv NativeOp env (InArgs args)
          -> StateT Accumulated (CodeGen Native) (Env (FromArg' NativeOp env) (OutArgs args))
  -- evalOp _ _ _ _ _ = error "todo: add depth checks to all matches"
  evalOp (d,_,_) _ NMap gamma (Push (Push (Push Env.Empty (BAE _ _)) (BAE (Value' x' (Shape' shr sh)) (BCAN2 _ d'))) (BAE f _))
    = lift $ Push Env.Empty . FromArg . flip Value' (Shape' shr sh) <$> case x' of
      CJ x | d == d' -> CJ <$> traceIfDebugging ("map" <> show d') (app1 (llvmOfFun1 @Native f gamma) x)
      _   -> pure CN
  evalOp _ _ NBackpermute _ (Push (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE (Value' x _) _)) _)
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' x $ Shape' shr sh
  evalOp (d',_,is) _ NGenerate gamma (Push (Push Env.Empty (BAE (Shape' shr (CJ sh)) _)) (BAE f (BCAN2 Nothing _d)))
    | shr `isAtDepth'` d' = traceIfDebugging ("generate" <> show d') $ lift $ Push Env.Empty . FromArg . flip Value' (Shape' shr (CJ sh)) . CJ <$> app1 (llvmOfFun1 @Native f gamma) (multidim shr is)
    -- | d' == d = error $ "how come we didn't hit the case above?" <> show (d', d, rank shr)
    | otherwise        = pure $ Push Env.Empty $ FromArg $ Value' CN (Shape' shr (CJ sh))
  evalOp (d',_,is) _ NGenerate gamma (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE f (BCAN2 (Just (BP shrO shrI idxTransform _ls)) _d)))
    | not $ shrO `isAtDepth'` d'
    = pure $ Push Env.Empty $ FromArg $ Value' CN (Shape' shr sh)
    | Just Refl <- matchShapeR shrI shr
    = traceIfDebugging ("generate" <> show d') $ lift $ Push Env.Empty . FromArg . flip Value' (Shape' shr sh) . CJ <$> app1 (llvmOfFun1 @Native (compose f idxTransform) gamma) (multidim shrO is)
    | otherwise = error "bp shapeR doesn't match generate's output"
  -- For Permute, we ignore all the BP info here and simply assume that there is none
  evalOp (d',_,is) _ NPermute gamma (Push (Push (Push (Push (Push Env.Empty
    (BAE (Value' x' (Shape' shrx _))           (BCAN2 _ d))) -- input
    (BAE (flip (llvmOfFun1 @Native) gamma -> f) _)) -- index function
    (BAE (ArrayDescriptor shrl shl bufl, lty)   _)) -- lock
    (BAE (ArrayDescriptor shrt sht buft, tty)   _)) -- target
    (BAE (flip (llvmOfFun2 @Native) gamma -> c) _)) -- combination function
    | CJ x <- x'
    , d == d'
    = traceIfDebugging ("permute" <> show d') $ lift $ do
        ix' <- app1 f (multidim shrx is)
        -- project element onto the destination array and (atomically) update
        when (isJust ix') $ do
          let ix = fromJust ix'
          let sht' = aprjParameters (unsafeToExpVars sht) gamma
          j <- intOfIndex shrt sht' ix
          atomically gamma (ArgArray Mut (ArrayR shrl lty) shl bufl) j $ do
            y <- readArray TypeInt gamma (ArgArray Mut (ArrayR shrt tty) sht buft) j
            r <- app2 c x y
            writeArray TypeInt gamma (ArgArray Mut (ArrayR shrt tty) sht buft) j r
        pure Env.Empty
    | d == d' = error "case above?"
    | otherwise = pure Env.Empty
  evalOp (d',_,ixs) l NScanl1 gamma (Push (Push _ (BAE (Value' x' sh) (BCAN2 Nothing d))) (BAE f' _))
    | f <- llvmOfFun2 @Native f' gamma
    , Lam (lhsToTupR -> ty :: TypeR e) _ <- f'
    , CJ x <- x'
    , d == d'
    , inner:_ <- ixs
    = traceIfDebugging ("scan" <> show d') $ StateT $ \acc -> do
        let (Exists (unsafeCoerce @(Operands _) @(Operands e) -> accX), eTy) = acc M.! l
        z <- ifThenElse (ty, eq singleType inner (constant typerInt 0)) (pure x) (app2 f accX x) -- note: need to apply the accumulator as the _left_ argument to the function
        pure (Push Env.Empty $ FromArg (Value' (CJ z) sh), M.adjust (const (Exists z, eTy)) l acc)
    | otherwise = pure $ Push Env.Empty $ FromArg (Value' CN sh)
  evalOp _ _ NScanl1 _ (Push (Push _ (BAE _ (BCAN2 (Just BP{}) _))) (BAE _ _)) = error "backpermuted scan"
  evalOp _ _ NFold1 _ _ = error "todo: fold1"
  -- we can ignore the index permutation for folds here
  evalOp (d',_,ixs) l NFold2 gamma (Push (Push _ (BAE (Value' x' (Shape' (ShapeRsnoc shr') (CJ (OP_Pair sh _)))) (BCAN2 _ d))) (BAE f' _))
    | f <- llvmOfFun2 @Native f' gamma
    , Lam (lhsToTupR -> ty :: TypeR e) _ <- f'
    , CJ x <- x'
    , d == d'
    , inner:_ <- ixs
    = traceIfDebugging ("fold2work" <> show d') $ StateT $ \acc -> do
        let (Exists (unsafeCoerce @(Operands _) @(Operands e) -> accX), eTy) = acc M.! l
        z <- ifThenElse (ty, eq singleType inner (constant typerInt 0)) (pure x) (app2 f accX x) -- note: need to apply the accumulator as the _left_ argument to the function
        pure (Push Env.Empty $ FromArg (Value' (CJ z) (Shape' shr' (CJ sh))), M.adjust (const (Exists z, eTy)) l acc)
    | Lam (lhsToTupR -> _ty :: TypeR e) _ <- f'
    , d == d'+1 -- the fold was in the iteration above; we grab the result from the accumulator now
    = traceIfDebugging ("fold2done" <> show d') $ StateT $ \acc -> do
        let (Exists (unsafeCoerce @(Operands _) @(Operands e) -> x), _) = acc M.! l
        pure (Push Env.Empty $ FromArg (Value' (CJ x) (Shape' shr' (CJ sh))), acc)
    | otherwise = pure $ Push Env.Empty $ FromArg (Value' CN (Shape' shr' (CJ sh)))
  evalOp _ _ _ _ _ = error "unmatched pattern?"


instance TupRmonoid Operands where
  pair' = OP_Pair
  unpair' (OP_Pair x y) = (x, y)

instance (TupRmonoid f) => TupRmonoid (Compose Maybe f) where
  pair' (Compose l) (Compose r) = Compose $ pair' <$> l <*> r
  unpair' (Compose p) = maybe (CN, CN) (bimap CJ CJ . unpair') p

unsafeToExpVars :: GroundVars env sh -> ExpVars env sh
unsafeToExpVars TupRunit = TupRunit
unsafeToExpVars (TupRpair l r) = TupRpair (unsafeToExpVars l) (unsafeToExpVars r)
unsafeToExpVars (TupRsingle (Var g idx)) = case g of
  GroundRbuffer _ -> error "unsafeToExpVars on a buffer"
  GroundRscalar t -> TupRsingle (Var t idx)

maybeTy :: TypeR a -> TypeR (PrimMaybe a)
maybeTy ty = TupRpair (TupRsingle scalarTypeWord8) (TupRpair TupRunit ty)









-- TODO: rename to 'static info' or 'symbolic execution' or so
newtype JustAccumulator a b = JA (a b)

data Loopsizes where
  LS :: ShapeR sh -> Operands sh -> Loopsizes

instance Show Loopsizes where
  show (LS shr _) = "Loop of rank " <> show (rank shr)

merge :: Loopsizes -> GroundVars env sh -> Gamma env -> Loopsizes
merge ls v gamma = combine ls $ LS (gvarsToShapeR v) (aprjParameters (unsafeToExpVars v) gamma)

-- mkls :: Int -> ShapeR sh -> Operands sh -> Bool -> Loopsizes
-- mkls d shr sh b
--   | d == rank shr = LS shr sh b
--   | d > rank shr = mkls d (ShapeRsnoc shr) (multidim (ShapeRsnoc shr) $ foldr (:) [constant typerInt 1] $ multidim' shr sh) b
--   | d < rank shr = case shr of 
--       ShapeRsnoc shr' -> mkls d shr' (multidim shr' $ init $ multidim' shr sh) b
--       _ -> error ""
--   | otherwise = error ""

-- merge' :: Loopsizes -> Loopsizes -> Loopsizes
-- merge' ls1@(LS shr1 sh1) ls2@(LS shr2 sh2)
--   | rank shr1 >= rank shr2 && (b1 || not b2) = ls1
--   | rank shr1 <= rank shr2 && (b2 || not b1) = ls2
--   | otherwise = let (big, small) = if rank shr1 > rank shr2 then (ls1,ls2) else (ls2,ls1)
--                 in case (big,small) of
--                   (LS shrB (flipShape shrB -> shB), LS shrS (flipShape shrS -> shS)) 
--                     -> Debug.Trace.traceShow (rank shrB, rank shrS) $ 
--                       LS shrB (multidim shrB $ Prelude.take (rank shrB - rank shrS) (multidim' shrB shB) ++ multidim' shrS shS) 
--                           -- (flipShape shrB . multidim shrB $ multidim' shrS shS ++ drop (rank shrS) (multidim' shrB shB)) 
--                           -- False
--                   _ -> error "huh"
--     where flipShape x y = y

    -- error "todo: take the known indices from the smaller True one, and the rest from the larger False one, call the result False"

instance EvalOp (JustAccumulator NativeOp) where
  type EvalMonad (JustAccumulator NativeOp) = StateT (Accumulated, Loopsizes) (CodeGen Native)
  type Index (JustAccumulator NativeOp) = ()
  type Embed' (JustAccumulator NativeOp) = Both TypeR Operands
  type EnvF (JustAccumulator NativeOp) = GroundOperand

  unit = Both TupRunit OP_Unit
  embed = error "not needed"
  indexsh  vars gamma = pure $ Both (mapTupR varType $ unsafeToExpVars vars) (aprjParameters (unsafeToExpVars vars) gamma)
  indexsh' vars gamma = pure $ Both (mapTupR varType vars) (aprjParameters vars gamma)

  subtup SubTupRskip _ = Both TupRunit OP_Unit
  subtup SubTupRkeep x = x
  subtup (SubTupRpair a b) (Both (TupRpair x y) (OP_Pair x' y')) = case (subtup @(JustAccumulator NativeOp) a (Both x x'), subtup @(JustAccumulator NativeOp) b (Both y y')) of
    (Both l l', Both r r') -> Both (TupRpair l r) (OP_Pair l' r')
  subtup _ _ = error "subtup-pair with non-pair TypeR"

  readInput _ _ _ _ (BCA2JA IsUnit) _ = pure $ Both TupRunit OP_Unit
  readInput ty sh _ gamma (BCA2JA (BCAN2 Nothing               _)) _ = StateT $ \(acc,ls) -> pure (Both (TupRsingle ty) (zeroes $ TupRsingle ty), (acc, merge ls sh gamma))
  readInput ty _ _  gamma (BCA2JA (BCAN2 (Just (BP _ _ _ ls')) _)) _ = StateT $ \(acc,ls) -> pure (Both (TupRsingle ty) (zeroes $ TupRsingle ty), (acc, merge ls ls' gamma))

  writeOutput _ sh _ gamma _ _ = StateT $ \(acc,ls) -> pure ((), (acc, merge ls sh gamma))

  evalOp () l (JA NScanl1) _ (Push (Push _ (BAE (Value' (Both ty x) sh) _)) (BAE _ _))
    = StateT $ \(acc,ls) -> do
        let thing = zeroes ty
        pure (Push Env.Empty $ FromArg (Value' (Both ty x) sh), (M.insert l (Exists thing, Exists ty) acc, ls))
  evalOp () _ (JA NFold1) _ _ = undefined
  evalOp () l (JA NFold2) _ (Push (Push _ (BAE (Value' (Both ty x) (Shape' (ShapeRsnoc shr) sh)) _)) (BAE _ _))
    = StateT $ \(acc,ls) -> do
        let thing = zeroes ty
        pure (Push Env.Empty $ FromArg (Value' (Both ty x) (Shape' shr (case sh of Both (TupRpair x _) (OP_Pair x' _) -> Both x x'))), (M.insert l (Exists thing, Exists ty) acc, ls))
  evalOp () _ (JA NMap) _ (Push (Push (Push Env.Empty (BAE _ _)) (BAE (Value' _ (Shape' shr sh)) _)) (BAE f _))
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' (Both (getOutputType f) (zeroes (getOutputType f))) (Shape' shr sh)
  evalOp () _ (JA NBackpermute) _ (Push (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE (Value' x _) _)) _)
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' x $ Shape' shr sh
  evalOp () _ (JA NGenerate) _ (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE f _))
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' (Both (getOutputType f) (zeroes (getOutputType f))) (Shape' shr sh)
  evalOp _ _ (JA NPermute) _ (Push (Push (Push (Push (Push Env.Empty (BAE (Value' _ (Shape' shr (Both _ sh))) _)) _) _) _) _)
    = StateT $ \(acc,ls) -> pure (Env.Empty, (acc, combine ls $ LS shr sh))


getOutputType :: Fun env (i -> o) -> TypeR o
getOutputType (Lam _ (Body e)) = expType e
getOutputType _ = error "nope"

instance MakesILP op => MakesILP (JustAccumulator op) where
  type BackendVar (JustAccumulator op) = BackendVar op
  type BackendArg (JustAccumulator op) = BackendArg op
  newtype BackendClusterArg (JustAccumulator op) a = BCAJA (BackendClusterArg op a)
  mkGraph (JA _) = undefined -- do not want to run the ILP solver again!
  finalize = undefined
  labelLabelledArg = undefined
  getClusterArg = undefined
  encodeBackendClusterArg = undefined
  combineBackendClusterArg = undefined
  defaultBA = undefined
  -- probably just never running anything here
  -- this is really just here because MakesILP is a superclass


instance (StaticClusterAnalysis op, EnvF (JustAccumulator op) ~ EnvF op) => StaticClusterAnalysis (JustAccumulator op) where
  newtype BackendClusterArg2 (JustAccumulator op) x y = BCA2JA (BackendClusterArg2 op x y)
  onOp a b c d   = coerce @(BackendArgs        op _ _) @(BackendArgs        (JustAccumulator op) _ _) $ onOp (coerce a) (coerce b) (coerce c) d
  def      x y z = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ def x y (coerce z)
  valueToIn    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ valueToIn $ coerce x
  valueToOut   x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ valueToOut $ coerce x
  inToValue    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ inToValue $ coerce x
  inToVar      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ inToVar $ coerce x
  outToValue   x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ outToValue $ coerce x
  outToSh      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ outToSh $ coerce x
  shToOut      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ shToOut $ coerce x
  shToValue    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ shToValue $ coerce x
  varToValue   x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ varToValue $ coerce x
  varToSh      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ varToSh $ coerce x
  outToVar     x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ outToVar $ coerce x
  shToVar      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ shToVar $ coerce x
  shrinkOrGrow a b x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ shrinkOrGrow a b $ coerce x
  addTup       x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ addTup $ coerce x
  unitToVar    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ unitToVar $ coerce x
  varToUnit    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ varToUnit $ coerce x
  pairinfo a x y = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ pairinfo a (coerce x) (coerce y)
  bcaid        x = coerce @(BackendClusterArg op _)    @(BackendClusterArg (JustAccumulator op) _)    $ bcaid $ coerce x
  

deriving instance (Eq (BackendClusterArg2 op x y)) => Eq (BackendClusterArg2 (JustAccumulator op) x y)
deriving instance (Show (BackendClusterArg2 op x y)) => Show (BackendClusterArg2 (JustAccumulator op) x y)
deriving instance (ShrinkArg (BackendClusterArg op)) => ShrinkArg (BackendClusterArg (JustAccumulator op))


toOnlyAcc :: Cluster op args -> Cluster (JustAccumulator op) args
toOnlyAcc (Fused f l r) = Fused f (toOnlyAcc l) (toOnlyAcc r)
toOnlyAcc (Op (SLV (SOp (SOAOp op soa) sort) subargs) l) = Op (SLV (SOp (SOAOp (JA op) soa) sort) subargs) l

pattern CJ :: f a -> Compose Maybe f a
pattern CJ x = Compose (Just x)
pattern CN :: Compose Maybe f a
pattern CN = Compose Nothing
{-# COMPLETE CJ,CN #-}

varsContainsThisShape :: Vars f x sh -> ShapeR sh' -> Maybe (sh :~: sh')
varsContainsThisShape vs shr
  | isAtDepth vs (rank shr) = unsafeCoerce $ Just Refl
  | otherwise = Nothing

-- Does this Vars contain exactly `x` variables, i.e., is `sh` `x`-dimensional?
isAtDepth :: Vars f x sh -> Int -> Bool
isAtDepth vs x = x == depth vs
  where
    depth :: Vars x y z -> Int
    depth TupRunit = 0
    depth (TupRpair l r) = depth l + depth r
    depth TupRsingle{} = 1

isAtDepth' :: ShapeR sh -> Int -> Bool
isAtDepth' vs x = x == rank vs


zeroes :: TypeR a -> Operands a
zeroes TupRunit = OP_Unit
zeroes (TupRpair l r) = OP_Pair (zeroes l) (zeroes r)
zeroes ty@(TupRsingle t) = case t of
  VectorScalarType _ -> error "todo"
  SingleScalarType (NumSingleType t) -> case t of
    IntegralNumType t -> case t of
      TypeInt    -> constant ty 0
      TypeInt8   -> constant ty 0
      TypeInt16  -> constant ty 0
      TypeInt32  -> constant ty 0
      TypeInt64  -> constant ty 0
      TypeWord   -> constant ty 0
      TypeWord8  -> constant ty 0
      TypeWord16 -> constant ty 0
      TypeWord32 -> constant ty 0
      TypeWord64 -> constant ty 0
    FloatingNumType t -> case t of
      TypeHalf   -> constant ty 0
      TypeFloat  -> constant ty 0
      TypeDouble -> constant ty 0

gvarsToShapeR :: Vars GroundR x sh -> ShapeR sh
gvarsToShapeR TupRunit = ShapeRz
gvarsToShapeR (TupRpair sh (TupRsingle x)) = case x of
  Var (GroundRscalar (SingleScalarType (NumSingleType (IntegralNumType TypeInt)))) _ -> ShapeRsnoc $ gvarsToShapeR sh
  _ -> error "not a shape"
gvarsToShapeR _ = error "not a shape"
