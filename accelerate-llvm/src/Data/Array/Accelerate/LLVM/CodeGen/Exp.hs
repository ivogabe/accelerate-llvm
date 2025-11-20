{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Exp
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Exp
  ( module Data.Array.Accelerate.LLVM.CodeGen.Exp, intOfIndex )
  where

import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Vec
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.Sugar.Foreign                as A

import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.Foreign
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic      as A
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop            as L

import Data.Primitive.Vec

import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Operand                                        ( Operand )

import Control.Applicative                                          hiding ( Const )
import Control.Monad
import Prelude                                                      hiding ( exp, any )

import GHC.TypeNats
import Data.Primitive (Ptr(Ptr))
import Data.Array.Accelerate.LLVM.CodeGen.Base (call, call')
import qualified LLVM.AST.Type.Function as F
import LLVM.AST.Type.Representation (IsPrim(primType), Type(..))
import LLVM.AST.Type.Name (Label(Label))


-- Scalar expressions
-- ==================

{-# INLINEABLE llvmOfFun1 #-}
llvmOfFun1
    :: (HasCallStack, CompileForeignExp arch, IsArrayInstr arr)
    => CompileArrayInstr arch arr
    -> PreOpenFun arr () (a -> b)
    -> IRFun1 arch (a -> b)
llvmOfFun1 arrayInstr (Lam lhs (Body body))
  = IRFun1 $ \x -> llvmOfOpenExp arrayInstr body (Empty `pushE` (lhs, x))
llvmOfFun1 _ _ = internalError "impossible evaluation"

{-# INLINEABLE llvmOfFun2 #-}
llvmOfFun2
    :: (HasCallStack, CompileForeignExp arch, IsArrayInstr arr)
    => CompileArrayInstr arch arr
    -> PreOpenFun arr () (a -> b -> c)
    -> IRFun2 arch (a -> b -> c)
llvmOfFun2 arrayInstr (Lam lhs1 (Lam lhs2 (Body body)))
  = IRFun2 $ \x y -> llvmOfOpenExp arrayInstr body (Empty `pushE` (lhs1, x) `pushE` (lhs2, y))
llvmOfFun2 _ _ = internalError "impossible evaluation"

type CompileArrayInstr arch arr = forall env s t. arr (s -> t) -> Operands s -> IROpenExp arch env t

compileArrayInstrGamma :: forall arch genv. Gamma genv -> CompileArrayInstr arch (ArrayInstr genv)
compileArrayInstrGamma genv arr arg = case arr of
  Parameter var -> param var
  Index var -> linearIndex var arg
  where
    linearIndex :: GroundVar genv (Buffer e) -> Operands Int -> IROpenExp arch env e
    linearIndex var@(Var (GroundRbuffer tp) _) idx =
      ir tp <$> readBuffer tp integralType irbuffer (op scalarTypeInt idx) Nothing
      where
        irbuffer = aprjBuffer var genv
    linearIndex (Var (GroundRscalar tp) _) _ = bufferImpossible tp

    param :: ExpVar genv e -> IROpenExp arch env e
    param var@(Var tp _) = return $ ir tp $ aprjParameter var genv

compileNoArrayInstr :: CompileArrayInstr arch NoArrayInstr
compileNoArrayInstr arr _ = case arr of {}

compileArrayInstrEnvs :: forall arch genv idxEnv. Envs genv idxEnv -> CompileArrayInstr arch (ArrayInstr genv)
compileArrayInstrEnvs envs arr arg = case arr of
  Parameter var -> param var
  Index var -> linearIndex var arg
  where
    linearIndex :: GroundVar genv (Buffer e) -> Operands Int -> IROpenExp arch env e
    linearIndex var@(Var (GroundRbuffer tp) _) idx =
      ir tp <$> readBuffer tp integralType irbuffer (op scalarTypeInt idx) Nothing
      where
        irbuffer = envsPrjBuffer var envs
    linearIndex (Var (GroundRscalar tp) _) _ = bufferImpossible tp

    param :: ExpVar genv e -> IROpenExp arch env e
    param var@(Var tp _) = return $ ir tp $ envsPrjParameter var envs

{-# INLINEABLE llvmOfExp #-}
llvmOfExp
    :: forall arr arch t. (HasCallStack, CompileForeignExp arch, IsArrayInstr arr)
    => CompileArrayInstr arch arr
    -> PreOpenExp arr () t
    -> IROpenExp arch () t
llvmOfExp arrayInstr expr = llvmOfOpenExp arrayInstr expr Empty

-- | Convert an open scalar expression into a sequence of LLVM Operands instructions.
-- Code is generated in depth first order, and uses a monad to collect the
-- sequence of instructions used to construct basic blocks.
--
{-# INLINEABLE llvmOfOpenExp #-}
llvmOfOpenExp
    :: forall arr arch env _t. (HasCallStack, CompileForeignExp arch, IsArrayInstr arr)
    => CompileArrayInstr arch arr
    -> PreOpenExp arr env _t
    -> Val env
    -> IROpenExp arch env _t
llvmOfOpenExp arrayInstr top env = cvtE top
  where

    cvtF1 :: PreOpenFun arr env (a -> b) -> IROpenFun1 arch env (a -> b)
    cvtF1 (Lam lhs (Body body)) = IRFun1 $ \x -> llvmOfOpenExp arrayInstr body (env `pushE` (lhs, x))
    cvtF1 _                     = internalError "impossible evaluation"

    cvtE :: forall t. PreOpenExp arr env t -> IROpenExp arch env t
    cvtE exp =
      case exp of
        Let lhs bnd body            -> do x <- cvtE bnd
                                          llvmOfOpenExp arrayInstr body (env `pushE` (lhs, x))
        Evar (Var tp ix)            -> return $ ir tp $ prj ix env
        Const tp c                  -> return $ ir tp $ scalar tp c
        PrimConst c                 -> let tp = (SingleScalarType $ primConstType c)
                                       in  return $ ir tp $ scalar tp $ primConst c
        PrimApp f x                 -> primFun f x
        Undef tp                    -> return $ ir tp $ undef tp
        Nil                         -> return $ OP_Unit
        Pair e1 e2                  -> join $ pair <$> cvtE e1 <*> cvtE e2
        VecPack   vecr e            -> vecPack   vecr =<< cvtE e
        VecUnpack vecr e            -> vecUnpack vecr =<< cvtE e
        Foreign tp asm f x          -> foreignE tp asm f =<< cvtE x
        Case tag xs mx              -> A.caseof (expType (snd (head xs))) (cvtE tag) [(t,cvtE e) | (t,e) <- xs] (fmap cvtE mx)
        Cond c t e                  -> cond (expType t) (cvtE c) (cvtE t) (cvtE e)
        IndexSlice slice slix sh    -> indexSlice slice <$> cvtE slix <*> cvtE sh
        IndexFull slice slix sh     -> indexFull slice  <$> cvtE slix <*> cvtE sh
        ToIndex shr sh ix           -> join $ intOfIndex shr <$> cvtE sh <*> cvtE ix
        FromIndex shr sh ix         -> join $ indexOfInt shr <$> cvtE sh <*> cvtE ix
        ArrayInstr arr arg          -> arrayInstr arr =<< cvtE arg
        ShapeSize shr sh            -> shapeSize shr =<< cvtE sh
        While c f x                 -> while (expType x) (cvtF1 c) (cvtF1 f) (cvtE x)
        Coerce t1 t2 x              -> coerce t1 t2 =<< cvtE x
        Assert c e                  -> assert (cvtE c) (cvtE e)
        Assume _ e                  -> cvtE e

    indexSlice :: SliceIndex slix sl co sh -> Operands slix -> Operands sh -> Operands sl
    indexSlice SliceNil              OP_Unit               OP_Unit          = OP_Unit
    indexSlice (SliceAll sliceIdx)   (OP_Pair slx OP_Unit) (OP_Pair sl sz)  =
      let sl' = indexSlice sliceIdx slx sl
        in OP_Pair sl' sz
    indexSlice (SliceFixed sliceIdx) (OP_Pair slx _i)      (OP_Pair sl _sz) =
      indexSlice sliceIdx slx sl

    indexFull :: SliceIndex slix sl co sh -> Operands slix -> Operands sl -> Operands sh
    indexFull SliceNil              OP_Unit               OP_Unit         = OP_Unit
    indexFull (SliceAll sliceIdx)   (OP_Pair slx OP_Unit) (OP_Pair sl sz) =
      let sh' = indexFull sliceIdx slx sl
        in OP_Pair sh' sz
    indexFull (SliceFixed sliceIdx) (OP_Pair slx sz)      sl              =
      let sh' = indexFull sliceIdx slx sl
        in OP_Pair sh' sz

    vecPack :: forall n single tuple. (HasCallStack, KnownNat n) => VecR n single tuple -> Operands tuple -> CodeGen arch (Operands (Vec n single))
    vecPack vecr tuple = ir tp <$> go vecr n tuple
      where
        go :: VecR n' single tuple' -> Int -> Operands tuple' -> CodeGen arch (Operand (Vec n single))
        go (VecRnil _)      0 OP_Unit        = return $ undef $ VectorScalarType tp
        go (VecRnil _)      _ OP_Unit        = internalError "index mismatch"
        go (VecRsucc vecr') i (OP_Pair xs x) = do
          vec <- go vecr' (i - 1) xs
          instr' $ InsertElement (fromIntegral i - 1) vec (op singleTp x)

        singleTp :: SingleType single -- GHC 8.4 cannot infer this type for some reason
        tp@(VectorType n singleTp) = vecRvector vecr

    vecUnpack :: forall n single tuple. (HasCallStack, KnownNat n) => VecR n single tuple -> Operands (Vec n single) -> CodeGen arch (Operands tuple)
    vecUnpack vecr (OP_Vec vec) = go vecr n
      where
        go :: VecR n' single tuple' -> Int -> CodeGen arch (Operands tuple')
        go (VecRnil _)      0 = return $ OP_Unit
        go (VecRnil _)      _ = internalError "index mismatch"
        go (VecRsucc vecr') i = do
          xs <- go vecr' (i - 1)
          x  <- instr' $ ExtractElement (fromIntegral i - 1) vec
          return $ OP_Pair xs (ir singleTp x)

        singleTp :: SingleType single -- GHC 8.4 cannot infer this type for some reason
        VectorType n singleTp = vecRvector vecr

    pair :: Operands t1 -> Operands t2 -> IROpenExp arch env (t1, t2)
    pair a b = return $ OP_Pair a b

    bool :: IROpenExp arch env PrimBool
         -> IROpenExp arch env Bool
    bool p = instr . IntToBool integralType . op integralType =<< p

    primbool :: IROpenExp arch env Bool
             -> IROpenExp arch env PrimBool
    primbool b = instr . BoolToInt integralType . A.unbool =<< b

    cond :: TypeR a
         -> IROpenExp arch env PrimBool
         -> IROpenExp arch env a
         -> IROpenExp arch env a
         -> IROpenExp arch env a
    cond tp p t e =
      A.ifThenElse (tp, bool p) t e

    assert :: IROpenExp arch env PrimBool
           -> IROpenExp arch env a
           -> IROpenExp arch env a
    assert c e = do
      A.unless (bool c) trap
      e

    while :: TypeR a
          -> IROpenFun1 arch env (a -> PrimBool)
          -> IROpenFun1 arch env (a -> a)
          -> IROpenExp  arch env a
          -> IROpenExp  arch env a
    while tp p f x =
      L.while [] tp (bool . app1 p) (app1 f) =<< x

    land :: Operands PrimBool
         -> Operands PrimBool
         -> IROpenExp arch env PrimBool
    land x y = do
      x' <- instr (IntToBool integralType (op integralType x))
      y' <- instr (IntToBool integralType (op integralType y))
      primbool (A.land x' y')

    lor :: Operands PrimBool
        -> Operands PrimBool
        -> IROpenExp arch env PrimBool
    lor x y = do
      x' <- instr (IntToBool integralType (op integralType x))
      y' <- instr (IntToBool integralType (op integralType y))
      primbool (A.lor x' y')

    foreignE :: A.Foreign asm
             => TypeR b
             -> asm    (a -> b)
             -> PreOpenFun NoArrayInstr () (a -> b)
             -> Operands a
             -> IRExp arch b
    foreignE _ asm no x =
      case foreignExp asm of
        Just f                           -> app1 f x
        Nothing | Lam lhs (Body b) <- no -> llvmOfOpenExp compileNoArrayInstr b (Empty `pushE` (lhs, x))
        _                                -> error "when a grid's misaligned with another behind / that's a moiré..."

    coerce :: ScalarType a -> ScalarType b -> Operands a -> IROpenExp arch env b
    coerce s t x
      | Just Refl <- matchScalarType s t = return $ x
      | otherwise                        = ir t <$> instr' (BitCast t (op s x))

    primFun :: PrimFun (a -> r)
            -> PreOpenExp arr env a
            -> IROpenExp arch env r
    primFun f x =
      case f of
        PrimAdd t                 -> A.uncurry (A.add t)            =<< cvtE x
        PrimSub t                 -> A.uncurry (A.sub t)            =<< cvtE x
        PrimMul t                 -> A.uncurry (A.mul t)            =<< cvtE x
        PrimNeg t                 -> A.negate t                     =<< cvtE x
        PrimAbs t                 -> A.abs t                        =<< cvtE x
        PrimSig t                 -> A.signum t                     =<< cvtE x
        PrimQuot t                -> A.uncurry (A.quot t)           =<< cvtE x
        PrimRem t                 -> A.uncurry (A.rem t)            =<< cvtE x
        PrimQuotRem t             -> A.uncurry (A.quotRem t)        =<< cvtE x
        PrimIDiv t                -> A.uncurry (A.idiv t)           =<< cvtE x
        PrimMod t                 -> A.uncurry (A.mod t)            =<< cvtE x
        PrimDivMod t              -> A.uncurry (A.divMod t)         =<< cvtE x
        PrimBAnd t                -> A.uncurry (A.band t)           =<< cvtE x
        PrimBOr t                 -> A.uncurry (A.bor t)            =<< cvtE x
        PrimBXor t                -> A.uncurry (A.xor t)            =<< cvtE x
        PrimBNot t                -> A.complement t                 =<< cvtE x
        PrimBShiftL t             -> A.uncurry (A.shiftL t)         =<< cvtE x
        PrimBShiftR t             -> A.uncurry (A.shiftR t)         =<< cvtE x
        PrimBRotateL t            -> A.uncurry (A.rotateL t)        =<< cvtE x
        PrimBRotateR t            -> A.uncurry (A.rotateR t)        =<< cvtE x
        PrimPopCount t            -> A.popCount t                   =<< cvtE x
        PrimCountLeadingZeros t   -> A.countLeadingZeros t          =<< cvtE x
        PrimCountTrailingZeros t  -> A.countTrailingZeros t         =<< cvtE x
        PrimFDiv t                -> A.uncurry (A.fdiv t)           =<< cvtE x
        PrimRecip t               -> A.recip t                      =<< cvtE x
        PrimSin t                 -> A.sin t                        =<< cvtE x
        PrimCos t                 -> A.cos t                        =<< cvtE x
        PrimTan t                 -> A.tan t                        =<< cvtE x
        PrimSinh t                -> A.sinh t                       =<< cvtE x
        PrimCosh t                -> A.cosh t                       =<< cvtE x
        PrimTanh t                -> A.tanh t                       =<< cvtE x
        PrimAsin t                -> A.asin t                       =<< cvtE x
        PrimAcos t                -> A.acos t                       =<< cvtE x
        PrimAtan t                -> A.atan t                       =<< cvtE x
        PrimAsinh t               -> A.asinh t                      =<< cvtE x
        PrimAcosh t               -> A.acosh t                      =<< cvtE x
        PrimAtanh t               -> A.atanh t                      =<< cvtE x
        PrimAtan2 t               -> A.uncurry (A.atan2 t)          =<< cvtE x
        PrimExpFloating t         -> A.exp t                        =<< cvtE x
        PrimFPow t                -> A.uncurry (A.fpow t)           =<< cvtE x
        PrimSqrt t                -> A.sqrt t                       =<< cvtE x
        PrimLog t                 -> A.log t                        =<< cvtE x
        PrimLogBase t             -> A.uncurry (A.logBase t)        =<< cvtE x
        PrimTruncate ta tb        -> A.truncate ta tb               =<< cvtE x
        PrimRound ta tb           -> A.round ta tb                  =<< cvtE x
        PrimFloor ta tb           -> A.floor ta tb                  =<< cvtE x
        PrimCeiling ta tb         -> A.ceiling ta tb                =<< cvtE x
        PrimMax t                 -> A.uncurry (A.max t)            =<< cvtE x
        PrimMin t                 -> A.uncurry (A.min t)            =<< cvtE x
        PrimFromIntegral ta tb    -> A.fromIntegral ta tb           =<< cvtE x
        PrimToFloating ta tb      -> A.toFloating ta tb             =<< cvtE x
        PrimLAnd                  -> A.uncurry land                 =<< cvtE x
        PrimLOr                   -> A.uncurry lor                  =<< cvtE x
        PrimIsNaN t               -> primbool $ A.isNaN t           =<< cvtE x
        PrimIsInfinite t          -> primbool $ A.isInfinite t      =<< cvtE x
        PrimLt t                  -> primbool $ A.uncurry (A.lt t)  =<< cvtE x
        PrimGt t                  -> primbool $ A.uncurry (A.gt t)  =<< cvtE x
        PrimLtEq t                -> primbool $ A.uncurry (A.lte t) =<< cvtE x
        PrimGtEq t                -> primbool $ A.uncurry (A.gte t) =<< cvtE x
        PrimEq t                  -> primbool $ A.uncurry (A.eq t)  =<< cvtE x
        PrimNEq t                 -> primbool $ A.uncurry (A.neq t) =<< cvtE x
        PrimLNot                  -> primbool $ A.lnot              =<< bool (cvtE x)
          -- no missing patterns, whoo!


-- | Extract the head of an index
--
indexHead :: Operands (sh, sz) -> Operands sz
indexHead (OP_Pair _ sz) = sz

-- | Extract the tail of an index
--
indexTail :: Operands (sh, sz) -> Operands sh
indexTail (OP_Pair sh _) = sh

-- | Construct an index from the head and tail
--
indexCons :: Operands sh -> Operands sz -> Operands (sh, sz)
indexCons sh sz = OP_Pair sh sz

-- | Number of elements contained within a shape
--
shapeSize :: ShapeR sh -> Operands sh -> CodeGen arch (Operands Int)
shapeSize ShapeRz OP_Unit
  = return $ A.liftInt 1
shapeSize (ShapeRsnoc shr) (OP_Pair sh sz)
  = case shr of
      ShapeRz -> return sz
      _       -> do
        a <- shapeSize shr sh
        b <- A.mul numType a sz
        return b


-- | Convert a linear index into into a multidimensional index
--
indexOfInt :: ShapeR sh -> Operands sh -> Operands Int -> CodeGen arch (Operands sh)
indexOfInt ShapeRz OP_Unit _
  = return OP_Unit
indexOfInt (ShapeRsnoc shr) (OP_Pair sh sz) i
  = do
        i'    <- A.quot integralType i sz
        -- If we assume the index is in range, there is no point computing
        -- the remainder of the highest dimension since (i < sz) must hold
        r     <- case shr of
                  ShapeRz -> return i     -- TODO: in debug mode assert (i < sz)
                  _       -> A.rem  integralType i sz
        sh'   <- indexOfInt shr sh i'
        return $ OP_Pair sh' r

-- | Reads from an array at a multidimensional index.
readArrayIndex
    :: forall genv idxEnv m sh e arch.
       Envs genv idxEnv
    -> Arg genv (m sh e) -- m is In or Mut
    -> Operands sh
    -> CodeGen arch (Operands e)
readArrayIndex env array@(ArgArray _ (ArrayR shr _) _ _) ix = do
  int <- intOfIndex shr (arraySize array env) ix
  readArray integralType env array int

pushE :: Val env -> (ELeftHandSide t env env', Operands t) -> Val env'
pushE env (LeftHandSideSingle tp , e)               = env `Push` op tp e
pushE env (LeftHandSideWildcard _, _)               = env
pushE env (LeftHandSidePair l1 l2, (OP_Pair e1 e2)) = pushE env (l1, e1) `pushE` (l2, e2)

trap :: CodeGen arch ()
trap = do
  _ <- call' (F.Body VoidType Nothing (Label "llvm.trap")) F.ArgumentsNil []
  return ()
