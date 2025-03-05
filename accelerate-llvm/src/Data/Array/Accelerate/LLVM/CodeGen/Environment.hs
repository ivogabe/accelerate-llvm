{-# LANGUAGE GADTs                #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Environment
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Environment
  ( Env(..)
  , Val, prj
  , Gamma, GroundOperand(..), AccessGroundR(..)
  , aprjParameter, aprjParameters, aprjBuffer
  , arraySize
  , MarshalArg, MarshalFun, MarshalFun', MarshalEnv
  , marshalScalarArg
  -- , scalarParameter, ptrParameter
  , bindEnv, envType
  , Envs(..), initEnv, bindLocals, bindLocalsInTile
  , envsGamma, envsPrjBuffer, envsPrjParameter
  , envsPrjParameters, envsPrjSh, envsPrjIndex, envsPrjIndices
  , parallelIterSize
  )
  where

import Data.String

import Data.Array.Accelerate.AST.Environment                    hiding ( Val, prj )
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Partitioned                    hiding ( Label )
import Data.Array.Accelerate.AST.Idx                            ( Idx )
import Data.Array.Accelerate.AST.IdxSet                         (IdxSet)
import qualified Data.Array.Accelerate.AST.IdxSet               as IdxSet
import Data.Array.Accelerate.Error                              ( internalError )
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Constant

import LLVM.AST.Type.AddrSpace
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Function                                   as LLVM
import LLVM.AST.Type.Global
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Metadata
import LLVM.AST.Type.Name
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation
import qualified LLVM.AST.ParameterAttribute as ParameterAttribute
import qualified LLVM.AST.Operand as LLVM

import GHC.Stack
import Data.Typeable
import Data.Foldable
import Data.ByteString.Short                                    ( ShortByteString(..) )
import Control.Monad

data Envs env idxEnv = Envs
  -- The current loop depth
  { envsLoopDepth :: LoopDepth
  -- The number of nested loops
  , envsLoopCount :: LoopDepth
  -- The valuation of the ground environment.
  -- This is a partial environment as some local (fused away) buffers are only
  -- available in deeper loop depths.
  , envsGround :: PartialEnv GroundOperand env
  -- A list of the local buffers (fused away or dead buffers).
  -- These buffers are not allocated outside the kernel, but inside the kernel
  -- via alloca. (LLVM's mem2reg will move these from the stack to registers.)
  , envsLocal :: [EnvBinding LocalBufferR env]
  -- The valuation of the index environment.
  -- This is a partial environment as some indices are only available in
  -- deeper loop depths.
  , envsIdx :: PartialEnv Operand idxEnv
  -- The index of the tile, if this is in a parallel tiled loop
  , envsTileIndex :: Operands Int
  -- The index within the tile, if this is in a parallel tiled loop
  , envsTileLocalIndex :: Operands Int
  -- The index within a SIMD loop, if this is in a SIMD loop
  , envsSimdLane :: Operands Int
  -- Whether the iteration at the current loop depth is the first iteration of
  -- the loop If this is in a tile loop, this says if this is the first
  -- iteration of that tile loop.
  , envsIsFirst :: Operands Bool
  -- Whether the loop at the current loop depth is descending
  -- (iterating from high indices to low indices)
  , envsDescending :: Bool
  }

initEnv
  :: forall target env env' idxEnv sh local.
     Gamma env
  -- Fields from FlatCluster
  -- Info on the index environment
  -> ShapeR sh
  -> ELeftHandSide sh () idxEnv
  -> GroundVars env sh
  -> TupR LoopDirection sh
  -- Info on local (fused away or dead) buffers
  -> TupR LocalBufferR local
  -> GLeftHandSide local env env'
  ->
    ( Envs env' idxEnv
    -- At index d, contains the index variable, iteration direction and size of
    -- the loop introduced at loop depth d.
    , [(Idx idxEnv Int, LoopDirection Int, Operands Int)]
    )
initEnv gamma shr idxLHS iterSize iterDir localsR localLHS
  | Just idxVars <- lhsFullVars idxLHS =
    ( Envs
      { envsLoopDepth = 0
      , envsLoopCount = rank shr
      , envsGround = partialEnvSkipLHS localLHS $ envToPartial gamma
      , envsLocal = partialEnvToList $ partialEnvPushLHS localLHS localsR PEnd
      , envsIdx = PEnd
      , envsTileIndex = OP_Int $ scalar scalarTypeInt 0
      , envsTileLocalIndex = OP_Int $ scalar scalarTypeInt 0
      , envsSimdLane = OP_Int $ scalar scalarTypeInt 0
      , envsIsFirst = OP_Bool $ boolean True
      , envsDescending = False
      }
    , reverse $ loops shr idxVars iterSize iterDir
    )
  | otherwise =
    internalError "Index LeftHandSide should bind all variables"
  where
    -- Gets the loop sizes and directions (in reverse order since ShapeR is a snoc list)
    loops :: ShapeR sh' -> ExpVars idxEnv sh' -> GroundVars env sh' -> TupR LoopDirection sh' -> [(Idx idxEnv Int, LoopDirection Int, Operands Int)]
    loops ShapeRz _ _ _ = []
    loops (ShapeRsnoc shr') (ixs `TupRpair` TupRsingle ix) (sh' `TupRpair` TupRsingle sz) (dirs' `TupRpair` TupRsingle dir) =
      (varIdx ix, dir, szOperand) : loops shr' ixs sh' dirs'
      where
        szOperand = OP_Int $ aprjParameter (Var scalarTypeInt $ varIdx sz) gamma

bindLocals :: LoopDepth -> Envs env idxEnv -> CodeGen target (Envs env idxEnv)
bindLocals depth = \envs -> foldlM go envs $ envsLocal envs
  where
    go :: Envs env idxEnv -> EnvBinding LocalBufferR env -> CodeGen target (Envs env idxEnv)
    go envs (EnvBinding idx (LocalBufferR tp depth'))
      | depth /= depth' = return envs
      | Just _ <- prjPartial idx (envsGround envs) = return envs -- Already bound
      | otherwise = do
        -- Introduce a new mutable variable on the stack
        ptr <- instr' $ Alloca $ ScalarPrimType tp
        ptr' <- instr' $ PtrCast (PtrPrimType (ScalarPrimType $ SingleScalarType $ scalarArrayDataR tp) defaultAddrSpace) ptr
        let value = IRBuffer ptr' defaultAddrSpace NonVolatile IRBufferScopeSingle Nothing
        return envs{ envsGround = partialUpdate (GroundOperandBuffer value) idx $ envsGround envs }

bindLocalsInTile :: forall target env idxEnv. LoopDepth -> Int -> Int -> IdxSet env -> Envs env idxEnv -> CodeGen target (Envs env idxEnv)
bindLocalsInTile depth tileSize interleaveSize acrossTileLoops = \envs -> foldlM go envs $ envsLocal envs
  where
    go :: Envs env idxEnv -> EnvBinding LocalBufferR env -> CodeGen target (Envs env idxEnv)
    go envs (EnvBinding idx (LocalBufferR tp depth'))
      | depth /= depth' = return envs
      | Just _ <- prjPartial idx (envsGround envs) = return envs -- Already bound
      | otherwise = do
        -- Introduce a new mutable variable on the stack
        let allocTile = IdxSet.member idx acrossTileLoops
        let size = if allocTile then tileSize else interleaveSize
        ptr <- instr' $ Alloca $ ArrayPrimType (fromIntegral size) (ScalarPrimType tp)
        ptr' <- instr' $ PtrCast (PtrPrimType (ScalarPrimType $ SingleScalarType $ scalarArrayDataR tp) defaultAddrSpace) ptr
        let value = IRBuffer ptr' defaultAddrSpace NonVolatile (if allocTile then IRBufferScopeTile else IRBufferScopeSIMD) Nothing
        return envs{ envsGround = partialUpdate (GroundOperandBuffer value) idx $ envsGround envs }

envsGamma :: HasCallStack => Envs env idxEnv -> Gamma env
envsGamma = envFromPartialLazy "Value missing in environment at this loop depth. Are the loop depths incorrect?" . envsGround

envsPrjParameter :: HasCallStack => ExpVar env t -> Envs env idxEnv -> Operand t
envsPrjParameter (Var tp idx) env =
  case prjPartial idx $ envsGround env of
    Just (GroundOperandParam x)  -> x
    Just (GroundOperandBuffer _) -> bufferImpossible tp
    Nothing -> internalError "Value missing in environment"

envsPrjParameters :: HasCallStack => ExpVars env t -> Envs env idxEnv -> Operands t
envsPrjParameters (TupRsingle var) env = ir (varType var) $ envsPrjParameter var env
envsPrjParameters (TupRpair v1 v2) env = OP_Pair (envsPrjParameters v1 env) (envsPrjParameters v2 env)
envsPrjParameters TupRunit         _   = OP_Unit

envsPrjSh :: HasCallStack => ShapeR sh -> Vars s env sh -> Envs env idxEnv -> Operands sh
envsPrjSh ShapeRz _ _ = OP_Unit
envsPrjSh (ShapeRsnoc shr) (sh `TupRpair` TupRsingle sz) env = case prjPartial (varIdx sz) (envsGround env) of
  Nothing -> internalError "Value missing in environment"
  Just (GroundOperandParam sz') ->
    envsPrjSh shr sh env `OP_Pair` OP_Int sz'

envsPrjIndex :: HasCallStack => Var s idxEnv t -> Envs env idxEnv -> Operand t
envsPrjIndex (Var _ idx) env = case prjPartial idx $ envsIdx env of
  Just operand -> operand
  Nothing -> internalError "Index missing in index environment at this loop depth. Are the loop depths incorrect?"

envsPrjIndices :: HasCallStack => ExpVars idxEnv t -> Envs env idxEnv -> Operands t
envsPrjIndices (TupRsingle var) env = ir (varType var) $ envsPrjIndex var env
envsPrjIndices (TupRpair v1 v2) env = OP_Pair (envsPrjIndices v1 env) (envsPrjIndices v2 env)
envsPrjIndices TupRunit         _   = OP_Unit

-- Projection of a buffer from the ground environment using a de Bruijn index.
-- This returns the operand of pointer to the buffer and its address space and
-- volatility.
--
envsPrjBuffer :: HasCallStack => GroundVar env (Buffer t) -> Envs env idxEnv -> IRBuffer t
envsPrjBuffer (Var (GroundRbuffer _) idx) env =
  case prjPartial idx $ envsGround env of
    Just (GroundOperandBuffer buffer) -> buffer
    Just (GroundOperandParam _)       -> internalError "Scalar impossible"
    Nothing -> internalError "Buffer missing in environment at this loop depth. Are the loop depths incorrect?"
envsPrjBuffer (Var (GroundRscalar tp) _) _ = bufferImpossible tp

-- Returns the iteration size of the dimensions we parallelize over
parallelIterSize :: ShapeR sh -> [(Idx idxEnv Int, LoopDirection Int, Operands Int)] -> Operands sh
parallelIterSize shr loops = go shr $ reverse $ take (rank shr) loops
  where
    go :: ShapeR sh -> [(Idx idxEnv Int, LoopDirection Int, Operands Int)] -> Operands sh
    go ShapeRz [] = OP_Unit
    go (ShapeRsnoc shr') ((_, _, sz) : loops') = go shr' loops' `OP_Pair` sz

-- Scalar environment
-- ==================

-- | An environment for local scalar expression bindings, encoded at the value
-- level as a heterogenous snoc list, and on the type level as nested tuples.
--
type Val = Env Operand

prj :: Idx env t -> Val env -> Operand t
prj = prj'

-- Ground environment
-- =================

-- | A mapping between the environment index of a free scalar or buffer variable and the
-- Name of that variable to be used in the generated code.
--
-- This simply compresses the indices into a continuous range, rather than
-- directly using the integer equivalent of the de Bruijn index. Thus, the
-- result is still sensitive to the order of let bindings, but not of any
-- intermediate (unused) free array variables.
--
type Gamma = Env GroundOperand

data GroundOperand t where
  GroundOperandParam  :: Operand t  -> GroundOperand t
  GroundOperandBuffer :: IRBuffer t -> GroundOperand (Buffer t)

-- Projection of a scalar from the ground environment using a de Bruijn index.
--
aprjParameter :: HasCallStack => ExpVar genv t -> Gamma genv -> Operand t
aprjParameter (Var tp idx) env =
  case prj' idx env of
    GroundOperandParam x  -> x
    GroundOperandBuffer _ -> bufferImpossible tp

aprjParameters :: HasCallStack => ExpVars genv t -> Gamma genv -> Operands t
aprjParameters (TupRsingle var) env = ir (varType var) $ aprjParameter var env
aprjParameters (TupRpair v1 v2) env = OP_Pair (aprjParameters v1 env) (aprjParameters v2 env)
aprjParameters TupRunit         _   = OP_Unit

-- Projection of a buffer from the ground environment using a de Bruijn index.
-- This returns the operand of pointer to the buffer and its address space and
-- volatility.
--
aprjBuffer :: HasCallStack => GroundVar genv (Buffer t) -> Gamma genv -> IRBuffer t
aprjBuffer (Var (GroundRbuffer _) idx) env =
  case prj' idx env of
    GroundOperandBuffer buffer -> buffer
    GroundOperandParam _       -> internalError "Scalar impossible"
aprjBuffer (Var (GroundRscalar tp) _) _ = bufferImpossible tp

arraySize :: HasCallStack => Arg genv (m sh e) -> Gamma genv -> Operands sh
arraySize (ArgArray _ (ArrayR shr _) sh _) = aprjParameters $ shapeExpVars shr sh

type family MarshalArg a where
  MarshalArg (Buffer e) = Ptr (ScalarArrayDataR e)
  MarshalArg e = e

-- | Converts a typed environment into a function type.
-- For instance, (((), Int), Float) is converted to Int -> Float -> ().
-- The accumulating parameter 'r' is needed as the type would be in reverse
-- order without such accumulator.
--
type MarshalFun env = MarshalFun' env ()
type family MarshalFun' env r where
  MarshalFun' () r = r
  MarshalFun' (env, t) r = MarshalFun' env (MarshalArg t -> r)

type family MarshalEnv env where
  MarshalEnv (env, t) = (MarshalEnv env, MarshalArg t)
  MarshalEnv ()       = ()

envType :: Env AccessGroundR env -> TupR PrimType (MarshalEnv env)
envType Empty = TupRunit
envType (Push env (AccessGroundRscalar tp))
  | Refl <- marshalScalarArg tp = envType env `TupRpair` TupRsingle (ScalarPrimType tp)
envType (Push env (AccessGroundRbuffer _ (SingleScalarType tp)))
  | SingleArrayDict <- singleArrayDict tp 
  = envType env `TupRpair` TupRsingle (PtrPrimType (ScalarPrimType $ SingleScalarType tp) defaultAddrSpace)
envType (Push env (AccessGroundRbuffer _ (VectorScalarType (VectorType n tp))))
  = envType env `TupRpair` TupRsingle (PtrPrimType (ScalarPrimType $ SingleScalarType tp) defaultAddrSpace)

bindEnv
  :: forall arch env. Env AccessGroundR env
  -> ( PrimType (Struct (MarshalEnv env))
     , CodeGen arch ()
     , Gamma env
     )
bindEnv environment =
  let (gen, gamma, _, _, mutOutCount) = go id environment
  in
    ( envTp
    , do
      -- Declare domain for alias annotations
      domain <- addMetadata (\d -> [Just $ MetadataNodeOperand $ MetadataNodeReference d])
      when (domain /= LLVM.MetadataNodeID 0) $
        internalError "bindEnv assumes this is the first place where metadata nodes are created"

      -- The metadata nodes are introduced as follows:
      -- 0 is the domain
      -- 1 is the list with all scopes we define here
      -- 2 is the scope for all inputs (which share one domain)
      -- 3 is the list containing only the scope for all inputs (i.e. the alias.scope)
      -- 4 is the list containing all scopes but the input scope (i.e. the noalias)
      -- 5 + 3 * k is the scope of the kth Out or Mut buffer
      -- 6 + 3 * k is the list containing only this scope
      -- 7 + 3 * k is the list containing all other scopes,
      --   i.e. the noalias list of the kth Out or Mut buffer
      
      let allScopes = [ LLVM.MetadataNodeID (2 + 3 * fromIntegral k) | k <- [0 .. mutOutCount + 1] ]
      _ <- addMetadata (\_ -> map (Just . MetadataNodeOperand . MetadataNodeReference) allScopes)
      forM_ allScopes $ \scope -> do
        -- scope
        scope' <- addMetadata (\s -> [Just $ MetadataNodeOperand $ MetadataNodeReference s, Just $ MetadataNodeOperand $ MetadataNodeReference domain])
        when (scope /= scope') $
          internalError "Index of scope does not match"
        -- alias.scope
        _ <- addMetadata (\_ -> [Just $ MetadataNodeOperand $ MetadataNodeReference scope])
        -- noalias list
        _ <- addMetadata (\_ -> map (Just . MetadataNodeOperand . MetadataNodeReference) $ filter (/= scope) allScopes)
        return ()

      gen
    , gamma)
  where
    envTp = StructPrimType False $ envType environment
    operandEnv = LocalReference (PrimType (PtrPrimType envTp defaultAddrSpace)) "env"
    go :: (forall t. TupleIdx (MarshalEnv env') t -> TupleIdx (MarshalEnv env) t)
       -> Env AccessGroundR env'
       -> ( CodeGen arch () -- Gets names of scopes as argument
          , Gamma env'
          , Int -- Next fresh scalar variable index
          , Int -- Next fresh buffer variable index
          , Int -- Next fresh index for an Out or Mut argument (i.e. the number of Out and Mut arguments so far)
          )
    go _ Empty = (return (), Empty, 0, 0, 0)
    go toTupleIdx (Push env (AccessGroundRscalar tp))
      | Refl <- marshalScalarArg tp = 
        ( instr_ (downcast $
            namePtr := GetStructElementPtr (ScalarPrimType tp) operandEnv (toTupleIdx $ TupleIdxRight TupleIdxSelf)
          )
          >> instr_ (downcast $
            name := Load tp NonVolatile operandPtr
          )
          >> codegen
        , gamma `Push` GroundOperandParam operand
        , freshScalar + 1
        , freshBuffer
        , mutOutCount
        )
      where
        (codegen, gamma, freshScalar, freshBuffer, mutOutCount) = go (toTupleIdx . TupleIdxLeft) env
        operand = LocalReference (PrimType $ ScalarPrimType tp) name
        operandPtr = LocalReference (PrimType $ PtrPrimType (ScalarPrimType tp) defaultAddrSpace) namePtr
        name = fromString $ "param." ++ show freshScalar
        namePtr = fromString $ "param." ++ show freshScalar ++ ".ptr"
    go toTupleIdx (Push env (AccessGroundRbuffer m (tp :: ScalarType t))) =
      ( instr_ (downcast $
          namePtr := GetStructElementPtr ptrType operandEnv (toTupleIdx $ TupleIdxRight TupleIdxSelf)
        )
        >> instr_ (downcast $
          name := LoadPtr NonVolatile operandPtr
        )
        >> annotation
        >> codegen
      , gamma `Push` GroundOperandBuffer irbuffer
      , freshScalar
      , freshBuffer + 1
      , mutOutCount'
      )
      where
        (codegen, gamma, freshScalar, freshBuffer, mutOutCount) = go (toTupleIdx . TupleIdxLeft) env
        operand = LocalReference (PrimType ptrType) name
        operandPtr = LocalReference (PrimType $ PtrPrimType ptrType defaultAddrSpace) namePtr
        prefix = case m of
          In  -> "in."
          Out -> "out."
          Mut -> "mut."
        name' = prefix ++ show freshBuffer
        name = fromString name'
        namePtr = fromString $ prefix ++ show freshBuffer ++ ".ptr"
        irbuffer :: IRBuffer t
        irbuffer = IRBuffer operand defaultAddrSpace NonVolatile IRBufferScopeArray alias
        ptrType :: PrimType (MarshalArg (Buffer t))
        ptrType = case tp of
          SingleScalarType t
            | SingleArrayDict <- singleArrayDict t -> PtrPrimType (ScalarPrimType tp) defaultAddrSpace
          VectorScalarType (VectorType _ t) -> PtrPrimType (ScalarPrimType $ SingleScalarType t) defaultAddrSpace

        mutOutCount'
          | In <- m = mutOutCount
          | otherwise = mutOutCount + 1

        alias
          | In <- m = Just (LLVM.MetadataNodeID 3, LLVM.MetadataNodeID 4)
          | otherwise = Just (LLVM.MetadataNodeID $ fromIntegral mutOutCount' * 3 + 6, LLVM.MetadataNodeID $ fromIntegral mutOutCount' * 3 + 7)

        annotation :: CodeGen arch ()
        annotation
          | In <- m = do
            _ <- call'
              (lamUnnamed (primType @Int64)
                $ lamUnnamed (primType @(Ptr Word8))
                $ LLVM.Body (PrimType (primType @(Ptr Word8))) Nothing (Label "llvm.invariant.start.p0")) 
              -- Note: we use 'name' as a Word8 pointer here, instead of a pointer to 'tp'.
              -- This is allowed, as LLVM now has a single concrete pointer type,
              -- instead of a parameterized pointer type.
              ( ArgumentsCons (scalar scalarType (-1)) []
                $ ArgumentsCons (LocalReference type' $ fromString name') [ParameterAttribute.NoCapture] ArgumentsNil)
              []
            return ()
          | otherwise = return ()

marshalScalarArg :: ScalarType t -> t :~: MarshalArg t
-- Pattern match to prove that 't' is not a buffer
marshalScalarArg (VectorScalarType _) = Refl
marshalScalarArg (SingleScalarType (NumSingleType (IntegralNumType tp))) = case tp of
  TypeInt    -> Refl
  TypeInt8   -> Refl
  TypeInt16  -> Refl
  TypeInt32  -> Refl
  TypeInt64  -> Refl
  TypeWord   -> Refl
  TypeWord8  -> Refl
  TypeWord16 -> Refl
  TypeWord32 -> Refl
  TypeWord64 -> Refl
marshalScalarArg (SingleScalarType (NumSingleType (FloatingNumType tp))) = case tp of
  TypeHalf   -> Refl
  TypeFloat  -> Refl
  TypeDouble -> Refl
