{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE ImpredicativeTypes   #-}
{-# LANGUAGE LambdaCase           #-}
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
  , MarshalArg, MarshalFun, MarshalEnv
  , marshalScalarArg
  -- , scalarParameter, ptrParameter
  , marshalFunResultUnit
  , bindEnvFromStruct, bindEnvArgs, envStructType
  , Envs(..), initEnv, bindLocals, bindLocalsInTile
  , envsGamma, envsPrjBuffer, envsPrjParameter
  , envsPrjParameters, envsPrjSh, envsPrjIndex, envsPrjIndices
  , parallelIterSize
  , sizeOfEnv
  )
  where

import Data.String

import Data.Array.Accelerate.AST.Environment                    hiding ( Val, prj )
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Partitioned                    hiding ( Label )
import Data.Array.Accelerate.AST.Idx                            ( Idx )
import Data.Array.Accelerate.AST.Kernel
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

import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Function                                   as LLVM
import LLVM.AST.Type.Global
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Metadata
import LLVM.AST.Type.Name
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation

import GHC.Stack
import Data.Bits
import Data.Typeable
import Data.Foldable
import Control.Monad
import Foreign.Storable

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
  -- Whether the iteration at the current loop depth is the first iteration of
  -- the loop If this is in a tile loop, this says if this is the first
  -- iteration of that tile loop.
  , envsIsFirst :: Operands Bool
  -- Whether the loop at the current loop depth is descending
  -- (iterating from high indices to low indices)
  , envsDescending :: Bool
  , envsShardIdx :: Maybe (Operand Word64)
  }

initEnv
  :: forall env env' idxEnv sh local.
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
    loops _ _ _ _ = internalError "Tuple mismatch"

bindLocals :: LoopDepth -> Envs env idxEnv -> CodeGen target (Envs env idxEnv)
bindLocals depth = \envs -> foldlM go envs $ envsLocal envs
  where
    go :: Envs env idxEnv -> EnvBinding LocalBufferR env -> CodeGen target (Envs env idxEnv)
    go envs (EnvBinding idx (LocalBufferR tp depth'))
      | depth /= depth' = return envs
      | Just _ <- prjPartial idx (envsGround envs) = return envs -- Already bound
      | otherwise = do
        -- Introduce a new mutable variable on the stack
        ptr <- hoistAlloca $ ScalarPrimType tp
        ptr' <- instr' $ PtrCast (PtrPrimType (ScalarPrimType tp) defaultAddrSpace) ptr
        let value = IRBuffer ptr' defaultAddrSpace NonVolatile IRBufferScopeSingle Nothing
        return envs{ envsGround = partialUpdate (GroundOperandBuffer value) idx $ envsGround envs }

bindLocalsInTile
  :: forall target env idxEnv.
     (forall t. Idx env (Buffer t) -> Bool)
  -> LoopDepth -> Int -> Envs env idxEnv -> CodeGen target (Envs env idxEnv)
bindLocalsInTile needsTileArray depth tileSize = \envs -> foldlM go envs $ envsLocal envs
  where
    go :: Envs env idxEnv -> EnvBinding LocalBufferR env -> CodeGen target (Envs env idxEnv)
    go envs (EnvBinding idx (LocalBufferR tp depth'))
      | depth /= depth' = return envs
      | Just _ <- prjPartial idx (envsGround envs) = return envs -- Already bound
      | not (needsTileArray idx) = return envs
      | otherwise = do
        -- Introduce a new mutable variable on the stack
        ptr <- hoistAlloca $ ArrayPrimType (fromIntegral tileSize) (ScalarPrimType tp)
        ptr' <- instr' $ PtrCast (PtrPrimType (ScalarPrimType tp) defaultAddrSpace) ptr
        let value = IRBuffer ptr' defaultAddrSpace NonVolatile IRBufferScopeTile Nothing
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

arraySize :: HasCallStack => Arg genv (m sh e) -> Envs genv idxEnv -> Operands sh
arraySize (ArgArray _ (ArrayR shr _) sh _) = envsPrjParameters $ shapeExpVars shr sh

type family MarshalArg a where
  MarshalArg (Buffer e) = Ptr e
  MarshalArg e = e

-- | Converts a typed environment into a function type.
-- For instance, (((), Int), Float) is converted to Float -> Int -> ().
-- This is in reverse order to make it easier to work with this type family.
-- Otherwise we would need an accumulating type argument.
--
type family MarshalFun env where
  MarshalFun () = ()
  MarshalFun (env, t) = MarshalArg t -> MarshalFun env

type family MarshalEnv env where
  MarshalEnv (env, t) = (MarshalEnv env, MarshalArg t)
  MarshalEnv ()       = ()

marshalFunResultUnit :: Env AccessGroundR env -> Result (MarshalFun env) :~: ()
marshalFunResultUnit Empty = Refl
marshalFunResultUnit (Push env _) = marshalFunResultUnit env

bindEnvArgs
  :: forall arch env. Env AccessGroundR env
  -> ( forall k. (LLVM.Function k () -> LLVM.Function k (MarshalFun env))
     , CodeGen arch ()
     , Gamma env
     )
bindEnvArgs environment =
  let
    (args, gen, gamma, _, _, mutOutCount) = go environment
  in
    ( args
    , do
      declareAliasScopes mutOutCount
      gen
    , gamma)
  where
    go
      :: Env AccessGroundR env'
      ->
        ( forall k. LLVM.Function k () -> LLVM.Function k (MarshalFun env')
        , CodeGen arch ()
        , Gamma env'
        , Int -- Next fresh scalar variable index
        , Int -- Next fresh buffer variable index
        , Int -- Next fresh index for an Out or Mut argument (i.e. the number of Out and Mut arguments so far)
        )
    go Empty = (id, return (), Empty, 0, 0, 0)
    go (Push env (AccessGroundRscalar tp))
      | Refl <- marshalScalarArg tp
      , (bnd, codegen, gamma, freshScalar, freshBuffer, mutOutCount) <- go env
      , name <- fromString $ "param." ++ show freshScalar
      , operand <- LocalReference (PrimType $ ScalarPrimType tp) name
      = ( LLVM.Lam (ScalarPrimType tp) name . bnd
        , codegen
        , gamma `Push` GroundOperandParam operand
        , freshScalar + 1
        , freshBuffer
        , mutOutCount)
    go (Push env (AccessGroundRbuffer m tp)) =
      ( LLVM.Lam ptrType name . bnd
      , annotation >> codegen
      , gamma `Push` GroundOperandBuffer irbuffer
      , freshScalar
      , freshBuffer + 1
      , mutOutCount'
      )
      where
        (bnd, codegen, gamma, freshScalar, freshBuffer, mutOutCount) = go env
        operand = LocalReference (PrimType ptrType) name
        prefix = case m of
          In  -> "in."
          Out -> "out."
          Mut -> "mut."
        name' = prefix ++ show freshBuffer
        name = fromString name'
        irbuffer = IRBuffer operand defaultAddrSpace NonVolatile IRBufferScopeArray alias
        ptrType = PtrPrimType (ScalarPrimType tp) defaultAddrSpace

        mutOutCount'
          | In <- m = mutOutCount
          | otherwise = mutOutCount + 1

        alias
          | In <- m = Just (3, 4)
          | otherwise = Just ( fromIntegral mutOutCount' * 3 + 6,  fromIntegral mutOutCount' * 3 + 7)

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
                $ ArgumentsCons (LocalReference type' $ fromString name') [{- ParameterAttribute.NoCapture -}] ArgumentsNil)
              []
            return ()
          | otherwise = return ()

declareAliasScopes :: Int -> CodeGen arch ()
declareAliasScopes mutOutCount = do
  -- Declare domain for alias annotations
  domain <- addMetadata (\d -> [Just $ MetadataNodeOperand $ MetadataNodeReference d])
  when (domain /= 0) $
    internalError "bindEnvFromStruct assumes this is the first place where metadata nodes are created"

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
  
  let allScopes = [ 2 + 3 * fromIntegral k | k <- [0 .. mutOutCount + 1] ]
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

envStructType :: Env AccessGroundR env -> TupR PrimType (MarshalEnv env)
envStructType Empty = TupRunit
envStructType (Push env (AccessGroundRscalar tp))
  | Refl <- marshalScalarArg tp = envStructType env `TupRpair` TupRsingle (ScalarPrimType tp)
envStructType (Push env (AccessGroundRbuffer _ tp))
  = envStructType env `TupRpair` TupRsingle (PtrPrimType (ScalarPrimType tp) defaultAddrSpace)

bindEnvFromStruct
  :: forall arch env. Env AccessGroundR env
  -> ( PrimType (Struct (MarshalEnv env))
     , CodeGen arch ()
     , Gamma env
     )
bindEnvFromStruct environment =
  let (gen, gamma, _, _, mutOutCount) = go id environment
  in
    ( envTp
    , do
      declareAliasScopes mutOutCount
      gen
    , gamma)
  where
    envTp = StructPrimType False $ envStructType environment
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
            namePtr := GetElementPtr (gepStruct (ScalarPrimType tp) operandEnv $ toTupleIdx $ TupleIdxRight TupleIdxSelf)
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
          namePtr := GetElementPtr (gepStruct ptrType operandEnv $ toTupleIdx $ TupleIdxRight TupleIdxSelf)
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
        ptrType = PtrPrimType (ScalarPrimType tp) defaultAddrSpace

        mutOutCount'
          | In <- m = mutOutCount
          | otherwise = mutOutCount + 1

        alias
          | In <- m = Just (3, 4)
          | otherwise = Just ( fromIntegral mutOutCount' * 3 + 6,  fromIntegral mutOutCount' * 3 + 7)

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
                $ ArgumentsCons (LocalReference type' $ fromString name') [{- ParameterAttribute.NoCapture -}] ArgumentsNil)
              []
            return ()
          | otherwise = return ()

sizeOfEnv :: KernelFun kernel f -> Int
sizeOfEnv = sizeOfEnv' 0

sizeOfEnv' :: Int -> OpenKernelFun kernel env f -> Int
sizeOfEnv' cursor (KernelFunLam argR fun)
  | (align, size) <- alignmentAndSizeOfArgument argR
  = sizeOfEnv' (makeIntAligned cursor align + size) fun
sizeOfEnv' cursor (KernelFunBody _) = cursor

alignmentAndSizeOfArgument :: forall s t. KernelArgR s t -> (Int, Int)
alignmentAndSizeOfArgument = \case
  KernelArgRbuffer _ _ -> go @(Ptr ())
  KernelArgRscalar (SingleScalarType tp)
    | SingleDict <- singleDict tp -> go @t
  KernelArgRscalar (VectorScalarType (VectorType n (tp :: SingleType u)))
    | SingleDict <- singleDict tp
    , (align, size) <- go @u
    -> (align, n * size)
  where
    go :: forall a. Storable a => (Int, Int)
    go = (alignment (undefined :: a), sizeOf (undefined :: a))

makeIntAligned :: Int -> Int -> Int
makeIntAligned cursor align = cursor + m
  where
    m = (-cursor) `mod` align

-- Rounds a number up to the next power of 2
nextPowerOfTwo :: Int -> Int
nextPowerOfTwo x = 1 `shiftL` (finiteBitSize (0 :: Int) - countLeadingZeros (x - 1))

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
