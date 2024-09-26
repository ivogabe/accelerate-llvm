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

module Data.Array.Accelerate.LLVM.Native.Link.Schedule (
  linkSchedule, NativeProgram(..), unsafeGetPtrFromLifetimeFunPtr
) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet ( IdxSet )
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Lifetime
import Data.Array.Accelerate.Analysis.Match ((:~:)(..))
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.Compile.Cache ( UID )
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.Native.Target
import Data.Array.Accelerate.LLVM.Native.Kernel
import Data.Array.Accelerate.LLVM.Native.Compile
import Data.Array.Accelerate.LLVM.Native.State
import Data.Array.Accelerate.LLVM.Native.Link
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.Error

import LLVM.AST.Type.Representation
import LLVM.AST.Type.Downcast
import qualified LLVM.AST.Type.Function as LLVM
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Name
import LLVM.AST.Type.AddrSpace

import Control.Concurrent
import Data.String
import Foreign.Ptr
import Foreign.Storable
import System.IO.Unsafe ( unsafePerformIO )

data NativeProgram = NativeProgram
  !(Lifetime (FunPtr (Ptr Int8 -> Ptr Int8 -> Int32 -> ())))
  !Int -- The size of the program structure.
  !(Ptr Int8 -> IO ()) -- The IO action to fill the imports part of a program structure,
  !Int -- The offset of the data in the program structure.

linkSchedule :: UID -> UniformScheduleFun NativeKernel () t -> NativeProgram
linkSchedule uid schedule = unsafePerformIO $ evalLLVM defaultTarget $ linkSchedule' uid schedule

linkSchedule' :: UID -> UniformScheduleFun NativeKernel () t -> LLVM Native NativeProgram
linkSchedule' uid schedule
  | (sz, offset, prepInput, body) <- codegenSchedule schedule
  = do
    let ptrTp = PtrPrimType (ScalarPrimType scalarType) defaultAddrSpace

    let name = fromString $ "schedule_" ++ show uid
    m <- codeGenFunction name VoidType
        (LLVM.Lam ptrTp "workers" . LLVM.Lam ptrTp "program" . LLVM.Lam (primType @Int32) "location")
        body

    obj <- compile uid name m
    fun <- link obj
    return $ NativeProgram fun sz prepInput offset

unsafeGetPtrFromLifetimeFunPtr :: Lifetime (FunPtr f) -> Ptr f
unsafeGetPtrFromLifetimeFunPtr lifetime = unsafePerformIO $ do
  _ <- forkIO $ do
    threadDelay (365 * 24 * 60 * 60 * 1000000)
    touchLifetime lifetime
  return $ castFunPtrToPtr $ unsafeGetValue lifetime

programType :: PrimType imports -> PrimType state -> PrimType (Struct (((Int64, Ptr Int8), imports), state))
programType importsTp stateTp = StructPrimType False $
  TupRsingle primType
  `TupRpair` TupRsingle primType
  `TupRpair` TupRsingle importsTp
  `TupRpair` TupRsingle stateTp

-- Here we use that imports only contains pointers, and that the cursor is already pointer aligned
prepareInput :: TupR PrimType imports -> TupR IO imports -> Ptr Int8 -> Int -> IO Int
prepareInput TupRunit TupRunit _ cursor = return cursor
prepareInput (TupRpair t1 t2) (TupRpair i1 i2) ptr cursor = prepareInput t1 i1 ptr cursor >>= prepareInput t2 i2 ptr
prepareInput (TupRsingle tp) (TupRsingle io) ptr cursor = case tp of
  PtrPrimType _ _ -> do
    value <- io
    poke (plusPtr ptr cursor) value
    return $ cursor + sizeOf (1 :: Int)
  _ -> internalError "Unexpected type in imports of program"

codegenSchedule :: forall t. UniformScheduleFun NativeKernel () t -> (Int, Int, Ptr Int8 -> IO (), CodeGen Native ())
codegenSchedule schedule
  | Exists2 schedule1 <- convertFun schedule =
    ( fst $ primSizeAlignment $ programType
      (StructPrimType False $ importsType schedule1)
      (StructPrimType False $ stateType schedule1)
    , makeAligned
        (2 * (sizeOf (1 :: Int))
          + fst (primSizeAlignment $ StructPrimType False $ importsType schedule1))
        (snd $ primSizeAlignment $ StructPrimType False $ stateType schedule1)
    , \ptr -> do
        prepareInput (importsType schedule1) (importsInit schedule1) ptr (2 * sizeOf (1 :: Int))
        return ()
    , do
        -- Add 2 for the initial block and the destructor block
        let blocks = blockCount schedule1 + 2

        typedef "kernel_t" $ Just $ downcast $ StructPrimType False $ TupRsingle $ primType @Int8

        -- Contains pointers of all used kernel functions and constant buffers.
        -- Instead of relying on the linker, we provide pointers to these functions
        -- and buffers via this structure.
        typedef "imports_t" $ Just $ downcast $ StructPrimType False $ importsType schedule1
        let importsTp = NamedPrimType "imports_t" $ StructPrimType False $ importsType schedule1
        let ptrImportsTp = PtrPrimType importsTp defaultAddrSpace

        -- Contains the part of the state of this function that needs to be
        -- preserved when the function suspends, and the arguments to kernels.
        typedef "state_t" $ Just $ downcast $ StructPrimType False $ stateType schedule1
        let stateTp = NamedPrimType "state_t" $ StructPrimType False $ stateType schedule1
        let ptrStateTp = PtrPrimType stateTp defaultAddrSpace

        -- The program has type (i64, ptr, imports_t, state_t)
        let dataTp = programType importsTp stateTp
        let ptrDataTp = PtrPrimType dataTp defaultAddrSpace

        -- Step over the reference count and function pointer (16 bytes)
        dataPtr <- instr' $ PtrCast ptrDataTp operandProgram
        instr_ $ downcast $ "imports" := GetStructElementPtr importsTp dataPtr (TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
        instr_ $ downcast $ "state" := GetStructElementPtr stateTp dataPtr (TupleIdxRight TupleIdxSelf)

        _ <- switch
          (ir scalarType operandLocation)
          (newBlockNamed $ blockName 0)
          [(fromIntegral i, newBlockNamed $ blockName i) | i <- [1 .. blocks - 1]]

        -- Initial block
        let block0 = newBlockNamed $ blockName 0
        setBlock block0
        phase2 schedule1
          (LocalReference (PrimType ptrImportsTp) "imports")
          (LocalReference (PrimType ptrStateTp) "state")
          PEnd PEnd TupleIdxSelf TupleIdxSelf 2

        -- Destructor block
        let block1 = newBlockNamed $ blockName 1
        setBlock block1
        -- TODO: Add code that releases any held buffers
        return_

        -- Return block (for any branch that may return, for instance in SignalAwait)
        let blockRet = newBlockNamed "return"
        setBlock blockRet
        return_
    )

operandWorkers :: Operand (Ptr Int8)
operandWorkers = LocalReference type' "workers"

operandProgram :: Operand (Ptr Int8)
operandProgram = LocalReference type' "program"

operandLocation :: Operand (Int32)
operandLocation = LocalReference type' "location"

-- Kernels are actually functions, but to simplify the code generation here, we just use an untyped pointer.
-- To separate pointers to buffers from pointer to kernels however, we introduce this type.
kernelTp :: PrimType (Ptr (Struct Int8))
kernelTp = PtrPrimType (NamedPrimType "kernel_t" $ StructPrimType False $ TupRsingle primType) defaultAddrSpace

typeSignalWaiter :: PrimType (Struct (Ptr Int8, (Int32, Ptr Int8)))
typeSignalWaiter = StructPrimType False $ TupRpair (TupRsingle primType) $ TupRpair (TupRsingle primType) (TupRsingle primType)

type family ReprBaseR t where
  ReprBaseR Signal = Word
  ReprBaseR SignalResolver = Word
  ReprBaseR (Ref t) = ReprBaseR t
  ReprBaseR (OutputRef t) = ReprBaseR t
  ReprBaseR (Buffer t) = Ptr t
  ReprBaseR t = t

-- Note: we store the code to get access to a value here (in the CodeGen monad)
-- instead of only the operand.
-- This variable may be accessed in a different block than were it was defined,
-- and is not in scope there. This is due to the generator-style definition
-- of the generated code.
data StructVar t = StructVar
  -- Whether this is an input or output of the program.
  -- i.e., whether this is bound by an Slam of the toplevel program.
  !Bool
  !(CodeGen Native (Operand (Ptr (ReprBaseR t))))
type StructVars = PartialEnv StructVar
newtype LocalVar t = LocalVar (Operand (ReprBaseR t))
type LocalVars = PartialEnv LocalVar

data Exists2 f where
  Exists2 :: f a b -> Exists2 f

data Phase1 env imports state where
  Phase1 :: {
    blockCount :: Int,
    importsType :: TupR PrimType imports,
    importsInit :: TupR IO imports,
    stateType :: TupR PrimType state,
    varsFree :: IdxSet env,
    varsInStruct :: IdxSet env,
    maySuspend :: Bool,
    phase2 :: Phase2 env imports state
  } -> Phase1 env imports state

type Phase2 env imports state
  = forall fullImports fullState.
     Operand (Ptr (Struct fullImports))
  -> Operand (Ptr (Struct fullState))
  -- The environment for the used variables
  -> StructVars env
  -> LocalVars env
  -> TupleIdx fullImports imports
  -> TupleIdx fullState state
  -- The index of the next block index
  -> Int
  -> CodeGen Native ()

convertFun :: forall env t. UniformScheduleFun NativeKernel env t -> Exists2 (Phase1 env)
convertFun (Slam (LeftHandSideWildcard _) fun) = convertFun fun
convertFun (Slam (LeftHandSidePair lhs1 lhs2) fun)
  = convertFun (Slam lhs1 $ Slam lhs2 fun)
convertFun (Slam (LeftHandSideSingle tp) fun)
  | Exists2 fun1 <- convertFun fun =
  Exists2 $ Phase1{
    blockCount = blockCount fun1,
    importsType = importsType fun1,
    importsInit = importsInit fun1,
    stateType = TupRsingle tp' `TupRpair` stateType fun1,
    varsFree = IdxSet.drop $ varsFree fun1,
    varsInStruct = IdxSet.drop $ varsInStruct fun1,
    maySuspend = maySuspend fun1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock ->
      let getPtr' = instr' $ GetStructElementPtr tp' fullState (tupleLeft stateIdx)
      in phase2 fun1 imports fullState (structVars `PPush` StructVar True getPtr') (PNone localVars) importsIdx (tupleRight stateIdx) nextBlock
  }
  where
    tp' = toPrimType tp
convertFun (Sbody body) = convert body

convert :: forall env. UniformSchedule NativeKernel env -> Exists2 (Phase1 env)
convert Return =
  Exists2 Phase1{
    blockCount = 0,
    importsType = TupRunit,
    importsInit = TupRunit,
    stateType = TupRunit,
    varsFree = IdxSet.empty,
    varsInStruct = IdxSet.empty,
    maySuspend = False,
    phase2 = \_ _ _ _ _ _ _ -> return_
  }
-- convert (Spawn (Effect (SignalAwait signals) a) b)
convert (Spawn a b)
  | Exists2 a1 <- convert a
  , Exists2 b1 <- convert b =
  Exists2 $ Phase1{
    -- We need one block here, and any blocks that the subterms need
    blockCount = blockCount a1 + blockCount b1 + 1,
    importsType = importsType a1 `TupRpair` importsType b1,
    importsInit = importsInit a1 `TupRpair` importsInit b1,
    stateType = stateType a1 `TupRpair` stateType b1,
    varsFree = varsFree a1 `IdxSet.union` varsFree b1,
    -- All free variables of a1 must be stored in the state structure,
    -- since 'a' is invoked via a separate function call.
    varsInStruct = varsFree a1 `IdxSet.union` varsInStruct b1,
    maySuspend = maySuspend b1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      _ <- call (LLVM.lamUnnamed primType $ LLVM.lamUnnamed primType $ LLVM.lamUnnamed primType $ LLVM.Body VoidType Nothing (Label "accelerate_schedule")) 
        (LLVM.ArgumentsCons operandWorkers []
          $ LLVM.ArgumentsCons operandProgram []
          $ LLVM.ArgumentsCons (integral TypeWord32 $ fromIntegral $ nextBlock + blockCount b1) []
          LLVM.ArgumentsNil)
        []
      phase2 b1 imports fullState
        (IdxSet.partialEnvFilterSet (varsFree b1) structVars)
        (IdxSet.partialEnvFilterSet (varsFree b1) localVars)
        (tupleRight importsIdx)
        (tupleRight stateIdx)
        nextBlock

      let aBlock = newBlockNamed $ blockName (nextBlock + blockCount b1)
      setBlock aBlock
      phase2 a1 imports fullState
        (IdxSet.partialEnvFilterSet (varsFree a1) structVars)
        PEnd
        (tupleLeft importsIdx)
        (tupleLeft stateIdx)
        (nextBlock + blockCount b1 + 1)
  }
-- Control flow
convert (Acond cond whenTrue whenFalse next)
  | Exists2 whenTrue1 <- convert whenTrue
  , Exists2 whenFalse1 <- convert whenFalse
  , Exists2 next1 <- convert next
  , branchMaySuspend <- maySuspend whenTrue1 || maySuspend whenFalse1 =
  Exists2 $ Phase1{
    blockCount = blockCount whenTrue1 + blockCount whenFalse1 + blockCount next1,
    importsType = (importsType whenTrue1 `TupRpair` importsType whenFalse1) `TupRpair` importsType next1,
    importsInit = (importsInit whenTrue1 `TupRpair` importsInit whenFalse1) `TupRpair` importsInit next1,
    stateType = (stateType whenTrue1 `TupRpair` stateType whenFalse1) `TupRpair` stateType next1,
    varsFree = IdxSet.insertVar cond $ varsFree whenTrue1 `IdxSet.union` varsFree whenFalse1 `IdxSet.union` varsFree next1,
    varsInStruct =
      if branchMaySuspend then
        -- Place all free variables of 'next' in the state structure, as the true and/or false branch may suspend.
        varsInStruct whenTrue1 `IdxSet.union` varsInStruct whenFalse1 `IdxSet.union` varsFree next1
      else
        -- No need to place extra things in the state structure.
        varsInStruct whenTrue1 `IdxSet.union` varsInStruct whenFalse1 `IdxSet.union` varsInStruct next1,
    maySuspend = branchMaySuspend || maySuspend next1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      (localVars', cond') <- getValue structVars localVars (GroundRscalar scalarTypeWord8) (varIdx cond)
      cond'' <- instr $ IntToBool TypeWord8 cond'
      blockTrue <- newBlock "acond.true"
      blockFalse <- newBlock "acond.false"
      blockExit <- newBlock "acond.next"
      _  <- cbr cond'' blockTrue blockFalse

      setBlock blockTrue
      phase2 whenTrue1 imports fullState structVars localVars'
        (tupleLeft $ tupleLeft importsIdx)
        (tupleLeft $ tupleLeft stateIdx)
        nextBlock
      _ <- br blockExit

      setBlock blockFalse
      phase2 whenFalse1 imports fullState structVars localVars'
        (tupleRight $ tupleLeft importsIdx)
        (tupleRight $ tupleLeft stateIdx)
        (nextBlock + blockCount whenTrue1)
      _ <- br blockExit

      setBlock blockExit
      phase2 next1 imports fullState structVars
        -- If the true or false branch may suspend, then we cannot use values from localVars.
        -- Instead they must be read from structVars.
        -- Hence we also include all free variables of 'next' in varsInStruct if 'branchMaySuspend'.
        (if branchMaySuspend then PEnd else localVars')
        (tupleRight importsIdx)
        (tupleRight stateIdx)
        (nextBlock + blockCount whenTrue1 + blockCount whenFalse1)
  }
-- TODO: Awhile
-- Effects
convert (Effect effect@(Exec _ kernel kargs) next)
  | Exists2 next1 <- convert next
  , (argsTp, argsTp') <- kernelArgsTp kargs =
  Exists2 $ Phase1{
    blockCount = blockCount next1 + 1,
    importsType = TupRsingle (PtrPrimType (primType @Int8) defaultAddrSpace) `TupRpair` importsType next1,
    importsInit = TupRsingle (veryUnsafeGetFunPtr kernel) `TupRpair` importsInit next1,
    stateType = TupRsingle argsTp `TupRpair` stateType next1,
    varsFree = varsFree next1 `IdxSet.union` effectFreeVars effect,
    varsInStruct = varsFree next1,
    maySuspend = True,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      let blockNext = newBlockNamed $ blockName nextBlock
      args <- instr' $ GetStructElementPtr argsTp fullState (tupleLeft stateIdx)

      -- Fill arguments struct
      -- Header
      workFnPtr' <- instr' $ GetStructElementPtr primType imports (tupleLeft importsIdx)
      workFn <- instr' $ LoadPtr NonVolatile workFnPtr'
      workFnPtr <- instr' $ GetStructElementPtr primType args (TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft TupleIdxSelf)
      _ <- instr' $ Store NonVolatile workFnPtr workFn
      programPtr <- instr' $ GetStructElementPtr primType args (TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      _ <- instr' $ Store NonVolatile programPtr operandProgram
      locationPtr <- instr' $ GetStructElementPtr primType args (TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      _ <- instr' $ Store NonVolatile locationPtr (integral TypeWord32 $ fromIntegral nextBlock)
      threadsPtr <- instr' $ GetStructElementPtr primType args (TupleIdxLeft $ TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      _ <- instr' $ Store NonVolatile threadsPtr (integral TypeWord32 1)
      workIdxPtr <- instr' $ GetStructElementPtr primType args (TupleIdxLeft $ TupleIdxRight TupleIdxSelf)
      _ <- instr' $ Store NonVolatile workIdxPtr (integral TypeWord32 0)
      -- Arguments
      args' <- instr' $ GetStructElementPtr argsTp' args $ TupleIdxRight TupleIdxSelf
      storeKernelArgs structVars localVars kargs args' TupleIdxSelf

      -- Call runtime function to launch kernel
      _ <- call
            (LLVM.lamUnnamed primType $
              LLVM.lamUnnamed (PtrPrimType argsTp defaultAddrSpace) $
              LLVM.Body VoidType Nothing (Label "accelerate_execute_kernel")) 
            (LLVM.ArgumentsCons operandWorkers []
              $ LLVM.ArgumentsCons args []
              LLVM.ArgumentsNil)
            []
      -- Function suspends now
      return_
      -- and resumes here
      setBlock blockNext
      phase2 next1 imports fullState structVars PEnd (tupleRight importsIdx) (tupleRight stateIdx) (nextBlock + 1)
  }

convert (Effect (SignalAwait []) next) = convert next
convert (Effect (SignalAwait signals) next)
  | Exists2 next1 <- convert next
  , signalsSet <- IdxSet.fromList' signals =
  Exists2 $ Phase1{
    blockCount = blockCount next1 + 1,
    importsType = importsType next1,
    importsInit = importsInit next1,
    stateType = TupRpair (TupRsingle typeSignalWaiter) $ stateType next1,
    varsFree = varsFree next1 `IdxSet.union` signalsSet,
    -- All free vars must be placed in the struct, since the function may be suspended.
    varsInStruct = varsFree next1 `IdxSet.union` signalsSet,
    maySuspend = True,
    phase2 = \imports fullState structVars _ importsIdx stateIdx nextBlock -> do
      let blockNext = newBlockNamed $ blockName nextBlock
      let blockAwait = newBlockNamed "return"
      waiter <- instr' $ GetStructElementPtr typeSignalWaiter fullState (tupleLeft stateIdx)
      -- For await [a, b, c, d], we generate the following code:
      -- if accelerate_schedule_after_or(workers, program, nextBlock, a, waiter) return;
      -- nextBlock:
      -- if accelerate_schedule_after_or(workers, program, nextBlock, b, waiter) return;
      -- if accelerate_schedule_after_or(workers, program, nextBlock, c, waiter) return;
      -- if accelerate_schedule_after_or(workers, program, nextBlock, d, waiter) return;
      --
      -- Note that if 'b' is not resolved the first time nextBlock is executed,
      -- nextBlock will be executed again.
      -- This is fine: we may call accelerate_schedule_after_or again
      -- when it is resolved.
      -- Doing this reduces the number of blocks we need.
      let
        go :: Int -> [Idx env Signal] -> CodeGen Native ()
        go _ [] = return ()
        go i (idx : idxs) = do
          let blockContinue = if i == 0 then blockNext else newBlockNamed $ blockName nextBlock ++ ".continue." ++ show i
          signal <- getPtr structVars idx
          p <- call
            (LLVM.lamUnnamed primType $ LLVM.lamUnnamed primType $ LLVM.lamUnnamed primType $
              LLVM.lamUnnamed primType $ LLVM.lamUnnamed (PtrPrimType typeSignalWaiter defaultAddrSpace) $
              LLVM.Body (PrimType BoolPrimType) Nothing (Label "accelerate_schedule_after_or"))
            (LLVM.ArgumentsCons operandWorkers []
              $ LLVM.ArgumentsCons operandProgram []
              $ LLVM.ArgumentsCons (integral TypeWord32 $ fromIntegral nextBlock) []
              $ LLVM.ArgumentsCons signal []
              $ LLVM.ArgumentsCons waiter []
              LLVM.ArgumentsNil)
            []
          _ <- cbr p blockAwait blockContinue
          setBlock blockContinue
          go (i + 1) idxs

      go 0 signals

      phase2 next1 imports fullState structVars PEnd importsIdx (tupleRight stateIdx) (nextBlock + 1)
  }
convert (Effect (SignalResolve signals) next)
  | Exists2 next1 <- convert next
  , signalsSet <- IdxSet.fromList' signals =
  Exists2 $ Phase1{
    blockCount = blockCount next1,
    importsType = importsType next1,
    importsInit = importsInit next1,
    stateType = stateType next1,
    varsFree = varsFree next1 `IdxSet.union` signalsSet,
    varsInStruct = varsInStruct next1 `IdxSet.union` signalsSet,
    maySuspend = maySuspend next1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      let
        go :: [Idx env SignalResolver] -> CodeGen Native ()
        go [] = return ()
        go (idx : idxs) = case prjPartial idx structVars of
          Just (StructVar True m) -> do
            mvarPtr <- m
            mvarPtr' <- instr' $ PtrCast (PtrPrimType (primType @(Ptr Int8)) defaultAddrSpace) mvarPtr
            mvar <- instr' $ LoadPtr NonVolatile mvarPtr'
            _ <- call
              (LLVM.lamUnnamed primType $ LLVM.lamUnnamed primType $
                LLVM.Body VoidType Nothing (Label "hs_try_putmvar")) 
              (LLVM.ArgumentsCons (integral TypeInt32 $ -1) []
                $ LLVM.ArgumentsCons mvar []
                LLVM.ArgumentsNil)
              []
            go idxs
          Just (StructVar False m) -> do
            signal <- m
            _ <- call
              (LLVM.lamUnnamed primType $ LLVM.lamUnnamed primType $
                LLVM.Body VoidType Nothing (Label "accelerate_signal_resolve")) 
              (LLVM.ArgumentsCons operandWorkers []
                $ LLVM.ArgumentsCons signal []
                LLVM.ArgumentsNil)
              []
            go idxs
          Nothing -> internalError "SignalResolver missing in StructVars"
      go signals
      phase2 next1 imports fullState structVars localVars importsIdx stateIdx nextBlock
  }
convert (Effect (RefWrite ref value) next)
  | Exists2 next1 <- convert next =
  Exists2 $ Phase1{
    blockCount = blockCount next1,
    importsType = importsType next1,
    importsInit = importsInit next1,
    stateType = stateType next1,
    varsFree = IdxSet.insertVar ref $ IdxSet.insertVar value $ varsFree next1,
    varsInStruct = IdxSet.insertVar ref $ varsInStruct next1,
    maySuspend = maySuspend next1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      ref' <- getPtr structVars $ varIdx ref
      (localVars', value') <- getValue structVars localVars tp (varIdx value)
      _ <- instr' $ Store NonVolatile ref' value'
      phase2 next1 imports fullState structVars localVars' importsIdx stateIdx nextBlock
  }
  where
    tp = case varType ref of
      BaseRrefWrite t -> t
      _ -> internalError "OutputRef impossible"
-- Bindings
convert (Alet (LeftHandSideWildcard _) _ next) = convert next
-- Non-GroundR bindings: NewSignal and NewRef
-- These bindings are special, in that they define two variables,
-- which are at runtime the same variable.
-- The read-end and write-end both point to the same thing.
convert (Alet lhs (NewSignal _) next)
  | Exists2 next1 <- convert next =
  Exists2 $ Phase1{
    blockCount = blockCount next1,
    importsType = importsType next1,
    importsInit = importsInit next1,
    stateType = TupRsingle (primType :: PrimType Word) `TupRpair` stateType next1,
    varsFree = IdxSet.drop' lhs $ varsFree next1,
    varsInStruct = IdxSet.drop' lhs $ varsInStruct next1,
    maySuspend = maySuspend next1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      let getPtr' = instr' $ GetStructElementPtr primType fullState $ tupleLeft stateIdx
      ptr <- getPtr'
      _ <- instr' $ Store NonVolatile ptr $ integral TypeWord 0
      let (structVars', localVars') = pushTwoSame lhs structVars localVars getPtr'
      phase2 next1 imports fullState structVars' localVars' importsIdx (tupleRight stateIdx) nextBlock
  }
convert (Alet lhs (NewRef (GroundRscalar tp)) next)
  | Refl <- scalarReprBase tp
  , Exists2 next1 <- convert next =
  Exists2 $ Phase1{
    blockCount = blockCount next1,
    importsType = importsType next1,
    importsInit = importsInit next1,
    stateType = TupRsingle (ScalarPrimType tp) `TupRpair` stateType next1,
    varsFree = IdxSet.drop' lhs $ varsFree next1,
    varsInStruct = IdxSet.drop' lhs $ varsInStruct next1,
    maySuspend = maySuspend next1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      let getPtr' = instr' $ GetStructElementPtr (ScalarPrimType tp) fullState $ tupleLeft stateIdx
      let (structVars', localVars') = pushTwoSame lhs structVars localVars getPtr'
      phase2 next1 imports fullState structVars' localVars' importsIdx (tupleRight stateIdx) nextBlock
  }
convert (Alet lhs (NewRef (GroundRbuffer tp)) next)
  | Exists2 next1 <- convert next =
  Exists2 $ Phase1{
    blockCount = blockCount next1,
    importsType = importsType next1,
    importsInit = importsInit next1,
    stateType = TupRsingle (PtrPrimType (ScalarPrimType tp) defaultAddrSpace) `TupRpair` stateType next1,
    varsFree = IdxSet.drop' lhs $ varsFree next1,
    varsInStruct = IdxSet.drop' lhs $ varsInStruct next1,
    maySuspend = maySuspend next1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      let getPtr' = instr' $ GetStructElementPtr (PtrPrimType (ScalarPrimType tp) defaultAddrSpace) fullState $ tupleLeft stateIdx
      let (structVars', localVars') = pushTwoSame lhs structVars localVars getPtr'
      phase2 next1 imports fullState structVars' localVars' importsIdx (tupleRight stateIdx) nextBlock
  }
-- GroundR bindings
convert (Alet lhs (Alloc shr tp sz) next)
  | Refl <- scalarReprBase tp
  , Exists2 next1 <- convert next
  , Exists bnd <- pushBindingSingle lhs $ varsInStruct next1 =
  Exists2 $ Phase1{
    blockCount = blockCount next1,
    importsType = importsType next1,
    importsInit = importsInit next1,
    stateType = bStateType bnd `TupRpair` stateType next1,
    varsFree = IdxSet.insertVars sz $ IdxSet.drop' lhs $ varsFree next1,
    varsInStruct = IdxSet.drop' lhs $ varsInStruct next1,
    maySuspend = maySuspend next1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      let
        computeSize :: LocalVars env -> ShapeR sh -> ExpVars env sh -> Operand Word64 -> CodeGen Native (LocalVars env, Operand Word64)
        computeSize localVars' ShapeRz _ accum = return (localVars', accum)
        computeSize localVars' (ShapeRsnoc shr') (vs `TupRpair` TupRsingle v) accum = do
          (localVars'', value) <- getValue structVars localVars' (GroundRscalar scalarTypeInt) (varIdx v)
          -- Assumes that Int is 64-bit
          value' <- instr' $ BitCast scalarType value
          accum' <- instr' $ Mul numType accum value'
          computeSize localVars'' shr' vs accum'
        computeSize _ _ _ _ = internalError "Pair impossible"

      (localVars1, sz') <- computeSize localVars shr sz (integral TypeWord64 $ fromIntegral $ bytesElt $ TupRsingle tp)
      ptr <- call'
        (LLVM.lamUnnamed primType $
          LLVM.Body (PrimType ptrTp) Nothing (Label "accelerate_buffer_alloc"))
        (LLVM.ArgumentsCons sz' []
          LLVM.ArgumentsNil)
        []
      (structVars', localVars2) <- bPhase2 bnd structVars localVars1 fullState (tupleLeft stateIdx) ptr
      phase2 next1 imports fullState structVars' localVars2 importsIdx (tupleRight stateIdx) nextBlock
  }
  where
    ptrTp = PtrPrimType (ScalarPrimType tp) defaultAddrSpace
convert (Alet lhs (Use tp _ buffer) next)
  | Refl <- scalarReprBase tp
  , Exists2 next1 <- convert next
  , Exists bnd <- pushBindingSingle lhs $ varsInStruct next1
  , ptrTp <- PtrPrimType (ScalarPrimType tp) defaultAddrSpace =
  Exists2 $ Phase1{
    blockCount = blockCount next1,
    importsType = TupRsingle ptrTp `TupRpair` importsType next1,
    importsInit = TupRsingle (castPtr <$> bufferRetainAndGetRef buffer) `TupRpair` importsInit next1,
    stateType = bStateType bnd `TupRpair` stateType next1,
    varsFree = IdxSet.drop' lhs $ varsFree next1,
    varsInStruct = IdxSet.drop' lhs $ varsInStruct next1,
    maySuspend = maySuspend next1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      ptrPtr <- instr' $ GetStructElementPtr ptrTp imports (tupleLeft importsIdx)
      ptr <- instr' $ LoadPtr NonVolatile ptrPtr
      (structVars', localVars') <- bPhase2 bnd structVars localVars fullState (tupleLeft stateIdx) ptr
      phase2 next1 imports fullState structVars' localVars' (tupleRight importsIdx) (tupleRight stateIdx) nextBlock
  }
convert (Alet lhs (Unit (Var tp idx)) next)
  | Refl <- scalarReprBase tp
  , Exists2 next1 <- convert next
  , Exists bnd <- pushBindingSingle lhs $ varsInStruct next1 =
  Exists2 $ Phase1{
    blockCount = blockCount next1,
    importsType = importsType next1,
    importsInit = importsInit next1,
    stateType = bStateType bnd `TupRpair` stateType next1,
    varsFree = IdxSet.insert idx $ IdxSet.drop' lhs $ varsFree next1,
    varsInStruct = IdxSet.drop' lhs $ varsInStruct next1,
    maySuspend = maySuspend next1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      ptr <- call'
        (LLVM.lamUnnamed primType $
          LLVM.Body (PrimType ptrTp) Nothing (Label "accelerate_buffer_alloc"))
        (LLVM.ArgumentsCons (integral TypeWord64 $ fromIntegral $ bytesElt $ TupRsingle tp) []
          LLVM.ArgumentsNil)
        []
      (localVars', value) <- getValue structVars localVars (GroundRscalar tp) idx
      _ <- instr' $ Store NonVolatile ptr value
      (structVars', localVars'') <- bPhase2 bnd structVars localVars' fullState (tupleLeft stateIdx) ptr
      phase2 next1 imports fullState structVars' localVars'' importsIdx (tupleRight stateIdx) nextBlock
  }
  where
    ptrTp = PtrPrimType (ScalarPrimType tp) defaultAddrSpace
convert (Alet lhs (RefRead ref) next)
  | Exists2 next1 <- convert next
  , Exists bnd <- pushBindingSingle lhs (varsInStruct next1) =
  Exists2 $ Phase1{
    blockCount = blockCount next1,
    importsType = importsType next1,
    importsInit = importsInit next1,
    stateType = bStateType bnd `TupRpair` stateType next1,
    varsFree = IdxSet.insertVar ref $ IdxSet.drop' lhs $ varsFree next1,
    varsInStruct = IdxSet.insertVar ref $ IdxSet.drop' lhs $ varsInStruct next1,
    maySuspend = maySuspend next1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      (_, value) <- getValue structVars localVars tp $ varIdx ref
      (structVars', localVars') <- bPhase2 bnd structVars localVars fullState (tupleLeft stateIdx) value
      phase2 next1 imports fullState structVars' localVars' importsIdx (tupleRight stateIdx) nextBlock
  }
  where
    tp = case varType ref of
      BaseRref t -> t
      _ -> internalError "OutputRef impossible"
convert (Alet lhs (Compute expr) next)
  | Exists2 next1 <- convert next
  , Exists bnd <- pushBindings (expType expr) lhs (varsInStruct next1) =
  Exists2 $ Phase1{
    blockCount = blockCount next1,
    importsType = importsType next1,
    importsInit = importsInit next1,
    stateType = bStateType bnd `TupRpair` stateType next1,
    varsFree = bindingFreeVars (Compute expr) `IdxSet.union` IdxSet.drop' lhs (varsFree next1),
    varsInStruct = IdxSet.drop' lhs $ varsInStruct next1,
    maySuspend = maySuspend next1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      value <- llvmOfOpenExp (convertArrayInstr structVars localVars) expr Empty
      (structVars', localVars') <- bPhase2 bnd structVars localVars fullState (tupleLeft stateIdx) value
      phase2 next1 imports fullState structVars' localVars' importsIdx (tupleRight stateIdx) nextBlock
  }

convertArrayInstr
  :: StructVars env
  -> LocalVars env
  -> ArrayInstr env (s -> t1)
  -> Operands s
  -> CodeGen Native (Operands t1)
convertArrayInstr structVars localVars arr arg = case arr of
  Parameter (Var tp idx)
    | Refl <- scalarReprBase tp -> do
      (_, value) <- getValue structVars localVars (GroundRscalar tp) idx
      return $ ir tp value
  Index (Var tp idx)
    | GroundRbuffer tp' <- tp -> do
      (_, ptr) <- getValue structVars localVars tp idx
      ptr' <- instr' $ GetElementPtr tp' ptr [op scalarTypeInt arg]
      instr $ Load tp' NonVolatile ptr'
    | otherwise -> internalError "Buffer impossible"

blockName :: Int -> String
blockName 0 = "block.start"
blockName 1 = "block.destructor"
blockName idx = "block." ++ show idx

tupleLeft :: TupleIdx a (b, c) -> TupleIdx a b
tupleLeft (TupleIdxLeft  idx) = TupleIdxLeft  $ tupleLeft idx
tupleLeft (TupleIdxRight idx) = TupleIdxRight $ tupleLeft idx
tupleLeft TupleIdxSelf        = TupleIdxLeft TupleIdxSelf

tupleRight :: TupleIdx a (b, c) -> TupleIdx a c
tupleRight (TupleIdxLeft  idx) = TupleIdxLeft  $ tupleRight idx
tupleRight (TupleIdxRight idx) = TupleIdxRight $ tupleRight idx
tupleRight TupleIdxSelf        = TupleIdxRight TupleIdxSelf

getPtr :: StructVars env -> Idx env t -> CodeGen Native (Operand (Ptr (ReprBaseR t)))
getPtr env idx = case prjPartial idx env of
  Just (StructVar _ m) -> m
  Nothing -> internalError "Idx missing in StructVars."

getValue :: ReprBaseR t ~ ReprBaseR t' => StructVars env -> LocalVars env -> GroundR t -> Idx env t' -> CodeGen Native (LocalVars env, Operand (ReprBaseR t))
getValue structVars localVars groundR idx
  | Just (LocalVar operand) <- prjPartial idx localVars = return (localVars, operand)
  | Just (StructVar _ m) <- prjPartial idx structVars = do
    ptr <- m
    value <- case groundR of
      GroundRscalar tp
        | Refl <- scalarReprBase tp -> instr' $ Load tp NonVolatile ptr
      GroundRbuffer _ -> instr' $ LoadPtr NonVolatile ptr
    return (partialUpdate (LocalVar value) idx localVars, value)
  | otherwise = internalError "Idx missing in StructVars."

scalarReprBase :: ScalarType tp -> tp :~: ReprBaseR tp
scalarReprBase (VectorScalarType _) = Refl
scalarReprBase (SingleScalarType (NumSingleType (IntegralNumType tp))) = case tp of
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
scalarReprBase (SingleScalarType (NumSingleType (FloatingNumType tp))) = case tp of
  TypeHalf   -> Refl
  TypeFloat  -> Refl
  TypeDouble -> Refl

data Push1 op env env' t state where
  Push1 ::
    { bStateType :: TupR PrimType state
    , bPhase2 :: Push2 op env env' t state
    } -> Push1 op env env' t state

type Push2 op env env' t state
  = forall fullState.
     StructVars env
  -> LocalVars env
  -> Operand (Ptr (Struct fullState))
  -> TupleIdx fullState state
  -> op t
  -> CodeGen Native (StructVars env', LocalVars env')

pushBindingSingle :: BLeftHandSide t env env' -> IdxSet env' -> Exists (Push1 Operand env env' (ReprBaseR t))
pushBindingSingle (LeftHandSideWildcard _) _ = Exists $ Push1 TupRunit $
  \structVars localVars _ _ _ -> return (structVars, localVars)
pushBindingSingle (LeftHandSideSingle tp) inStruct
  | ZeroIdx `IdxSet.member` inStruct = Exists $ Push1 (TupRsingle tp') $
    \structVars localVars fullState tupleIdx value -> do
      let getPtr' = instr' $ GetStructElementPtr tp' fullState tupleIdx
      ptr <- getPtr'
      _ <- instr' $ Store NonVolatile ptr value
      return (structVars `PPush` StructVar False getPtr', localVars `PPush` LocalVar value)
  | otherwise = Exists $ Push1 TupRunit $
    \structVars localVars _ _ value -> do
      return (PNone structVars, localVars `PPush` LocalVar value)
  where
    tp' = toPrimType tp
pushBindingSingle (LeftHandSidePair _ _) _ = internalError "Expected single or no value"

pushBindings :: TypeR t -> BLeftHandSide t env env' -> IdxSet env' -> Exists (Push1 Operands env env' t)
pushBindings _ (LeftHandSideWildcard _) _ = Exists $ Push1 TupRunit $
  \structVars localVars _ _ _ -> return (structVars, localVars)
pushBindings (TupRpair t1 t2) (LeftHandSidePair lhs1 lhs2) inStruct
  | Exists x <- pushBindings t1 lhs1 $ IdxSet.drop' lhs2 inStruct
  , Exists y <- pushBindings t2 lhs2 inStruct
  = Exists $ Push1 (bStateType x `TupRpair` bStateType y) $
    \structVars localVars fullState tupleIdx value -> do
      let (valueX, valueY) = unpair value
      (structVars', localVars') <- bPhase2 x structVars localVars fullState (tupleLeft tupleIdx) valueX
      bPhase2 y structVars' localVars' fullState (tupleRight tupleIdx) valueY
  where
    unpair :: Operands (a, b) -> (Operands a, Operands b)
    unpair (OP_Pair a b) = (a, b)
pushBindings (TupRsingle t) lhs@(LeftHandSideSingle _) inStruct
  | Refl <- scalarReprBase t
  , Exists push1 <- pushBindingSingle lhs inStruct
  = Exists $ Push1 (bStateType push1) $
    \structVars localVars fullState tupleIdx value ->
      bPhase2 push1 structVars localVars fullState tupleIdx $ op t value
pushBindings _ _ _ = internalError "Tuple mismatch"

-- Pushes two bindings to the StructVars.
-- Requires that the two bindings have the same value.
-- In practice this means that they come from NewSignal or NewRef
pushTwoSame
  :: ReprBaseR t1 ~ ReprBaseR t2
  => BLeftHandSide (t1, t2) env env'
  -> StructVars env
  -> LocalVars env
  -> CodeGen Native (Operand (Ptr (ReprBaseR t1)))
  -> (StructVars env', LocalVars env')
pushTwoSame (LeftHandSideWildcard _) structVars localVars _ = (structVars, localVars)
pushTwoSame (LeftHandSideWildcard _ `LeftHandSidePair` LeftHandSideWildcard _) structVars localVars _ = (structVars, localVars)
pushTwoSame (LeftHandSideSingle _) _ _ _ = internalError "Pair impossible"
pushTwoSame (LeftHandSideSingle _ `LeftHandSidePair` LeftHandSideSingle _) structVars localVars value =
  ( structVars `PPush` StructVar False value `PPush` StructVar False value
  , PNone $ PNone localVars
  )
pushTwoSame (LeftHandSideWildcard _ `LeftHandSidePair` LeftHandSideSingle _) structVars localVars value =
  ( structVars `PPush` StructVar False value
  , PNone localVars
  )
pushTwoSame (LeftHandSideSingle _ `LeftHandSidePair` LeftHandSideWildcard _) structVars localVars value =
  ( structVars `PPush` StructVar False value
  , PNone localVars
  )
pushTwoSame _ _ _ _ = internalError "Nested pair not allowed"

toPrimType :: BaseR t -> PrimType (ReprBaseR t)
toPrimType (BaseRground (GroundRscalar tp))
  | Refl <- scalarReprBase tp = ScalarPrimType tp
toPrimType (BaseRground (GroundRbuffer tp)) = PtrPrimType (ScalarPrimType tp) defaultAddrSpace
toPrimType BaseRsignal = primType
toPrimType BaseRsignalResolver = primType
toPrimType (BaseRref tp) = toPrimType $ BaseRground tp
toPrimType (BaseRrefWrite tp) = toPrimType $ BaseRground tp

-- work_function: ptr
-- continuation: ptr, u32 (program, location)
-- active_threads: u32,
-- work_index: u32,
-- In the future, perhaps also store a work_size: u32
type family KernelArg a where
  KernelArg (m DIM1 e) = Ptr e
  KernelArg (Var' e) = e

type family KernelArgs f where
  KernelArgs () = ()
  KernelArgs (t -> f) = (KernelArg t, KernelArgs f)

kernelArgsTp' :: SArgs env f -> TupR PrimType (KernelArgs f)
kernelArgsTp' (SArgScalar (Var tp _) :>: args) = TupRsingle (ScalarPrimType tp) `TupRpair` kernelArgsTp' args
kernelArgsTp' (SArgBuffer _ (Var tp _) :>: args) = case tp of
  GroundRbuffer t -> TupRsingle (PtrPrimType (ScalarPrimType t) defaultAddrSpace) `TupRpair` kernelArgsTp' args
  _ -> internalError "Buffer impossible"
kernelArgsTp' ArgsNil = TupRunit

kernelArgsTp :: SArgs env f -> (PrimType (Struct (Header, Struct (KernelArgs f))), PrimType (Struct (KernelArgs f)))
kernelArgsTp args =
  ( StructPrimType False
    $ TupRpair headerType
    $ TupRsingle $ tp
  , tp
  )
  where
    tp = StructPrimType False $ kernelArgsTp' args

storeKernelArgs :: StructVars env -> LocalVars env -> SArgs env f -> Operand (Ptr (Struct struct)) -> TupleIdx struct (KernelArgs f) -> CodeGen Native ()
storeKernelArgs structVars localVars (SArgScalar (Var tp idx) :>: sargs) struct structIdx
  | Refl <- scalarReprBase tp = do
    (localVars', value) <- getValue structVars localVars (GroundRscalar tp) idx
    ptr <- instr' $ GetStructElementPtr (ScalarPrimType tp) struct (tupleLeft structIdx)
    _ <- instr' $ Store NonVolatile ptr value
    storeKernelArgs structVars localVars' sargs struct (tupleRight structIdx)
storeKernelArgs structVars localVars (SArgBuffer _ (Var tp idx) :>: sargs) struct structIdx = do
  (localVars', value) <- getValue structVars localVars tp idx
  ptr <- instr' $ GetStructElementPtr (PtrPrimType (ScalarPrimType tp') defaultAddrSpace) struct (tupleLeft structIdx)
  _ <- instr' $ Store NonVolatile ptr value
  storeKernelArgs structVars localVars' sargs struct (tupleRight structIdx)
  where
    tp' = case tp of
      GroundRbuffer t -> t
      _ -> internalError "Buffer impossible"
storeKernelArgs _ _ ArgsNil _ _ = return ()

-- TODO: Make this safe? I think we should move the linker to the C world as well, to make this sound...
-- Only the C side can decide when the ObjectR needs to be deallocated
veryUnsafeGetFunPtr :: OpenKernelFun NativeKernel env f -> IO (Ptr Int8)
veryUnsafeGetFunPtr (KernelFunLam _ f) = veryUnsafeGetFunPtr f
veryUnsafeGetFunPtr (KernelFunBody kernel) = return $ castPtr $ unsafeGetPtrFromLifetimeFunPtr $ kernelFunction kernel
