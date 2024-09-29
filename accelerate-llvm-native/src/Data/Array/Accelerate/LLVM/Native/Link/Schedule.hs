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
import Data.Array.Accelerate.AST.IdxSet ( IdxSet(..) )
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
import LLVM.AST.Type.Constant
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
prepareImports :: TupR PrimType imports -> TupR IO imports -> Ptr Int8 -> Int -> IO Int
prepareImports TupRunit TupRunit _ cursor = return cursor
prepareImports (TupRpair t1 t2) (TupRpair i1 i2) ptr cursor = prepareImports t1 i1 ptr cursor >>= prepareImports t2 i2 ptr
prepareImports (TupRsingle tp) (TupRsingle io) ptr cursor = case tp of
  PtrPrimType _ _ -> do
    value <- io
    poke (plusPtr ptr cursor) value
    return $ cursor + sizeOf (1 :: Int)
  _ -> internalError "Unexpected type in imports of program"
prepareImports _ _ _ _ = internalError "Tuple mismatch"

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
        prepareImports (importsType schedule1) (importsInit schedule1) ptr (2 * sizeOf (1 :: Int))
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
        destructor
          (LocalReference (PrimType ptrImportsTp) "imports")
          (importsType schedule1)
          TupleIdxSelf
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

destructor :: Operand (Ptr (Struct fullImports)) -> TupR PrimType imports -> TupleIdx fullImports imports -> CodeGen Native ()
destructor fullState (TupRpair i1 i2) idx = destructor fullState i1 (tupleLeft idx) >> destructor fullState i2 (tupleRight idx)
destructor _ TupRunit _ = return ()
-- This uses the assumption that imported kernels have kernelTp (which is a NamedPrimType),
-- and all buffers do not have a NamedPrimType
destructor fullState (TupRsingle tp) idx = do
  ptrPtr <- instr' $ GetStructElementPtr tp fullState idx
  case tp of
    PtrPrimType NamedPrimType{} _ -> do
      ptr <- instr' $ LoadPtr NonVolatile ptrPtr
      ptr' <- instr' $ PtrCast (primType @(Ptr Int8)) ptr
      _ <- call'
        (LLVM.lamUnnamed primType $
          LLVM.Body VoidType Nothing (Label "accelerate_function_release"))
        (LLVM.ArgumentsCons ptr' []
          LLVM.ArgumentsNil)
        []
      return ()
    PtrPrimType _ _ -> do
      ptr <- instr' $ LoadPtr NonVolatile ptrPtr
      ptr' <- instr' $ PtrCast (primType @(Ptr Int8)) ptr
      _ <- call'
        (LLVM.lamUnnamed primType $
          LLVM.Body VoidType Nothing (Label "accelerate_buffer_release"))
        (LLVM.ArgumentsCons ptr' []
          LLVM.ArgumentsNil)
        []
      return ()
    _ -> internalError "imports should only include pointers"

-- Kernels are actually functions, but to simplify the code generation here, we just use an untyped pointer.
-- To separate pointers to buffers from pointer to kernels however, we introduce this type.
kernelTp :: PrimType (Ptr (Struct Int8))
kernelTp = PtrPrimType (NamedPrimType "kernel_t" $ StructPrimType False $ TupRsingle primType) defaultAddrSpace

typeSignalWaiter :: PrimType (Struct (Ptr Int8, (Int32, Ptr Int8)))
typeSignalWaiter = StructPrimType False $ TupRpair (TupRsingle primType) $ TupRpair (TupRsingle primType) (TupRsingle primType)

type family ReprBaseR t where
  ReprBaseR Signal = Word
  ReprBaseR SignalResolver = Word
  -- Note: [reference counting for Ref]
  -- Reference counting on Refs and OutputRefs containing Buffers is more difficult than for regular Buffer variables.
  -- Before the Ref is filled, multiple references to a Ref may be constructed (via Spawn),
  -- which cannot update the reference count of the buffer yet, as that buffer is not known yet.
  -- When writing to the Ref, we should know how many references we should add to the reference count
  -- of the Buffer.
  -- We make this possible by storing the number of references to an unresolved Ref in that Ref.
  -- To separate an unfilled Ref from a filled Ref, we set the least significant bit of an unfilled Ref to 1.
  -- The number of references 'r' is stored as '(r << 1) | 1'
  -- This only applies to Refs containing Buffers, not to Refs containing scalars
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
  !(BaseR t)
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
      in phase2 fun1 imports fullState (structVars `PPush` StructVar True tp getPtr') (PNone localVars) importsIdx (tupleRight stateIdx) nextBlock
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
      (structVarsA, _, structVarsB, localVarsB) <- forkEnv structVars localVars (varsFree a1) (varsFree b1)

      _ <- call (LLVM.lamUnnamed primType $ LLVM.lamUnnamed primType $ LLVM.lamUnnamed primType $ LLVM.Body VoidType Nothing (Label "accelerate_schedule")) 
        (LLVM.ArgumentsCons operandWorkers []
          $ LLVM.ArgumentsCons operandProgram []
          $ LLVM.ArgumentsCons (integral TypeWord32 $ fromIntegral $ nextBlock + blockCount b1) []
          LLVM.ArgumentsNil)
        []

      phase2 b1 imports fullState
        structVarsB
        localVarsB
        (tupleRight importsIdx)
        (tupleRight stateIdx)
        nextBlock

      let aBlock = newBlockNamed $ blockName (nextBlock + blockCount b1)
      setBlock aBlock
      phase2 a1 imports fullState
        structVarsA
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
      -- Release the variables not used by whenTrue nor next
      (structVarsTrue, localVarsTrue) <-
        subEnv structVars localVars' (varsFree whenTrue1 `IdxSet.union` varsFree next1)
      -- Retain the variables used both in whenTrue and in next
      (structVarsTrue', localVarsTrue', _, _) <-
        forkEnv structVarsTrue localVarsTrue (varsFree whenTrue1) (varsFree next1)
      phase2 whenTrue1 imports fullState structVarsTrue' localVarsTrue'
        (tupleLeft $ tupleLeft importsIdx)
        (tupleLeft $ tupleLeft stateIdx)
        nextBlock
      _ <- br blockExit

      setBlock blockFalse
      -- Release the variables not used by whenFalse nor next
      (structVarsFalse, localVarsFalse) <-
        subEnv structVars localVars' (varsFree whenFalse1 `IdxSet.union` varsFree next1)
      -- Retain the variables used both in whenFalse and in next
      (structVarsFalse', localVarsFalse', _, _) <-
        forkEnv structVarsFalse localVarsFalse (varsFree whenFalse1) (varsFree next1)
      phase2 whenFalse1 imports fullState structVarsFalse' localVarsFalse'
        (tupleRight $ tupleLeft importsIdx)
        (tupleRight $ tupleLeft stateIdx)
        (nextBlock + blockCount whenTrue1)
      _ <- br blockExit

      setBlock blockExit
      phase2 next1 imports fullState
        (IdxSet.partialEnvFilterSet (varsFree next1) structVars)
        -- If the true or false branch may suspend, then we cannot use values from localVars.
        -- Instead they must be read from structVars.
        -- Hence we also include all free variables of 'next' in varsInStruct if 'branchMaySuspend'.
        (if branchMaySuspend then PEnd else IdxSet.partialEnvFilterSet (varsFree next1) localVars')
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
    importsType = TupRsingle kernelTp `TupRpair` importsType next1,
    importsInit = TupRsingle (veryUnsafeGetFunPtr kernel) `TupRpair` importsInit next1,
    stateType = TupRsingle argsTp `TupRpair` stateType next1,
    varsFree = varsFree next1 `IdxSet.union` effectFreeVars effect,
    -- Place all free variables of the kernel in the struct.
    -- We need those variables after the kernel (after the function resumes),
    -- to update the reference counts.
    -- Note that we could get these variables from the kernel arguments structure (of type argsTp),
    -- but that's some more work to set up.
    varsInStruct = varsFree next1 `IdxSet.union` effectFreeVars effect,
    maySuspend = True,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      let blockNext = newBlockNamed $ blockName nextBlock
      args <- instr' $ GetStructElementPtr argsTp fullState (tupleLeft stateIdx)

      -- Fill arguments struct
      -- Header
      workFnPtr' <- instr' $ GetStructElementPtr kernelTp imports (tupleLeft importsIdx)
      workFn <- instr' $ LoadPtr NonVolatile workFnPtr'
      workFnPtr <- instr' $ GetStructElementPtr kernelTp args (TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft $ TupleIdxLeft TupleIdxSelf)
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
      phase2Sub next1 imports fullState structVars PEnd (tupleRight importsIdx) (tupleRight stateIdx) (nextBlock + 1)
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
      initWaiter <- instr' $ GetStructElementPtr typeSignalWaiter fullState (tupleLeft stateIdx)
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
        go :: Operand (Ptr (Struct (Ptr Int8, (Int32, Ptr Int8)))) -> Int -> [Idx env Signal] -> CodeGen Native ()
        go waiter _ [] = return ()
        go waiter i (idx : idxs) = do
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
          -- Since function may suspend and return here if i == 0, we must again get a pointer to the waiter here.
          waiter' <-
            if i == 0 then
              instr' $ GetStructElementPtr typeSignalWaiter fullState (tupleLeft stateIdx)
            else
              return waiter
          go waiter' (i + 1) idxs

      go initWaiter 0 signals

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
          Just (StructVar True _ m) -> do
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
          Just (StructVar False _ m) -> do
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
      case tp of
        GroundRbuffer _ -> do
          ref'' <- instr' $ PtrCast (PtrPrimType primType defaultAddrSpace) ref'
          value'' <- instr' $ PtrCast primType value'
          -- See: [reference counting for Ref]
          _ <- call'
            (LLVM.lamUnnamed (PtrPrimType (primType @(Ptr Int8)) defaultAddrSpace) $
              LLVM.lamUnnamed (primType @(Ptr Int8)) $
              LLVM.Body VoidType Nothing (Label "accelerate_ref_write_buffer"))
            (LLVM.ArgumentsCons ref'' [] $
              LLVM.ArgumentsCons value'' []
              LLVM.ArgumentsNil)
            []
          return ()
        GroundRscalar _ -> do
          _ <- instr' $ Store NonVolatile ref' value'
          return ()
      phase2Sub next1 imports fullState structVars localVars' importsIdx stateIdx nextBlock
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
      phase2Sub next1 imports fullState structVars' localVars' importsIdx (tupleRight stateIdx) nextBlock
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
      phase2Sub next1 imports fullState structVars' localVars' importsIdx (tupleRight stateIdx) nextBlock
  }
convert (Alet lhs (NewRef (GroundRbuffer tp)) next)
  | Exists2 next1 <- convert next =
  Exists2 $ Phase1{
    blockCount = blockCount next1,
    importsType = importsType next1,
    importsInit = importsInit next1,
    stateType = TupRsingle t `TupRpair` stateType next1,
    varsFree = IdxSet.drop' lhs $ varsFree next1,
    varsInStruct = IdxSet.drop' lhs $ varsInStruct next1,
    maySuspend = maySuspend next1,
    phase2 = \imports fullState structVars localVars importsIdx stateIdx nextBlock -> do
      let getPtr' = instr' $ GetStructElementPtr t fullState $ tupleLeft stateIdx
      let (structVars', localVars') = pushTwoSame lhs structVars localVars getPtr'

      ptr <- getPtr'
      ptr' <- instr' $ PtrCast primType ptr
      _ <- instr' $ Store NonVolatile ptr' $ integral TypeWord initialRefCount

      phase2Sub next1 imports fullState structVars' localVars' importsIdx (tupleRight stateIdx) nextBlock
  }
  where
    t = PtrPrimType (ScalarPrimType tp) defaultAddrSpace
    initialRefCount = case lhs of
      LeftHandSidePair _ LeftHandSideSingle{} -> 1
      _ -> 0
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
      phase2Sub next1 imports fullState structVars' localVars2 importsIdx (tupleRight stateIdx) nextBlock
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
      callBufferRetain ptr
      (structVars', localVars') <- bPhase2 bnd structVars localVars fullState (tupleLeft stateIdx) ptr
      phase2Sub next1 imports fullState structVars' localVars' (tupleRight importsIdx) (tupleRight stateIdx) nextBlock
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
      phase2Sub next1 imports fullState structVars' localVars'' importsIdx (tupleRight stateIdx) nextBlock
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
      -- By default we would need to perform a buffer_retain on the read value, if it is a buffer.
      -- In case the Ref is not used in 'next', phase2Sub will release that value.
      -- These two cancel each other out.
      -- Hence we check for this scenario here, and only emit the retain if needed.
      structVars' <- case tp of
        -- Reference counting doesn't apply to scalar values, so no need to do anything here.
        GroundRscalar _ -> return structVars
        GroundRbuffer _
          -- Best case: 'ref' is not used any more.
          -- Don't call buffer_retain, and remove ref from structVars such that
          -- ref_release won't be called.
          | not $ varIdx ref `IdxSet.member` IdxSet.drop' lhs (varsFree next1) ->
            return $ partialRemove (varIdx ref) structVars
          -- Default case: we do need to perform buffer_retain
          | otherwise -> do
            callBufferRetain value
            return structVars
      (structVars'', localVars') <- bPhase2 bnd structVars' localVars fullState (tupleLeft stateIdx) value
      phase2Sub next1 imports fullState structVars'' localVars' importsIdx (tupleRight stateIdx) nextBlock
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
      phase2Sub next1 imports fullState structVars' localVars' importsIdx (tupleRight stateIdx) nextBlock
  }

-- Variant of 'phase' that performs the sub-environment rule (subEnv),
-- to release variables that are no longer used.
phase2Sub :: Phase1 env imports state -> Phase2 env imports state
phase2Sub phase1 imports fullState structVars localVars importsIdx stateIdx nextBlock = do
  (structVars', localVars') <- subEnv structVars localVars (varsFree phase1)
  phase2 phase1 imports fullState structVars' localVars' importsIdx stateIdx nextBlock

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
  Just (StructVar _ _ m) -> m
  Nothing -> internalError "Idx missing in StructVars."

getValue :: ReprBaseR t ~ ReprBaseR t' => StructVars env -> LocalVars env -> GroundR t -> Idx env t' -> CodeGen Native (LocalVars env, Operand (ReprBaseR t))
getValue structVars localVars groundR idx
  | Just (LocalVar operand) <- prjPartial idx localVars = return (localVars, operand)
  | Just (StructVar _ _ m) <- prjPartial idx structVars = do
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
      return (structVars `PPush` StructVar False tp getPtr', localVars `PPush` LocalVar value)
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
pushTwoSame (LeftHandSideSingle t1 `LeftHandSidePair` LeftHandSideSingle t2) structVars localVars value =
  ( structVars `PPush` StructVar False t1 value `PPush` StructVar False t2 value
  , PNone $ PNone localVars
  )
pushTwoSame (LeftHandSideWildcard _ `LeftHandSidePair` LeftHandSideSingle t2) structVars localVars value =
  ( structVars `PPush` StructVar False t2 value
  , PNone localVars
  )
pushTwoSame (LeftHandSideSingle t1 `LeftHandSidePair` LeftHandSideWildcard _) structVars localVars value =
  ( structVars `PPush` StructVar False t1 value
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
veryUnsafeGetFunPtr :: OpenKernelFun NativeKernel env f -> IO (Ptr (Struct Int8))
veryUnsafeGetFunPtr (KernelFunLam _ f) = veryUnsafeGetFunPtr f
veryUnsafeGetFunPtr (KernelFunBody kernel) = return $ castPtr $ unsafeGetPtrFromLifetimeFunPtr $ kernelFunction kernel

-- Releases any bindings that are not used according to 'used'
-- Returns the environments with only variables in 'used'
subEnv :: StructVars env -> LocalVars env -> IdxSet env -> CodeGen Native (StructVars env, LocalVars env)
subEnv = \structVars localVars used -> do
  go structVars localVars used
  return (IdxSet.partialEnvFilterSet used structVars, IdxSet.partialEnvFilterSet used localVars)
  where
    go :: StructVars env' -> LocalVars env' -> IdxSet env' -> CodeGen Native ()
    -- Base case
    go PEnd PEnd _ = return ()
    -- ZeroIdx is present in 'used'.
    -- No need to release anything here.
    go structVars localVars (IdxSet (PPush set _)) =
      go (partialEnvTail structVars) (partialEnvTail localVars) (IdxSet set)
    -- ZeroIdx is not present in 'used'.
    -- We may need to release some binding
    go (PPush structVars structVar) (PPush localVars localVar) set = do
      release (Just structVar) (Just localVar)
      go structVars localVars (IdxSet.drop set)
    go (PPush structVars structVar) localVars set = do
      release (Just structVar) Nothing
      go structVars (partialEnvTail localVars) (IdxSet.drop set)
    go structVars (PPush localVars localVar) set = do
      release Nothing (Just localVar)
      go (partialEnvTail structVars) localVars (IdxSet.drop set)
    go (PNone structVars) localVars set =
      go structVars (partialEnvTail localVars) (IdxSet.drop set)
    go PEnd (PNone localVars) set =
      go PEnd localVars (IdxSet.drop set)

    release :: Maybe (StructVar t) -> Maybe (LocalVar t) -> CodeGen Native ()
    -- Release a Ref containing a buffer, by calling accelerate_ref_release
    release (Just (StructVar _ (BaseRref (GroundRbuffer tp)) m)) _ = do
      ptr <- m
      ptr' <- instr' $ PtrCast (primType @(Ptr Int8)) ptr
      _ <- call'
        (LLVM.lamUnnamed primType $
          LLVM.Body VoidType Nothing (Label "accelerate_ref_release"))
        (LLVM.ArgumentsCons ptr' []
          LLVM.ArgumentsNil)
        []
      return ()
    -- Release a Buffer present in LocalVars
    release _ (Just (LocalVar ptr))
      | PrimType (PtrPrimType _ _) <- typeOf ptr = callBufferRelease ptr
      | otherwise = return ()
    -- Release a Buffer only present in StructVars
    release (Just (StructVar _ (BaseRground GroundRbuffer{}) m)) _ = do
      ptrPtr <- m
      ptr <- instr' $ LoadPtr NonVolatile ptrPtr
      callBufferRelease ptr
    release _ _ = return ()

-- Splits an environment in two, according to the uses of two terms denoted by
-- usedLeft and usedRight.
-- This is used to implement environment splitting in Spawn and Acond.
-- Bindings that are required in both environments are retained
-- (their reference count is increased).
forkEnv :: StructVars env -> LocalVars env -> IdxSet env -> IdxSet env -> CodeGen Native (StructVars env, LocalVars env, StructVars env, LocalVars env)
forkEnv = \structVars localVars usedLeft usedRight -> do
  let duplicate = IdxSet.intersect usedLeft usedRight
  go structVars localVars duplicate
  return
    (
      IdxSet.partialEnvFilterSet usedLeft structVars,
      IdxSet.partialEnvFilterSet usedLeft localVars,
      IdxSet.partialEnvFilterSet usedRight structVars,
      IdxSet.partialEnvFilterSet usedRight localVars
    )
  where
    go :: StructVars env' -> LocalVars env' -> IdxSet env' -> CodeGen Native ()
    go _ _ (IdxSet PEnd) = return ()
    go structVars localVars (IdxSet (PNone set)) =
      go (partialEnvTail structVars) (partialEnvTail localVars) (IdxSet set)
    go (PPush structVars structVar) (PPush localVars localVar) (IdxSet (PPush set _)) = do
      retain (Just structVar) (Just localVar)
      go structVars localVars (IdxSet set)
    go (PPush structVars structVar) localVars (IdxSet (PPush set _)) = do
      retain (Just structVar) Nothing
      go structVars (partialEnvTail localVars) (IdxSet set)
    go structVars (PPush localVars localVar) (IdxSet (PPush set _)) = do
      retain Nothing (Just localVar)
      go (partialEnvTail structVars) localVars (IdxSet set)
    go PNone{} PNone{} (IdxSet PPush{}) = internalError "expected binding missing in environment"

    retain :: Maybe (StructVar t) -> Maybe (LocalVar t) -> CodeGen Native ()
    -- Retain a Ref containing a buffer, by calling accelerate_ref_retain
    retain (Just (StructVar _ (BaseRref (GroundRbuffer _)) m)) _ = do
      ptr <- m
      ptr' <- instr' $ PtrCast (primType @(Ptr Int8)) ptr
      _ <- call'
        (LLVM.lamUnnamed primType $
          LLVM.Body VoidType Nothing (Label "accelerate_ref_retain"))
        (LLVM.ArgumentsCons ptr' []
          LLVM.ArgumentsNil)
        []
      return ()
    -- Retain a Buffer present in LocalVars
    retain _ (Just (LocalVar ptr))
      | PrimType (PtrPrimType _ _) <- typeOf ptr = callBufferRetain ptr
      | otherwise = return ()
    -- Retain a Buffer only present in StructVars
    retain (Just (StructVar _ (BaseRground GroundRbuffer{}) m)) _ = do
      ptrPtr <- m
      ptr <- instr' $ LoadPtr NonVolatile ptrPtr
      callBufferRetain ptr
    retain _ _ = return () 

callBufferRelease :: Operand (Ptr t) -> CodeGen Native ()
callBufferRelease ptr = do
  ptr' <- instr' $ PtrCast primType ptr
  _ <- call'
    (LLVM.lamUnnamed (primType @(Ptr Int8)) $
      LLVM.Body VoidType Nothing (Label "accelerate_buffer_release"))
    (LLVM.ArgumentsCons ptr' []
      LLVM.ArgumentsNil)
    []
  return ()

callBufferRetain :: Operand (Ptr t) -> CodeGen Native ()
callBufferRetain ptr = do
  ptr' <- instr' $ PtrCast primType ptr
  _ <- call'
    (LLVM.lamUnnamed (primType @(Ptr Int8)) $
      LLVM.Body VoidType Nothing (Label "accelerate_buffer_retain"))
    (LLVM.ArgumentsCons ptr' []
      LLVM.ArgumentsNil)
    []
  return ()
