{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE ViewPatterns             #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Execute
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Execute (

) where

import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.AST.Execute
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Interpreter                ( evalExp, EvalArrayInstr(..) )
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.LLVM.Native.Kernel
import Data.Array.Accelerate.LLVM.Native.Execute.Environment
import Data.Array.Accelerate.LLVM.Native.Execute.KernelArguments
import Data.Array.Accelerate.LLVM.Native.Execute.Scheduler
import Data.Array.Accelerate.LLVM.Native.Link.Schedule

import Control.Exception
import Data.String
import Data.Int
import Data.Word
import Data.IORef
import Data.Typeable
import Language.Haskell.TH.Syntax
import qualified Crypto.Hash.XKCP as Hash
import Control.Concurrent
import Foreign.Ptr
import Foreign.StablePtr
import Foreign.ForeignPtr
import Foreign.Storable
import GHC.Conc
import System.IO
import System.IO.Unsafe ( unsafePerformIO )
import LLVM.AST.Type.Representation

instance Execute UniformScheduleFun NativeKernel where
  data Linked UniformScheduleFun NativeKernel t = NativeLinked !(NativeProgram) !(UniformScheduleFun NativeKernel () t)

  linkAfunSchedule schedule =
    NativeLinked
      (linkSchedule (Hash.hash $ fromString "todo") schedule) schedule
  executeAfunSchedule _ (NativeLinked (NativeProgram fun size imports offset) schedule) =
    prepareProgram schedule start final
    where
      start :: IO (Ptr Int8, Int)
      start = do
        -- Allocate space for the program imports, arguments and local state
        program <- runtimeProgramAlloc (fromIntegral size) $ castPtr $ unsafeGetPtrFromLifetimeFunPtr fun
        -- Initialize the struct with the imports
        imports program
        -- 'prepareProgram' will initialize struct with the arguments of the function
        return (program, offset)
      final :: Ptr Int8 -> IO ()
      final program = do
        -- All imports and arguments are placed in the struct, we can start the program
        runtimeSchedule defaultRuntimeWorkers program 0
        runtimeProgramRelease program

prepareProgram
  :: UniformScheduleFun NativeKernel env f
  -> IO (Ptr Int8, Int)
  -> (Ptr Int8 -> IO ())
  -> IOFun f
prepareProgram (Slam lhs f) accum final =
  \x -> prepareProgram f (accum >>= write lhs x) final
  where
    write :: BLeftHandSide s env env' -> s -> (Ptr Int8, Int) -> IO (Ptr Int8, Int)
    write (LeftHandSideWildcard _) _ ptrCursor = return ptrCursor
    write (LeftHandSideSingle (BaseRground _)) _ _ = internalError "Ground inputs not allowed. These should be passed in a Ref"
    -- An input value
    write (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle (BaseRref tp)) (Signal mvar, Ref ioref) (ptr, cursor) = do
      poke (plusPtr ptr cursor1) (0 :: Word)
      case tp of
        -- Intialize reference count of Ref with 1.
        -- Number is shifted by one bit.
        -- See: [reference counting for Ref]
        GroundRbuffer _ -> do
          poke (plusPtr ptr cursor2) (2 :: Word)
        _ -> return ()
      -- In a separate thread, wait on the MVar and resolve the signal
      runtimeProgramRetain ptr
      _ <- forkIO $ do
        readMVar mvar
        value <- readIORef ioref
        pokeGround tp (plusPtr ptr cursor2) value
        runtimeSignalResolve defaultRuntimeWorkers (plusPtr ptr cursor1)
        runtimeProgramRelease ptr
      return (ptr, cursor2 + sz)
      where
        cursor1 = makeAligned cursor (sizeOf (0 :: Int))
        cursor2 = makeAligned (cursor1 + sizeOf (0 :: Int)) a
        (sz, a) = groundSizeAlignment tp
    -- An output value
    write (LeftHandSideSingle BaseRsignalResolver `LeftHandSidePair` LeftHandSideSingle (BaseRrefWrite tp)) (SignalResolver mvar, OutputRef ioref) (ptr, cursor) = do
      localMVar <- newEmptyMVar
      sp <- newStablePtrPrimMVar localMVar
      poke (plusPtr ptr cursor1) sp
      runtimeProgramRetain ptr
      case tp of
        -- Intialize reference count of OutputRef with 1.
        -- Number is shifted by one bit.
        -- See: [reference counting for Ref]
        GroundRbuffer _ -> do
          poke (plusPtr ptr cursor2) (2 :: Word)
        _ -> return ()
      _ <- forkIO $ do
        readMVar localMVar
        value <- peekGround tp (plusPtr ptr cursor2)
        writeIORef ioref value
        runtimeProgramRelease ptr
        putMVar mvar ()
      return (ptr, cursor2 + sz)
      where
        cursor1 = makeAligned cursor (sizeOf (0 :: Int))
        cursor2 = makeAligned (cursor1 + sizeOf (0 :: Int)) a
        (sz, a) = groundSizeAlignment tp
    write (LeftHandSidePair l1 l2) (v1, v2) ptrCursor = do
      ptrCursor1 <- write l1 v1 ptrCursor
      write l2 v2 ptrCursor1
    write _ _ _ = internalError "Unexpected LeftHandSide. Does the program have a Signal without Ref, SignalResolver without RefWrite, or the other way around?"
prepareProgram (Sbody _) accum final = do
  (ptr, _) <- accum
  final ptr

pokeGround :: GroundR a -> Ptr Int8 -> a -> IO ()
pokeGround (GroundRbuffer _) dest (Buffer fp) =
  withForeignPtr fp $ \ptr ->
    runtimeRefWriteBuffer (castPtr dest) (castPtr ptr)
pokeGround (GroundRscalar (SingleScalarType tp)) dest value
  | SingleDict <- singleDict tp = do
    poke (castPtr dest) value
pokeGround (GroundRscalar (VectorScalarType _)) _ _ = internalError "Not yet supported: VectorScalarType as input to an Acc function"

peekGround :: GroundR a -> Ptr Int8 -> IO a
peekGround (GroundRbuffer _) dest = do
  ptr <- peek $ castPtr dest
  bufferFromPtr ptr
peekGround (GroundRscalar (SingleScalarType tp)) dest
  | SingleDict <- singleDict tp = do
    peek $ castPtr dest
peekGround (GroundRscalar (VectorScalarType _)) _ = internalError "Not yet supported: VectorScalarType as output to an Acc function"

groundSizeAlignment :: GroundR a -> (Int, Int)
groundSizeAlignment (GroundRbuffer _) = (sizeOf (0 :: Int), sizeOf (0 :: Int))
groundSizeAlignment (GroundRscalar (SingleScalarType tp)) = (s, s)
  where s = bytesElt $ TupRsingle $ SingleScalarType tp
groundSizeAlignment (GroundRscalar (VectorScalarType (VectorType n tp))) = (n * s, s)
  where s = bytesElt $ TupRsingle $ SingleScalarType tp

runValuesIOFun
  :: Workers
  -> GFunctionR t
  -> ValuesIOFun (Scheduled UniformScheduleFun t)
  -> IOFun (Scheduled UniformScheduleFun t)
runValuesIOFun workers (GFunctionRlam argTp funTp) f = \arg -> runValuesIOFun workers funTp $ f (input argTp arg)
  where
    input :: GroundsR t -> Input t -> Values (Input t)
    input = values workers . inputR
runValuesIOFun workers (GFunctionRbody tp) f
  | Refl <- reprIsBody @UniformScheduleFun tp = \arg -> schedule workers $ Job $ \_ -> f $ output tp arg
  where
    output :: GroundsR t -> Output t -> Values (Output t)
    output = values workers . outputR

-- Schedules a ScheduleFun (to be executed on a worker thread) and returns its result
scheduleScheduleFun :: Workers -> NativeEnv env -> UniformScheduleFun NativeKernel env t -> ValuesIOFun t
scheduleScheduleFun !workers !env (Sbody body) = schedule workers $ Job $ \threadIdx -> executeSchedule workers threadIdx env body
scheduleScheduleFun !workers !env (Slam lhs fun) = \input -> scheduleScheduleFun workers (env `push` (lhs, input)) fun

-- Executes a ScheduleFun
executeScheduleFun :: Workers -> ThreadIdx -> NativeEnv env -> UniformScheduleFun NativeKernel env t -> ValuesIOFun t
executeScheduleFun !workers !threadIdx !env (Sbody body) = executeSchedule workers threadIdx env body
executeScheduleFun !workers !threadIdx !env (Slam lhs fun) = \input -> executeScheduleFun workers threadIdx (env `push` (lhs, input)) fun

executeSchedule :: Workers -> ThreadIdx -> NativeEnv env -> UniformSchedule NativeKernel env -> IO ()
executeSchedule !workers !threadIdx !env = \case
  Return -> return ()
  Alet lhs binding body -> do
    value <- executeBinding workers env (lhsToTupR lhs) binding
    let env' = env `push` (lhs, value)
    executeSchedule workers threadIdx env' body
  Effect effect next -> do
    executeEffect workers threadIdx env effect $ Job $ \threadIdx' -> executeSchedule workers threadIdx' env next
  Acond var true false next -> do
    let value = prj (varIdx var) env
    let branch = if value == 1 then true else false
    executeSchedule workers threadIdx env branch
    executeSchedule workers threadIdx env next
  Awhile io step input next -> do
    executeAwhile workers threadIdx env io step (prjVars input env) next
  Spawn (Effect (SignalAwait signals) a) b -> do
    scheduleAfter workers (map (`prj` env) signals) $ Job $ \threadIdx' -> do
      executeSchedule workers threadIdx' env a
    executeSchedule workers threadIdx env b
  Spawn a b -> do
    schedule workers $ Job $ \threadIdx' -> executeSchedule workers threadIdx' env a
    executeSchedule workers threadIdx env b

executeBinding :: Workers -> NativeEnv env -> BasesR t -> Binding env t -> IO (Values t)
executeBinding workers !env tp = \case
  Compute expr ->
    return $ values workers tp $ evalExp expr $ evalArrayInstr env
  NewSignal _ -> do
    signal <- newSignal
    return $ ValuesSingle (Value signal) `ValuesPair` ValuesSingle (Value signal)
  NewRef _ -> do
    ioref <- newIORef $ internalError "Illegal schedule: Read from ref without value. Some synchronization might be missing."
    return $ ValuesSingle (Value $ Ref ioref) `ValuesPair` ValuesSingle (Value $ OutputRef ioref)
  Alloc shr tp sh -> do
    let n = size' shr $ prjVars sh env
    MutableBuffer buffer <- newBuffer tp n
    return $ ValuesSingle $ Value $ Buffer buffer
  Use _ _ buffer ->
    return $ ValuesSingle $ Value buffer
  Unit (Var tp ix) -> do
    mbuffer@(MutableBuffer buffer) <- newBuffer tp 1
    writeBuffer tp mbuffer 0 $ prjGroundVar (Var (GroundRscalar tp) ix) env
    return $ ValuesSingle $ Value $ Buffer buffer
  RefRead ref@(Var (BaseRref tp) ix) -> do
    let Ref ioref = prj ix env
    ValuesSingle . groundValue tp <$> readIORef ioref
  RefRead _ -> internalError "Ref impossible"

executeEffect :: forall env. Workers -> ThreadIdx -> NativeEnv env -> Effect NativeKernel env -> Job -> IO ()
executeEffect !workers !threadIdx !env !effect !next = case effect of
  Exec md kernelFun args -> do
    Exists kernelCall <- prepareKernel env md kernelFun args
    executeKernel workers threadIdx kernelCall (Job $ \threadIdx' -> touchKernel env kernelFun args >> runJob next threadIdx)
  SignalAwait signals -> do
    scheduleAfterOrRun (map (`prj` env) signals) threadIdx $ next
  SignalResolve signals -> do
    mapM_ resolve signals
    runJob next threadIdx
  RefWrite ref@(Var (BaseRrefWrite tp) _) valueVar -> do
    let OutputRef ioref = prj (varIdx ref) env
    let value = prjGroundVar (Var tp $ varIdx valueVar) env
    writeIORef ioref value
    runJob next threadIdx
  RefWrite _ _ -> internalError "OutputRef impossible"
  where
    resolve :: Idx env SignalResolver -> IO ()
    resolve idx = do
      let signal = prj idx env
      resolveSignal workers signal

executeAwhile
  :: Workers
  -> ThreadIdx
  -> NativeEnv env
  -> InputOutputR input output
  -> UniformScheduleFun NativeKernel env (input -> Output PrimBool -> output -> ())
  -> Values input
  -> UniformSchedule NativeKernel env
  -> IO ()
executeAwhile !workers !threadIdx !env !io !step !input !next = do
  -- Set up the output variables for this iteration (and the input for the next)
  signal <- newSignal
  ioref <- newIORef $ internalError "Illegal schedule: Read from ref without value. Some synchronization might be missing."
  (output, nextInput) <- bindAwhileIO io

  -- Check condition when it is available
  scheduleAfter workers [signal] $ Job $ \threadIdx' -> do
    condition <- readIORef ioref
    if condition == 1 then
      executeAwhile workers threadIdx' env io step nextInput next
    else
      executeSchedule workers threadIdx' env next

  -- Execute a step
  executeScheduleFun workers threadIdx env step input (ValuesSingle (Value signal) `ValuesPair` ValuesSingle (Value $ OutputRef ioref)) output

bindAwhileIO :: InputOutputR input output -> IO (Values output, Values input)
bindAwhileIO InputOutputRsignal = do
  signal <- newSignal
  return (ValuesSingle $ Value signal, ValuesSingle $ Value signal)
bindAwhileIO (InputOutputRref _) = do
  ioref <- newIORef $ internalError "Illegal schedule: Read from ref without value. Some synchronization might be missing."
  return (ValuesSingle $ Value $ OutputRef ioref, ValuesSingle $ Value $ Ref ioref)
bindAwhileIO (InputOutputRpair io1 io2) = do
  (output1, input1) <- bindAwhileIO io1
  (output2, input2) <- bindAwhileIO io2
  return (output1 `ValuesPair` output2, input1 `ValuesPair` input2)
bindAwhileIO InputOutputRunit =
  return (ValuesUnit, ValuesUnit)


evalArrayInstr :: NativeEnv env -> EvalArrayInstr (ArrayInstr env)
evalArrayInstr env = EvalArrayInstr $ \instr arg -> case instr of
  Index buffer -> indexBuffer (groundRelt $ varType buffer) (prj (varIdx buffer) env) arg
  Parameter (Var tp ix) -> prjGroundVar (Var (GroundRscalar tp) ix) env


size' :: ShapeR sh -> Values sh -> Int
size' ShapeRz _ = 1
size' (ShapeRsnoc shr) (sh `ValuesPair` ValuesSingle (Value sz))
  | sz <= 0 = 0
  | otherwise = size' shr sh * sz

{-# NOINLINE defaultRuntimeWorkers #-}
defaultRuntimeWorkers :: Ptr Int8
defaultRuntimeWorkers = unsafePerformIO $ runtimeStartWorkers 1 -- TODO: Set correct number of threads

foreign import ccall unsafe "accelerate_start_workers" runtimeStartWorkers :: Word64 -> IO (Ptr Int8)
foreign import ccall unsafe "accelerate_signal_resolve" runtimeSignalResolve :: Ptr Int8 -> Ptr Int8 -> IO ()
foreign import ccall unsafe "accelerate_program_alloc" runtimeProgramAlloc :: Word64 -> Ptr Int8 -> IO (Ptr Int8)
foreign import ccall unsafe "accelerate_program_retain" runtimeProgramRetain :: Ptr Int8 -> IO ()
foreign import ccall unsafe "accelerate_program_release" runtimeProgramRelease :: Ptr Int8 -> IO ()
foreign import ccall unsafe "accelerate_schedule" runtimeSchedule :: Ptr Int8 -> Ptr Int8 -> Word32 -> IO ()
foreign import ccall unsafe "accelerate_ref_write_buffer" runtimeRefWriteBuffer :: Ptr (Ptr Int8) -> Ptr Int8 -> IO ()
