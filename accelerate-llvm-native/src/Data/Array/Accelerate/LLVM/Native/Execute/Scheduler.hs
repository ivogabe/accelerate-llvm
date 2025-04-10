{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE UnboxedTuples       #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Execute.Scheduler
-- Copyright   : [2018..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Execute.Scheduler (
  {- Job(..), ThreadIdx, Workers,

  schedule,
  hireWorkers, hireWorkersOn, numWorkers,
  defaultWorkers,
  
  runJob,

  executeKernel,

  -- Signals
  NativeSignal, newSignal, resolveSignal, scheduleAfter, scheduleAfterOrRun -}
) where

import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Lifetime
import qualified Data.Array.Accelerate.LLVM.Native.Debug            as Debug
import Data.Array.Accelerate.LLVM.Native.Kernel
import Data.Array.Accelerate.LLVM.Native.Execute.Sleep
import Data.Array.Accelerate.LLVM.Native.Execute.Kernel

import Control.Concurrent
import Control.Concurrent.Extra
import Control.DeepSeq
import Control.Exception
import Control.Monad
import System.Environment
import System.IO.Unsafe
import Data.Proxy
import Data.Atomics
import Data.Concurrent.Queue.MichaelScott
import Data.IORef
import Data.Int
import Data.Sequence                                                ( Seq )
import Data.Maybe
import Text.Read (readMaybe)
import Formatting
import qualified Data.Sequence                                      as Seq
import Foreign.Ptr
import Foreign.ForeignPtr

import GHC.Base                                                     hiding ( build )
import System.IO
import GHC.Conc

#include "MachDeps.h"

instrumentedForkOn :: String -> Int -> IO () -> IO ThreadId
instrumentedForkOn name i act =
  forkOn i $
    catch act $ \e ->
      hPutStrLn stderr $ "[instrumentedForkIO] Thread '" ++ name ++ show i ++ "' crashed: " ++ show (e :: SomeException)


{- newtype Job = Job { runJob :: ThreadIdx -> IO () }

data Workers = Workers
  -- Number of worker threads
  { workerCount       :: {-# UNPACK #-} Int
  -- Sleep scope, to wake threads when new work becomes available
  , workerSleep       :: {-# UNPACK #-} !SleepScope
  -- Tasks currently waiting to be executed; may be from different jobs
  , workerTaskQueue   :: {-# UNPACK #-} !(LinkedQueue Job)
  -- Array of activities, containing for each thread, the activity it's currently performing.
  -- The array only contains own activities. If a thread helps the activity of another thread, then it
  -- won't duplicate that activity into this array.
  -- TODO: Should we add padding in this array to place each element in a different cache line?
  , workerActivity    :: {-# UNPACK #-} !(MutableArray RealWorld Activity)
  -- To attach a (reliable) finalizer to Workers, we add an IORef.
  -- Adding a finalizer to other objects is not reliable, and may cause that
  -- the finalizer runs too early. Hence we attach the finalizer to an IORef.
  -- https://hackage.haskell.org/package/base-4.19.1.0/docs/Data-IORef.html#v:mkWeakIORef
  , workerIORef       :: {-# UNPACK #-} !(IORef ())
  }

data Activity where
  Inactive :: Activity
  Active
    -- Kernel currently being executed:
    :: {-# UNPACK #-} !(Proxy env)
    -> !(FunPtr (KernelType env)) -- Function
    -> !(ForeignPtr ()) -- Arguments struct
    -- Continuation, to be executed after this kernel:
    -> !Job
    -> Activity

type ThreadIdx = Int

instance Show Activity where
  show Inactive = "Inactive"
  show (Active _ fun ptr _) = "Active " ++ show fun ++ " " ++ show ptr

-- Schedule a job to be executed by the worker threads. May be called
-- concurrently.
--
schedule :: Workers -> Job -> IO ()
schedule workers job = do
  pushL (workerTaskQueue workers) job
  wakeAll $ workerSleep workers

runWorker :: Workers -> ThreadIdx -> IO ()
runWorker !workers !threadIdx = do
  tryRunWork workers threadIdx 0

tryRunWork :: Workers -> ThreadIdx -> Int16 -> IO ()
tryRunWork !workers !threadIdx 16 = do
  reason <- sleepIf (workerSleep workers) ({- Last check before sleeping -} noWork workers)
  case reason of
    Work -> runWorker workers threadIdx
    Exit -> return ()
tryRunWork !workers !threadIdx !retries = do
  mjob <- tryDequeue workers
  case mjob of
    Just job -> do
      runJob job threadIdx
      runWorker workers threadIdx
    Nothing ->
      -- tryRunWork workers threadIdx (retries + 1)
      trySteal workers threadIdx (stealingNextThreadIdx workers threadIdx threadIdx) (retries + 1)

trySteal :: Workers -> ThreadIdx -> ThreadIdx -> Int16 -> IO ()
trySteal !workers !myThreadIdx !otherThreadIdx !retries
  | myThreadIdx == otherThreadIdx -- Traversed all worker threads in the array, no work found :(
    = tryRunWork workers myThreadIdx (retries + 1)
trySteal !workers !myThreadIdx !otherThreadIdx !retries = do
  helpKernel workers myThreadIdx otherThreadIdx
    (do
      -- 'otherThreadIdx' was inactive.
      -- Try next thread.
      let nextThreadIdx = stealingNextThreadIdx workers myThreadIdx otherThreadIdx
      trySteal workers myThreadIdx nextThreadIdx retries
    )
    (
      -- 'otherThreadIdx' was active.
      -- Go back to worker loop.
      runWorker workers myThreadIdx
    )

stealingNextThreadIdx :: Workers -> ThreadIdx -> ThreadIdx -> ThreadIdx
stealingNextThreadIdx workers myThreadIdx otherThreadIdx
  | even myThreadIdx
    = if otherThreadIdx == workerCount workers - 1 then 0 else otherThreadIdx + 1
  | otherwise
    = if otherThreadIdx == 0 then workerCount workers - 1 else otherThreadIdx - 1

noWork :: Workers -> IO Bool
noWork !workers = do
  queueEmpty <- nullQ (workerTaskQueue workers)
  if queueEmpty then
    return True
  else
    not <$> hasActivity workers

tryDequeue :: Workers -> IO (Maybe Job)
tryDequeue !workers = tryPopR (workerTaskQueue workers)

-- Spawn a new worker thread for each capability
--
hireWorkers :: IO Workers
hireWorkers = do
  nproc <- getNumProcessors
  ncaps <- getNumCapabilities
  menv  <- (readMaybe =<<) <$> lookupEnv "ACCELERATE_LLVM_NATIVE_THREADS"

  let nthreads = fromMaybe nproc menv

  workers <- hireWorkersOn [0 .. nthreads-1]
  return workers

-- Spawn worker threads on the specified capabilities
--
hireWorkersOn :: [Int] -> IO Workers
hireWorkersOn caps = do
  sleep <- newSleepScope
  queue <- newQ
  let count = length caps
  activities <- newArray count Inactive
  ioref <- newIORef ()
  _ <- mkWeakIORef ioref $ exitAll sleep
  let workers = Workers count sleep queue activities ioref
  forM_ caps $ \cpu -> do
    tid <- instrumentedForkOn "worker" cpu $ do
            tid <- myThreadId
            -- Debug.init_thread
            -- withCString (printf "Thread %d" cpu) Debug.set_thread_name
            runWorker workers cpu
            {- catch
              (restore $ runWorker worker)
              (appendMVar workerException . (tid,)) -}
    message ("sched: fork Thread " % int % " on capability " % int) (getThreadId tid) cpu
    return tid
  return workers

{-# NOINLINE defaultWorkers #-}
defaultWorkers :: Workers
defaultWorkers = unsafePerformIO hireWorkers

-- Number of workers
--
numWorkers :: Workers -> Int
numWorkers = workerCount

hasActivity :: Workers -> IO Bool
hasActivity workers = go 0
  where
    go :: Int -> IO Bool
    go i
      | i == workerCount workers = return False
      | otherwise = do
        activity <- readArray (workerActivity workers) i
        case activity of
          Inactive -> go (i + 1)
          Active{} -> return True

data WaitingJob = WaitingJob
  { waitingDependencies :: {-# UNPACK #-} !Atomic
  , waitingJobJob       :: !Job
  }

resolveDependency :: Workers -> WaitingJob -> IO ()
resolveDependency !workers !job = do
  remaining <- fetchSubAtomic (waitingDependencies job) 1 -- returns old value
  if remaining == 1 then
    -- Add job to queue
    schedule workers (waitingJobJob job)
  else
    return ()

resolveJobsDependency :: Workers -> WaitingJobs -> IO ()
resolveJobsDependency !workers = go
  where
    go :: WaitingJobs -> IO ()
    go WaitingJobsNil = return ()
    go (WaitingJobsCons j js) = do
      resolveDependency workers j
      go js

newtype NativeSignal = NativeSignal (IORef NativeSignalState)

data NativeSignalState
  = Pending !WaitingJobs
  | Resolved

newSignal :: IO NativeSignal
newSignal = NativeSignal <$> newIORef pendingNone

pendingNone :: NativeSignalState
pendingNone = Pending WaitingJobsNil

data WaitingJobs = WaitingJobsNil | WaitingJobsCons {-# UNPACK #-} !WaitingJob !WaitingJobs

resolveSignal :: Workers -> NativeSignal -> IO ()
resolveSignal !workers (NativeSignal ioref) = do
  old <- atomicModifyIORef' ioref (\o -> (Resolved, o))
  case old of
    Resolved -> internalError "Signal is resolved twice."
    Pending jobs -> resolveJobsDependency workers jobs

-- Executes a kernel.
-- Registers it in 'workerActivity' such that other workers can assist on this kernel.
--
-- Assumes that 'workerActivity !! myIdx' is Inactive (ie this thread is
-- currently not in a kernel).
--
executeKernel :: forall env. Workers -> ThreadIdx -> KernelCall env -> Job -> IO ()
executeKernel !workers !myIdx (KernelCall fun arg) continuation = do
  writeArray (workerActivity workers) myIdx $ Active @env Proxy fun arg continuation
  wakeAll $ workerSleep workers
  helpKernel workers myIdx myIdx (return ()) (return ())

{-# INLINE helpKernel #-}
helpKernel :: Workers -> ThreadIdx -> ThreadIdx -> IO () -> IO () -> IO ()
helpKernel !workers !myIdx !otherIdx !whenInactive !afterActive = do
  ticket <- readArrayElem (workerActivity workers) otherIdx
  case peekTicket ticket of
    Inactive -> whenInactive
    Active (Proxy :: Proxy env) fun arg continuation -> do
      isLast <- callKernel @env fun arg
      
      -- Store 'Inactive' in the array
      -- This uses a CAS as the thread which we help may already have progressed
      -- and started working on a new task.
      -- Note that this CAS is only required for helping threads. If we duplicate
      -- this function, with a variant for helping threads and one for the starting
      -- thread, then we could avoid the CAS in the latter.
      _ <- casArrayElem (workerActivity workers) otherIdx ticket Inactive
      
      when isLast (runJob continuation myIdx)
      afterActive

-- Schedules a job to be executed when the given signals are resolved.
scheduleAfter :: Workers -> [NativeSignal] -> Job -> IO ()
scheduleAfter !workers !signals !job = do
  direct <- scheduleAfterOr signals job
  if direct then
    schedule workers job
  else
    return ()

-- Similar to 'scheduleAfter', but if all signals are already resolved,
-- it will directly execute the job instead of scheduling it on the queue.
scheduleAfterOrRun :: [NativeSignal] -> ThreadIdx -> Job -> IO ()
scheduleAfterOrRun !signals !threadIdx !job = do
  direct <- scheduleAfterOr signals job
  if direct then
    runJob job threadIdx
  else
    return ()

-- Similar to 'scheduleAfter'. If all signals are already resolved,
-- it will not schedule the job.
-- Returns whether all signals were already resolved.
scheduleAfterOr :: [NativeSignal] -> Job -> IO Bool
scheduleAfterOr nativeSignals job = do
  let count = length nativeSignals
  dependencies <- newAtomic count
  let
    waitingJob = WaitingJob dependencies job
    go :: [NativeSignal] -> Int -> IO Bool
    go (NativeSignal ioref : signals) resolvedCount = do
      ticket <- readForCAS ioref
      try' ticket
      where
        try' :: Ticket NativeSignalState -> IO Bool
        try' ticket = do
          case peekTicket ticket of
            -- Signal was already resolved, no need to wait
            Resolved -> go signals (resolvedCount + 1)
            -- Signal is still pending. Add this job to the list.
            Pending other -> do
              -- Attempt to add this job using CAS
              (success, newTicket) <- casIORef ioref ticket (Pending (WaitingJobsCons waitingJob other))
              if success then
                -- Job is added to the list
                go signals resolvedCount
              else
                -- This thread was interleaved with another operation on the
                -- Signal, try again with the new value.
                try' newTicket
    go [] resolvedCount
      | count == resolvedCount = return True
      | resolvedCount == 0 = return False
      | otherwise = do
        old <- fetchSubAtomic dependencies resolvedCount
        -- Note that in a rare situation it might occur that a signal was
        -- intially unresolved, but resolved at this point. Hence we must check
        -- whether the counter is now 0
        return $ old == resolvedCount
  go nativeSignals 0


{-
-- An individual computation is a job consisting of a sequence of actions to be
-- executed by the worker threads in parallel.
--
type Action = IO ()

data Task
  = Work Action
  | Retire

data Job = Job
  { jobTasks  :: !(Seq Action)    -- actions required to complete this job
  , jobDone   :: !(Maybe Action)  -- execute after the last action is completed
  }

data Workers = Workers
  { workerCount       :: {-# UNPACK #-} !Int                      -- number of worker threads (length workerThreadIds)
  , workerActive      :: {-# UNPACK #-} !(IORef (MVar ()))        -- fill to signal to the threads to wake up
  , workerTaskQueue   :: {-# UNPACK #-} !(LinkedQueue Task)       -- tasks currently being executed; may be from different jobs
  , workerThreadIds   :: ![ThreadId]                              -- to send signals to / kill
  , workerException   :: !(MVar (Seq (ThreadId, SomeException)))  -- XXX: what should we do with these?
  }


-- Schedule a job to be executed by the worker threads. May be called
-- concurrently.
--
{-# INLINEABLE schedule #-}
schedule :: Workers -> Job -> IO ()
schedule workers Job{..} = do
  -- Generate the work list. If there is a finalisation action, there is a bit
  -- of extra work to do at each step.
  --
  tasks <- case jobDone of
             Nothing    -> return $ fmap Work jobTasks
             Just done  -> do
                -- The thread which finishes the last task runs the finalisation
                -- action, so keep track of how many items have been completed.
                --
                count <- newAtomic (Seq.length jobTasks)
                return $ flip fmap jobTasks $ \io -> Work $ do
                  _result   <- io
                  remaining <- fetchSubAtomic count -- returns old value
                  when (remaining == 1) done

  -- Submit the tasks to the queue to be executed by the worker threads.
  --
  pushTasks workers tasks


-- Workers can either be executing tasks (real work), waiting for work, or
-- going into retirement (whence the thread will exit).
--
-- So that threads don't spin endlessly on an empty queue waiting for work,
-- they will automatically sleep waiting on the signal MVar after several
-- failed retries. Note that 'readMVar' is multiple wake up, so all threads
-- will be efficiently woken up when new work is added via 'submit'.
--
-- The MVar is stored in an IORef. When scheduling new work, we resolve the
-- old MVar by putting a value in it, and we put a new, at that moment
-- unresolved, MVar in the IORef. If the queue is empty in runWorker, then
-- we will after some attempts wait on an MVar. It is essential that we
-- first get the MVar out of the IORef, before trying to read from the
-- queue. If this would have been done the other way around, we could have
-- a race condition, where new work is pushed after we tried to dequeue
-- work and before we wait on an MVar. We then wait on the new MVar, which
-- may cause that this thread stalls forever.
--
runWorker :: ThreadId -> IORef (MVar ()) -> LinkedQueue Task -> IO ()
runWorker tid ref queue = loop 0
  where
    loop :: Int16 -> IO ()
    loop !retries = do
      -- Extract the activation MVar from the IORef, before trying to claim
      -- an item from the work queue
      var <- readIORef ref
      req <- tryPopR queue
      case req of
        -- The number of retries and thread delay on failure are knobs which can
        -- be tuned. Having these values too high results in busy work which
        -- will detract from time spent adding new work thus reducing
        -- productivity, whereas low values will reduce responsiveness and thus
        -- also reduce productivity.
        --
        -- TODO: Tune these values a bit
        --
        Nothing   -> if retries < 16
                       then loop (retries+1)
                       else do
                         -- This thread will sleep, by waiting on the MVar (var) we previously
                         -- extracted from the IORef (ref)
                         --
                         -- When some other thread pushes new work, it will also write to that MVar
                         -- and this thread will wake up.
                         message ("sched: Thread " % int % " sleeping") (getThreadId tid)

                         -- blocking, wake-up when new work is available
                         () <- readMVar var
                         loop 0
        --
        Just task -> case task of
                       Work io -> io >> loop 0
                       Retire  -> message ("sched: Thread " % int % " shutting down") (getThreadId tid)


-- Spawn a new worker thread for each capability
--
hireWorkers :: IO Workers
hireWorkers = do
  ncpu    <- getNumCapabilities
  workers <- hireWorkersOn [0 .. ncpu-1]
  return workers

-- Spawn worker threads on the specified capabilities
--
hireWorkersOn :: [Int] -> IO Workers
hireWorkersOn caps = do
  active          <- newEmptyMVar
  workerActive    <- newIORef active
  workerException <- newEmptyMVar
  workerTaskQueue <- newQ
  workerThreadIds <- forM caps $ \cpu -> do
                       tid <- mask_ $ forkOnWithUnmask cpu $ \restore -> do
                                tid <- myThreadId
                                catch
                                  (restore $ runWorker tid workerActive workerTaskQueue)
                                  (appendMVar workerException . (tid,))
                       --
                       message ("sched: fork Thread " % int % " on capability " % int) (getThreadId tid) cpu
                       return tid
  --
  workerThreadIds `deepseq` return Workers { workerCount = length workerThreadIds, ..}


-- Submit a job telling every worker to retire. Currently pending tasks will be
-- completed first.
--
retireWorkers :: Workers -> IO ()
retireWorkers workers@Workers{..} =
  pushTasks workers (Seq.replicate workerCount Retire)


-- Pushes work to the task queue
--
-- Wakes up the worker threads if needed, by writing to the old MVar in
-- workerActive. We replace workerActive with a new, empty MVar, such that
-- we can wake them up later when we again have new work.
--
pushTasks :: Workers -> Seq Task -> IO ()
pushTasks Workers{..} tasks = do
  -- Push work to the queue
  mapM_ (pushL workerTaskQueue) tasks

  -- Create a new MVar, which we use in a later call to pushTasks to wake
  -- up the threads, then swap the MVar in the IORef workerActive, with the
  -- new MVar.
  --
  -- This must be atomic, to prevent race conditions when two threads are
  -- adding new work. Without the atomic, it may occur that some MVar is
  -- never resolved, causing that a worker thread which waits on that MVar
  -- to stall.
  new <- newEmptyMVar
  old <- atomicModifyIORef' workerActive (new,)

  -- Resolve the old MVar to wake up all waiting threads
  putMVar old ()


-- Kill worker threads immediately.
--
fireWorkers :: Workers -> IO ()
fireWorkers Workers{..} =
  mapM_ killThread workerThreadIds

-- Number of workers
--
numWorkers :: Workers -> Int
numWorkers = workerCount

-}

-- Utility
-- -------

data Atomic = Atomic !(MutableByteArray# RealWorld)

{-# INLINE newAtomic #-}
newAtomic :: Int -> IO Atomic
newAtomic (I# n#) = IO $ \s0 ->
  case SIZEOF_HSINT                 of { I# size#       ->
  case newByteArray# size# s0       of { (# s1, mba# #) ->
  case writeIntArray# mba# 0# n# s1 of { s2             ->  -- non-atomic is ok
    (# s2, Atomic mba# #) }}}

{-# INLINE fetchSubAtomic #-}
fetchSubAtomic :: Atomic -> Int -> IO Int
fetchSubAtomic (Atomic mba#) (I# i) = IO $ \s0 ->
  case fetchSubIntArray# mba# 0# i s0 of { (# s1, old# #) ->
    (# s1, I# old# #) }

{-
{-# INLINE appendMVar #-}
appendMVar :: MVar (Seq a) -> a -> IO ()
appendMVar mvar a =
  mask_ $ do
    ma <- tryTakeMVar mvar
    case ma of
      Nothing -> putMVar mvar (Seq.singleton a)
      Just as -> putMVar mvar (as Seq.|> a)
-}

-- Debug
-- -----

{-# INLINE message #-}
message :: Format (IO ()) a -> a
message = Debug.traceM Debug.dump_sched
-}
