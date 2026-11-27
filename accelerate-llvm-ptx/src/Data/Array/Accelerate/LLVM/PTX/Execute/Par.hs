-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.Execute.Par
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.Execute.Par (
  Par, evalPar, ptxStream, liftPar, spawnPar, block,
  cleanUpTouchLifetime, cleanUpTouchForeignPtr, cleanUpUnregisterBuffer,
  cleanUpIO,
  bufferRegister, bufferUnregister,
) where

import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Lifetime

import Data.Array.Accelerate.LLVM.State

import Data.Array.Accelerate.LLVM.PTX.State
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Array.Accelerate.LLVM.PTX.Execute.Stream                ( Stream )
import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Event       as Event
import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Stream      as Stream

import qualified Foreign.CUDA.Driver.Stream                         as CUDA
import qualified Foreign.CUDA.Ptr                                   as CUDA
import qualified Foreign.CUDA.Driver                                as CUDA

import Foreign.Ptr
import Foreign.ForeignPtr

import Control.Monad                                                ( forM_, void )
import Control.Monad.IO.Class                                       ( MonadIO(liftIO) )
import Control.Monad.Reader                                         ( MonadReader, ReaderT )
import qualified Control.Monad.Reader                               as Reader
import Control.Monad.State                                          ( MonadState, StateT )
import qualified Control.Monad.State                                as State
import Control.Monad.Trans                                          ( MonadTrans(lift) )
import Control.Concurrent
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Word
import System.IO.Unsafe                                             ( unsafePerformIO )


newtype Par a = Par { runPar :: ReaderT Stream (StateT [CleanUp] (LLVM PTX)) a }
    deriving ( Functor, Applicative, Monad, MonadIO, MonadReader Stream, MonadState [CleanUp] )

-- CleanUp to be executed after the Par monad synchronises the CPU and GPU (via block)
data CleanUp where
  TouchLifetime :: Lifetime t -> CleanUp
  TouchForeignPtr :: ForeignPtr t -> CleanUp
  Unregister :: Ptr t -> CleanUp
  CleanUpIO :: IO () -> CleanUp

-- | Evaluate a parallel computation
--
{-# INLINE evalPar #-}
evalPar :: Par a -> LLVM PTX a
evalPar p = do
  stream <- Stream.create
  result <- State.evalStateT (Reader.runReaderT (runPar (p <* block)) stream) []
  Stream.destroy stream
  return result

ptxStream :: Stream -> Stream
ptxStream = id

liftPar :: LLVM PTX a -> Par a
liftPar = Par . lift . lift

spawnPar :: Par () -> Par ()
spawnPar spawned = do
  target <- liftPar $ Reader.asks llvmTarget
  stream <- Reader.asks ptxStream
  event <- liftPar $ Event.waypoint stream
  _ <- liftIO $ forkIO $ evalPTX target $ evalPar $ do
    spawnedStream <- Reader.asks ptxStream
    liftIO $ Event.after event spawnedStream
    spawned
  return ()

cleanUpTouchLifetime :: Lifetime t -> Par ()
cleanUpTouchLifetime lifetime =
  State.modify' (TouchLifetime lifetime :)

cleanUpTouchForeignPtr :: ForeignPtr t -> Par ()
cleanUpTouchForeignPtr ptr =
  State.modify' (TouchForeignPtr ptr :)

cleanUpUnregisterBuffer :: Ptr t -> Par ()
cleanUpUnregisterBuffer ptr =
  State.modify' (Unregister ptr :)

cleanUpIO :: IO () -> Par ()
cleanUpIO action =
  State.modify' (CleanUpIO action :)

runCleanUp :: Par ()
runCleanUp = do
  list <- State.get
  State.put []
  -- Run oldest clean up instruction first
  liftIO $ forM_ (reverse list) $ \case
    TouchLifetime lifetime -> touchLifetime lifetime
    TouchForeignPtr ptr -> touchForeignPtr ptr
    Unregister ptr -> bufferUnregister ptr
    CleanUpIO action -> action

-- Synchronises the CPU with the GPU. Blocks execution on the CPU until all
-- operations submitted to the GPU, from this Par instance, have been completed.
block :: Par ()
block = do
  stream <- Reader.ask
  liftIO $ CUDA.block stream
  runCleanUp

-- Keep track of which buffers (on the host) are registered to CUDA.
-- Registering of buffers should only happen once per buffer, and thus
-- needs extra protection for concurrent execution.
data BufferState
  -- | The buffer is registered to CUDA.
  -- We keep track of the number of threads using this allocation.
  = BufferStateRegistered {-# UNPACK #-} !Int
  -- | A thread is registering or unregistering this buffer.
  -- While this is in progress, other threads cannot register or
  -- unregister this buffer. They can wait by reading from the MVar.
  | BufferStateLocked !(MVar ())

{-# NOINLINE bufferStates #-}
bufferStates :: MVar (IntMap BufferState)
bufferStates = unsafePerformIO $ newMVar IntMap.empty

-- Concurrent uses of the same ptr should have the same size
-- (which is the case for Accelerate arrays)
bufferRegister :: Bool -> Int -> Ptr Word8 -> IO ()
bufferRegister unique byteSize ptr = do
  if unique then
    -- If this thread is the only thread working with ptr (eg because we just
    -- allocated a new array), then we do not need to worry about a lock.
    go Nothing
  else do
    -- Otherwise, we first need to acquire the lock.
    states <- takeMVar bufferStates
    case states IntMap.!? key of
      Nothing -> do
        -- Not registered yet. Create a lock, to prevent other threads from
        -- concurrently working with the same buffer.
        lock <- newEmptyMVar
        putMVar bufferStates $! IntMap.insert key (BufferStateLocked lock) states
        go $ Just lock
      Just (BufferStateLocked lock) -> do
        -- Wait on lock, and try again
        putMVar bufferStates states
        readMVar lock -- Blocks until lock is released
        bufferRegister unique byteSize ptr
      Just (BufferStateRegistered count) -> do
        -- Already registered. Increase the reference count
        putMVar bufferStates $! IntMap.insert key (BufferStateRegistered $ count + 1) states
  where
    key = fromIntegral $ ptrToIntPtr ptr
    go :: Maybe (MVar ()) -> IO ()
    go lock = do
      void $ CUDA.registerArray [] byteSize ptr
      states <- takeMVar bufferStates
      -- Set reference count to 1
      putMVar bufferStates $! IntMap.insert key (BufferStateRegistered 1) states
      -- Release the lock
      case lock of
        Nothing -> return ()
        Just l -> putMVar l ()

-- Note: while a buffer may have been unique in bufferRegister, it might now be
-- shared, since clean-up code runs asynchronously
bufferUnregister :: Ptr a -> IO ()
bufferUnregister ptr = do
  -- Decrement reference count and create lock when reference count becomes 0
  states <- takeMVar bufferStates
  case states IntMap.!? key of
    Nothing -> internalError "Cannot unregister a pointer that was not registered"
    Just (BufferStateLocked _) -> internalError "Invalid internal state of buffer. Buffer cannot be unregistered yet when a thread still holds a reference to the buffer."
    Just (BufferStateRegistered count)
      | count < 1 -> internalError "Non-positive reference count is not possible"
      | count > 1 -> do
        -- Decrement reference count
        putMVar bufferStates $! IntMap.insert key (BufferStateRegistered $ count - 1) states
      | otherwise -> do
        -- Reference count becomes zero. Create a lock.
        lock <- newEmptyMVar
        putMVar bufferStates $! IntMap.insert key (BufferStateLocked lock) states

        -- Unregister the pointer
        void $ CUDA.unregisterArray $ CUDA.HostPtr ptr

        -- Remove the entry from the state
        states2 <- takeMVar bufferStates
        putMVar bufferStates $! IntMap.delete key states2
        -- Release the lock
        putMVar lock ()
  where
    key = fromIntegral $ ptrToIntPtr ptr


-- Implementation
-- --------------


{-instance Async PTX where
  type FutureR PTX = Future

  newtype Par PTX a = Par { runPar :: ReaderT ParState (LLVM PTX) a }
    deriving ( Functor, Applicative, Monad, MonadIO )

  {-# INLINEABLE new     #-}
  {-# INLINEABLE newFull #-}
  new       = Future <$> liftIO (newIORef (Empty (return ())))
  newFull v = Future <$> liftIO (newIORef (Full v))

  {-# INLINEABLE spawn #-}
  spawn m = do
    s' <- liftPar Stream.create
    r  <- localParState (const (s', Nothing)) m
    liftIO (Stream.destroy s')
    return r

  {-# INLINEABLE fork #-}
  fork m = do
    s' <- liftPar (Stream.create)
    () <- localParState (const (s', Nothing)) m
    liftIO (Stream.destroy s')

  -- When we call 'put' the actual work may not have been evaluated yet; get
  -- a new event in the current execution stream and once that is filled we can
  -- transition the IVar to Full.
  --
  {-# INLINEABLE put #-}
  put (Future ref) v = do
    stream <- asksParState ptxStream
    kernel <- asksParState ptxKernel
    event  <- liftPar (Event.waypoint stream)
    ready  <- liftIO  (Event.query event)
    let cleanupK = case kernel of
                     Just k -> touchLifetime k
                     Nothing -> return ()
    liftIO . atomicModifyIORef' ref $ \case
      Empty cleanup -> if ready then (Full v, ())
                                else (Pending event (cleanup >> cleanupK) v, ())
      _     -> internalError "multiple put"

  -- Get the value of Future. Since the actual cross-stream synchronisation
  -- happens on the device, we should never have to block/reschedule the main
  -- thread waiting on a value; if we get an empty IVar at this point, something
  -- has gone wrong.
  --
  {-# INLINEABLE get #-}
  get (Future ref) = do
    stream <- asksParState ptxStream
    liftIO  $ do
      ivar <- readIORef ref
      case ivar of
        Full v            -> return v
        Pending event cleanup v -> do
          ready <- Event.query event
          if ready
            then do
              writeIORef ref (Full v)
              cleanup
            else
              Event.after event stream
          return v
        Empty _         -> internalError "blocked on an IVar"

  {-# INLINEABLE block #-}
  block = liftIO . wait

  {-# INLINE liftPar #-}
  liftPar = Par . lift


-- | Block the calling _host_ thread until the value offered by the future is
-- available.
--
{-# INLINEABLE wait #-}
wait :: Future a -> IO a
wait (Future ref) = do
  ivar <- readIORef ref
  case ivar of
    Full v            -> return v
    Pending event cleanup v -> do
      Event.block event
      writeIORef ref (Full v)
      cleanup
      return v
    Empty _         -> internalError "blocked on an IVar"
-}

{-
{-# INLINEABLE putCleanup #-}
putCleanup :: HasCallStack => FutureR PTX a -> IO () -> a -> Par PTX ()
putCleanup (Future ref) cleanup v = do
  stream <- asksParState ptxStream
  kernel <- asksParState ptxKernel
  event  <- liftPar (Event.waypoint stream)
  ready  <- liftIO  (Event.query event)
  let cleanupK = case kernel of
                   Just k -> touchLifetime k
                   Nothing -> return ()
  liftIO . atomicModifyIORef' ref $ \case
    Empty cleanup2 -> if ready then (Full v, ())
                               else (Pending event (cleanup2 >> cleanup >> cleanupK) v, ())
    _     -> internalError "multiple put"

{-# INLINEABLE addCleanup #-}
addCleanup :: HasCallStack => FutureR PTX a -> IO () -> Par PTX ()
addCleanup (Future ref) cleanup = liftIO $ do
  toRunNow <- atomicModifyIORef' ref $ \case
    Full v -> (Full v, cleanup)
    Pending event cleanup2 v -> (Pending event (cleanup2 >> cleanup) v, return ())
    Empty cleanup2 -> (Empty (cleanup2 >> cleanup), return ())
  toRunNow
-}
