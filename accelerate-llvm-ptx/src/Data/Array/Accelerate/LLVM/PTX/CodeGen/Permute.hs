-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen.Permute
-- Copyright   : [2016..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen.Permute (
  lockArraySize, atomically
) where

import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic                as A
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Sugar

import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.Target

import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.RMW                                as RMW
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.GetElementPtr
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation

import Prelude

{-
-- Forward permutation specified by an indexing mapping. The resulting array is
-- initialised with the given defaults, and any further values that are permuted
-- into the result array are added to the current value using the combination
-- function.
--
-- The combination function must be /associative/ and /commutative/. Elements
-- that are mapped to the magic index 'ignore' are dropped.
--
-- Parallel forward permutation has to take special care because different
-- threads could concurrently try to update the same memory location. Where
-- available we make use of special atomic instructions and other optimisations,
-- but in the general case each element of the output array has a lock which
-- must be obtained by the thread before it can update that memory location.
--
-- TODO: After too many failures to acquire the lock on an element, the thread
-- should back off and try a different element, adding this failed element to
-- a queue or some such.
--
mkPermute
    :: HasCallStack
    => UID
    -> Gamma            aenv
    -> ArrayR (Array sh e)
    -> ShapeR sh'
    -> IRPermuteFun PTX aenv (e -> e -> e)
    -> IRFun1       PTX aenv (sh -> PrimMaybe sh')
    -> MIRDelayed   PTX aenv (Array sh e)
    -> CodeGen      PTX      (IROpenAcc PTX aenv (Array sh' e))
mkPermute uid aenv repr shr' IRPermuteFun{..} project arr =
  case atomicRMW of
    Just (rmw, f) -> mkPermute_rmw   uid aenv repr shr' rmw f   project arr
    _             -> mkPermute_mutex uid aenv repr shr' combine project arr


-- Parallel forward permutation function which uses atomic instructions to
-- implement lock-free array updates.
--
-- Atomic instruction support on CUDA devices is a bit patchy, so depending on
-- the element type and compute capability of the target hardware we may need to
-- emulate the operation using atomic compare-and-swap.
--
--              Int32    Int64    Float16    Float32    Float64
--           +-------------------------------------------------
--    (+)    |  2.0       2.0       7.0        2.0        6.0
--    (-)    |  2.0       2.0        x          x          x
--    (.&.)  |  2.0       3.2
--    (.|.)  |  2.0       3.2
--    xor    |  2.0       3.2
--    min    |  2.0       3.2        x          x          x
--    max    |  2.0       3.2        x          x          x
--    CAS    |  2.0       2.0
--
-- Note that NVPTX requires at least compute 2.0, so we can always implement the
-- lockfree update operations in terms of compare-and-swap.
--
mkPermute_rmw
    :: HasCallStack
    => UID
    -> Gamma aenv
    -> ArrayR (Array sh e)
    -> ShapeR sh'
    -> RMWOperation
    -> IRFun1     PTX aenv (e -> e)
    -> IRFun1     PTX aenv (sh -> PrimMaybe sh')
    -> MIRDelayed PTX aenv (Array sh e)
    -> CodeGen    PTX      (IROpenAcc PTX aenv (Array sh' e))
mkPermute_rmw uid aenv (ArrayR shr tp) shr' rmw update project marr = do
  dev <- liftCodeGen $ asks ptxDeviceProperties
  --
  let
      outR                = ArrayR shr' tp
      (arrOut, paramOut)  = mutableArray outR "out"
      (arrIn,  paramIn)   = delayedArray "in" marr
      paramEnv            = envParam aenv
      start               = liftInt 0
      --
      bytes               = bytesElt tp
      compute             = computeCapability dev
      compute32           = Compute 3 2
      compute60           = Compute 6 0
      compute70           = Compute 7 0
  --
  makeOpenAcc uid "permute_rmw" (paramOut ++ paramIn ++ paramEnv) $ do

    shIn  <- delayedExtent arrIn
    end   <- shapeSize shr shIn

    imapFromTo start end $ \i -> do

      ix  <- indexOfInt shr shIn i
      ix' <- app1 project ix

      when (isJust ix') $ do
        j <- intOfIndex shr' (irArrayShape arrOut) =<< fromJust ix'
        x <- app1 (delayedLinearIndex arrIn) i
        r <- app1 update x

        case rmw of
          Exchange
            -> writeArray TypeInt arrOut j r
          --
          _ | TupRsingle (SingleScalarType s)   <- tp
            , adata                             <- irArrayData arrOut
            -> do
                  addr <- instr' $ GetElementPtr $ GEP1 (SingleScalarType s) (asPtr defaultAddrSpace (op s adata)) (op integralType j)
                  --
                  let
                      rmw_integral :: IntegralType t -> Operand (Ptr t) -> Operand t -> CodeGen PTX ()
                      rmw_integral t ptr val
                        | primOk    = void . instr' $ AtomicRMW (IntegralNumType t) NonVolatile rmw ptr val (CrossThread, AcquireRelease)
                        | otherwise =
                            case rmw of
                              RMW.And -> atomicCAS_rmw s' (A.band t (ir t val)) ptr
                              RMW.Or  -> atomicCAS_rmw s' (A.bor  t (ir t val)) ptr
                              RMW.Xor -> atomicCAS_rmw s' (A.xor  t (ir t val)) ptr
                              RMW.Min -> atomicCAS_cmp s' A.lt ptr val
                              RMW.Max -> atomicCAS_cmp s' A.gt ptr val
                              _       -> internalError "unexpected transition"
                        where
                          s'      = NumSingleType (IntegralNumType t)
                          primOk  = compute >= compute32
                                 || bytes == 4
                                 || case rmw of
                                      RMW.Add -> True
                                      RMW.Sub -> True
                                      _       -> False

                      rmw_floating :: FloatingType t -> Operand (Ptr t) -> Operand t -> CodeGen PTX ()
                      rmw_floating t ptr val =
                        case rmw of
                          RMW.Min       -> atomicCAS_cmp s' A.lt ptr val
                          RMW.Max       -> atomicCAS_cmp s' A.gt ptr val
                          RMW.Sub       -> atomicCAS_rmw s' (A.sub n (ir t val)) ptr
                          RMW.Add
                            | primAdd   -> atomicAdd_f t ptr val
                            | otherwise -> atomicCAS_rmw s' (A.add n (ir t val)) ptr
                          _             -> internalError "unexpected transition"
                        where
                          n       = FloatingNumType t
                          s'      = NumSingleType n
                          primAdd =
                            case t of
                              TypeHalf   -> compute >= compute70
                              TypeFloat  -> True
                              TypeDouble -> compute >= compute60
                  case s of
                    NumSingleType (IntegralNumType t) -> rmw_integral t addr (op t r)
                    NumSingleType (FloatingNumType t) -> rmw_floating t addr (op t r)
          --
          _ -> internalError "unexpected transition"

    return_


-- Parallel forward permutation function which uses a spinlock to acquire
-- a mutex before updating the value at that location.
--
mkPermute_mutex
    :: UID
    -> Gamma          aenv
    -> ArrayR (Array sh e)
    -> ShapeR sh'
    -> IRFun2     PTX aenv (e -> e -> e)
    -> IRFun1     PTX aenv (sh -> PrimMaybe sh')
    -> MIRDelayed PTX aenv (Array sh e)
    -> CodeGen    PTX      (IROpenAcc PTX aenv (Array sh' e))
mkPermute_mutex uid aenv (ArrayR shr tp) shr' combine project marr =
  let
      outR                  = ArrayR shr' tp
      lockR                 = ArrayR (ShapeRsnoc ShapeRz) (TupRsingle scalarTypeWord32)
      (arrOut,  paramOut)   = mutableArray outR "out"
      (arrLock, paramLock)  = mutableArray lockR "lock"
      (arrIn,   paramIn)    = delayedArray "in" marr
      paramEnv              = envParam aenv
      start                 = liftInt 0
  in
  makeOpenAcc uid "permute_mutex" (paramOut ++ paramLock ++ paramIn ++ paramEnv) $ do

    shIn  <- delayedExtent arrIn
    end   <- shapeSize shr shIn

    imapFromTo start end $ \i -> do

      ix  <- indexOfInt shr shIn i
      ix' <- app1 project ix

      -- project element onto the destination array and (atomically) update
      when (isJust ix') $ do
        j <- intOfIndex shr' (irArrayShape arrOut) =<< fromJust ix'
        x <- app1 (delayedLinearIndex arrIn) i

        atomically arrLock j $ do
          y <- readArray TypeInt arrOut j
          r <- app2 combine x y
          writeArray TypeInt arrOut j r

    return_
-}

-- Number of locks in the array of locks.
lockArraySize :: Int
lockArraySize = 64 * 1024 * 8

-- Atomically execute the critical section only when the lock at the given
-- array index is obtained. The thread spins waiting for the lock to be
-- released with exponential backoff on failure in case the lock is
-- contended.
--
-- > uint32_t ns = 8;
-- > while ( atomic_exchange(&lock[i], 1) == 1 ) {
-- >     __nanosleep(ns);
-- >     if ( ns < 256 ) {
-- >         ns *= 2;
-- >     }
-- > }
--
-- Requires independent thread scheduling features of SM7+.
-- Previous versions of Accelerate also had a variant for older GPUs.
-- These older GPUs use lockstep execution
-- and the current implementation of atomically would cause deadlocks if
-- multiple threads in the same warp try to acquire the same lock. We do not
-- support these GPUs (for other reasons).
--
atomically
    :: Operands Word64
    -> CodeGen PTX a
    -> CodeGen PTX a
atomically idx action = do
  byteIdx <- A.quot TypeWord64 idx $ A.liftWord64 8
  bitIdx <- A.rem TypeWord64 idx $ A.liftWord64 8
  bitIdx' <- A.fromIntegral TypeWord64 (IntegralNumType TypeInt) bitIdx

  let
      i32 = TupRsingle scalarTypeInt32
      bufptr = LocalReference (PrimType (PtrPrimType (primType @Word8) defaultAddrSpace)) "locks_array"

  --
  entry <- newBlock "spinlock.entry"
  sleep <- newBlock "spinlock.backoff"
  moar  <- newBlock "spinlock.backoff-moar"
  start <- newBlock "spinlock.critical-start"
  end   <- newBlock "spinlock.critical-end"
  exit  <- newBlock "spinlock.exit"
  ns    <- fresh i32

  addr  <- instr' $ GetElementPtr $ GEP1 bufptr $ op integralType byteIdx
  top   <- br entry

  OP_Word64 mask' <- A.shiftL TypeWord64 (A.liftWord64 1) bitIdx'
  mask <- instr' $ Trunc (IntegralBoundedType TypeWord64) (IntegralBoundedType TypeWord8) mask'

  -- Loop until this thread has completed its critical section. If the slot
  -- was unlocked we just acquired the lock and the thread can perform its
  -- critical section, otherwise sleep the thread and try again later.
  setBlock entry
  -- Using atomic_fetch_or, acquire the lock on the computed bit.
  old  <- instrMD (AtomicRMW numType NonVolatile Or addr mask (CrossThread, Acquire)) (bufferMetadata' Nothing)
  -- Check if the bit was zero before our atomic_fetch_or.
  check <- A.band TypeWord8 old (OP_Word8 mask)
  -- If it is zero, we acquired the lock
  ok   <- A.eq singleType check $ A.liftWord8 0
  _     <- cbr ok start sleep

  -- We did not acquire the lock. Sleep the thread for a small amount of
  -- time and (possibly) increase the sleep duration for the next round
  setBlock sleep
  _     <- nanosleep ns
  p     <- A.lt singleType ns (ir TypeInt32 (integral integralType 256))
  _     <- cbr p moar entry

  setBlock moar
  ns'   <- A.mul numType ns (ir TypeInt32 (integral integralType 2))
  _     <- phi' i32 entry ns [(ir TypeInt32 (integral (integralType) 8), top), (ns, sleep), (ns', moar)]
  _     <- br entry

  -- If we just acquired the lock, execute the critical section, then
  -- release the lock and continue with your day.
  setBlock start
  r     <- action
  _     <- br end

  setBlock end
  OP_Word8 maskComplement <- A.complement TypeWord8 (OP_Word8 mask)
  _     <- instrMD (AtomicRMW numType NonVolatile And addr maskComplement (CrossThread, Release)) (bufferMetadata' Nothing)
  _     <- __threadfence_grid   -- TODO: why is this required?
  _     <- br exit

  setBlock exit
  return r


