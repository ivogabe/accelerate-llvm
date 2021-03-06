{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen.Queue
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Abstractions for creating simply dynamically scheduled work queues. This
-- works by atomically incrementing a global counter (in global memory) and
-- distributing this result to each thread in the block (via shared memory).
-- Thus there is an additional ~1000 cycle overhead for a thread block to
-- determine their next work item. This also implies all thread blocks are
-- contending for the same global counter.
--
-- In practice this extra overhead is not always worth paying. We use it for
-- segmented reductions, because the length of each segment is unknown apriori
-- and the entire thread block participates in the reduction of a segment. On
-- the other hand, the arithmetically unbalanced mandelbrot fractal program was
-- (generally) slower with this addition, so for now at least keep (morally)
-- balanced operations (map, generate) with a static schedule. (Admittidely this
-- test was on my very old 650M, so newer/more powerful GPUs with faster atomic
-- instructions or more inflight thread blocks could benefit more.)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen.Queue
  where

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic                as A
import Data.Array.Accelerate.LLVM.CodeGen.Downcast
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Sugar

import Data.Array.Accelerate.LLVM.PTX.Analysis.Launch
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.Target

import LLVM.AST.Type.Constant
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation
import qualified LLVM.AST.Global                                    as LLVM
import qualified LLVM.AST.Linkage                                   as LLVM
import qualified LLVM.AST.Name                                      as LLVM
import qualified LLVM.AST.Type                                      as LLVM
import qualified LLVM.AST.Type.Instruction.RMW                      as RMW


-- Interface
-- ---------

type WorkQueue = (Operand (Ptr Int32), Operand (Ptr Int32))

-- Declare a new dynamically scheduled global work queue. Don't forget to
-- initialise the queue with the kernel generated by 'mkQueueInit'.
--
globalWorkQueue :: CodeGen WorkQueue
globalWorkQueue = do
  sn <- freshName
  declare $ LLVM.globalVariableDefaults
    { LLVM.name         = LLVM.Name "__queue__"
    , LLVM.type'        = LLVM.IntegerType 32
    , LLVM.alignment    = 4
    }
  declare $ LLVM.globalVariableDefaults
    { LLVM.name         = downcast sn
    , LLVM.addrSpace    = sharedMemAddrSpace
    , LLVM.type'        = LLVM.IntegerType 32
    , LLVM.linkage      = LLVM.Internal
    , LLVM.alignment    = 4
    }
  return ( ConstantOperand (GlobalReference type' "__queue__")
         , ConstantOperand (GlobalReference type' sn) )


-- Dequeue the next 'n' items from the work queue for evaluation by the calling
-- thread block. Each thread in the thread block receives the index of the start
-- of the newly acquired range.
--
dequeue :: WorkQueue -> IR Int32 -> CodeGen (IR Int32)
dequeue (queue, smem) n = do
  tid <- threadIdx
  when (A.eq scalarType tid (lift 0)) $ do
    v <- instr' $ AtomicRMW integralType NonVolatile RMW.Add queue (op integralType n) (CrossThread, AcquireRelease)
    _ <- instr' $ Store Volatile smem v
    return ()
  --
  __syncthreads
  v <- instr' $ Load scalarType Volatile smem
  return (ir integralType v)


-- Initialisation kernel
-- ---------------------

-- This kernel is used to initialise the dynamically scheduled work queue. It
-- must be called before the main kernel, which uses the work queue, is invoked.
--
mkQueueInit
    :: DeviceProperties
    -> CodeGen (IROpenAcc PTX aenv a)
mkQueueInit dev =
  let
      (start, _end, paramGang)  = gangParam
      config                    = launchConfig dev [1] (\_ -> 0) (\_ _ -> 1) [|| \_ _ -> 1 ||]
  in
  makeOpenAccWith config "qinit" paramGang $ do
    (queue,_) <- globalWorkQueue
    _         <- instr' $ Store Volatile queue (op integralType start)
    return_

