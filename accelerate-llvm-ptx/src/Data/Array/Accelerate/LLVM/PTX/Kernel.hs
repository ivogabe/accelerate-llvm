{-# LANGUAGE GADTs             #-}
{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.Kernel
-- Copyright   : [2014..2022] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.Kernel (
  PTXKernel(..),
  PTXKernelPhase(..),
  PTXKernelMetadata(..),
  KernelType
) where

-- accelerate

import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Backend
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Lifetime
import Data.Array.Accelerate.Pretty.Schedule

import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.Operation
import Data.Array.Accelerate.LLVM.PTX.Compile.Cache
import Data.Array.Accelerate.LLVM.PTX.CodeGen
import Data.Array.Accelerate.LLVM.PTX.Compile
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.State
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Array.Accelerate.LLVM.PTX.Link
import Data.Array.Accelerate.LLVM.PTX.Analysis.Launch
import Crypto.Hash.XKCP
import LLVM.AST.Type.Function
import Data.ByteString.Short                                        ( ShortByteString, fromShort )
import qualified Data.ByteString.Char8 as Char8
import System.FilePath                                              ( FilePath, (<.>) )
import System.IO.Unsafe
import Control.DeepSeq
import Control.Monad.Reader
import Data.Typeable
import Foreign.Ptr
import Prettyprinter
import Data.String
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Module

data PTXKernel env where
  PTXKernel
    :: { kernelInit       :: !(Maybe (PTXKernelPhase env))
       , kernelMain       :: !(PTXKernelPhase env)
       , kernelFinish     :: !(Maybe (PTXKernelPhase env))
       , kernelUID        :: {-# UNPACK #-} !UID
       -- Note: [PTX Kernel Grid Size]
       -- We always assign a one-dimensional grid size, for simplicity.
       -- The product of the variables in kernelElements denotes the number
       -- of elements handled by the kernel for the kernel. The maximum grid
       -- size can be computed by dividing this by kernelElementsPerThread.
       -- The actual grid size is the minimum of this
       -- number, and the number of threads that the GPU can execute
       -- concurrently (which depends on things like the register pressure),
       -- and is computed in 'launchConfig'.
       , kernelElements :: [Idx env Int]
       , kernelElementsPerThread :: Int
       -- Note: [Kernel Memory]
       -- Each kernel call gets a memory that is shared between all the threads
       -- working on this kernel.
       -- The storage can for instance be used to synchronise the threads in
       -- case of a parallel scan.
       -- This additional memory is word aligned (e.g. 64-bit on a 64-bit system).
       -- This field contains the size of the kernel memory for this kernel.
       , kernelMemorySize :: {-# UNPACK #-} !Int
       , kernelDescDetail :: String
       , kernelDescBrief  :: String
       }
    -> PTXKernel env

-- There are two notions of 'kernels' in this file. From the Accelerate side, a
-- kernel the compiled variant of a cluster of array operations. Since an array
-- operation may require initialization and finalization code, this may be
-- compiled to three 'CUDA kernels', kernels from the CUDA perspective. The
-- first and last kernel are then executed with a single warp or single thread,
-- and the middle kernel performs the parallel work.
data PTXKernelPhase env where
  PTXKernelPhase
    :: { kernelPhaseObject :: ObjectR (KernelType env)
       , kernelPhaseLinked :: Lifetime KernelObject
       , kernelPhaseId     :: {-# UNPACK #-} !ShortByteString
       }
    -> PTXKernelPhase env

instance NFData' PTXKernel where
  rnf' (PTXKernel p1 p2 p3 !_ sz !_ !_ s l) =
    maybe () rnf' p1 `seq` rnf' p2 `seq` maybe () rnf' p3
      `seq` rnf sz `seq` rnf s `seq` rnf l

instance NFData' PTXKernelPhase where
  rnf' (PTXKernelPhase obj !_ !_) = rnf' obj

newtype PTXKernelMetadata f =
  PTXKernelMetadata { kernelArgsSize :: Int }
    deriving Show

instance NFData' PTXKernelMetadata where
  rnf' (PTXKernelMetadata sz) = rnf sz

instance IsKernel PTXKernel where
  type KernelOperation PTXKernel = PTXOp
  type KernelMetadata  PTXKernel = PTXKernelMetadata

  compileKernel env cluster args = unsafePerformIO $ evalPTX defaultTarget $ do
    ptxCode <- codegen fullName env cluster args

    phaseInit   <- compilePhase uid 1 `mapM` ptxCodeInit   ptxCode
    phaseWork   <- compilePhase uid 0  $     ptxCodeWork   ptxCode
    phaseFinish <- compilePhase uid 2 `mapM` ptxCodeFinish ptxCode
    
    return $ PTXKernel
      phaseInit
      phaseWork
      phaseFinish
      uid
      (ptxCodeElements ptxCode)
      (ptxCodeElementsPerThread ptxCode)
      (ptxCodeKernelMemory ptxCode)
      detail
      brief
    where
      (name, detail, brief) = generateKernelNameAndDescription operationName cluster
      fullName = name ++ "_" ++ show uid
      uid = hashOperation cluster args

  kernelMetadata kernel = PTXKernelMetadata $ sizeOfEnv kernel

  encodeKernel = Left . kernelUID

compilePhase :: UID -> Int -> Module (KernelType env) -> LLVM PTX (PTXKernelPhase env)
compilePhase uid variant m = do
  let uid' = hashIncrement (fromIntegral variant) uid
  dev <- asks ptxDeviceProperties
  let name = fromString $ moduleName m
  obj <- compile uid' name (simpleLaunchConfig dev) m
  obj `seq` return ()
  linked <- link obj
  return $ PTXKernelPhase obj linked name

instance PrettyKernel PTXKernel where
  prettyKernel = PrettyKernelFun go
    where
      go :: OpenKernelFun PTXKernel env t -> Adoc
      go (KernelFunLam _ f) = go f
      go (KernelFunBody (PTXKernel _ phase _ _ _ _ _ "" _))
        = fromString $ take 32 $ toString $ kernelPhaseId phase
      go (KernelFunBody (PTXKernel _ phase _ _ _ _ _ detail brief))
        = fromString (take 32 $ toString $ kernelPhaseId phase)
        <+> flatAlt (group $ line' <> "-- " <> desc)
          ("{- " <> desc <> "-}")
        where desc = group $ flatAlt (fromString brief) (fromString detail)

      toString :: ShortByteString -> String
      toString = Char8.unpack . fromShort

operationName :: PTXOp t -> (Int, String, String)
operationName = \case
  PTXMap         -> (2, "map", "maps")
  PTXBackpermute -> (1, "backpermute", "backpermutes")
  PTXGenerate    -> (2, "generate", "generates")
  PTXPermute     -> (5, "permute", "permutes")
  PTXPermute'    -> (5, "permute", "permutes")
  PTXScan LeftToRight
               -> (4, "scanl", "scanls")
  PTXScan RightToLeft
               -> (4, "scanr", "scanrs")
  PTXScan1 LeftToRight
               -> (4, "scanl", "scanls")
  PTXScan1 RightToLeft
               -> (4, "scanr", "scanrs")
  PTXScan' LeftToRight
               -> (4, "scanl", "scanls")
  PTXScan' RightToLeft
               -> (4, "scanr", "scanrs")
  PTXFold        -> (3, "fold", "folds")
  PTXFold1       -> (3, "fold", "folds")
