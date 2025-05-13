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
  PTXKernelMetadata(..),
  KernelType
) where

-- accelerate

import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Type
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
import LLVM.AST.Type.Function
import Data.ByteString.Short                                        ( ShortByteString, fromShort )
import qualified Data.ByteString.Char8 as Char8
import System.FilePath                                              ( FilePath, (<.>) )
import System.IO.Unsafe
import Control.DeepSeq
import Control.Monad.State
import Data.Typeable
import Foreign.Ptr
import Prettyprinter
import Data.String
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Representation

data PTXKernel env where
  PTXKernel
    :: { kernelObject     :: ObjectR (KernelType env)
       , kernelLinked     :: Lifetime KernelObject
       , kernelId         :: {-# UNPACK #-} !ShortByteString
       , kernelUID        :: {-# UNPACK #-} !UID
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

instance NFData' PTXKernel where
  rnf' (PTXKernel obj !_ !_ !_ !_ s l) = rnf' obj `seq` rnf s `seq` rnf l

newtype PTXKernelMetadata f =
  PTXKernelMetadata { kernelArgsSize :: Int }
    deriving Show

instance NFData' PTXKernelMetadata where
  rnf' (PTXKernelMetadata sz) = rnf sz

instance IsKernel PTXKernel where
  type KernelOperation PTXKernel = PTXOp
  type KernelMetadata  PTXKernel = PTXKernelMetadata

  compileKernel env cluster args = unsafePerformIO $ evalLLVM defaultTarget $ do
    (sz, module') <- codegen fullName env cluster args
    dev <- gets ptxDeviceProperties
    -- TODO: Change simpleLaunchConfig to launchConfig when we use shared memory
    obj <- compile uid (fromString $ fullName) (simpleLaunchConfig dev) module'
    obj `seq` return ()
    linked <- link obj
    return $ PTXKernel obj linked (fromString $ fullName) uid sz detail brief
    where
      (name, detail, brief) = generateKernelNameAndDescription operationName cluster
      fullName = name ++ "_" ++ show uid
      uid = hashOperation cluster args

  kernelMetadata kernel = PTXKernelMetadata $ sizeOfEnv kernel

  encodeKernel = Left . kernelUID

instance PrettyKernel PTXKernel where
  prettyKernel = PrettyKernelFun go
    where
      go :: OpenKernelFun PTXKernel env t -> Adoc
      go (KernelFunLam _ f) = go f
      go (KernelFunBody (PTXKernel _ _ name _ _ "" _))
        = fromString $ take 32 $ toString name
      go (KernelFunBody (PTXKernel _ _ name _ _ detail brief))
        = fromString (take 32 $ toString name)
        <+> flatAlt (group $ line' <> "-- " <> desc)
          ("{- " <> desc <> "-}")
        where desc = group $ flatAlt (fromString brief) (fromString detail)

      toString :: ShortByteString -> String
      toString = Char8.unpack . fromShort

operationName :: PTXOp t -> (Int, String, String)
operationName = \case
  -- PTXMap         -> (2, "map", "maps")
  -- PTXBackpermute -> (1, "backpermute", "backpermutes")
  PTXGenerate    -> (2, "generate", "generates")
  {- PTXPermute     -> (5, "permute", "permutes")
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
  PTXFold1       -> (3, "fold", "folds") -}
