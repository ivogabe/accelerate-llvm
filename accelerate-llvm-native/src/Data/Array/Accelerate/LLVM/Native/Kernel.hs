{-# LANGUAGE GADTs             #-}
{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Accelerate
-- Copyright   : [2014..2022] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Kernel (
  NativeKernel(..),
  NativeKernelMetadata(..),
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
import Data.Array.Accelerate.LLVM.Native.State
import Data.Array.Accelerate.LLVM.Native.Operation
import Data.Array.Accelerate.LLVM.Native.Compile.Cache
import Data.Array.Accelerate.LLVM.Native.CodeGen
import Data.Array.Accelerate.LLVM.Native.Compile
import Data.Array.Accelerate.LLVM.Native.Link
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.Execute.Marshal
import qualified LLVM.AST                                           as LLVM
import LLVM.AST.Type.Function
import Data.ByteString.Short                                        ( ShortByteString, fromShort )
import qualified Data.ByteString.Char8 as Char8
import System.FilePath                                              ( FilePath, (<.>) )
import System.IO.Unsafe
import Control.DeepSeq
import Data.Typeable
import Foreign.Ptr
import Prettyprinter
import Data.String
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Representation

data NativeKernel env where
  NativeKernel
    :: { kernelFunction   :: !(Lifetime (FunPtr (KernelType env)))
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
    -> NativeKernel env

instance NFData' NativeKernel where
  rnf' (NativeKernel fn !_ !_ !_ s l) = unsafeGetValue fn `seq` rnf s `seq` rnf l

newtype NativeKernelMetadata f =
  NativeKernelMetadata { kernelArgsSize :: Int }
    deriving Show

instance NFData' NativeKernelMetadata where
  rnf' (NativeKernelMetadata sz) = rnf sz

instance IsKernel NativeKernel where
  type KernelOperation NativeKernel = NativeOp
  type KernelMetadata  NativeKernel = NativeKernelMetadata

  compileKernel env cluster args = unsafePerformIO $ evalLLVM defaultTarget $ do
    (sz, module') <- codegen fullName env cluster args
    obj <- compile uid fullName module'
    funPtr <- link obj
    return $ NativeKernel funPtr fullName uid sz detail brief
    where
      (name, detail, brief) = generateKernelNameAndDescription operationName cluster
      fullName = fromString $ name ++ "-" ++ show uid
      uid = hashOperation cluster args

  kernelMetadata kernel = NativeKernelMetadata $ sizeOfEnv kernel

  encodeKernel = Left . kernelUID

instance PrettyKernel NativeKernel where
  prettyKernel = PrettyKernelFun go
    where
      go :: OpenKernelFun NativeKernel env t -> Adoc
      go (KernelFunLam _ f) = go f
      go (KernelFunBody (NativeKernel _ name _ _ "" _))
        = fromString $ take 32 $ toString name
      go (KernelFunBody (NativeKernel _ name _ _ detail brief))
        = fromString (take 32 $ toString name)
        <+> flatAlt (group $ line' <> "-- " <> desc)
          ("{- " <> desc <> "-}")
        where desc = group $ flatAlt (fromString brief) (fromString detail)

      toString :: ShortByteString -> String
      toString = Char8.unpack . fromShort

operationName :: NativeOp t -> (Int, String, String)
operationName = \case
  NMap         -> (2, "map", "maps")
  NBackpermute -> (1, "backpermute", "backpermutes")
  NGenerate    -> (2, "generate", "generates")
  NPermute     -> (5, "permute", "permutes")
  NPermute'    -> (5, "permute", "permutes")
  NScan LeftToRight
               -> (4, "scanl", "scanls")
  NScan RightToLeft
               -> (4, "scanr", "scanrs")
  NScan1 LeftToRight
               -> (4, "scanl", "scanls")
  NScan1 RightToLeft
               -> (4, "scanr", "scanrs")
  NScan' LeftToRight
               -> (4, "scanl", "scanls")
  NScan' RightToLeft
               -> (4, "scanr", "scanrs")
  NFold        -> (3, "fold", "folds")
  NFold1       -> (3, "fold", "folds")
