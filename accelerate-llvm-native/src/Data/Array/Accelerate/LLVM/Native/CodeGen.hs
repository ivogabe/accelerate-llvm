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
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen
  ( codegen )
  where

-- accelerate
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (shapeRFromRank, shapeType, rank)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Partitioned as P hiding (combine)
import Data.Array.Accelerate.Analysis.Exp
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment hiding ( Empty )
import Data.Array.Accelerate.LLVM.CodeGen.Cluster
import Data.Array.Accelerate.LLVM.CodeGen.Loop (imapFromStepTo, iterFromStepTo)
import Data.Array.Accelerate.LLVM.CodeGen.Default
import Data.Array.Accelerate.LLVM.Native.Operation
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.Target
import Data.Maybe

import LLVM.AST.Type.Module
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Operand
import LLVM.AST.Type.GetElementPtr
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.RMW
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified LLVM.AST.Type.Function as LLVM
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Sugar (IROpenFun2 (app2))
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import Data.Array.Accelerate.LLVM.Native.CodeGen.Permute (atomically)
import Data.Array.Accelerate.AST.LeftHandSide (Exists (Exists))
import Control.Monad
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop as Loop
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import qualified Text.LLVM as LP

codegen :: String
        -> Env AccessGroundR env
        -> Clustered NativeOp args
        -> Args env args
        -> LLVM Native
           ( Int -- The size of the kernel data, shared by all threads working on this kernel.
           , Module (KernelType env))
codegen name env cluster args
 | flat@(FlatCluster shr idxLHS sizes dirs localR localLHS flatOps) <- toFlatClustered cluster args
 , parallelDepth <- flatClusterIndependentLoopDepth flat
 , Exists parallelShr <- shapeRFromRank parallelDepth =
  codeGenFunction linkage name type' (LLVM.Lam argTp "arg" . LLVM.Lam primType "workassist.flag") $ do
    extractEnv

    -- Before the parallel work of a kernel is started, we first run the function once.
    -- This first call will initialize kernel memory (SEE: Kernel Memory)
    -- and decide whether the runtime may try to let multiple threads work on this kernel.
    initBlock <- newBlock "init"
    finishBlock <- newBlock "finish" -- Finish function from the work assisting paper
    workBlock <- newBlock "work"
    _ <- switch (OP_Word64 flag) workBlock [(0xFFFFFFFF, initBlock), (0xFFFFFFFE, finishBlock)]
    let hasPermute = hasNPermute flat
    let useSharded = hasFold flat -- Probably check if scan

    if parallelDepth == 0 && rank shr /= 0 then do
      let (envs, loops) = initEnv gamma shr idxLHS sizes dirs localR localLHS
      let ((idxVar, direction, size), loops') = case loops of
            [] -> internalError "Expected at least one loop since rank shr /= 0"
            (l:ls) -> (l, ls)

      -- let opCode = opCodeGens opCodeGen flatOps
      -- let parGen = parCodeGens (parCodeGen (isDescending direction)) 0 opCode
      -- let parGenSharded = parCodeGens (parCodeGenSharded (isDescending direction)) 0 opCode
      -- Parallelise over first dimension using parallel folds or scans
      case parCodeGens (
        (if useSharded then parCodeGenSharded else parCodeGen) -- Use sharded if operation has a fold
        (isDescending direction)) 0 $ opCodeGens opCodeGen flatOps of
        Nothing -> internalError "Could not generate code for a cluster. Does parCodeGen lack a case for a collective parallel operation?"
        Just (Exists parCodes) -> do
          let hasScan = parCodeGenHasMultipleTileLoops parCodes
          let tileSize =
                if rank shr > 1 then
                  32
                else if hasScan then
                  -- We need to choose a tile size such that the values in the
                  -- first tile loop (the reduce step of the chained scan) are
                  -- still in the cache during the second tile loop (the scan
                  -- step of the chained scan).
                  1024 * 2
                else if useSharded then
                  1024 -- Use smaller tile size when we are using sharded self scheduling
                else
                  1024 * 16 -- TODO: Implement a better heuristic to choose the tile size

          -- Number of tiles
          sizeAdd <- A.add numType size (A.liftInt $ tileSize - 1)
          OP_Int tileCount' <- A.quot TypeInt sizeAdd (A.liftInt tileSize)
          tileCount <- instr' $ BitCast scalarType tileCount'

          let envs' = envs{
            envsLoopDepth = 0,
            envsDescending = isDescending direction,
            envsTileCount = tileCount'
          }

          -- Kernel memory
          let memoryTp' = parCodeGenMemory parCodes
          let memoryTp = StructPrimType False memoryTp'
          kernelMem <- instr' $ PtrCast (PtrPrimType memoryTp defaultAddrSpace) kernelMem'

          setBlock initBlock
          do
            -- Initialize kernel memory
            parCodeGenInitMemory kernelMem envs' TupleIdxSelf parCodes

            when useSharded $ initShards shardIndexes shardSizes workassistIndex (OP_Word64 tileCount)

            -- Decide whether tileCount is large enough
            OP_Bool isSmall <- A.lt singleType (OP_Int tileCount') $ A.liftInt 2
            value <- instr' $ Select isSmall (scalar (scalarType @Word8) 0) (scalar scalarType 1)
            retval_ value

          setBlock finishBlock
          do
            -- Declare fused-away and dead arrays at level zero.
            -- This is for instance needed for `map (+1) $ fold ...`,
            -- or a scanl' or scanr' whose reduced value is not used (like in prescanl).
            envs'' <- bindLocals 0 envs'
            -- Execute code for after the parallel work of this kernel, for
            -- instance to write the result of a fold to the output array.
            parCodeGenFinish kernelMem envs'' TupleIdxSelf parCodes
            retval_ $ scalar (scalarType @Word8) 0

          setBlock workBlock

          -- Emit code to initialize a thread, and get the codes for the tile loops
          tileLoops <- genParallel kernelMem envs' TupleIdxSelf parCodes

          -- Declare fused away arrays
          -- Declare as a tile array if there are multiple tile loops,
          -- otherwise as a single value.
          -- TODO: We can make this more precise by tracking whether arrays are
          -- only used in one tile loop. These arrays can also be stored as a
          -- single value.
          envs'' <- bindLocalsInTile (\_ -> not $ null $ ptOtherLoops tileLoops) 1 tileSize envs'

          let processTile :: (Operand Bool -> Operand Word64 -> Maybe (Operand Word64) -> CodeGen Native ())
              processTile seqMode tileIdx' shardIdx = do
                -- workassistLoop workassistIndex tileCount $ \seqMode tileIdx' -> do
                tileIdx <- instr' $ BitCast scalarType tileIdx'

                tileIdxAbsolute <-
                  -- For a scanr, convert low-to-high indices to high-to-low indices:
                  -- The first block (with tileIdx 0) should now correspond with the last
                  -- values of the array. We implement that by reversing the tile indices here.
                  if isDescending direction then do
                    i <- A.sub numType (OP_Int tileCount') (OP_Int tileIdx)
                    OP_Int j <- A.sub numType i (A.liftInt 1)
                    return j
                  else
                    return tileIdx
                lower <- A.mul numType (OP_Int tileIdxAbsolute) (A.liftInt tileSize)
                upper' <- A.add numType lower (A.liftInt tileSize)
                upper <- A.min singleType upper' size

                -- If there is only a single tile loop (i.e. no parallel scans),
                -- then we don't generate code for a single-threaded mode:
                -- the default mode already is as fast as a single-threaded mode.
                let seqMode' = if null (ptOtherLoops tileLoops) then boolean False else seqMode

                let envs''' = envs''{
                    envsTileIndex = OP_Int tileIdx,
                    envsShardIdx = shardIdx
                  }

                -- Note: ifThenElse' does not generate code for the then-branch if
                -- the condition is a constant. Thus, if a kernel does not have a
                -- scan, we won't generate separate code for a single-threaded mode.
                _ <- A.ifThenElse' (TupRunit, OP_Bool seqMode')
                  -- Sequential mode
                  (do
                    let tileLoop = ptSingleThreaded tileLoops
                    let ann =
                          -- Only do loop peeling if requested and when there are no nested loops.
                          -- Peeling over nested loops causes a lot of code duplication,
                          -- and is probably not worth it.
                          [ Loop.LoopPeel | ptPeel tileLoop && null loops' ]
                          -- We can use LoopNonEmpty since we
                          -- know that each tile is non-empty.
                          -- We cannot vectorize this loop (yet), as LLVM cannot vectorize loops
                          -- containing scans. We should either wait until LLVM supports this,
                          -- or vectorize loops (partially) ourselves.
                          -- As an alternative to vectorization, we ask LLVM to interleave the loop.
                          ++ [ Loop.LoopNonEmpty, Loop.LoopInterleave ]

                    ptBefore tileLoop envs'''
                    Loop.loopWith ann (isDescending direction) lower upper $ \isFirst idx -> do
                      localIdx <- A.sub numType idx lower
                      let envs'''' = envs'''{
                          envsLoopDepth = 1,
                          envsIdx = Env.partialUpdate (op TypeInt idx) idxVar $ envsIdx envs'',
                          envsIsFirst = isFirst,
                          envsTileLocalIndex = localIdx
                        }
                      genSequential envs'''' loops' $ ptIn tileLoop
                    ptAfter tileLoop envs'''
                    return OP_Unit
                  )
                  -- Parallel mode
                  (do
                    forM_ ((True, ptFirstLoop tileLoops) : map (False, ) (ptOtherLoops tileLoops)) $ \(isFirstTileLoop, tileLoop) -> do
                      -- All nested loops are placed in the first tile loop by parCodeGens
                      let loops'' = if isFirstTileLoop then loops' else []
                      let ann =
                            -- Only do loop peeling if requested and when there are no nested loops.
                            -- Peeling over nested loops causes a lot of code duplication,
                            -- and is probably not worth it.
                            [ Loop.LoopPeel | ptPeel tileLoop && null loops'' ]
                            -- LLVM cannot vectorize loops containing scans (yet).
                            -- The first tile loop only does a reduction, others will perform a scan.
                            -- Loops containing permute (not permuteUnique) can
                            -- also not be vectorized.
                            -- Reduction cannot always be vectorized. This might in particular fail
                            -- on reductions of multiple values (tuples/pairs). For now, we thus do
                            -- not request vectorization, until we can reliably know whether LLVM can
                            -- vectorize something, or generate our code in a form that LLVM can
                            -- definitely vectorize.
                            ++ [ Loop.LoopInterleave ] -- Loop.LoopVectorize
                            -- We can use LoopNonEmpty since we
                            -- know that each tile is non-empty.
                            ++ [ Loop.LoopNonEmpty ]

                      ptBefore tileLoop envs'''
                      Loop.loopWith ann (isDescending direction) lower upper $ \isFirst idx -> do
                        localIdx <- A.sub numType idx lower
                        let envs'''' = envs'''{
                            envsLoopDepth = 1,
                            envsIdx = Env.partialUpdate (op TypeInt idx) idxVar $ envsIdx envs'',
                            envsIsFirst = isFirst,
                            envsTileLocalIndex = localIdx
                          }
                        genSequential envs'''' loops'' $ ptIn tileLoop
                      ptAfter tileLoop envs'''
                    return OP_Unit
                  )
                return ()

          if useSharded
            then shardedSelfScheduling shardIndexes shardSizes workassistIndex processTile
            else workassistLoop workassistIndex tileCount (\seq tile -> processTile seq tile Nothing)

          ptExit tileLoops envs'

          retval_ $ scalar (scalarType @Word8) 0
          -- Return the size of kernel memory
          pure $ fst $ primSizeAlignment memoryTp
    else do
      -- Parallelise over all independent dimensions
      let (envs, loops) = initEnv gamma shr idxLHS sizes dirs localR localLHS

      -- If we parallelize over all dimensions, choose a large tile size.
      -- The work per iteration is probably very small.
      -- If we do not parallelize over all dimensions, choose a tile size of 1.
      -- The work per iteration is probably large enough.
      let tileSize = if parallelDepth == rank shr then chunkSize parallelShr else chunkSizeOne parallelShr
      let parSizes = parallelIterSize parallelShr loops

      setBlock initBlock

      tileCount <- chunkCount parallelShr parSizes (A.lift (shapeType parallelShr) tileSize)
      tileCount' <- shapeSize parallelShr tileCount

      -- We are not using kernel memory, so no need to initialize it.

      tileCount64 <- A.fromIntegral TypeInt (IntegralNumType TypeWord64) tileCount'
      initShards shardIndexes shardSizes workassistIndex tileCount64

      OP_Bool isSmall <- A.lt singleType tileCount' $ A.liftInt 2
      value <- instr' $ Select isSmall (scalar (scalarType @Word8) 0) (scalar scalarType 1)

      retval_ value

      setBlock finishBlock
      -- Nothing has to be done in the finish function for this kernel.
      retval_ $ scalar (scalarType @Word8) 0

      setBlock workBlock
      let ann =
            if parallelDepth /= rank shr then []
            else if hasPermute then [Loop.LoopInterleave]
            else [Loop.LoopVectorize]

      tileCount <- chunkCount parallelShr parSizes (A.lift (shapeType parallelShr) tileSize)

      shardedSelfSchedulingChunked ann parallelShr shardIndexes shardSizes workassistIndex tileSize parSizes tileCount $ \idx -> do
        let envs' = envs{
            envsLoopDepth = parallelDepth,
            envsIdx =
              foldr (\(o, i) -> Env.partialUpdate o i) (envsIdx envs)
              $ zip (shapeOperandsToList parallelShr idx) (map (\(i, _, _) -> i) loops),
            -- Independent operations should not depend on envsIsFirst.
            envsIsFirst = OP_Bool $ boolean False,
            envsDescending = False
          }
        genSequential envs' (drop parallelDepth loops) $ opCodeGens opCodeGen flatOps

      pure 0
  where
    (argTp, extractEnv, shardIndexes, shardSizes, workassistIndex, flag, kernelMem', gamma) = bindHeaderEnv env

    isDescending :: LoopDirection Int -> Bool
    isDescending LoopDescending = True
    isDescending _ = False

linkage :: Maybe LP.Linkage
linkage = Just LP.DLLExport

-- initShards needs to be called before sharded self scheduling.
initShards
  :: Operand (Ptr (SizedArray Word64))  -- work indexes of shards
  -> Operand (Ptr (SizedArray Word64))  -- sizes of the shards
  -> Operand (Ptr Word64) -- Finished shards count
  -> Operands Word64 -- Amount of tiles to be divided over the shards. Must be greater than the number of shards
  -> CodeGen Native ()
initShards shardIndexes shardSizes finishedShards tileCount = do

  OP_Bool notenoughTiles <- A.lt singleType tileCount (A.liftWord64 shardAmount)
  OP_Word64 tileDiff <- A.sub numType (A.liftWord64 shardAmount) tileCount
  finished <- instr' $ Select notenoughTiles tileDiff (integral TypeWord64 0)
  _ <- instr' $ Store NonVolatile finishedShards finished

  (OP_Word64 shardMinSize, remainder) <- A.unpair <$> A.quotRem TypeWord64 tileCount (A.liftWord64 shardAmount)

  -- Initialize shardIndexes with the start index of every shard.
  imapFromStepTo [Loop.LoopVectorize, Loop.LoopNonEmpty] (A.liftWord64 0) (A.liftWord64 1) (A.liftWord64 shardAmount) (\(OP_Word64 i) -> do
    shardStart <- A.mul numType (OP_Word64 i) (OP_Word64 shardMinSize)
    addRemainder <- A.min singleType (OP_Word64 i) remainder
    OP_Word64 shard <- A.add numType shardStart addRemainder

    -- Multiply the index by the cache width in bytes to ensure every shard is on a seperate cache line.
    OP_Word64 idxCacheWidth <- A.mul numType (OP_Word64 i) (A.liftWord64 (cacheWidth `div` 8))
    shardIdxArr <- instr' $ GetElementPtr $ GEP shardIndexes (integral TypeWord64 0) $ GEPArray idxCacheWidth GEPEmpty
    _ <- instr' $ Store NonVolatile shardIdxArr shard

    return ()
    )

  -- Initialize shardSizeArray with the last index + 1 of every shard.
  imapFromStepTo [Loop.LoopVectorize, Loop.LoopNonEmpty] (A.liftWord64 0) (A.liftWord64 1) (A.liftWord64 shardAmount) (\(OP_Word64 i) -> do
    indexPlus1 <- A.add numType (OP_Word64 i) (A.liftWord64 1)
    shardStart <- A.mul numType indexPlus1 (OP_Word64 shardMinSize)
    addRemainder <- A.min singleType indexPlus1 remainder
    OP_Word64 shard <- A.add numType shardStart addRemainder

    -- Multiplying by the cache width is not necessary here as shardSizes is only read.
    shardSizeArray <- instr' $ GetElementPtr $ GEP shardSizes (integral TypeWord64 0) $ GEPArray i GEPEmpty
    _ <- instr' $ Store NonVolatile shardSizeArray shard
    return ()
    )

opCodeGen :: FlatOp NativeOp env idxEnv -> (LoopDepth, OpCodeGen Native NativeOp env idxEnv)
opCodeGen (FlatOp NGenerate args idxArgs) = defaultCodeGenGenerate args idxArgs
opCodeGen (FlatOp NMap args idxArgs) = defaultCodeGenMap args idxArgs
opCodeGen (FlatOp NBackpermute args idxArgs) = defaultCodeGenBackpermute args idxArgs
opCodeGen (FlatOp NPermute
    (combineFun :>: output :>: locks :>: source :>: _)
    (i1 :>: i2 :>: _ :>: i3 :>: _)) =
  defaultCodeGenPermute
    (\envs j _ -> atomically envs locks $ OP_Int j)
    (combineFun :>: output :>: source :>: ArgsNil)
    (i1 :>: i2 :>: i3 :>: ArgsNil)
opCodeGen (FlatOp NPermute' args idxArgs) = defaultCodeGenPermuteUnique args idxArgs
opCodeGen flatOp@(FlatOp NFold (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _) (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx depth outputIdx :>: _)) =
  ( depth
  , OpCodeGenLoop
    flatOp
    PeelNot
    (\envs -> do
      var <- tupleAlloca tp
      seed' <- llvmOfExp (compileArrayInstrEnvs envs) seed
      tupleStore tp var seed'
      return var
    )
    (\var envs -> do
      x <- readArray' envs input inputIdx
      accum <- tupleLoad tp var
      new <-
        if envsDescending envs then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
      tupleStore tp var new
    )
    (\var envs -> do
      value <- tupleLoad tp var
      writeArray' envs output outputIdx value
    )
  )
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
opCodeGen flatOp@(FlatOp NFold1 (ArgFun fun :>: input :>: output :>: _) (_ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx depth outputIdx :>: _)) =
  -- TODO: Try to find an identity value, and convert to NFold
  ( depth
  , OpCodeGenLoop
    flatOp
    PeelGuaranteed
    (\_ -> tupleAlloca tp)
    (\var envs -> do
      x <- readArray' envs input inputIdx
      -- Note: if the loop peeling is applied (separating the first iteration
      -- of the loop), then this code will be executed twice. envsIsFirst envs
      -- will then either be a constant True, or a constant False.
      -- ifThenElse' (opposed to the version with a prime) will then generate
      -- code for only one branch, and thus also without conditional jumps.
      new <- A.ifThenElse' (tp, envsIsFirst envs)
        ( do
          return x
        )
        ( do
          accum <- tupleLoad tp var
          if envsDescending envs then
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
          else
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
        )
      tupleStore tp var new
    )
    (\var envs -> do
      value <- tupleLoad tp var
      writeArray' envs output outputIdx value
    )
  )
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
opCodeGen flatOp@(FlatOp (NScan1 _) (ArgFun fun :>: input :>: output :>: _) (_ :>: IdxArgIdx depth inputIdx :>: IdxArgIdx _ outputIdx :>: _)) =
  -- TODO: Try to find an identity value to prevent loop peeling / the conditional in the body of the loop.
  -- Ideally we add a PostScan as primitive, such that we can convert a scan1 into a postscan
  ( depth - 1
  , OpCodeGenLoop
    flatOp
    PeelConditional
    (\_ -> tupleAlloca tp)
    (\var envs -> do
      x <- readArray' envs input inputIdx
      new <- A.ifThenElse' (tp, envsIsFirst envs)
        ( do
          return x
        )
        ( do
          accum <- tupleLoad tp var
          if envsDescending envs then
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
          else
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
        )
      tupleStore tp var new
      writeArray' envs output outputIdx new
    )
    (\_ _ -> return ())
  )
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
opCodeGen flatOp@(FlatOp (NScan' _)
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: foldOutput :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: IdxArgIdx depth foldOutputIdx :>: _)) =
  ( depth
  , OpCodeGenLoop
    flatOp
    PeelNot
    (\envs -> do
      var <- tupleAlloca tp
      seed' <- llvmOfExp (compileArrayInstrEnvs envs) seed
      tupleStore tp var seed'
      return var
    )
    (\var envs -> do
      accum <- tupleLoad tp var
      writeArray' envs output outputIdx accum
      x <- readArray' envs input inputIdx
      new <-
        if envsDescending envs then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
      tupleStore tp var new
    )
    (\var envs -> do
      value <- tupleLoad tp var
      writeArray' envs foldOutput foldOutputIdx value
    )
  )
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
opCodeGen flatOp@(FlatOp (NScan LeftToRight)
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx depth inputIdx :>: _ :>: _)) =
  ( depth - 1
  , OpCodeGenLoop
    flatOp
    PeelNot
    (\envs -> do
      var <- tupleAlloca tp
      seed' <- llvmOfExp (compileArrayInstrEnvs envs) seed
      tupleStore tp var seed'
      return var
    )
    (\var envs -> do
      accum <- tupleLoad tp var
      writeArray' envs output inputIdx accum
      x <- readArray' envs input inputIdx
      new <-
        if envsDescending envs then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
      tupleStore tp var new
    )
    (\var envs -> do
      value <- tupleLoad tp var
      let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
      writeArrayAt' envs output rowIdx n' value
    )
  )
  where
    ArgArray _ (ArrayR _ tp) inputSh _ = input
    n = case inputSh of
      TupRpair _ (TupRsingle n') -> n'
      _ -> internalError "Shape impossible"
    rowIdx = case inputIdx of
      TupRpair i _ -> i
      _ -> internalError "Shape impossible"
opCodeGen flatOp@(FlatOp (NScan RightToLeft)
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx depth inputIdx :>: _ :>: _)) =
  ( depth - 1
  , OpCodeGenLoop
    flatOp
    PeelNot
    (\envs -> do
      var <- tupleAlloca tp
      seed' <- llvmOfExp (compileArrayInstrEnvs envs) seed
      tupleStore tp var seed'
      let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
      writeArrayAt' envs output rowIdx n' seed'
      return var
    )
    (\var envs -> do
      accum <- tupleLoad tp var
      x <- readArray' envs input inputIdx
      new <-
        if envsDescending envs then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
      tupleStore tp var new
      writeArray' envs output inputIdx new
    )
    (\_ _ -> return ())
  )
  where
    ArgArray _ (ArrayR _ tp) inputSh _ = input
    n = case inputSh of
      TupRpair _ (TupRsingle n') -> n'
      _ -> internalError "Shape impossible"
    rowIdx = case inputIdx of
      TupRpair i _ -> i
      _ -> internalError "Shape impossible"
opCodeGen _ = internalError "Missing indices when generating code for an operation"

-- Parallel code generation for one-dimensional collective operations (folds and scans).
-- Other operations, either OpCodeGenSingle or nested deeper, are handled in opCodeGen
parCodeGen :: Bool -> FlatOp NativeOp env idxEnv -> Maybe (Exists (ParLoopCodeGen Native env idxEnv))
parCodeGen descending (FlatOp NFold
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _))
  = Just $ parCodeGenFold descending fun (Just seed) input output inputIdx outputIdx
parCodeGen descending (FlatOp NFold1
    (ArgFun fun :>: input :>: output :>: _)
    (_ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _))
  = Just $ parCodeGenFold descending fun Nothing input output inputIdx outputIdx
parCodeGen descending (FlatOp (NScan1 _)
    (ArgFun fun :>: input :>: output :>: _)
    (_ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _))
  = Just $ parCodeGenScan descending False fun Nothing input inputIdx
    (\_ _ -> return ())
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
    (\_ _ -> return ())
parCodeGen descending (FlatOp (NScan' _)
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: foldOutput :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: IdxArgIdx _ foldOutputIdx :>: _))
  = Just $ parCodeGenScan descending False fun (Just seed) input inputIdx
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
    (\_ _ -> return ())
    (\envs result -> writeArray' envs foldOutput foldOutputIdx result)
parCodeGen descending (FlatOp (NScan dir)
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: _ :>: _))
  = case dir of
      LeftToRight -> Just $ parCodeGenScan False descending fun (Just seed) input inputIdx
        (\_ _ -> return ())
        (\envs result -> writeArray' envs output inputIdx result)
        (\_ _ -> return ())
        (\envs result -> do
          let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
          writeArrayAt' envs output rowIdx n' result
        )
      RightToLeft -> Just $ parCodeGenScan False descending fun (Just seed) input inputIdx
        (\envs result -> writeArray' envs output inputIdx result)
        (\_ _ -> return ())
        (\envs result -> do
          let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
          writeArrayAt' envs output rowIdx n' result
        )
        (\_ _ -> return ())
  where
    ArgArray _ _ inputSh _ = input
    n = case inputSh of
      TupRpair _ (TupRsingle n') -> n'
      _ -> internalError "Shape impossible"
    rowIdx = case inputIdx of
      TupRpair i _ -> i
      _ -> internalError "Shape impossible"
parCodeGen _ _ = Nothing

parCodeGenSharded :: Bool -> FlatOp NativeOp env idxEnv -> Maybe (Exists (ParLoopCodeGen Native env idxEnv))
parCodeGenSharded descending (FlatOp NFold
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _))
  = Just $ parCodeGenFold descending fun (Just seed) input output inputIdx outputIdx
parCodeGenSharded descending (FlatOp NFold1
    (ArgFun fun :>: input :>: output :>: _)
    (_ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _))
  = Just $ parCodeGenFold descending fun Nothing input output inputIdx outputIdx
parCodeGenSharded _ _ = Nothing

parCodeGenFold
  :: Bool
  -> Fun env (e -> e -> e)
  -> Maybe (Exp env e)
  -> Arg env (In (sh, Int) e)
  -> Arg env (Out sh e)
  -> ExpVars idxEnv (sh, Int)
  -> ExpVars idxEnv sh
  -> Exists (ParLoopCodeGen Native env idxEnv)
parCodeGenFold descending fun Nothing input output inputIdx outputIdx
  | Just identity <- if descending then findRightIdentity fun else findLeftIdentity fun
  = parCodeGenFold descending fun (Just $ mkConstant tp identity) input output inputIdx outputIdx
  where
    ArgArray _ (ArrayR _ tp) _ _ = output
-- Specialized version for commutative folds with identity
parCodeGenFold descending fun seed input output inputIdx outputIdx
  | isCommutative fun
  , Just s <- seed
  , Just i <- identity
  = parCodeGenFoldCommutative descending fun s i input output inputIdx outputIdx
  | otherwise
  = parCodeGenFoldSharded descending fun seed input inputIdx
    (\envs result -> writeArray' envs output outputIdx result)
  where
    ArgArray _ (ArrayR _ tp) _ _ = output
    identity
      | Just s <- seed
      , if descending then isRightIdentity fun s else isLeftIdentity fun s
      = Just s
      | Just v <- if descending then findRightIdentity fun else findLeftIdentity fun
      = Just $ mkConstant tp v
      | otherwise
      = Nothing

parCodeGenFoldSharded
  :: forall env idxEnv sh e.
     Bool -- Whether the loop is descending
  -> Fun env (e -> e -> e)
  -> Maybe (Exp env e) -- Seed
  -> Arg env (In (sh, Int) e)
  -> ExpVars idxEnv (sh, Int)
  -- Code after the parallel loop
  -> (Envs env idxEnv -> Operands e -> CodeGen Native ())
  -> Exists (ParLoopCodeGen Native env idxEnv)
parCodeGenFoldSharded descending fun Nothing input index codeEnd
  | Just identity <- if descending then findRightIdentity fun else findLeftIdentity fun
  = parCodeGenFoldSharded descending fun (Just $ mkConstant tp identity) input index codeEnd
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
parCodeGenFoldSharded descending fun seed input index codeEnd = Exists $ ParLoopCodeGen
  -- If we know an identity value, we can implement this without loop peeling
  (isNothing identity)
  -- In kernel memory, store the index of the block we must now handle and the
  -- reduced value so far. 'Handle' here means that we should now add the value
  -- of that block.
  memoryTp
  -- Initialize kernel memory
  (\ptr envs -> do
    ptrs <- tuplePtrs' memoryTp ptr
    case ptrs of
      TupRpair (TupRpair (TupRsingle shardValues) (TupRsingle shardIndexes)) (TupRsingle shardStartIndexes) -> do
        let tileCount = envsTileCount envs
        -- OP_Bool notenoughTiles <- A.lt singleType tileCount (A.liftWord64 shardAmount)
        -- OP_Word64 tileDiff <- A.sub numType (A.liftWord64 shardAmount) tileCount
        -- finished <- instr' $ Select notenoughTiles tileDiff (integral TypeWord64 0)
        -- _ <- instr' $ Store NonVolatile finishedShards finished

        (OP_Int shardMinSize, remainder) <- A.unpair <$> A.quotRem TypeInt (OP_Int tileCount) (A.liftInt $ fromIntegral shardAmount)
        imapFromStepTo [Loop.LoopNonEmpty] (A.liftInt 0) (A.liftInt 1) (A.liftInt $ fromIntegral shardAmount) (\(OP_Int idx) -> do
          shardStart <- A.mul numType (OP_Int idx) (OP_Int shardMinSize)
          addRemainder <- A.min singleType (OP_Int idx) remainder
          OP_Int shard <- A.add numType shardStart addRemainder

          -- Multiply the index by the cache width in bytes to ensure every shard is on a seperate cache line.
          OP_Int idxCacheWidth <- A.mul numType (OP_Int idx) (A.liftInt $ fromIntegral $ valuesPerCacheLine scalarTypeInt)
          shardIdxArr <- instr' $ GetElementPtr $ GEP shardIndexes (integral TypeWord64 0) $ GEPArray idxCacheWidth GEPEmpty
          _ <- instr' $ Store Volatile shardIdxArr shard

          shardStartIdxArr <- instr' $ GetElementPtr $ GEP shardStartIndexes (integral TypeWord64 0) $ GEPArray idx GEPEmpty
          _ <- instr' $ Store NonVolatile shardStartIdxArr shard

          return ()
          )
        case seed of
          Nothing -> return ()
          Just s -> do
            value <- llvmOfExp (compileArrayInstrEnvs envs) s
            imapFromStepTo
              [Loop.LoopVectorize, Loop.LoopNonEmpty]
              (A.liftWord64 0)
              (A.liftWord64 $ valuesPerCacheLine tp)
              (A.liftWord64 (shardAmount * valuesPerCacheLine tp))
              (\(OP_Word64 idx) -> do
                _ <- tupleStoreArray tp shardValues idx value
                return ()
              )
      _ -> internalError "Pair impossible"
  )
  -- Initialize a thread
  (\_ _ -> tupleAlloca tp)
  -- Code before the tile loop
  (\_ accumVar _ envs ->
    case identity of
      Nothing -> return ()
      Just identity' -> do
        value <- llvmOfExp (compileArrayInstrEnvs envs) identity'
        tupleStore tp accumVar value
  )
  -- Code within the tile loop
  (\_ accumVar ptr envs -> do
    -- Parallel mode.
    -- Execute the reduce-phase of a parallel chained scan here.
    x <- readArray' envs input index
    new <-
      if isJust identity then do
        accum <- tupleLoad tp accumVar
        if envsDescending envs then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
      else do 
        ptrs <- tuplePtrs' memoryTp ptr
        
        case ptrs of
          TupRpair (TupRpair (TupRsingle _) (TupRsingle _)) (TupRsingle shardStartIndexes) -> do
            let shardIdx = fromMaybe (internalError "Missing shard index") $ envsShardIdx envs
            shardIdxPtr <- instr' $ GetElementPtr $ GEP shardStartIndexes (integral TypeWord64 0) $ GEPArray shardIdx GEPEmpty
            idx <- instr $ Load scalarTypeInt NonVolatile shardIdxPtr
            isFirst <- A.eq singleType idx (envsTileIndex envs)

            A.ifThenElse' (tp, isFirst)
              ( do
                return x
              )
              ( do
                accum <- tupleLoad tp accumVar
                if envsDescending envs then
                  app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
                else
                  app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
              )

          _ -> internalError "Pair impossible"
      
    tupleStore tp accumVar new
  )
  -- Code after the tile loop
  (\_ accumVar ptr envs -> do
    ptrs <- tuplePtrs' memoryTp ptr
    case ptrs of
      TupRpair (TupRpair (TupRsingle shardValues) (TupRsingle shardIndexes)) (TupRsingle shardStartIndexes) -> do
        let shardIdx = fromMaybe (internalError "Missing shard index") $ envsShardIdx envs
        OP_Word64 shardIdxCacheWidth <- A.mul numType (OP_Word64 shardIdx) (A.liftWord64 (valuesPerCacheLine scalarTypeInt))
        
        shardIdxPtr <- instr' $ GetElementPtr $ GEP shardIndexes (integral TypeWord64 0) $ GEPArray shardIdxCacheWidth GEPEmpty

        _ <- Loop.while [] TupRunit
          (\_ -> do
            idx <- instr $ Load scalarTypeInt Volatile shardIdxPtr
            A.neq singleType idx (envsTileIndex envs)
          )
          (\_ -> return OP_Unit)
          OP_Unit
        _ <- instr' $ Fence (CrossThread, Acquire)

        local <- tupleLoad tp accumVar

        OP_Word64 shardValueCacheWidth <- A.mul numType (OP_Word64 shardIdx) (A.liftWord64 (valuesPerCacheLine tp))

        new <-
          if isNothing seed then do
            -- If there is no seed, then write the output directly in the first tiles.
            -- The other tiles must combine their result with the given operator.
            shardStartPtr <- instr' $ GetElementPtr $ GEP shardStartIndexes (integral TypeWord64 0) $ GEPArray shardIdx GEPEmpty
            shardStart <- instr' $ Load scalarTypeInt NonVolatile shardStartPtr
            A.ifThenElse (tp, A.eq singleType (envsTileIndex envs) (OP_Int shardStart))
              (do
                return local
              )
              (do
                prefix <- tupleLoadArray tp shardValues shardValueCacheWidth
                tupleStore tp accumVar prefix
                if envsDescending envs then
                  app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) local prefix
                else
                  app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) prefix local
              )
          -- If there is a seed, then all tile will combine their local result with
          -- the already available value.
          else do
            prefix <- tupleLoadArray tp shardValues shardValueCacheWidth
            tupleStore tp accumVar prefix
            if envsDescending envs then
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) local prefix
            else
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) prefix local
        tupleStoreArray tp shardValues shardValueCacheWidth new


        _ <- instr' $ Fence (CrossThread, Release)
        OP_Int nextIdx <- A.add numType (envsTileIndex envs) (A.liftInt 1)
        _ <- instr' $ Store Volatile shardIdxPtr nextIdx
        return ()
      _ -> internalError "Pair impossible"
  )
  (\_ _ _ -> return ())
  -- Code after the loop
  (\ptr envs -> do
    ptrs <- tuplePtrs' memoryTp ptr
    case ptrs of
      TupRpair (TupRpair (TupRsingle shardValues) (TupRsingle _)) (TupRsingle _) -> do
        initValue <- tupleLoadArray tp shardValues (integral TypeWord64 0)
        value <- iterFromStepTo [Loop.LoopNonEmpty] tp (A.liftWord64 1) (A.liftWord64 1) (A.liftWord64 shardAmount) initValue (
          \idx accum -> do 
            OP_Word64 shardIdxCacheWidth <- A.mul numType idx (A.liftWord64 (valuesPerCacheLine tp)) -- TODO: FIX
            x <- tupleLoadArray tp shardValues shardIdxCacheWidth
            if envsDescending envs then
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
            else
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
          )
        -- value <- tupleLoad tp valuePtrs
        codeEnd envs value
      _ -> internalError "Pair impossible"
  )
  Nothing
  where
    memoryTp =  TupRsingle shardValues `TupRpair` TupRsingle shardIndexes `TupRpair` TupRsingle shardStartIndexes
    ArgArray _ (ArrayR _ tp) _ _ = input
    shardValues :: PrimType (SizedArray (Struct e))
    shardValues = ArrayPrimType (shardAmount * valuesPerCacheLine tp) $ StructPrimType False $ mapTupR ScalarPrimType tp -- TODO: How many actually needed?
    shardIndexes :: PrimType (SizedArray Int)
    shardIndexes = ArrayPrimType (shardAmount * valuesPerCacheLine scalarTypeInt) $ ScalarPrimType scalarType
    shardStartIndexes :: PrimType (SizedArray Int)
    shardStartIndexes = ArrayPrimType shardAmount $ ScalarPrimType scalarType
    identity
      | Just s <- seed
      , if descending then isRightIdentity fun s else isLeftIdentity fun s
      = Just s
      | Just v <- if descending then findRightIdentity fun else findLeftIdentity fun
      = Just $ mkConstant tp v
      | otherwise
      = Nothing


parCodeGenFoldCommutative
  :: Bool
  -> Fun env (e -> e -> e)
  -> Exp env e
  -> Exp env e
  -> Arg env (In (sh, Int) e)
  -> Arg env (Out sh e)
  -> ExpVars idxEnv (sh, Int)
  -> ExpVars idxEnv sh
  -> Exists (ParLoopCodeGen Native env idxEnv)
parCodeGenFoldCommutative _ fun seed identity input output inputIdx outputIdx = Exists $ ParLoopCodeGen
  False
  -- In kernel memory, store a lock (Word8) and the
  -- reduced value so far. The lock must be acquired to read or update the total value.
  -- Value 0 means unlocked, 1 is locked.
  (mapTupR ScalarPrimType memoryTp)
  -- Initialize kernel memory
  (\ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair (TupRsingle intPtr) valuePtrs -> do
        _ <- instr' $ Store NonVolatile intPtr (scalar scalarTypeWord8 0) -- unlocked
        value <- llvmOfExp (compileArrayInstrEnvs envs) seed
        tupleStore tp valuePtrs value
  )
  -- Initialize a thread
  (\_ envs -> do
    accumVar <- tupleAlloca tp
    value <- llvmOfExp (compileArrayInstrEnvs envs) identity
    tupleStore tp accumVar value
    return accumVar
  )
  -- Code before the tile loop
  (\_ _ _ _ -> return ())
  -- Code within the tile loop
  (\_ accumVar _ envs -> do
    x <- readArray' envs input inputIdx
    accum <- tupleLoad tp accumVar
    new <-
      if envsDescending envs then
        app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
      else
        app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
    tupleStore tp accumVar new
  )
  -- Code after the tile loop
  (\_ _ _ _ -> return ())
  -- Code at the end of a thread
  (\accumVar ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair (TupRsingle lock) valuePtrs -> do
        -- TODO: Use atomic compare-and-swap or read-modify-write
        -- to update the value in kernel memory lock-free,
        -- instead of taking a lock here.
        _ <- Loop.while [] TupRunit
          (\_ -> do
            -- While the lock is taken
            old <- instr $ AtomicRMW numType NonVolatile Exchange lock (scalar scalarTypeWord8 1) (CrossThread, Acquire)
            A.neq singleType old (A.liftWord8 0)
          )
          (\_ -> return OP_Unit)
          OP_Unit

        local <- tupleLoad tp accumVar

        old <- tupleLoad tp valuePtrs
        new <-
          if envsDescending envs then
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) local old
          else
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) old local
        tupleStore tp valuePtrs new

        -- Release the lock
        _ <- instr' $ Fence (CrossThread, Release)
        _ <- instr' $ Store Volatile lock (scalar scalarTypeWord8 0)
        return ()
  )
  -- Code after the loop
  (\ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair _ valuePtrs -> do
        value <- tupleLoad tp valuePtrs
        writeArray' envs output outputIdx value
  )
  Nothing
  where
    memoryTp = TupRsingle scalarTypeWord8 `TupRpair` tp
    ArgArray _ (ArrayR _ tp) _ _ = input

parCodeGenScan
  :: Bool -- Whether the loop is descending
  -- Whether this is a fold. Folds use similar code generation as scans, hence
  -- it is handled here. Commutative folds are handled separately.
  -> Bool
  -> Fun env (e -> e -> e)
  -> Maybe (Exp env e) -- Seed
  -> Arg env (In (sh, Int) e)
  -> ExpVars idxEnv (sh, Int)
  -- Code after evaluating the seed
  -- Must be 'return ()' if the seed is Nothing
  -> (Envs env idxEnv -> Operands e -> CodeGen Native ())
  -- Code in a tile loop, before the combination (for exclusive scans)
  -- Must be 'return ()' if the seed is Nothing
  -> (Envs env idxEnv -> Operands e -> CodeGen Native ())
  -- Code in a tile loop, after the combination (for inclusive scans)
  -> (Envs env idxEnv -> Operands e -> CodeGen Native ())
  -- Code after the parallel loop
  -> (Envs env idxEnv -> Operands e -> CodeGen Native ())
  -> Exists (ParLoopCodeGen Native env idxEnv)
parCodeGenScan descending isFold fun Nothing input index codeSeed codePre codePost codeEnd
  | Just identity <- if descending then findRightIdentity fun else findLeftIdentity fun
  = parCodeGenScan descending isFold fun (Just $ mkConstant tp identity) input index codeSeed codePre codePost codeEnd
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
parCodeGenScan descending isFold fun seed input index codeSeed codePre codePost codeEnd = Exists $ ParLoopCodeGen
  -- If we know an identity value, we can implement this without loop peeling
  (isNothing identity)
  -- In kernel memory, store the index of the block we must now handle and the
  -- reduced value so far. 'Handle' here means that we should now add the value
  -- of that block.
  (mapTupR ScalarPrimType memoryTp)
  -- Initialize kernel memory
  (\ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair (TupRsingle intPtr) valuePtrs -> do
        _ <- instr' $ Store NonVolatile intPtr (scalar scalarTypeInt 0)
        case seed of
          Nothing -> return ()
          Just s -> do
            value <- llvmOfExp (compileArrayInstrEnvs envs) s
            codeSeed envs value
            tupleStore tp valuePtrs value
  )
  -- Initialize a thread
  (\_ _ -> tupleAlloca tp)
  -- Code before the tile loop
  (\singleThreaded accumVar ptr envs ->
    if singleThreaded then do
      -- In the single threaded mode, we directly do a scan over this tile,
      -- instead of the reduce, lookback and scan phases.
      ptrs <- tuplePtrs memoryTp ptr
      case ptrs of
        TupRsingle _ -> internalError "Pair impossible"
        TupRpair _ valuePtrs -> do
          prefix <- tupleLoad tp valuePtrs
          tupleStore tp accumVar prefix
          -- Note: on the first tile, we read an undefined value if there is no
          -- seed. This is fine, as we don't use this value in the tile loop.
    else
      case identity of
        Nothing -> return ()
        Just identity' -> do
          value <- llvmOfExp (compileArrayInstrEnvs envs) identity'
          tupleStore tp accumVar value
  )
  -- Code within the tile loop
  (\singleThreaded accumVar _ envs ->
    if singleThreaded then do
      -- Single threaded mode. We directly perform a scan here.
      x <- readArray' envs input index
      if isJust seed then do
        accum <- tupleLoad tp accumVar
        codePre envs accum
        new <- if envsDescending envs then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
        codePost envs new
        tupleStore tp accumVar new
      else do
        isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
        new <- A.ifThenElse (tp, A.land isFirstTile $ envsIsFirst envs)
          ( do
            return x
          )
          ( do
            accum <- tupleLoad tp accumVar
            codePre envs accum
            if envsDescending envs then
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
            else
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
          )
        codePost envs new
        tupleStore tp accumVar new
    else do
      -- Parallel mode.
      -- Execute the reduce-phase of a parallel chained scan here.
      x <- readArray' envs input index
      new <-
        if isJust identity then do
          accum <- tupleLoad tp accumVar
          if envsDescending envs then
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
          else
            app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
        else
          A.ifThenElse' (tp, envsIsFirst envs)
            ( do
              return x
            )
            ( do
              accum <- tupleLoad tp accumVar
              if envsDescending envs then
                app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
              else
                app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
            )
      tupleStore tp accumVar new
  )
  -- Code after the tile loop
  (\singleThreaded accumVar ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair (TupRsingle idxPtr) valuePtrs -> do
        if singleThreaded then
          -- It is our turn since we are in the sequential mode,
          -- no need to wait
          return ()
        else do
          _ <- Loop.while [] TupRunit
            (\_ -> do
              idx <- instr $ Load scalarTypeInt Volatile idxPtr
              A.neq singleType idx (envsTileIndex envs)
            )
            (\_ -> return OP_Unit)
            OP_Unit
          _ <- instr' $ Fence (CrossThread, Acquire)
          return ()

        local <- tupleLoad tp accumVar

        new <-
          if singleThreaded then
            -- In the single threaded mode, 'local' is already the prefix,
            -- as this loop starts with the prefix value of the previous
            -- thread. We can directly write that to kernel memory.
            return local
          else if isNothing seed then
            -- If there is no seed, then write the output directly in the first tiles.
            -- The other tiles must combine their result with the given operator.
            A.ifThenElse (tp, A.eq singleType (envsTileIndex envs) (A.liftInt 0))
              (do
                return local
              )
              (do
                prefix <- tupleLoad tp valuePtrs
                tupleStore tp accumVar prefix
                if envsDescending envs then
                  app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) local prefix
                else
                  app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) prefix local
              )
          -- If there is a seed, then all tile will combine their local result with
          -- the already available value.
          else do
            prefix <- tupleLoad tp valuePtrs
            tupleStore tp accumVar prefix
            if envsDescending envs then
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) local prefix
            else
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) prefix local
        tupleStore tp valuePtrs new

        _ <- instr' $ Fence (CrossThread, Release)
        OP_Int nextIdx <- A.add numType (envsTileIndex envs) (A.liftInt 1)
        _ <- instr' $ Store Volatile idxPtr nextIdx
        return ()
  )
  (\_ _ _ -> return ())
  -- Code after the loop
  (\ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair _ valuePtrs -> do
        value <- tupleLoad tp valuePtrs
        codeEnd envs value
  )
  -- In the next tile loop, we prefer loop peeling iff there is no seed.
  -- In the first iteration, the first tile loop will then start without a prefix value,
  -- and we thus should do loop peeling there.
  -- Not executed when this tile is executed in the sequential mode.
  (if isFold then Nothing else
    Just (isNothing seed, \accumVar _ envs -> do
      x <- readArray' envs input index
      if isJust seed then do
        accum <- tupleLoad tp accumVar
        codePre envs accum
        new <- if envsDescending envs then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
        codePost envs new
        tupleStore tp accumVar new
      else do
        isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
        new <- A.ifThenElse (tp, A.land isFirstTile $ envsIsFirst envs)
          ( do
            return x
          )
          ( do
            accum <- tupleLoad tp accumVar
            codePre envs accum
            if envsDescending envs then
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) x accum
            else
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
          )
        codePost envs new
        tupleStore tp accumVar new
    )
  )
  where
    memoryTp = TupRsingle scalarTypeInt `TupRpair` tp
    ArgArray _ (ArrayR _ tp) _ _ = input
    identity
      | Just s <- seed
      , if descending then isRightIdentity fun s else isLeftIdentity fun s
      = Just s
      | Just v <- if descending then findRightIdentity fun else findLeftIdentity fun
      = Just $ mkConstant tp v
      | otherwise
      = Nothing

-- Checks if the cluster has a permute.
hasNPermute :: FlatCluster NativeOp env -> Bool
hasNPermute (FlatCluster _ _ _ _ _ _ flatOps) = go flatOps
  where
    go :: FlatOps NativeOp env idxEnv -> Bool
    go FlatOpsNil = False
    go (FlatOpsBind _ _ _ ops) = go ops
    go (FlatOpsOp (FlatOp NPermute _ _) _) = True
    go (FlatOpsOp (FlatOp NPermute' _ _) _) = True
    go (FlatOpsOp _ ops) = go ops

-- Checks if the cluster has a fold.
hasFold :: FlatCluster NativeOp env -> Bool
hasFold (FlatCluster _ _ _ _ _ _ flatOps) = go flatOps
  where
    go :: FlatOps NativeOp env idxEnv -> Bool
    go FlatOpsNil = False
    go (FlatOpsBind _ _ _ ops) = go ops
    go (FlatOpsOp (FlatOp NFold _ _) _) = True
    go (FlatOpsOp (FlatOp NFold1 _ _) _) = True
    go (FlatOpsOp _ ops) = go ops
