{-# LANGUAGE TypeFamilies #-}
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
import Data.Array.Accelerate.Representation.Shape (shapeRFromRank, shapeType, rank)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Partitioned as P hiding (combine)
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment hiding ( Empty )
import Data.Array.Accelerate.LLVM.CodeGen.Cluster
import Data.Array.Accelerate.LLVM.CodeGen.Default
import Data.Array.Accelerate.LLVM.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.Intrinsic
import Data.Array.Accelerate.LLVM.Native.Operation
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.Target
import Data.Maybe
import Data.Bits

import LLVM.AST.Type.Module
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Instruction as LLVM
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.RMW
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified LLVM.AST.Type.Function as LLVM
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import Data.Array.Accelerate.LLVM.Native.CodeGen.Permute (atomically, lockArraySize)
import Data.Array.Accelerate.AST.LeftHandSide (Exists (Exists))
import Control.Monad
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop as Loop
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import qualified Data.Array.Accelerate.LLVM.Internal.LLVMPretty as LP

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
  codeGenFunction linkage name type' (LLVM.Lam argTp "arg" . LLVM.Lam primType "locks_array" . LLVM.Lam primType "thread.index" . LLVM.Lam primType "thread.count") $ do
    extractEnv

    -- Before the parallel work of a kernel is started, we first run the function once.
    -- This first call will initialize kernel memory (SEE: Kernel Memory)
    -- and decide whether the runtime may try to let multiple threads work on this kernel.
    initBlock <- newBlock "init"
    finishBlock <- newBlock "finish" -- Finish function from the work assisting paper
    workBlock <- newBlock "work"
    _ <- switch (OP_Word32 threadIndex) workBlock [(0xFFFFFFFF, initBlock), (0xFFFFFFFE, finishBlock)]
    {- TODO WALL: DEAD CODE
    let hasPermute = hasNPermute flat
    -}

    if parallelDepth == 0 && rank shr /= 0 then do
      let (envs, loops) = initEnv gamma shr idxLHS sizes dirs localR localLHS
      let ((idxVar, direction, size), loops') = case loops of
            [] -> internalError "Expected at least one loop since rank shr /= 0"
            (l:ls) -> (l, ls)

      -- Parallelise over first dimension using parallel folds or scans
      case parCodeGens (parCodeGen $ isDescending direction) 0 $ opCodeGens opCodeGen flatOps of
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
                else
                  1024 * 16 -- TODO: Implement a better heuristic to choose the tile size

          -- Number of tiles
          sizeAdd <- A.add numType size (A.liftInt $ tileSize - 1)
          OP_Int tileCount' <- A.quot TypeInt sizeAdd (A.liftInt tileSize)
          tileCount <- instr' $ BitCast scalarType tileCount'

          let envs' = envs{
            envsLoopDepth = 0,
            envsTileSizeCount = [(tileSize, OP_Int tileCount')],
            envsDescending = isDescending direction
          }

          -- Kernel memory
          let memoryTp' = parCodeGenMemory parCodes
          let memoryTp = StructPrimType False memoryTp'
          kernelMem <- instr' $ PtrCast (PtrPrimType memoryTp defaultAddrSpace) kernelMem'

          setBlock initBlock
          do
            -- Initialize kernel memory
            parCodeGenInitMemory kernelMem envs' TupleIdxSelf parCodes
            -- Decide whether tileCount is large enough

            -- Assert that there are at most 2^47 tiles
            A.when (A.gt singleType (OP_Int tileCount') $ A.liftInt (1 `shiftL` 47)) $
              trapWithMessage "Accelerate: Parallel loops must have at most 2^47 tiles"

            OP_Bool isSmall <- A.lt singleType (OP_Int tileCount') $ A.liftInt 2
            value <- instr' $ LLVM.Select isSmall (scalar (scalarType @Word8) 0) (scalar scalarType 1)
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
          envs'' <-
            -- Binding locals on dimension 0. This is not needed for fused away
            -- arrays, but we use the same mechanism to handle unused outputs.
            -- This is particularly important for scanl, as we cannot fuse over
            -- the output of a scanl (opposed to scanl1 and scanl'). In
            -- SetOpIndices we do not set the index of the output, and that
            -- causes it to be placed on dimension 0. Hence we need to bind it
            -- here.
            bindLocals 0 envs' >>=
            bindLocalsInTile (\_ -> not $ null $ ptOtherLoops tileLoops) 1 tileSize
          -- TODO: Set maxClaim based on:
          -- * If the kernel contains scans, then 1.
          -- * If the kernel contains non-commutative folds, then a small number between 2 and 8 (only possible after implementing folds based on interleaved scans)
          -- * Otherwise, a high number like 1024. In this case, the kernel contains commutative folds which do not require a specific order.
          let maxClaim = 1
          workassistLoop workassistIndex workPerThread maxClaim threadIndex threadCount tileCount $ \seqMode tileIdx' -> do
            tileIdx <- instr' $ BitCast scalarType tileIdx'
            (_, lower, upper, _) <- tileRange (isDescending direction) (op TypeInt size) (integral TypeInt tileSize) tileCount' tileIdx

            -- If there is only a single tile loop (i.e. no parallel scans),
            -- then we don't generate code for a single-threaded mode:
            -- the default mode already is as fast as a single-threaded mode.
            let seqMode' = if null (ptOtherLoops tileLoops) then boolean False else seqMode

            let envs''' = envs''{
                envsTileIndex = OP_Int tileIdx
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
                      [ Loop.LoopPeel | cpuLoopPeel (ptAnalysis tileLoop) && null loops' ]
                      -- We can use LoopNonEmpty since we
                      -- know that each tile is non-empty.
                      -- We cannot vectorize this loop (yet), as LLVM cannot vectorize loops
                      -- containing scans. We should either wait until LLVM supports this,
                      -- or vectorize loops (partially) ourselves.
                      -- As an alternative to vectorization, we ask LLVM to interleave the loop.
                      ++ [ Loop.LoopNonEmpty, Loop.LoopInterleave ]

                ptBefore tileLoop envs'''
                Loop.loopWith ann (isDescending direction) (OP_Int lower) (OP_Int upper) $ \isFirst idx -> do
                  localIdx <- A.sub numType idx (OP_Int lower)
                  let envs'''' = envs'''{
                      envsLoopDepth = 1,
                      envsIdx = Env.partialUpdate (op TypeInt idx) idxVar $ envsIdx envs'',
                      envsIsFirst = isFirst,
                      envsTileLocalIndex = localIdx,
                      envsTileStorageIndex = localIdx
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
                        [ Loop.LoopPeel | cpuLoopPeel (ptAnalysis tileLoop) && null loops'' ]
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
                  Loop.loopWith ann (isDescending direction) (OP_Int lower) (OP_Int upper) $ \isFirst idx -> do
                    localIdx <- A.sub numType idx (OP_Int lower)
                    let envs'''' = envs'''{
                        envsLoopDepth = 1,
                        envsIdx = Env.partialUpdate (op TypeInt idx) idxVar $ envsIdx envs'',
                        envsIsFirst = isFirst,
                        envsTileLocalIndex = localIdx,
                        envsTileStorageIndex = localIdx
                      }
                    genSequential envs'''' loops'' $ ptIn tileLoop
                  ptAfter tileLoop envs'''
                return OP_Unit
              )
            return ()

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
      do
        tileCount <- chunkCount parallelShr parSizes (A.lift (shapeType parallelShr) tileSize)
        tileCount' <- shapeSize parallelShr tileCount
        -- We are not using kernel memory, so no need to initialize it.

        -- Assert that there are at most 2^47 tiles
        A.when (A.gt singleType tileCount' $ A.liftInt (1 `shiftL` 47)) $
          trapWithMessage "Accelerate: Parallel loops must have at most 2^47 tiles"

        OP_Bool isSmall <- A.lt singleType tileCount' $ A.liftInt 2
        value <- instr' $ LLVM.Select isSmall (scalar (scalarType @Word8) 0) (scalar scalarType 1)
        retval_ value

      setBlock finishBlock
      -- Nothing has to be done in the finish function for this kernel.
      retval_ $ scalar (scalarType @Word8) 0

      setBlock workBlock
      let ann =
            if parallelDepth /= rank shr then []
            else {- if hasPermute then -} [Loop.LoopInterleave]
            -- else [Loop.LoopVectorize]
      workassistChunked ann parallelShr workassistIndex workPerThread 1024 threadIndex threadCount tileSize parSizes $ \idx -> do
        let envs' = envs{
            -- Tile size and count are currently only needed when parallelizing
            -- collective operations; not when parallelizing over independent
            -- dimensions.
            envsTileSizeCount = internalError "Tile size and count are not available when parallelizing over independent dimensions.",
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
    (argTp, extractEnv, workassistIndex, workPerThread, threadIndex {- or flag -}, threadCount, kernelMem', gamma) = bindHeaderEnv env

linkage :: Maybe LP.Linkage
linkage = Just LP.DLLExport

opCodeGen :: FlatOp NativeOp env idxEnv -> (LoopDepth, OpCodeGen Native NativeOp env idxEnv)
opCodeGen flatOp@(FlatOp op args idxArgs) = case op of
  NGenerate -> defaultCodeGenGenerate args idxArgs
  NMap -> defaultCodeGenMap args idxArgs
  NBackpermute -> defaultCodeGenBackpermute args idxArgs
  NPermute -> defaultCodeGenPermute lockArraySize atomically args idxArgs
  NPermute' -> defaultCodeGenPermuteUnique args idxArgs
  NFold -> defaultCodeGenFold flatOp args idxArgs
  NFold1 -> defaultCodeGenFold1 flatOp args idxArgs
  NScan1 dir -> defaultCodeGenScan1 dir flatOp args idxArgs
  NScan' dir -> defaultCodeGenScan' dir flatOp args idxArgs
  NScan dir -> defaultCodeGenScan dir flatOp args idxArgs

type NParLoopCodeGen = ParLoopCodeGen Native CPULoopAnalysis

-- Parallel code generation for one-dimensional collective operations (folds and scans).
-- Other operations, either OpCodeGenSingle or nested deeper, are handled in opCodeGen
parCodeGen :: Bool -> FlatOp NativeOp env idxEnv -> Maybe (Exists (NParLoopCodeGen env idxEnv))
parCodeGen descending (FlatOp op' args idxArgs) = case op' of
  NScan1 _ -> defaultParCodeGenScan1 scanCode descending args idxArgs
  NScan' _ -> defaultParCodeGenScan' scanCode descending args idxArgs
  NScan _ -> defaultParCodeGenScan scanCode descending args idxArgs
  NFold -> defaultParCodeGenFold scanCode descending args idxArgs
  NFold1 -> defaultParCodeGenFold1 scanCode descending args idxArgs
  _ -> Nothing

scanCode :: FoldScanCodeGen Native CPULoopAnalysis
scanCode = FoldScanCodeGen (Just parCodeGenFoldCommutative) parCodeGenChainedScan

parCodeGenFoldCommutative
  :: ParCodeGenFoldCommutative Native CPULoopAnalysis env idxEnv sh e
parCodeGenFoldCommutative _ tp fun seed identity input output = Exists $ ParLoopCodeGen
  (CPULoopAnalysis False)
  -- In kernel memory, store a lock (Word8) and the
  -- reduced value so far. The lock must be acquired to read or update the total value.
  -- Value 0 means unlocked, 1 is locked.
  (bufferEltsR memoryTp)
  -- Initialize kernel memory
  (\ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair (TupRsingle intPtr) valuePtrs -> do
        _ <- instrMD' (Store NonVolatile intPtr (scalar scalarTypeWord8 0) Nothing) (bufferMetadata' Nothing) -- unlocked
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
    x <- input envs
    accum <- tupleLoad tp accumVar
    new <-
      -- TODO: we don't need to check for the direction here,
      -- since 'fun' is commutative in this function.
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
            old <- instrMD (AtomicRMW numType NonVolatile Exchange lock (scalar scalarTypeWord8 1) (CrossThread, Acquire)) (bufferMetadata' Nothing)
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
        _ <- instrMD' (AtomicStore scalarType lock (scalar scalarTypeWord8 0) Release) (bufferMetadata' Nothing)
        return ()
  )
  -- Code after the loop
  (\ptr envs -> do
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair _ valuePtrs -> do
        value <- tupleLoad tp valuePtrs
        output envs value
  )
  Nothing
  where
    memoryTp = TupRsingle scalarTypeWord8 `TupRpair` tp

-- Implements the single-pass chained scan with decoupled-lookback
-- (https://research.nvidia.com/sites/default/files/publications/nvr-2016-002.pdf)
-- Compared to the paper, we made two major changes:
-- 1. The scan is modified to work on CPUs, and features a specialized
--    single-threaded mode that is active as long as only one thread works on
--    the scan. It switches to the parallel mode dynamically.
--    (https://dl.acm.org/doi/pdf/10.1145/3649169.3649248)
-- 2. The array of descriptors (state per tile) is stored as a circular buffer.
--    This required additional synchronisations, as detailed below.
--
-- We want to make the following further improvements to these scans:
-- 1. Interleave multiple tiles on a single thread,
--    to hide the latency of blocking in the look-back.
--    Note that syncDistance (see below in the code) needs to be updated when
--    implementing this.
--    (https://studenttheses.uu.nl/items/3ef19878-f012-49c9-a86d-df79e1bd7c2d)
-- 2. (Need to re-evaluate if this is beneficial after implementing interleaved
--    scans): Optimize look-back for segmented scans, by using the boundaries
--    of segments
--    (https://studenttheses.uu.nl/server/api/core/bitstreams/c0289d3a-da20-4e79-bc90-f37b462f36cd/content)
-- 3. SIMD vectorization (general improvement for code generation)
-- 4. Reduce number of tile loops when scans are horizontally fused.
--    Fused scans add additional tile loops, but this is only necessary when
--    they are vertically or diagonally fused.
parCodeGenChainedScan
  :: forall env idxEnv sh e. ParCodeGenChainedScan Native CPULoopAnalysis env idxEnv sh e
parCodeGenChainedScan _descending foldOrScan inclusiveness tp fun seed identity input codeSeed codeElement codeEnd = Exists $ ParLoopCodeGen
  -- If we know an identity value, we can implement this without loop peeling
  (CPULoopAnalysis $ isNothing identity)
  -- In kernel memory, store the index of the block we must now handle and the
  -- reduced value so far. 'Handle' here means that we should now add the value
  -- of that block.
  (TupRsingle memoryTp)
  -- Initialize kernel memory
  (\ptr envs -> do
    valuePtrs <- chainedScanInit descriptorsLength tp ptr
    case seed of
      Nothing -> return ()
      Just s -> do
        value <- llvmOfExp (compileArrayInstrEnvs envs) s
        codeSeed envs value
        tupleStore tp valuePtrs value
  )
  -- Initialize a thread
  -- State of a thread consists of:
  -- * Accumulator within reduce or scan loop
  -- * Index of tile in look-back
  -- * Value (prefix/aggregate) of look-back
  (\_ _ -> do
    accumVar <- tupleAlloca tp
    lookbackIndex <- hoistAlloca $ ScalarPrimType scalarTypeInt
    lookbackValue <- tupleAlloca tp
    return (accumVar, lookbackIndex, lookbackValue)
  )
  -- Code before the tile loop
  (\singleThreaded (accumVar, _, _) ptr envs ->
    if singleThreaded then do
      -- In the single threaded mode, we directly do a scan over this tile,
      -- instead of the reduce, lookback and scan phases.
      (descIdx, _) <- descriptorIdxTag (envsTileIndex envs)
      (_, _, valuePtrs) <- getDescriptorSlot ptr descIdx
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
  (\singleThreaded (accumVar, _, _) _ envs ->
    if singleThreaded then do
      -- Single threaded mode. We directly perform a scan here.
      x <- input envs

      accum <- tupleLoad tp accumVar
      when (inclusiveness == ScanExclusive) $ codeElement envs accum
      isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
      first <- A.land isFirstTile $ envsIsFirst envs
      new <- combineInDirection envs tp fun seed first False accum x
      when (inclusiveness == ScanInclusive) $ codeElement envs new
      tupleStore tp accumVar new
    else do
      -- Parallel mode.
      -- Execute the reduce-phase of a parallel chained scan here.
      x <- input envs
      accum <- tupleLoad tp accumVar
      new <- combineInDirection envs tp fun identity (envsIsFirst envs) False accum x
      tupleStore tp accumVar new
  )
  -- Code after the tile loop
  (\singleThreaded (accumVar, lookbackIndex, lookbackValue) ptr envs -> do
    local <- tupleLoad tp accumVar

    if singleThreaded then do
      nextTileIdx <- A.add numType (envsTileIndex envs) (A.liftInt 1)
      (thisDescIdx, thisTag) <- descriptorIdxTag nextTileIdx
      (thisFlagPtr, _, thisPrefixPtrs) <- getDescriptorSlot ptr thisDescIdx
      -- In the single threaded mode, 'local' is already the prefix,
      -- as this loop starts with the prefix value of the previous
      -- thread. We can directly write that to kernel memory.
      -- It is our turn since we are in the sequential mode,
      -- no need to wait.
      tupleStore tp thisPrefixPtrs local
      OP_Word8 newFlag <- A.bor TypeWord8 thisTag $ OP_Word8 flagPrefix
      _ <- instrMD' (AtomicStore scalarType thisFlagPtr newFlag Release) (bufferMetadata' Nothing)
      return ()
    else do
      -- In the parallel mode, 'local' is the aggregate value of this tile.
      (exclusive, _) <- chainedScanLookback envs getThreadCount descriptorsLength tp ptr lookbackIndex lookbackValue fun seed identity local
      tupleStore tp accumVar exclusive -- Used in second tile loop (only in parallel mode)
    return ()
  )
  (\_ _ _ -> return ())
  -- Code after the loop
  (\ptr envs -> do
    value <- chainedScanFinish envs descriptorsLength tp ptr
    codeEnd envs value
  )
  -- In the next tile loop, we prefer loop peeling iff there is no seed.
  -- In the first iteration, the first tile loop will then start without a prefix value,
  -- and we thus should do loop peeling there.
  -- Not executed when this tile is executed in the sequential mode.
  (if foldOrScan == IsFold then Nothing else
    Just (CPULoopAnalysis $ isNothing seed, \(accumVar, _, _) _ envs -> do
      x <- input envs
      accum <- tupleLoad tp accumVar
      when (inclusiveness == ScanExclusive) $ codeElement envs accum
      isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
      first <- A.land isFirstTile $ envsIsFirst envs
      new <- combineInDirection envs tp fun seed first False accum x
      when (inclusiveness == ScanInclusive) $ codeElement envs new
      tupleStore tp accumVar new
    )
  )
  where
    -- ((flag, valueAggregate), valuePrefix)
    memoryTp = chainedScanKernelMemory descriptorsLength tp

    descriptorIdxTag = chainedScanDescriptorIdxTag descriptorsLength
    getDescriptorSlot = chainedScanGetDescriptorSlot descriptorsLength tp

{- TODO WALL: DEAD CODE
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
-}

-- Ideally, this should be at least three times the number of threads.
-- When this is set lower (or from the other perspective, there are too many
-- threads), scans will still function correctly, but have more
-- synchronisations. This will essentially convert the chained scan *with
-- decoupled look-back* to a regular chained scan.
--
-- This should be at least 2 (but preferably a lot larger, as noted above)
--
descriptorsLength :: Int
descriptorsLength = 1024
