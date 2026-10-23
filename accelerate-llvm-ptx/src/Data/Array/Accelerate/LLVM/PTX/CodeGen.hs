{-# LANGUAGE MultiWayIf #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen (

  PTXCode(..),
  codegen,
  KernelMetadata,

) where

-- accelerate

import Data.Array.Accelerate.Representation.Shape (shapeRFromRank, rank)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Partitioned as P hiding (combine)
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment hiding ( Empty )
import Data.Array.Accelerate.LLVM.CodeGen.Cluster
import Data.Array.Accelerate.LLVM.CodeGen.Default
import Data.Array.Accelerate.LLVM.CodeGen.Loop
import Data.Array.Accelerate.LLVM.PTX.Operation
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Fold
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Scan
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Intrinsic ()
import Data.Array.Accelerate.LLVM.PTX.Foreign
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Maybe

import LLVM.AST.Type.Module
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Instruction as LLVM
import LLVM.AST.Type.Instruction.Volatile
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified LLVM.AST.Type.Function as LLVM
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Permute (atomically, lockArraySize)
import Data.Array.Accelerate.AST.LeftHandSide (Exists (Exists), flattenTupR)
import Control.Monad
import Control.Monad.Reader ( asks )
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Constant as Const
import qualified Foreign.CUDA.Analysis                              as CUDA

data PTXCode env = PTXCode
  { ptxCodeElements :: [Idx env Int] -- The product of these variables divided by ptxCodeElementsPerThread is the maximum grid size for this kernel, see [PTX Kernel Grid Size]
  , ptxCodeElementsPerThread :: Int
  , ptxCodeKernelMemory :: Int  -- The size of the kernel data, shared by all threads working on this kernel.
  , ptxCodeInit :: Maybe (Module (KernelType env))
  , ptxCodeWork :: Module (KernelType env)
  , ptxCodeFinish :: Maybe (Module (KernelType env))
  }

codegen :: forall env args.
           String
        -> Env AccessGroundR env
        -> Clustered PTXOp args
        -> Args env args
        -> LLVM PTX (PTXCode env)
codegen name env cluster args
  | Refl <- marshalFunResultUnit env = if
    | independentLoopDepth == 0 && loopDepth /= 0 ->
      -- Parallelise over the first dimension using parallel folds or scans
      codegenDim1 name env flat
    -- | independentLoopDepth /= loopDepth ->
      -- Multi-dimensional fold or scan. Optionally parallelise within or between
      -- threadblocks.
    -- No folds or scans
    | otherwise ->
      codegenIndependent name env flat independentLoopDepth
  where
    flat = toFlatClustered cluster args
    independentLoopDepth = flatClusterIndependentLoopDepth flat
    loopDepth = flatClusterLoopDepth flat

-- Variant of 'codegen' that parallelises over the first 'parallelDepth'
-- dimensions, which are assumed to be independent (e.g. contain no folds and
-- scans on those dimensions).
--
-- 'parallelDepth <= flatClusterIndependentLoopDepth flat' should hold (but is
-- not checked in this function)
--
codegenIndependent
  :: forall env.
     LLVM.Result (MarshalFun env) ~ ()
  => String
  -> Env AccessGroundR env
  -> FlatCluster PTXOp env
  -> Int
  -> LLVM PTX (PTXCode env)
codegenIndependent name env flatCluster parallelDepth
  | FlatCluster shr idxLHS sizes dirs localR localLHS flatOps <- flatCluster
  , Exists parallelShr <- shapeRFromRank parallelDepth
  , (gamma, makeKernel') <- makeKernel name env = do
    kernelWork <- makeKernel' "" $ do
      let (envs, loops) = initEnv gamma shr idxLHS sizes dirs localR localLHS
      let parSizes = parallelIterSize parallelShr loops
      parSize <- shapeSize parallelShr parSizes

      imapFromTo (A.liftInt 0) parSize $ \linearIdx -> do
        idx <- indexOfInt parallelShr parSizes linearIdx
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

      return_

    return $ PTXCode
      (take parallelDepth $ map sizeVar $ flattenTupR sizes)
      1 -- Each thread handles one element
      0 -- We don't need kernel memory here
      Nothing -- No need to initialize kernel memory
      kernelWork
      Nothing -- No need to finalize kernel memory

codegenDim1
  :: forall env.
     LLVM.Result (MarshalFun env) ~ ()
  => String
  -> Env AccessGroundR env
  -> FlatCluster PTXOp env
  -> LLVM PTX (PTXCode env)
codegenDim1 name env flatCluster
  | FlatCluster shr idxLHS sizes dirs localR localLHS flatOps <- flatCluster
  -- Prepare environment
  , (gamma, makeKernel') <- makeKernel name env
  , (envs, loops) <- initEnv gamma shr idxLHS sizes dirs localR localLHS
  -- Get a list of loops
  , ((idxVar, direction, size), loops') <- case loops of
    [] -> internalError "Expected at least one loop since rank shr /= 0"
    (l:ls) -> (l, ls)
  -- Get the code of the individual operations in this kernel
  , Just (Exists parCodes) <- parCodeGens (parCodeGen $ isDescending direction) 0 $ opCodeGens opCodeGen flatOps
  , _hasScan <- parCodeGenHasMultipleTileLoops parCodes
  -- TODO: Better heuristic, possibly using hasScan and/or other information on register usage of the operations in this kernel
  , elementsPerThread <- if rank shr > 1 then 1 else 4
  , envs1 <- envs{
      envsLoopDepth = 0,
      -- TODO: Set number of tiles
      -- The number of tiles needs to be available in the finalization kernel, but we cannot properly compute the
      -- number of tiles there, as that is dynamically computed in the 'regular' kernel based on blockDim
      -- (which varies per GPU and exact instantiation of scan based on register pressure)
      -- We either need a way to properly propagate that information,
      -- or move the finalization into the 'regular' kernel (and make sure that kernel runs on empty inputs).
      envsDescending = isDescending direction
    }
  -- Kernel memory
  , memoryTp' <- TupRsingle (ScalarPrimType scalarTypeWord64) `TupRpair` parCodeGenMemory parCodes
  , memoryTp <- StructPrimType False memoryTp'
  , kernelMem <- LocalReference (PrimType $ PtrPrimType memoryTp defaultAddrSpace) "kernel_data"
  = do
    kernelInit <- makeKernel' "_init" $ do
      perThreadBlock $ do
        counter <- instr' $ GetElementPtr $ gepStruct (ScalarPrimType scalarTypeWord64) kernelMem $ TupleIdxLeft TupleIdxSelf
        _ <- instr' $ Store NonVolatile counter (integral TypeWord64 0) Nothing
        
        parCodeGenInitMemory kernelMem envs1 (TupleIdxRight TupleIdxSelf) parCodes
      return_

    kernelFinish <- makeKernel' "_finish" $ do
      perThreadBlock $ do
        -- Declare fused-away and dead arrays at level zero.
        -- This is for instance needed for `map (+1) $ fold ...`,
        -- or a scanl' or scanr' whose reduced value is not used (like in prescanl).
        envs2 <- bindLocals 0 envs1
        -- Execute code for after the parallel work of this kernel, for
        -- instance to write the result of a fold to the output array.
        parCodeGenFinish kernelMem envs2 (TupleIdxRight TupleIdxSelf) parCodes
      return_
    
    kernelWork <- makeKernel' "" $ do
      -- Atomic counter used for self scheduling
      counter <- instr' $ GetElementPtr $ gepStruct (ScalarPrimType scalarTypeWord64) kernelMem $ TupleIdxLeft TupleIdxSelf

      -- Compute the tile size
      blockDim' <- blockDim >>= A.fromIntegral TypeInt32 numType
      OP_Int tileSize <- A.mul numType blockDim' $ A.liftInt elementsPerThread

      -- Compute the number of tiles
      tileSizeSub <- A.sub numType (OP_Int tileSize) (A.liftInt 1)
      sizeAdd <- A.add numType size tileSizeSub
      OP_Int tileCount <- A.quot TypeInt sizeAdd (OP_Int tileSize)

      -- Emit code to initialize a thread, and get the codes for the tile loops
      tileLoops <- genParallel kernelMem envs1 (TupleIdxRight TupleIdxSelf) parCodes

      -- Declare fused away arrays
      envs2 <- bindLocalsInTile (\_ -> not $ null $ ptOtherLoops tileLoops) 1 elementsPerThread envs1

      -- Loop to claim tile
      OP_Word64 tileCount' <- A.fromIntegral TypeInt numType (OP_Int tileCount)
      loopSelfScheduled counter tileCount' $ \tileIdx' -> do
        tileIdx <- instr' $ BitCast scalarType tileIdx'
        (_, lower, upper, full) <- tileRange (isDescending direction) (op TypeInt size) tileSize tileCount tileIdx

        -- Compute the number of warps that are active
        (OP_Int32 groupCount, OP_Int32 activeWarps) <- do
          size' <- A.sub numType (OP_Int upper) (OP_Int lower)
          -- ceil(size'/warpSize) = (size' + warpSize - 1) / warpSize
          a <- A.sub numType size' (OP_Int $ integral TypeInt 1) >>= A.fromIntegral TypeInt numType
          warpSz <- warpSize
          b <- A.add numType a warpSz
          count1 <- A.quot TypeInt32 b warpSz
          -- Since each thread can handle multiple ('elementsPerThread')
          -- elements, 'count' may be more than the number of warps within a
          -- threadblock. Now compute the actual number of warps within the
          -- threadblock. Threadblock size should be a multiple of the warp
          -- size, so we don't have to worry about rounding here.
          threadblockSize <- blockDim
          count2 <- A.quot TypeInt32 threadblockSize warpSz
          count <- A.min singleType count1 count2
          return (count1, count)

        let envs3 = envs2{
            envsTileIndex = OP_Int tileIdx,
            envsGpuActiveWarps = activeWarps
          }

        -- Handle one tile, with index tileIndex
        -- For each tile loop
        forM_ ((True, ptFirstLoop tileLoops) : map (False, ) (ptOtherLoops tileLoops)) $ \(isFirstTileLoop, tileLoop) -> do
          let loops'' = if isFirstTileLoop then loops' else []

          unless isFirstTileLoop $ __syncthreads

          ptBefore tileLoop envs3
          let peel = gpuLoopPeel (ptAnalysis tileLoop) && null loops''
          loopInThreadblock (isDescending direction) peel elementsPerThread lower upper full groupCount activeWarps $ \isFirst activeInWarp idxForThread globalIdx -> do
            localIdx <- A.sub numType (OP_Int globalIdx) (OP_Int lower)
            let envs4 = envs3{
                envsLoopDepth = 1,
                envsIdx = Env.partialUpdate globalIdx idxVar $ envsIdx envs3,
                envsIsFirst = OP_Bool isFirst,
                envsTileLocalIndex = localIdx,
                envsTileStorageIndex = OP_Int idxForThread,
                envsGpuWarpActiveThreads = activeInWarp
              }
            genSequential envs4 loops' $ ptIn tileLoop
          __syncthreads
          ptAfter tileLoop envs3

      ptExit tileLoops envs1

      return_

    return $ PTXCode
      (take 1 $ map sizeVar $ flattenTupR sizes)
      elementsPerThread
      (fst $ primSizeAlignment memoryTp)
      (Just kernelInit)
      kernelWork
      (Just kernelFinish)

  | otherwise
  = internalError "Could not generate code for a cluster as parCodeGens returned Nothing. Does parCodeGen lack a case for a collective parallel operation?"

sizeVar :: Exists (Var GroundR env) -> Idx env Int
sizeVar (Exists (Var (GroundRscalar (SingleScalarType (NumSingleType (IntegralNumType TypeInt)))) idx))
  = idx
sizeVar _ = internalError "Expected Int variable"

-- Generates code for a PTX module.
makeKernel
  :: LLVM.Result (MarshalFun env) ~ ()
  => String
  -> Env AccessGroundR env
  -> (Gamma env, String -> CodeGen PTX () -> LLVM PTX (Module (KernelType env)))
makeKernel name env =
  ( gamma
  , \postfix body ->
    snd <$> codeGenKernel (name ++ postfix) (LLVM.Lam kernelDataRawType "kernel_data" . LLVM.Lam primType "locks_array" . bindArgs) (extractEnv >> body)
  )
  where
    (bindArgs, extractEnv, gamma) = bindEnvArgs @PTX env
    kernelDataRawType :: PrimType (Ptr (SizedArray Word))
    kernelDataRawType = PtrPrimType (ArrayPrimType 0 primType) defaultAddrSpace

opCodeGen :: FlatOp PTXOp env idxEnv -> (LoopDepth, OpCodeGen PTX PTXOp env idxEnv)
opCodeGen flatOp@(FlatOp op' args idxArgs) = case op' of
  PTXGenerate -> defaultCodeGenGenerate args idxArgs
  PTXMap -> defaultCodeGenMap args idxArgs
  PTXBackpermute -> defaultCodeGenBackpermute args idxArgs
  PTXPermute -> defaultCodeGenPermute lockArraySize atomically args idxArgs
  PTXPermute' -> defaultCodeGenPermuteUnique args idxArgs
  PTXFold -> defaultCodeGenFold flatOp args idxArgs
  PTXFold1 -> defaultCodeGenFold1 flatOp args idxArgs
  PTXScan1 dir -> defaultCodeGenScan1 dir flatOp args idxArgs
  PTXScan' dir -> defaultCodeGenScan' dir flatOp args idxArgs
  PTXScan dir -> defaultCodeGenScan dir flatOp args idxArgs

type PTXParLoopCodeGen = ParLoopCodeGen PTX GPULoopAnalysis

parCodeGen :: Bool -> FlatOp PTXOp env idxEnv -> Maybe (Exists (PTXParLoopCodeGen env idxEnv))
parCodeGen descending (FlatOp op' args idxArgs) = case op' of
  PTXScan1 _ -> defaultParCodeGenScan1 scanCode descending args idxArgs
  PTXScan' _ -> defaultParCodeGenScan' scanCode descending args idxArgs
  PTXScan _ -> defaultParCodeGenScan scanCode descending args idxArgs
  PTXFold -> defaultParCodeGenFold scanCode descending args idxArgs
  PTXFold1 -> defaultParCodeGenFold1 scanCode descending args idxArgs
  _ -> Nothing

scanCode :: FoldScanCodeGen PTX GPULoopAnalysis
scanCode = FoldScanCodeGen (Just parCodeGenFoldCommutative) parCodeGenChainedScan

parCodeGenFoldCommutative
  :: ParCodeGenFoldCommutative PTX GPULoopAnalysis env idxEnv sh e
parCodeGenFoldCommutative _ tp fun seed identity input output = Exists $ ParLoopCodeGen
  analysis
  (bufferEltsR $ foldCommKernelMemory tp)
  -- Initialize kernel memory
  (\ptr envs -> foldCommInit envs tp ptr seed)
  -- Initialize a thread
  (\_ envs -> do
    -- Store one value per warp in shared memory
    smemAll <- staticSharedMemTuple tp maxWarps
    idx <- warpId
    -- The entry in shared memory for this warp
    smemWarp <- tupleArrayGep tp smemAll idx
    -- Local value of thread
    accumVar <- tupleAlloca tp
    -- Initialize local value to identity
    value <- llvmOfExp (compileArrayInstrEnvs envs) identity
    tupleStore tp accumVar value
    return (smemAll, smemWarp, accumVar)
  )
  -- Code before the tile loop
  (\_ _ _ _ -> return ())
  -- Code within the tile loop
  (\_ (_, _, accumVar) _ envs -> do
    x <- input envs
    accum <- tupleLoad tp accumVar
    new <- app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) accum x
    tupleStore tp accumVar new
  )
  -- Code after the tile loop
  (\_ _ _ _ -> return ())
    -- Code at the end of a thread (block)
  (\(smemAll, smemWarp, accumVar) ptr envs -> do
    -- tupleLoad tp accumVar >>= foldCommFinishThread envs tp ptr fun


    dev <- liftCodeGen $ asks ptxDeviceProperties
    let fun' = llvmOfFun2 (compileArrayInstrEnvs envs) fun
    threadLocal <- tupleLoad tp accumVar
    -- Perform a reduction per warp
    warpValue <- reduceWarp
      dev tp fun'
      (OP_Int32 <$> envsGpuWarpActiveThreads envs)
      threadLocal

    -- Share value of the warp
    perWarp $ tupleStore tp smemWarp warpValue

    -- Compute number of warps per threadblock
    blockDim' <- blockDim
    OP_Int32 warpCount <- A.quot TypeInt32 blockDim' (A.liftInt32 $ fromIntegral $ CUDA.warpSize dev)

    -- Reduce values per warp to single value for this thread block
    __syncthreads
    warpPerThreadBlock $ do
      aggregate <- reduceFromSMem dev tp fun' (fromIntegral maxWarps) warpCount smemAll
      perWarp $ do
        foldCommFinishThread envs tp ptr fun aggregate
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
    analysis = mempty
      { gpuLoopScheduleAscending = False
      , gpuLoopFullWarp = False
      , gpuLoopPeel = False
      }

parCodeGenChainedScan
  :: forall env idxEnv sh e. ParCodeGenChainedScan PTX GPULoopAnalysis env idxEnv sh e
parCodeGenChainedScan descending foldOrScan inclusiveness tp fun seed identity input codeSeed codeElement codeEnd = Exists $ ParLoopCodeGen
  analysis
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
  -- Initialize a thread(group)
  (\_ _ -> do
    -- Store one value per warp in shared memory
    smemAll <- staticSharedMemTuple tp maxWarps
    idx <- warpId
    -- The entry in shared memory for this warp
    smemWarp <- tupleArrayGep tp smemAll idx
    -- State of look-back
    lookbackIndex <- staticSharedMemSingle scalarTypeInt
    lookbackValue <- staticSharedMemTupleSingle tp
    return (smemAll, smemWarp, lookbackIndex, lookbackValue)
  )
  -- Code before the tile loop: initialize value of this warp to identity (zero)
  (\_ (_, smemWarp, _, _) _ envs -> do
    case identity of
      Nothing -> return ()
      Just identity' -> perThreadBlock $ do
        value <- llvmOfExp (compileArrayInstrEnvs envs) identity'
        tupleStore tp smemWarp value
  )
  -- Code within the tile loop: perform reduction
  (\_ (_, smemWarp, _, _) _ envs -> do
    dev <- liftCodeGen $ asks ptxDeviceProperties
    let fun' = llvmOfFun2 (compileArrayInstrEnvs envs) fun
    x <- input envs
    -- TODO: When 'fun' is commutative, we can optimize this by only doing the
    -- warp-wide reduction once, at the end.
    warpValue <- reduceWarp
      dev tp fun'
      (OP_Int32 <$> envsGpuWarpActiveThreads envs)
      x
    perWarp $ do
      accum <- tupleLoad tp smemWarp
      new <- combineInDirection envs tp fun identity (envsIsFirst envs) (envsDescending envs) accum warpValue
      tupleStore tp smemWarp new
  )
  -- Code after the tile loop
  (\_ (smem, _, lookbackIndex, lookbackValue) kernelMem envs -> warpPerThreadBlock $ do
    let identity' = fmap (llvmOfExp $ compileArrayInstrEnvs envs) identity
    let fun' = llvmOfFun2 (compileArrayInstrEnvs envs) fun
    dev <- liftCodeGen $ asks ptxDeviceProperties

    aggregate <-
      if foldOrScan == IsFold then
        -- Reduce all per-warp values in smem to a single value.
        reduceFromSMem dev tp fun' (fromIntegral maxWarps) (envsGpuActiveWarps envs) smem
      else
        -- Perform an exclusive over the per-warp values in smem,
        -- and compute the total aggregate (reduced value).
        -- This is executed on a single warp.
        scanFromSMem dir dev tp identity' fun' (fromIntegral maxWarps) (envsGpuActiveWarps envs) smem

    -- Perform look-back to find exclusive prefix for this tile
    exclusivePrefix <- perWarp' tp $ fmap fst $
      chainedScanLookback envs gridDim' descriptorsLength tp kernelMem lookbackIndex lookbackValue fun seed identity aggregate 
    
    when (foldOrScan == IsScan) $ do
      -- Add exclusivePrefix to all values in smem
      lane <- laneId

      let action =
            A.when (A.lt singleType lane $ OP_Int32 $ envsGpuActiveWarps envs) $ do
              ptr <- tupleArrayGep tp smem lane
              value <- tupleLoad tp ptr
              new <- if envsDescending envs then app2 fun' value exclusivePrefix else app2 fun' exclusivePrefix value
              tupleStore tp ptr new

          action' =
            -- If there is no identity, do not do anything with the first (undefined) value
            if isNothing identity then
              A.when (firstLane dir dev (OP_Int32 <$> envsGpuWarpActiveThreads envs) >>= A.neq singleType lane) action
            else
              -- Otherwise, handle all values
              action

      -- If this scan does not have a seed, we need to check if we are in the first tile
      if isNothing seed then
        A.when (A.neq singleType (envsTileIndex envs) (A.liftInt 0)) action'
      else
        action'
  )
  -- Finialize a thread(group)
  (\_ _ _ -> return ())
  -- Finalize the kernel
  (\ptr envs -> do
    value <- chainedScanFinish envs descriptorsLength tp ptr
    codeEnd envs value
  )
  -- Code in next tile loop
  (if foldOrScan == IsFold then Nothing else Just (analysis, \(_, smemWarp, _, _) _ envs -> do
    dev <- liftCodeGen $ asks ptxDeviceProperties
    let fun' = llvmOfFun2 (compileArrayInstrEnvs envs) fun
    x <- input envs

    (scanned, reduced) <- case seed of
      Just _ -> do
        -- If there is a seed, then each block and each warp will have a
        -- prefix.
        accum <- tupleLoad tp smemWarp
        scanWarp dir inclusiveness dev tp (Just (False, return accum)) fun'
          (OP_Int32 <$> envsGpuWarpActiveThreads envs) x
      Nothing
        | ScanExclusive <- inclusiveness -> internalError "Exclusive scans (scanl, scanl', scanr') should have a seed"
        | otherwise -> do
          -- Not all blocks and warps have a prefix: the first block does not
          -- have one.
          --
          -- Combine the first value of this warp with the prefix of this warp.
          -- When we then scan over the values in this warp, the prefix is part
          -- of each value in the warp
          lane <- laneId
          y <- A.ifThenElse (tp, firstLane dir dev (OP_Int32 <$> envsGpuWarpActiveThreads envs) >>= A.eq singleType lane)
            ( do
              -- The first item does not have a prefix
              isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
              A.ifThenElse (tp, A.land isFirstTile $ envsIsFirst envs)
                (return x)
                ( do
                  accum <- tupleLoad tp smemWarp
                  if envsDescending envs then
                    app2 fun' x accum
                  else
                    app2 fun' accum x
                )
            )
            (return x)
          
          scanWarp dir inclusiveness dev tp Nothing fun'
            (OP_Int32 <$> envsGpuWarpActiveThreads envs) y

    codeElement envs scanned

    perWarp $ do
      tupleStore tp smemWarp reduced
  ))
  where
    memoryTp = chainedScanKernelMemory descriptorsLength tp

    dir = if descending then RightToLeft else LeftToRight
    analysis = mempty
      { gpuLoopScheduleAscending = True
      , gpuLoopFullWarp = True
      -- If we know an identity value, we can implement this without loop peeling
      , gpuLoopPeel = isNothing identity
      }
    
    gridDim' :: CodeGen PTX (Operand Word32)
    gridDim' = do
      i <- gridDim
      OP_Word32 w <- A.fromIntegral TypeInt32 numType i
      return w

-- Maximum number of warps per threadgroup
maxWarps :: Word64
maxWarps = 32

-- Ideally at least three times the number of shading multiprocessors (SMPs).
-- Should be a power of 2, and at least 2
descriptorsLength :: Int
descriptorsLength = 2048
