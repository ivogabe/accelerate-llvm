{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
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

  codegen,
  KernelMetadata,

) where

-- accelerate

import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (shapeRFromRank, shapeType, rank)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Partitioned as P hiding (combine)
import Data.Array.Accelerate.Analysis.Exp
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment hiding ( Empty )
import Data.Array.Accelerate.LLVM.CodeGen.Cluster
import Data.Array.Accelerate.LLVM.CodeGen.Default
import Data.Array.Accelerate.LLVM.PTX.Operation
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Fold
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Scan
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Intrinsic ()
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Permute
import Data.Array.Accelerate.LLVM.PTX.Foreign
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Maybe

import LLVM.AST.Type.Module
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.RMW
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified LLVM.AST.Type.Function as LLVM
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Sugar (app1, IROpenFun2 (app2))
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
-- import Data.Array.Accelerate.LLVM.PTX.CodeGen.Permute (atomically)
import Data.Array.Accelerate.AST.LeftHandSide (Exists (Exists), flattenTupR)
import Control.Monad
import Control.Monad.State ( gets )
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop as Loop
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import qualified Text.LLVM as LP

codegen :: String
        -> Env AccessGroundR env
        -> Clustered PTXOp args
        -> Args env args
        -> LLVM PTX
           ( ( [Idx env Int] -- The product of these variables is the maximum grid size for this kernel, see [PTX Kernel Grid Size]
             , Int ) -- The size of the kernel data, shared by all threads working on this kernel.
           , Module (KernelType env))
codegen name env cluster args
 | flat@(FlatCluster shr idxLHS sizes dirs localR localLHS flatOps) <- toFlatClustered cluster args
 , parallelDepth <- flatClusterIndependentLoopDepth flat
 , Exists parallelShr <- shapeRFromRank parallelDepth
 , Refl <- marshalFunResultUnit env =
  codeGenKernel name (LLVM.Lam kernelDataRawType "kernel_data" . bindArgs) $ do
    extractEnv
    if parallelDepth == 0 && rank shr /= 0 then do
      internalError "TODO: Implement parallel collective operations on one-dimensional arrays"
    else if parallelDepth /= rank shr then do
      internalError "TODO: Implement parallel collective operations on multi-dimensional arrays"
    else do
      -- Parallelise over all independent dimensions
      let (envs, loops) = initEnv gamma shr idxLHS sizes dirs localR localLHS
      let parSizes = parallelIterSize parallelShr loops
      parSize <- shapeSize parallelShr parSizes

      imapFromTo (A.liftInt 0) parSize $ \linearIdx -> do
        idx <- indexOfInt parallelShr parSizes linearIdx
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

      return_

    let maxGridSize = map sizeVar $ flattenTupR sizes
    let kernelMemSize = 0 -- We don't use kernel data yet
    return (maxGridSize, kernelMemSize)
  where
    (bindArgs, extractEnv, gamma) = bindEnvArgs @PTX env
    kernelDataRawType :: PrimType (Ptr (SizedArray Word))
    kernelDataRawType = PtrPrimType (ArrayPrimType 0 primType) defaultAddrSpace

    sizeVar :: Exists (Var GroundR env) -> Idx env Int
    sizeVar (Exists (Var (GroundRscalar (SingleScalarType (NumSingleType (IntegralNumType TypeInt)))) idx))
      = idx
    sizeVar _ = internalError "Expected Int variable"

opCodeGen :: FlatOp PTXOp env idxEnv -> (LoopDepth, OpCodeGen PTX PTXOp env idxEnv)
opCodeGen flatOp@(FlatOp op args idxArgs) = case op of
  PTXGenerate -> defaultCodeGenGenerate args idxArgs
  PTXMap -> defaultCodeGenMap args idxArgs
  PTXBackpermute -> defaultCodeGenBackpermute args idxArgs
  PTXPermute
    | combineFun :>: output :>: locks :>: source :>: _ <- args
    , i1 :>: i2 :>: _ :>: i3 :>: _ <- idxArgs ->
      defaultCodeGenPermute
        (\envs j _ -> atomically envs locks $ OP_Int j)
        (combineFun :>: output :>: source :>: ArgsNil)
        (i1 :>: i2 :>: i3 :>: ArgsNil)
  PTXPermute' -> defaultCodeGenPermuteUnique args idxArgs
  PTXFold -> defaultCodeGenFold flatOp args idxArgs
  PTXFold1 -> defaultCodeGenFold1 flatOp args idxArgs
  PTXScan1 dir -> defaultCodeGenScan1 dir flatOp args idxArgs
  PTXScan' dir -> defaultCodeGenScan' dir flatOp args idxArgs
  PTXScan dir -> defaultCodeGenScan dir flatOp args idxArgs

type PTXParLoopCodeGen = ParLoopCodeGen PTX GPULoopAnalysis

parCodeGen :: Bool -> FlatOp PTXOp env idxEnv -> Maybe (Exists (PTXParLoopCodeGen env idxEnv))
-- TODO: parCodeGen for Folds
-- TODO: Make defaultParCodeGenScan{,',1}?
parCodeGen descending (FlatOp (PTXScan1 _)
    (ArgFun fun :>: input :>: output :>: _)
    (_ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: _))
  = Just $ parCodeGenScan descending IsScan ScanInclusive fun Nothing input inputIdx
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
    (\_ _ -> return ())
parCodeGen descending (FlatOp (PTXScan' _)
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: foldOutput :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: IdxArgIdx _ foldOutputIdx :>: _))
  = Just $ parCodeGenScan descending IsScan ScanExclusive fun (Just seed) input inputIdx
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
    (\envs result -> writeArray' envs foldOutput foldOutputIdx result)
parCodeGen descending (FlatOp (PTXScan dir)
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: _ :>: _))
  = case dir of
      LeftToRight -> Just $ parCodeGenScan descending IsScan ScanExclusive fun (Just seed) input inputIdx
        (\_ _ -> return ())
        (\envs result -> writeArray' envs output inputIdx result)
        (\envs result -> do
          let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
          writeArrayAt' envs output rowIdx n' result
        )
      RightToLeft -> Just $ parCodeGenScan descending IsScan ScanInclusive fun (Just seed) input inputIdx
        (\envs result -> do
          let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
          writeArrayAt' envs output rowIdx n' result
        )
        (\envs result -> writeArray' envs output inputIdx result)
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

parCodeGenScan
  :: Bool -- Whether the loop is descending
  -- Whether this is a fold. Folds use similar code generation as scans, hence
  -- it is handled here. Commutative folds are handled separately.
  -> FoldOrScan
  -> ScanInclusiveness
  -> Fun env (e -> e -> e)
  -> Maybe (Exp env e) -- Seed. Optional for inclusive scans, required for exclusive scans
  -> Arg env (In (sh, Int) e)
  -> ExpVars idxEnv (sh, Int)
  -- Code after evaluating the seed
  -- Must be 'return ()' if the seed is Nothing
  -> (Envs env idxEnv -> Operands e -> CodeGen PTX ())
  -- Code in a tile loop, to handle one item of the output
  -> (Envs env idxEnv -> Operands e -> CodeGen PTX ())
  -- Code after the parallel loop
  -> (Envs env idxEnv -> Operands e -> CodeGen PTX ())
  -> Exists (PTXParLoopCodeGen env idxEnv)
parCodeGenScan descending foldOrScan inclusiveness fun Nothing input index codeSeed codeElement codeEnd
  -- TODO: Move this logic to default implementations
  | Just identity <- if descending then findRightIdentity fun else findLeftIdentity fun
  = parCodeGenScan descending foldOrScan inclusiveness fun (Just $ mkConstant tp identity) input index codeSeed codeElement codeEnd
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
parCodeGenScan descending foldOrScan inclusiveness fun seed input index codeSeed codeElement codeEnd = Exists $ ParLoopCodeGen
  analysis
  -- In kernel memory, store the index of the block we must now handle and the
  -- reduced value so far. 'Handle' here means that we should now add the value
  -- of that block.
  (mapTupR ScalarPrimType memoryTp)
  -- Initialize kernel memory
  (\kernelMem envs -> do
    ptrs <- tuplePtrs memoryTp kernelMem
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
  -- Initialize a thread(group)
  (\_ _ -> do
    -- Store one value per warp in shared memory
    smemAll <- staticSharedMemTuple tp maxWarps
    idx <- warpId
    -- The entry in shared memory for this warp
    smemWarp <- tupleArrayGep tp smemAll idx
    return (smemAll, smemWarp)
  )
  -- Code before the tile loop: initialize value of this warp to identity (zero)
  (\_ (_, smemWarp) _ envs -> do
    case identity of
      Nothing -> return ()
      Just identity' -> perThreadBlock $ do
        value <- llvmOfExp (compileArrayInstrEnvs envs) identity'
        tupleStore tp smemWarp value
  )
  -- Code within the tile loop: perform reduction
  (\_ (_, smemWarp) _ envs -> do
    dev <- liftCodeGen $ gets ptxDeviceProperties
    let identity' = fmap (llvmOfExp $ compileArrayInstrEnvs envs) identity
    let fun' = llvmOfFun2 (compileArrayInstrEnvs envs) fun
    x <- readArray' envs input index
    warpValue <- reduceWarpShfl
      dev tp identity' fun'
      (if envsGpuFullWarp envs then Nothing else Just $ OP_Int32 $ envsGpuWarpActiveThreads envs)
      x
    perWarp $ do
      new <-
        if isJust identity then do
          accum <- tupleLoad tp smemWarp
          if envsDescending envs then
            app2 fun' warpValue accum
          else
            app2 fun' accum warpValue
        else
          A.ifThenElse' (tp, OP_Bool $ envsGpuFirstForThread envs)
            ( do
              return x
            )
            ( do
              accum <- tupleLoad tp smemWarp
              if envsDescending envs then
                app2 fun' warpValue accum
              else
                app2 fun' accum warpValue
            )
      tupleStore tp smemWarp new
  )
  -- Code after the tile loop
  (\_ (smem, _) kernelMem envs -> warpPerThreadBlock $ do
    let identity' = fmap (llvmOfExp $ compileArrayInstrEnvs envs) identity
    let fun' = llvmOfFun2 (compileArrayInstrEnvs envs) fun
    dev <- liftCodeGen $ gets ptxDeviceProperties

    aggregate <-
      if foldOrScan == IsFold then
        -- Reduce all per-warp values in smem to a single value.
        reduceFromSMem dev tp identity' fun' (fromIntegral maxWarps) (envsGpuWarpActiveThreads envs) smem
      else
        -- Perform an exclusive over the per-warp values in smem,
        -- and compute the total aggregate (reduced value).
        -- This is executed on a single warp.
        scanFromSMem dev tp identity' fun' (fromIntegral maxWarps) (envsGpuWarpActiveThreads envs) smem

    -- Share aggregate
    prefix <- perWarp' tp $ do
      ptrs <- tuplePtrs memoryTp kernelMem
      case ptrs of
        TupRsingle _ -> internalError "Pair impossible"
        TupRpair (TupRsingle idxPtr) valuePtrs -> do
          -- Wait on our turn
          _ <- Loop.while [] TupRunit
            (\_ -> do
              idx <- instr $ Load scalarTypeInt Volatile idxPtr
              A.neq singleType idx (envsTileIndex envs)
            )
            (\_ -> return OP_Unit) -- TODO: Maybe add nanosleep here
            OP_Unit
          _ <- instr' $ Fence (CrossThread, Acquire)
          
          OP_Pair exclusive inclusive <-
            if isNothing seed then
              -- If there is no seed, then write the output directly in the first tiles.
              -- The other tiles must combine their result with the given operator.
              A.ifThenElse (TupRpair tp tp, A.eq singleType (envsTileIndex envs) (A.liftInt 0))
                (do
                  return $ OP_Pair (undefs tp) aggregate
                )
                (do
                  prefix <- tupleLoad tp valuePtrs
                  inc <-
                    if envsDescending envs then
                      app2 fun' aggregate prefix
                    else
                      app2 fun' prefix aggregate
                  return $ OP_Pair prefix inc
                )
            -- If there is a seed, then all tiles will combine their local result with
            -- the already available value.
            else do
              prefix <- tupleLoad tp valuePtrs
              inc <-
                if envsDescending envs then
                  app2 fun' aggregate prefix
                else
                  app2 fun' prefix aggregate
              return $ OP_Pair prefix inc

          tupleStore tp valuePtrs inclusive

          _ <- instr' $ Fence (CrossThread, Release)
          OP_Int nextIdx <- A.add numType (envsTileIndex envs) (A.liftInt 1)
          _ <- instr' $ Store Volatile idxPtr nextIdx
          return exclusive
    
    when (foldOrScan == IsScan) $ do
      -- Add prefix to all values in smem
      lane <- laneId

      let action =
            A.when (A.lt singleType lane $ OP_Int32 $ envsGpuActiveWarps envs) $ do
              ptr <- tupleArrayGep tp smem lane
              value <- tupleLoad tp ptr
              new <- if envsDescending envs then app2 fun' value prefix else app2 fun' prefix value
              tupleStore tp ptr new
      
          action' =
            -- If there is no identity, do not do anything with the first (undefined) value
            if isNothing identity then
              A.when (A.gt singleType lane $ A.liftInt32 0) action
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
    ptrs <- tuplePtrs memoryTp ptr
    case ptrs of
      TupRsingle _ -> internalError "Pair impossible"
      TupRpair _ valuePtrs -> do
        value <- tupleLoad tp valuePtrs
        codeEnd envs value
  )
  -- Code in next tile loop
  (if foldOrScan == IsFold then Nothing else Just (analysis, \(_, smemWarp) _ envs -> do
    dev <- liftCodeGen $ gets ptxDeviceProperties
    let identity' = fmap (llvmOfExp $ compileArrayInstrEnvs envs) identity
    let fun' = llvmOfFun2 (compileArrayInstrEnvs envs) fun
    x <- readArray' envs input index

    -- Combine the first value of this warp with the prefix of this warp.
    -- When we then scan over the values in this warp, the prefix is part
    -- of each value in the warp
    lane <- laneId
    y <- A.ifThenElse (tp, A.eq singleType lane (A.liftInt32 0))
      ( if isNothing seed then do
          -- The first item does not have a prefix
          isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
          A.ifThenElse (tp, A.land isFirstTile $ OP_Bool $ envsGpuFirstForThread envs)
            (return x)
            ( do
              accum <- tupleLoad tp smemWarp
              if envsDescending envs then
                app2 fun' x accum
              else
                app2 fun' accum x
            )
        else do
          accum <- tupleLoad tp smemWarp
          if envsDescending envs then
            app2 fun' x accum
          else
            app2 fun' accum x
      )
      (return x)
    
    (scanned, reduced) <- scanWarpShfl
      dir inclusiveness dev tp identity' fun'
      (if envsGpuFullWarp envs then Nothing else Just $ OP_Int32 $ envsGpuWarpActiveThreads envs)
      y

    codeElement envs scanned

    perWarp $ do
      tupleStore tp smemWarp reduced
  ))
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
    dir = if descending then RightToLeft else LeftToRight
    analysis = mempty
      { gpuLoopScheduleAscending = True
      , gpuLoopFullWarp = True
      -- If we know an identity value, we can implement this without loop peeling
      , gpuLoopPeel = isNothing identity
      }

-- Maximum number of warps per threadgroup
maxWarps :: Word64
maxWarps = 32

