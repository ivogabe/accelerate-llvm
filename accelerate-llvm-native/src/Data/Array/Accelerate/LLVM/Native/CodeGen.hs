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
import LLVM.AST.Type.GetElementPtr
import LLVM.AST.Type.Operand
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified LLVM.AST.Type.Function as LLVM
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import qualified Data.Array.Accelerate.LLVM.CodeGen.Constant as A
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import Data.Array.Accelerate.LLVM.Native.CodeGen.Permute (atomically)
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
    let hasPermute = hasNPermute flat

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

    isDescending :: LoopDirection Int -> Bool
    isDescending LoopDescending = True
    isDescending _ = False

linkage :: Maybe LP.Linkage
linkage = Just LP.DLLExport

opCodeGen :: FlatOp NativeOp env idxEnv -> (LoopDepth, OpCodeGen Native NativeOp env idxEnv)
opCodeGen flatOp@(FlatOp op args idxArgs) = case op of
  NGenerate -> defaultCodeGenGenerate args idxArgs
  NMap -> defaultCodeGenMap args idxArgs
  NBackpermute -> defaultCodeGenBackpermute args idxArgs
  NPermute
    | (_ :>: output :>: _ :>: _) <- args ->
      defaultCodeGenPermute (\envs j _ -> atomically envs output $ OP_Int j) args idxArgs
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
  = Just $ parCodeGenScan descending IsScan fun Nothing input inputIdx
    (\_ _ -> return ())
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
    (\_ _ -> return ())
parCodeGen descending (FlatOp (NScan' _)
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: foldOutput :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx _ outputIdx :>: IdxArgIdx _ foldOutputIdx :>: _))
  = Just $ parCodeGenScan descending IsScan fun (Just seed) input inputIdx
    (\_ _ -> return ())
    (\envs result -> writeArray' envs output outputIdx result)
    (\_ _ -> return ())
    (\envs result -> writeArray' envs foldOutput foldOutputIdx result)
parCodeGen descending (FlatOp (NScan dir)
    (ArgFun fun :>: ArgExp seed :>: input :>: output :>: _)
    (_ :>: _ :>: IdxArgIdx _ inputIdx :>: _ :>: _))
  = case dir of
      LeftToRight -> Just $ parCodeGenScan descending IsScan fun (Just seed) input inputIdx
        (\_ _ -> return ())
        (\envs result -> writeArray' envs output inputIdx result)
        (\_ _ -> return ())
        (\envs result -> do
          let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
          writeArrayAt' envs output rowIdx n' result
        )
      RightToLeft -> Just $ parCodeGenScan descending IsScan fun (Just seed) input inputIdx
        (\envs result -> do
          let n' = envsPrjParameter (Var scalarTypeInt $ varIdx n) envs
          writeArrayAt' envs output rowIdx n' result
        )
        (\_ _ -> return ())
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

parCodeGenFold
  :: Bool
  -> Fun env (e -> e -> e)
  -> Maybe (Exp env e)
  -> Arg env (In (sh, Int) e)
  -> Arg env (Out sh e)
  -> ExpVars idxEnv (sh, Int)
  -> ExpVars idxEnv sh
  -> Exists (NParLoopCodeGen env idxEnv)
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
  = parCodeGenScan descending IsFold fun seed input inputIdx
    (\_ _ -> return ())
    (\_ _ -> return ())
    (\_ _ -> return ())
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

parCodeGenFoldCommutative
  :: Bool
  -> Fun env (e -> e -> e)
  -> Exp env e
  -> Exp env e
  -> Arg env (In (sh, Int) e)
  -> Arg env (Out sh e)
  -> ExpVars idxEnv (sh, Int)
  -> ExpVars idxEnv sh
  -> Exists (NParLoopCodeGen env idxEnv)
parCodeGenFoldCommutative _ fun seed identity input output inputIdx outputIdx = Exists $ ParLoopCodeGen
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
        _ <- instr' $ Store NonVolatile intPtr (scalar scalarTypeWord8 0) Nothing -- unlocked
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
        _ <- instr' $ AtomicStore singleType lock (scalar scalarTypeWord8 0) Release
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
  :: forall env idxEnv sh e.
     Bool -- Whether the loop is descending
  -- Whether this is a fold. Folds use similar code generation as scans, hence
  -- it is handled here. Commutative folds are handled separately.
  -> FoldOrScan
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
  -> Exists (NParLoopCodeGen env idxEnv)
parCodeGenScan descending foldOrScan fun Nothing input index codeSeed codePre codePost codeEnd
  | Just identity <- if descending then findRightIdentity fun else findLeftIdentity fun
  = parCodeGenScan descending foldOrScan fun (Just $ mkConstant tp identity) input index codeSeed codePre codePost codeEnd
  where
    ArgArray _ (ArrayR _ tp) _ _ = input
parCodeGenScan descending foldOrScan fun seed input index codeSeed codePre codePost codeEnd = Exists $ ParLoopCodeGen
  -- If we know an identity value, we can implement this without loop peeling
  (CPULoopAnalysis $ isNothing identity)
  -- In kernel memory, store the index of the block we must now handle and the
  -- reduced value so far. 'Handle' here means that we should now add the value
  -- of that block.
  (TupRsingle memoryTp)
  -- Initialize kernel memory
  (\ptr envs -> do
    -- Initialize all flags to flagInit
    imapFromTo (A.liftInt 0) (A.liftInt descriptorsLength) $ \i -> do
      (flagPtr, _, _) <- getDescriptorSlot memorySlotTp ptr i
      -- Initialize with 0xFF:
      -- Tag is stored in 7 most significant bits, and 0xFE is the tag
      -- before 0 (with wrap around).
      -- The state is stored in the least significant bit, and 1 denotes
      -- that that tile is finished (flagPrefix).
      _ <- instr' $ Store NonVolatile flagPtr (integral TypeWord8 0xFF) Nothing
      return ()

    case seed of
      Nothing -> return ()
      Just s -> do
        (flagPtr, _, valuePtrs) <- getDescriptorSlot memorySlotTp ptr $ A.liftInt 0 -- $ descriptorsLength - 1
        -- tag = 0, tag | flagPrefix = flagPrefix, so
        -- we can write flagPrefix directly.
        _ <- instr' $ Store NonVolatile flagPtr flagPrefix Nothing
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
      (_, _, valuePtrs) <- getDescriptorSlot memorySlotTp ptr descIdx
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
      x <- readArray' envs input index

      accum <- tupleLoad tp accumVar
      codePre envs accum
      isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
      first <- A.land isFirstTile $ envsIsFirst envs
      new <- combineInDirection envs seed first False accum x
      codePost envs new
      tupleStore tp accumVar new
    else do
      -- Parallel mode.
      -- Execute the reduce-phase of a parallel chained scan here.
      x <- readArray' envs input index
      accum <- tupleLoad tp accumVar
      new <- combineInDirection envs identity (envsIsFirst envs) False accum x
      tupleStore tp accumVar new
  )
  -- Code after the tile loop
  (\singleThreaded (accumVar, lookbackIndex, lookbackValue) ptr envs -> do
    nextTileIdx <- A.add numType (envsTileIndex envs) (A.liftInt 1)
    (thisDescIdx, thisTag) <- descriptorIdxTag nextTileIdx
    (thisFlagPtr, thisAggregatePtrs, thisPrefixPtrs) <- getDescriptorSlot memorySlotTp ptr thisDescIdx

    local <- tupleLoad tp accumVar

    inclusivePrefix <-
      if singleThreaded then
        -- In the single threaded mode, 'local' is already the prefix,
        -- as this loop starts with the prefix value of the previous
        -- thread. We can directly write that to kernel memory.
        -- It is our turn since we are in the sequential mode,
        -- no need to wait.
        return local
      else do
        -- Before sharing our aggregate, check if we can overwrite this value
        -- (i.e. synchronize with previous tiles that may read from this field,
        -- as the field may be reuse a prior slot in the cyclic buffer.)
        -- TODO

        -- Share our aggregate
        -- In the parallel mode, 'local' is the aggregate value of this tile.
        tupleStore tp thisAggregatePtrs local
        OP_Word8 newFlag <- A.bor TypeWord8 thisTag $ OP_Word8 flagAggregate
        _ <- instr' $ AtomicStore singleType thisFlagPtr newFlag Release

        -- Initialize look-back
        _ <- instr' $ Store NonVolatile lookbackIndex (op scalarTypeInt $ envsTileIndex envs) Nothing
        case identity of
          Nothing -> return ()
          Just identity' -> do
            value <- llvmOfExp (compileArrayInstrEnvs envs) identity'
            tupleStore tp lookbackValue value

        -- Decoupled look-back
        _ <- Loop.while [] TupRunit
          (\_ -> do
            idx <- instr $ Load NonVolatile lookbackIndex Nothing
            (prevDescIdx, prevTag) <- descriptorIdxTag idx
            (prevFlagPtr, prevAggregatePtrs, prevPrefixPtrs) <- getDescriptorSlot memorySlotTp ptr prevDescIdx

            flag <- instr $ AtomicLoad singleType prevFlagPtr Acquire

            flagAggregate' <- A.bor TypeWord8 prevTag $ OP_Word8 flagAggregate
            flagPrefix' <- A.bor TypeWord8 prevTag $ OP_Word8 flagPrefix

            -- TODO: Should we limit the length of the look-back to prevent cyclic buffer wrap around?
            hasAggregate <- A.eq singleType flag flagAggregate'
            hasPrefix <- A.eq singleType flag flagPrefix'
            
            _ <- A.ifThenElse (TupRunit, A.lor hasAggregate hasPrefix)
              (do
                value <- A.ifThenElse (tp, return hasPrefix)
                  (tupleLoad tp prevPrefixPtrs) (tupleLoad tp prevAggregatePtrs)
                current <- tupleLoad tp lookbackValue

                isFirst <- A.eq singleType idx $ envsTileIndex envs

                new <- combineInDirection envs identity isFirst True current value
                tupleStore tp lookbackValue new

                -- Increment lookbackIndex
                -- Note that this will only be used when hasAggregate = true;
                -- when hasPrefix = true the loop will exit and this value will
                -- not be used.
                OP_Int idx' <- A.sub numType idx $ A.liftInt 1
                instr $ Store NonVolatile lookbackIndex idx' Nothing

                return OP_Unit
              )
              ( return OP_Unit ) -- TODO: sleep?

            A.lnot hasPrefix
          )
          (\_ -> return OP_Unit)
          OP_Unit
        exclusivePrefix <- tupleLoad tp lookbackValue
        tupleStore tp accumVar exclusivePrefix -- Used in second tile loop (only in parallel mode)

        isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
        -- Add local value to exclusive prefix to compute inclusive prefix
        combineInDirection envs seed isFirstTile False exclusivePrefix local

    tupleStore tp thisPrefixPtrs inclusivePrefix

    OP_Word8 newFlag <- A.bor TypeWord8 thisTag $ OP_Word8 flagPrefix
    _ <- instr' $ AtomicStore singleType thisFlagPtr newFlag Release
    return ()
  )
  (\_ _ _ -> return ())
  -- Code after the loop
  (\ptr envs -> do
    let tileCount
          | envsLoopDepth envs /= 0 = internalError "Parallel scan should be 1-dimensional here"
          | (_, tc) : _ <- envsTileSizeCount envs = tc
          | otherwise = internalError "envsTileSizeCount should not be empty during codegen of parallel scan"

    (descIdx, _) <- descriptorIdxTag tileCount
    (_, _, valuePtrs) <- getDescriptorSlot memorySlotTp ptr descIdx
    value <- tupleLoad tp valuePtrs
    codeEnd envs value
  )
  -- In the next tile loop, we prefer loop peeling iff there is no seed.
  -- In the first iteration, the first tile loop will then start without a prefix value,
  -- and we thus should do loop peeling there.
  -- Not executed when this tile is executed in the sequential mode.
  (if foldOrScan == IsFold then Nothing else
    Just (CPULoopAnalysis $ isNothing seed, \(accumVar, _, _) _ envs -> do
      x <- readArray' envs input index
      accum <- tupleLoad tp accumVar
      codePre envs accum
      isFirstTile <- A.eq singleType (envsTileIndex envs) (A.liftInt 0)
      new <- combineInDirection envs seed isFirstTile False accum x
      codePost envs new
      tupleStore tp accumVar new
    )
  )
  where
    -- ((flag, valueAggregate), valuePrefix)
    memorySlotTp = TupRsingle scalarTypeWord8 `TupRpair` tp `TupRpair` tp
    memoryTp = ArrayPrimType (fromIntegral descriptorsLength) $ StructPrimType False $ bufferEltsR memorySlotTp
    flagAggregate = scalar scalarTypeWord8 0
    flagPrefix = scalar scalarTypeWord8 1
    ArgArray _ (ArrayR _ tp) _ _ = input
    identity
      | Just s <- seed
      , if descending then isRightIdentity fun s else isLeftIdentity fun s
      = Just s
      | Just v <- if descending then findRightIdentity fun else findLeftIdentity fun
      = Just $ mkConstant tp v
      | otherwise
      = Nothing

    -- initial: the initial value of the accumulator ('a'). This function
    --   checks whether this is Just or Nothing to know whether the variable
    --   was initialized or not.
    -- isFirst: whether this is the first iteration. When isFirst is true and
    --   initial Nothing, this function will not use the value in 'a' and
    --   directly return 'b'. Otherwise it will combine 'a' and 'b'.
    -- reversed: whether the direction should be reversed (ie fun should be flipped)
    combineInDirection :: Envs env idxEnv -> Maybe a -> Operands Bool -> Bool -> Operands e -> Operands e -> CodeGen Native (Operands e)
    combineInDirection envs initial isFirst reversed a b
      | isJust initial = do
        if envsDescending envs /= reversed then
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) b a
        else
          app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) a b
      | otherwise =
        A.ifThenElse' (tp, isFirst)
          ( return b )
          ( do
            if envsDescending envs /= reversed then
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) b a
            else
              app2 (llvmOfFun2 (compileArrayInstrEnvs envs) fun) a b
          )

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

maxLookbackLength :: Int
maxLookbackLength = 512

descriptorsLength :: Int
descriptorsLength = maxLookbackLength * 2

nextDescriptor :: Operands Int -> CodeGen Native (Operands Int)
nextDescriptor i = do
  OP_Int j <- A.add numType i (A.liftInt 1)
  OP_Bool overflow <- A.gte singleType (OP_Int j) (A.liftInt descriptorsLength)
  OP_Int sub <- A.sub numType (OP_Int j) (A.liftInt descriptorsLength)
  instr $ LLVM.Select overflow sub j

descriptorIdxTag :: Operands Int -> CodeGen Native (Operands Int, Operands Word8)
descriptorIdxTag tileIdx = do
  descIdx <- A.rem TypeInt tileIdx (A.liftInt descriptorsLength)
  tag <- A.quot TypeInt tileIdx (A.liftInt descriptorsLength) >>= A.mul numType (A.liftInt 2)
  tag8 <- A.fromIntegral TypeInt (numType @Word8) tag
  return (descIdx, tag8)

getDescriptorSlot
  :: TupR ScalarType ((Word8, value), value)
  -> Operand (Ptr (Struct (SizedArray (Struct (BufferEltR ((Word8, value), value))))))
  -> Operands Int
  -> CodeGen Native
      ( Operand (Ptr Word8)
      , TupR Operand (Distribute Ptr (BufferEltR value))
      , TupR Operand (Distribute Ptr (BufferEltR value)))
getDescriptorSlot memorySlotTp ptr (OP_Int i) = do
  slot <- instr' $ GetElementPtr $
    GEP ptr (A.num numType 0 :: Operand Int32) $
    GEPStruct (ArrayPrimType (fromIntegral descriptorsLength) $ StructPrimType False $ bufferEltsR memorySlotTp) TupleIdxSelf $
    GEPArray i GEPEmpty
  ptrs <- tuplePtrs memorySlotTp slot
  case ptrs of
    TupRsingle flag `TupRpair` valueAggregate `TupRpair` valuePrefix -> return (flag, valueAggregate, valuePrefix)
    _ -> internalError "Pair impossible"
