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
-- (
--   codegen
--   )
  where

-- accelerate
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (shapeRFromRank, shapeType, ShapeR(..), rank)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Partitioned as P hiding (combine)
import Data.Array.Accelerate.Analysis.Exp
import Data.Array.Accelerate.Eval
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment hiding ( Empty )
import Data.Array.Accelerate.LLVM.CodeGen.Cluster
import Data.Array.Accelerate.LLVM.Native.Operation
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.Target
import Data.Typeable
import Data.Maybe

import LLVM.AST.Type.Module
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.RMW
import LLVM.AST.Type.AddrSpace
import qualified LLVM.AST.Type.Instruction.Compare as Compare
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified LLVM.AST.Type.Function as LLVM
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.LLVM.CodeGen.Sugar (app1, IROpenFun2 (app2))
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.Trafo.Desugar (ArrayDescriptor(..))
import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import Data.Array.Accelerate.Analysis.Match (matchShapeR)
import Data.Array.Accelerate.Trafo.Exp.Substitution (compose)
import Data.Array.Accelerate.LLVM.Native.CodeGen.Permute (atomically)
import Control.Monad.State (StateT(..), lift, execStateT)
import qualified Data.Map as M
import Data.ByteString.Short ( ShortByteString )
import Data.Array.Accelerate.AST.LeftHandSide (Exists (Exists), lhsToTupR)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Label)
import Data.Array.Accelerate.LLVM.CodeGen.Constant (constant)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP(..))
import Data.Coerce (coerce)
import Data.Functor.Compose
import Control.Monad
import Data.Bifunctor (Bifunctor(..))
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop as Loop
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Constant

traceIfDebugging :: String -> a -> a
traceIfDebugging _ a = a --Debug.Trace.trace str a

-- Temporary flag to enable the new (currently sequential) code generator.
-- I'm keeping both code generators functional for now, such that we can
-- evaluate them easily and then decide which code generator we want to keep.
-- At that point, we can remove the code of the other code generator.
newCodeGen :: Bool
newCodeGen = True

codegen :: ShortByteString
        -> Env AccessGroundR env
        -> Clustered NativeOp args
        -> Args env args
        -> LLVM Native
           ( Int -- The size of the kernel data, shared by all threads working on this kernel.
           , Module (KernelType env))
codegen name env cluster args
 | newCodeGen
 , flat@(FlatCluster shr idxLHS sizes dirs localR localLHS flatOps) <- toFlatClustered cluster args
 , parallelDepth <- flatClusterIndependentLoopDepth flat
 , Exists parallelShr <- shapeRFromRank parallelDepth =
  codeGenFunction name type' (LLVM.Lam argTp "arg" . LLVM.Lam primType "workassist.first_index" . LLVM.Lam primType "workassist.activities_slot") $ do
    extractEnv

    -- Before the parallel work of a kernel is started, we first run the function once.
    -- This first call will initialize kernel memory (SEE: Kernel Memory)
    -- and decide whether the runtime may try to let multiple threads work on this kernel.
    initBlock <- newBlock "init"
    finishBlock <- newBlock "finish" -- Finish function from the work assisting paper
    workBlock <- newBlock "work"
    switch (OP_Word32 workassistFirstIndex) workBlock [(0xFFFFFFFF, initBlock), (0xFFFFFFFE, finishBlock)]

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
                  1024 * 4
                else
                  1024 * 16 -- TODO: Implement a better heuristic to choose the tile size

          -- Number of tiles
          sizeAdd <- A.add numType size (A.liftInt $ tileSize - 1)
          OP_Int tileCount' <- A.quot TypeInt sizeAdd (A.liftInt tileSize)
          tileCount <- instr' $ Trunc boundedType boundedType tileCount'

          let envs' = envs{
            envsLoopDepth = 0,
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
          envs'' <- bindLocalsInTile 1 tileSize envs'
          workassistLoop workassistIndex workassistFirstIndex workassistActivitiesSlot tileCount $ \seqMode tileIdx' -> do
            tileIdx <- instr' $ Ext boundedType boundedType tileIdx'

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
                envsTileIndex = OP_Int tileIdx
              }

            -- Note: ifThenElse' does not generate code for the then-branch if
            -- the condition is a constant. Thus, if a kernel does not have a
            -- scan, we won't generate separate code for a single-threaded mode.
            _ <- A.ifThenElse' (TupRunit, OP_Bool seqMode')
              -- Sequential mode
              (do
                let tileLoop = ptSingleThreaded tileLoops
                -- Only do loop peeling if requested and when there are no nested loops.
                -- Peeling over nested loops causes a lot of code duplication,
                -- and is probably not worth it.
                let peel = if ptPeel tileLoop && null loops' then PeelGuaranteed else PeelNot
                -- We can use PeelGuaranteed instead of PeelConditional since we
                -- know that each tile is non-empty.

                ptBefore tileLoop envs'''
                Loop.loopWith peel (isDescending direction) lower upper $ \isFirst idx -> do
                  localIdx <- A.sub numType idx lower
                  let envs'''' = envs'''{
                      envsLoopDepth = 1,
                      envsIdx = Env.partialUpdate (op TypeInt idx) idxVar $ envsIdx envs'',
                      envsIsFirst = isFirst,
                      envsTileLocalIndex = localIdx
                    }
                  genSequential envs'''' loops $ ptIn tileLoop
                ptAfter tileLoop envs'''
                return OP_Unit
              )
              -- Parallel mode
              (do
                forM_ ((True, ptFirstLoop tileLoops) : map (False, ) (ptOtherLoops tileLoops)) $ \(isFirstTileLoop, tileLoop) -> do
                  -- All nested loops are placed in the first tile loop by parCodeGens
                  let loops'' = if isFirstTileLoop then loops' else []
                  -- Only do loop peeling if requested and when there are no nested loops.
                  -- Peeling over nested loops causes a lot of code duplication,
                  -- and is probably not worth it.
                  let peel = if ptPeel tileLoop && null loops'' then PeelGuaranteed else PeelNot
                  -- We can use PeelGuaranteed instead of PeelConditional since we
                  -- know that each tile is non-empty.

                  ptBefore tileLoop envs'''
                  Loop.loopWith peel (isDescending direction) lower upper $ \isFirst idx -> do
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

        OP_Bool isSmall <- A.lt singleType tileCount' $ A.liftInt 2
        value <- instr' $ Select isSmall (scalar (scalarType @Word8) 0) (scalar scalarType 1)
        retval_ value

      setBlock finishBlock
      -- Nothing has to be done in the finish function for this kernel.
      retval_ $ scalar (scalarType @Word8) 0

      setBlock workBlock
      workassistChunked parallelShr workassistIndex workassistFirstIndex workassistActivitiesSlot tileSize parSizes $ \idx -> do
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
    (argTp, extractEnv, workassistIndex, workassistFirstIndex, workassistActivitiesSlot, kernelMem', gamma) = bindHeaderEnv env

    isDescending :: LoopDirection Int -> Bool
    isDescending LoopDescending = True
    isDescending _ = False

codegen name env (Clustered c b) args =
  codeGenFunction name type' (LLVM.Lam argTp "arg" . LLVM.Lam primType "workassist.first_index" . LLVM.Lam primType "workassist.activities_slot") $ do
    extractEnv

    -- Before the parallel work of a kernel is started, we first run the function once.
    -- This first call will initialize kernel memory (SEE: Kernel Memory)
    -- and decide whether the runtime may try to let multiple threads work on this kernel.
    init <- instr $ Cmp singleType Compare.EQ workassistFirstIndex (scalar scalarType 0xFFFFFFFF)
    initBlock <- newBlock "init"
    workBlock <- newBlock "work"
    _ <- cbr init initBlock workBlock

    setBlock initBlock
    retval_ $ scalar (scalarType @Word8) 1

    setBlock workBlock

    let b' = mapArgs BCAJA b
    (acc, loopsize) <- execStateT (evalCluster (toOnlyAcc c) b' args gamma ()) (mempty, LS ShapeRz OP_Unit)
    _acc' <- operandsMapToPairs acc $ \(accTypeR, toOp, fromOp) -> fmap fromOp $ flip execStateT (toOp acc) $ case loopsize of
      LS loopshr loopsh -> 
        workassistChunked' loopshr workassistIndex workassistFirstIndex workassistActivitiesSlot (flipShape loopshr loopsh) accTypeR
          (body loopshr toOp fromOp, -- the LoopWork
          StateT $ \op -> second toOp <$> runStateT (foo (A.liftInt 0) []) (fromOp op)) -- the action to run after the outer loop
    -- acc'' <- flip execStateT acc' $ foo (liftInt 0) []
    pure 0
    where
      ba = makeBackendArg @NativeOp args gamma c b
      (argTp, extractEnv, workassistIndex, workassistFirstIndex, workassistActivitiesSlot, _, gamma) = bindHeaderEnv env
      body :: ShapeR sh -> (Accumulated -> a) -> (a -> Accumulated) -> LoopWork sh (StateT a (CodeGen Native))
      body ShapeRz _ _ = LoopWorkZ
      body (ShapeRsnoc shr) toOp fromOp = LoopWorkSnoc (body shr toOp fromOp) (\i is -> StateT $ \op -> second toOp <$> runStateT (foo i is) (fromOp op))
      foo :: Operands Int -> [Operands Int] -> StateT Accumulated (CodeGen Native) ()
      foo linix ixs = do
        let d = length ixs -- TODO check: this or its inverse (i.e. totalDepth - length ixs)?
        let i = (d, linix, ixs)
        newInputs <- readInputs @_ @_ @NativeOp i args ba gamma
        outputs <- evalOps @NativeOp i c newInputs args gamma
        writeOutputs @_ @_ @NativeOp i args outputs gamma

opCodeGen :: FlatOp NativeOp env idxEnv -> (LoopDepth, OpCodeGen Native NativeOp env idxEnv)
opCodeGen (FlatOp NGenerate (ArgFun fun :>: array :>: _) (_ :>: IdxArgIdx depth idxs :>: _)) =
  ( depth
  , OpCodeGenSingle $ \envs -> do
    let idxs' = envsPrjIndices idxs envs
    r <- app1 (llvmOfFun1 (compileArrayInstrEnvs envs) fun) idxs'
    writeArray' envs array idxs r
  )
opCodeGen (FlatOp NMap (ArgFun fun :>: input :>: output :>: _) (_ :>: IdxArgIdx depth idxs :>: _)) =
  ( depth
  , OpCodeGenSingle $ \envs -> do
    x <- readArray' envs input idxs
    r <- app1 (llvmOfFun1 (compileArrayInstrEnvs envs) fun) x
    writeArray' envs output idxs r
  )
opCodeGen (FlatOp NBackpermute (_ :>: input :>: output :>: _) (_ :>: IdxArgIdx depth inputIdx :>: IdxArgIdx _ outputIdx :>: _)) =
  ( depth
  , OpCodeGenSingle $ \envs -> do
    -- Note that the index transformation (the function in the first argument)
    -- is already executed and part of the idxEnv. The index transformation is
    -- thus now given by 'inputIdx' and 'outputIdx'.
    x <- readArray' envs input inputIdx
    writeArray' envs output outputIdx x
  )
opCodeGen (FlatOp NPermute
    (ArgFun combine :>: output :>: locks :>: source :>: _)
    (_ :>: _ :>: _ :>: IdxArgIdx depth sourceIdx :>: _)) =
  ( depth
  , OpCodeGenSingle $ \envs -> do
    -- project element onto the destination array and (atomically) update
    x' <- readArray' envs source sourceIdx
    A.when (A.isJust x') $ do
      let idxx = A.fromJust x'
      let idx = A.fst idxx
      let x = A.snd idxx
      let sh' = envsPrjParameters (shapeExpVars shr sh) envs
      j <- intOfIndex shr sh' idx
      -- TODO: Rewrite the function below to take Envs as argument instead of Gamma,
      -- and then get rid of envsGamma
      let gamma = envsGamma envs
      atomically gamma locks j $ do
        y <- readArray TypeInt gamma output j
        r <- app2 (llvmOfFun2 (compileArrayInstrEnvs envs) combine) x y
        writeArray TypeInt gamma output j r
  )
  where
    ArgArray _ (ArrayR shr tp) sh _ = output
opCodeGen (FlatOp NPermute'
    (output :>: source :>: _)
    (_ :>: IdxArgIdx depth sourceIdx :>: _)) =
  ( depth
  , OpCodeGenSingle $ \envs -> do
    x' <- readArray' envs source sourceIdx
    A.when (A.isJust x') $ do
      let idxx = A.fromJust x'
      let idx = A.fst idxx
      let x = A.snd idxx
      let sh' = envsPrjParameters (shapeExpVars shr sh) envs
      j <- intOfIndex shr sh' idx
      let gamma = envsGamma envs
      writeArray TypeInt gamma output j x
  )
  where
    ArgArray _ (ArrayR shr tp) sh _ = output
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
    (_ :>: IdxArgIdx _ inputIdx :>: IdxArgIdx depth outputIdx :>: _))
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
    ArgArray _ (ArrayR _ tp) inputSh _ = input
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
  = parCodeGenScan descending True fun seed input inputIdx
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
  -> Exists (ParLoopCodeGen Native env idxEnv)
parCodeGenFoldCommutative descending fun seed identity input output inputIdx outputIdx = Exists $ ParLoopCodeGen
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
  (\ptr envs -> do
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
        _ <- Loop.while TupRunit
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
  (\ptr envs -> tupleAlloca tp)
  -- Code before the tile loop
  (\singleThreaded accumVar ptr envs ->
    if singleThreaded then do
      -- In the single threaded mode, we directly do a scan over this tile,
      -- instead of the reduce, lookback and scan phases.
      ptrs <- tuplePtrs memoryTp ptr
      case ptrs of
        TupRsingle _ -> internalError "Pair impossible"
        TupRpair (TupRsingle idxPtr) valuePtrs -> do
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
          _ <- Loop.while TupRunit
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
    Just (isNothing seed, \accumVar ptr envs -> do
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

-- Old, EvalOp based implementation

-- We use some unsafe coerces in the context of the accumulators. 
-- Some, in this function, are very local. Others, like in evalOp, 
-- just deal with the assumption that the specific operand stored at index l indeed belongs to operation l.
operandsMapToPairs
  :: Accumulated
  -> (forall accR. ( TypeR accR
     , Accumulated -> Operands accR
     , Operands accR -> Accumulated) -> r)
  -> r
operandsMapToPairs acc k
  = case existentialStuff of
    (Exists accR, toR, fromR) -> k ( accR
                                   , unsafeUnExists . toR . map (fst.snd) . M.toList
                                   , M.fromList . zip labels . fromR . Exists)
  where
  (labels, (_, existentialStuff)) = second (second (foldr
      (\(Exists newR) (Exists accR, toR, fromR) ->
        ( Exists (TupRpair newR accR)
        , \(Exists this : rest') -> case toR rest' of Exists rest -> Exists $ OP_Pair this rest
        , \(Exists hastobepair) -> case unsafeCoerce hastobepair of OP_Pair this rest -> (Exists this, Exists newR) : fromR (Exists rest)))
      (   Exists TupRunit
        , \[] -> Exists OP_Unit
        , const [])) -- should always get "Exists OP_Unit" as argument
    . unzip)
    . unzip
    $ M.toList acc
  unsafeUnExists :: Exists f -> f a
  unsafeUnExists (Exists fa) = unsafeCoerce fa

-- type family ShapeMinus big small where
--   ShapeMinus sh () = sh
--   ShapeMinus (sh, Int) (sh', Int) = ShapeMinus sh sh'



-- TODO: we need to only consider each _in-order_ vertical argument
-- TODO: we ignore backpermute currently. Could use this function to check the outputs and vertical, and the staticclusteranalysis evalI for the inputs.
-- e.g. backpermute . fold: shape of backpermute output plus the extra dimension of fold.
-- loopsizeOutVertical :: forall args env. Cluster NativeOp args -> Gamma env -> Args env args -> Loopsizes
-- loopsizeOutVertical = undefined
-- loopsizeOutVertical (Cluster _ (Cluster' io _)) gamma args = go io args
--   where
--     go :: ClusterIO a i o -> Args env a -> Loopsizes
--     go Empty ArgsNil = LS ShapeRz OP_Unit
--     go (Input io')                     (ArgArray _ (ArrayR shr _) sh _ :>: args') = go io' args' -- $ \x -> combine x (shr, aprjParameters (unsafeToExpVars sh) gamma) k
--     go (Output _ _ _ io')              (ArgArray _ (ArrayR shr _) sh _ :>: args') = combine (go io' args') $ LS shr (aprjParameters (unsafeToExpVars sh) gamma)
--     go (Trivial io')                   (ArgArray _ (ArrayR shr _) sh _ :>: args') = combine (go io' args') $ LS shr (aprjParameters (unsafeToExpVars sh) gamma)
--     go (Vertical _ (ArrayR shr _) io') (ArgVar sh                      :>: args') = combine (go io' args') $ LS shr (aprjParameters                  sh  gamma)
--     go (MutPut io')                    (_                              :>: args') = go io' args'
--     go (ExpPut io')                    (_                              :>: args') = go io' args'
--     go (VarPut io')                    (_                              :>: args') = go io' args'
--     go (FunPut io')                    (_                              :>: args') = go io' args'
-- get the largest ShapeR, and the corresponding shape
combine :: Loopsizes -> Loopsizes -> Loopsizes
combine x@(LS a _) y@(LS b _) = if rank a > rank b then x else y



type Accumulated = M.Map Label (Exists Operands, Exists TypeR)
-- type Accumulator = (Accumulated, Block, Block)

instance EvalOp NativeOp where
  type EvalMonad NativeOp = StateT Accumulated (CodeGen Native) -- should be a ReaderT
  -- dimension and linear and multidim index. The last has 'trust me, this is the right shape' levels of type safety, but trust me. It is the right shape.
  type Index NativeOp = (Int, Operands Int, [Operands Int])
  type Embed' NativeOp = Compose Maybe Operands
  type EnvF NativeOp = GroundOperand

  embed (GroundOperandParam  x) = Compose $ Just $ ir' x
  embed (GroundOperandBuffer _) = error "does this ever happen?"

  unit = Compose $ Just OP_Unit

  -- don't need to be in the monad!
  indexsh vars gamma = pure . CJ $ aprjParameters (unsafeToExpVars vars) gamma
  indexsh' vars gamma = pure . CJ $ aprjParameters vars gamma

  subtup _ CN = CN
  subtup SubTupRskip (CJ _) = CJ OP_Unit
  subtup SubTupRkeep (CJ x) = CJ x
  subtup (SubTupRpair a b) (CJ (OP_Pair x y)) = CJ $ OP_Pair ((\(CJ z)->z) $ subtup @NativeOp a $ CJ x) ((\(CJ z)->z) $ subtup @NativeOp b $ CJ y)

  writeOutput tp sh (TupRsingle buf) gamma (d,i,_) = \case
    CN -> pure ()
    CJ x
      | Refl <- reprIsSingle @ScalarType @_ @Buffer tp
      -> lift $ when (sh `isAtDepth` d) $ writeBuffer tp TypeInt (aprjBuffer buf gamma) (op TypeInt i) Nothing (op tp x)
  writeOutput _ _ _ _ _ = error "not single"

  readInput :: forall e env sh. ScalarType e -> GroundVars env sh -> GroundVars env (Buffers e) -> Gamma env -> BackendClusterArg2 NativeOp env (In sh e) -> (Int, Operands Int, [Operands Int]) -> StateT Accumulated (CodeGen Native) (Compose Maybe Operands e)
  readInput _ _ _ _ _ (d,_,is) | d /= length is = error "fail"
  readInput tp _ (TupRsingle buf) gamma (BCAN2 Nothing d') (d,i, _)
    | d /= d' = pure CN
    | Refl <- reprIsSingle @ScalarType @e @Buffer tp
    = lift $ CJ . ir tp <$> readBuffer tp TypeInt (aprjBuffer buf gamma) (op TypeInt i) Nothing
  readInput tp sh (TupRsingle buf) gamma (BCAN2 (Just (BP shr1 (shr2 :: ShapeR sh2) f _ls)) _) (d,_,ix)
    | Just Refl <- varsContainsThisShape sh shr2
    , shr1 `isAtDepth'` d
    , Refl <- reprIsSingle @ScalarType @e @Buffer tp
    = lift $ CJ . ir tp <$> do
      sh2 <- app1 (llvmOfFun1 @Native (compileArrayInstrGamma gamma) f) $ multidim shr1 ix
      let sh' = aprjParameters (groundToExpVar (shapeType shr2) sh) gamma
      i <- intOfIndex shr2 sh' sh2
      readBuffer tp TypeInt (aprjBuffer (buf) gamma) (op TypeInt i) Nothing
    | otherwise = pure CN
  readInput _ _ (TupRsingle _) _ _ (_,_,_) = error "here"
  -- assuming no bp, and I'll just make a read at every depth?
    -- lift $ CJ . ir tp <$> readBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i)
    -- second attempt, the above segfaults: never read instead
    -- pure CN
    -- also segfaults :(
    {- weird: this implies that a is a `IsUnit`, but it happens on Int
    error $ show tp <> case buf of
    TupRsingle _ -> "single"
    TupRpair _ _ -> "pair"
    TupRunit -> "unit" -}
  readInput _ _ _ _ _ _ = error "not single"

  evalOp  :: (Int, Operands Int, [Operands Int])
          -> Label
          -> NativeOp args
          -> Gamma env
          -> BackendArgEnv NativeOp env (InArgs args)
          -> StateT Accumulated (CodeGen Native) (Env (FromArg' NativeOp env) (OutArgs args))
  -- evalOp _ _ _ _ _ = error "todo: add depth checks to all matches"
  evalOp (d,_,_) _ NMap gamma (Push (Push (Push Env.Empty (BAE _ _)) (BAE (Value' x' (Shape' shr sh)) (BCAN2 _ d'))) (BAE f _))
    = lift $ Push Env.Empty . FromArg . flip Value' (Shape' shr sh) <$> case x' of
      CJ x | d == d' -> CJ <$> traceIfDebugging ("map" <> show d') (app1 (llvmOfFun1 @Native (compileArrayInstrGamma gamma) f) x)
      _   -> pure CN
  evalOp _ _ NBackpermute _ (Push (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE (Value' x _) _)) _)
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' x $ Shape' shr sh
  evalOp (d',_,is) _ NGenerate gamma (Push (Push Env.Empty (BAE (Shape' shr (CJ sh)) _)) (BAE f (BCAN2 Nothing _d)))
    | shr `isAtDepth'` d' = traceIfDebugging ("generate" <> show d') $ lift $ Push Env.Empty . FromArg . flip Value' (Shape' shr (CJ sh)) . CJ <$> app1 (llvmOfFun1 @Native (compileArrayInstrGamma gamma) f) (multidim shr is)
    -- | d' == d = error $ "how come we didn't hit the case above?" <> show (d', d, rank shr)
    | otherwise        = pure $ Push Env.Empty $ FromArg $ Value' CN (Shape' shr (CJ sh))
  evalOp (d',_,is) _ NGenerate gamma (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE f (BCAN2 (Just (BP shrO shrI idxTransform _ls)) _d)))
    | not $ shrO `isAtDepth'` d'
    = pure $ Push Env.Empty $ FromArg $ Value' CN (Shape' shr sh)
    | Just Refl <- matchShapeR shrI shr
    = traceIfDebugging ("generate" <> show d') $ lift $ Push Env.Empty . FromArg . flip Value' (Shape' shr sh) . CJ <$> app1 (llvmOfFun1 @Native (compileArrayInstrGamma gamma) (compose f idxTransform)) (multidim shrO is)
    | otherwise = error "bp shapeR doesn't match generate's output"
  -- For Permute, we ignore all the BP info here and simply assume that there is none
  evalOp (d',_,is) _ NPermute gamma (Push (Push (Push (Push Env.Empty
    (BAE (Value' x'' (Shape' shrx _))           (BCAN2 _ d))) -- input
    (BAE (ArrayDescriptor shrl shl bufl, lty)   _)) -- lock
    (BAE (ArrayDescriptor shrt sht buft, tty)   _)) -- target
    (BAE (llvmOfFun2 @Native (compileArrayInstrGamma gamma) -> c) _)) -- combination function
    | CJ x' <- x''
    , d == d'
    = traceIfDebugging ("permute" <> show d') $ lift $ do
        -- project element onto the destination array and (atomically) update
        A.when (A.isJust x') $ do
          let ixx = A.fromJust x'
          let ix = A.fst ixx
          let x = A.snd ixx
          let sht' = aprjParameters (unsafeToExpVars sht) gamma
          j <- intOfIndex shrt sht' ix
          atomically gamma (ArgArray Mut (ArrayR shrl lty) shl bufl) j $ do
            y <- readArray TypeInt gamma (ArgArray Mut (ArrayR shrt tty) sht buft) j
            r <- app2 c x y
            writeArray TypeInt gamma (ArgArray Mut (ArrayR shrt tty) sht buft) j r
        pure Env.Empty
    | d == d' = error "case above?"
    | otherwise = pure Env.Empty
  evalOp (d',_,is) _ NPermute' gamma (Push (Push Env.Empty
    (BAE (Value' x'' (Shape' shrx _))           (BCAN2 _ d))) -- input
    (BAE (ArrayDescriptor shrt sht buft, tty)   _)) -- target
    | CJ x' <- x''
    , d == d'
    = traceIfDebugging ("permute'" <> show d') $ lift $ do
        -- project element onto the destination array and (atomically) update
        A.when (A.isJust x') $ do
          let ixx = A.fromJust x'
          let ix = A.fst ixx
          let x = A.snd ixx
          let sht' = aprjParameters (unsafeToExpVars sht) gamma
          j <- intOfIndex shrt sht' ix
          writeArray TypeInt gamma (ArgArray Mut (ArrayR shrt tty) sht buft) j x
        pure Env.Empty
    | d == d' = error "case above?"
    | otherwise = pure Env.Empty
  evalOp (d',_,ixs) l (NScan1 LeftToRight) gamma (Push (Push _ (BAE (Value' x' sh) (BCAN2 Nothing d))) (BAE f' _))
    | f <- llvmOfFun2 @Native (compileArrayInstrGamma gamma) f'
    , Lam (lhsToTupR -> ty :: TypeR e) _ <- f'
    , CJ x <- x'
    , d == d'
    , inner:_ <- ixs
    = traceIfDebugging ("scan" <> show d') $ StateT $ \acc -> do
        let (Exists (unsafeCoerce @(Operands _) @(Operands e) -> accX), eTy) = acc M.! l
        z <- A.ifThenElse (ty, A.eq singleType inner (constant typerInt 0)) (pure x) (app2 f accX x) -- note: need to apply the accumulator as the _left_ argument to the function
        pure (Push Env.Empty $ FromArg (Value' (CJ z) sh), M.adjust (const (Exists z, eTy)) l acc)
    | otherwise = pure $ Push Env.Empty $ FromArg (Value' CN sh)
  evalOp _ _ (NScan1 _) _ (Push (Push _ (BAE _ (BCAN2 (Just BP{}) _))) (BAE _ _)) = error "backpermuted scan"
  evalOp _ _ NFold _ _ = error "todo: fold"
  -- we can ignore the index permutation for folds here
  evalOp (d',_,ixs) l NFold1 gamma (Push (Push _ (BAE (Value' x' (Shape' (ShapeRsnoc shr') (CJ (OP_Pair sh _)))) (BCAN2 _ d))) (BAE f' _))
    | f <- llvmOfFun2 @Native (compileArrayInstrGamma gamma) f'
    , Lam (lhsToTupR -> ty :: TypeR e) _ <- f'
    , CJ x <- x'
    , d == d'
    , inner:_ <- ixs
    = traceIfDebugging ("fold2work" <> show d') $ StateT $ \acc -> do
        let (Exists (unsafeCoerce @(Operands _) @(Operands e) -> accX), eTy) = acc M.! l
        z <- A.ifThenElse (ty, A.eq singleType inner (constant typerInt 0)) (pure x) (app2 f accX x) -- note: need to apply the accumulator as the _left_ argument to the function
        pure (Push Env.Empty $ FromArg (Value' (CJ z) (Shape' shr' (CJ sh))), M.adjust (const (Exists z, eTy)) l acc)
    | Lam (lhsToTupR -> _ty :: TypeR e) _ <- f'
    , d == d'+1 -- the fold was in the iteration above; we grab the result from the accumulator now
    = traceIfDebugging ("fold2done" <> show d') $ StateT $ \acc -> do
        let (Exists (unsafeCoerce @(Operands _) @(Operands e) -> x), _) = acc M.! l
        pure (Push Env.Empty $ FromArg (Value' (CJ x) (Shape' shr' (CJ sh))), acc)
    | otherwise = pure $ Push Env.Empty $ FromArg (Value' CN (Shape' shr' (CJ sh)))
  evalOp _ _ _ _ _ = error "unmatched pattern?"


instance TupRmonoid Operands where
  pair' = OP_Pair
  unpair' (OP_Pair x y) = (x, y)

instance (TupRmonoid f) => TupRmonoid (Compose Maybe f) where
  pair' (Compose l) (Compose r) = Compose $ pair' <$> l <*> r
  unpair' (Compose p) = maybe (CN, CN) (bimap CJ CJ . unpair') p

unsafeToExpVars :: GroundVars env sh -> ExpVars env sh
unsafeToExpVars TupRunit = TupRunit
unsafeToExpVars (TupRpair l r) = TupRpair (unsafeToExpVars l) (unsafeToExpVars r)
unsafeToExpVars (TupRsingle (Var g idx)) = case g of
  GroundRbuffer _ -> error "unsafeToExpVars on a buffer"
  GroundRscalar t -> TupRsingle (Var t idx)

maybeTy :: TypeR a -> TypeR (PrimMaybe a)
maybeTy ty = TupRpair (TupRsingle scalarTypeWord8) (TupRpair TupRunit ty)









-- TODO: rename to 'static info' or 'symbolic execution' or so
newtype JustAccumulator a b = JA (a b)

data Loopsizes where
  LS :: ShapeR sh -> Operands sh -> Loopsizes

instance Show Loopsizes where
  show (LS shr _) = "Loop of rank " <> show (rank shr)

merge :: Loopsizes -> GroundVars env sh -> Gamma env -> Loopsizes
merge ls v gamma = combine ls $ LS (gvarsToShapeR v) (aprjParameters (unsafeToExpVars v) gamma)

-- mkls :: Int -> ShapeR sh -> Operands sh -> Bool -> Loopsizes
-- mkls d shr sh b
--   | d == rank shr = LS shr sh b
--   | d > rank shr = mkls d (ShapeRsnoc shr) (multidim (ShapeRsnoc shr) $ foldr (:) [constant typerInt 1] $ multidim' shr sh) b
--   | d < rank shr = case shr of 
--       ShapeRsnoc shr' -> mkls d shr' (multidim shr' $ init $ multidim' shr sh) b
--       _ -> error ""
--   | otherwise = error ""

-- merge' :: Loopsizes -> Loopsizes -> Loopsizes
-- merge' ls1@(LS shr1 sh1) ls2@(LS shr2 sh2)
--   | rank shr1 >= rank shr2 && (b1 || not b2) = ls1
--   | rank shr1 <= rank shr2 && (b2 || not b1) = ls2
--   | otherwise = let (big, small) = if rank shr1 > rank shr2 then (ls1,ls2) else (ls2,ls1)
--                 in case (big,small) of
--                   (LS shrB (flipShape shrB -> shB), LS shrS (flipShape shrS -> shS)) 
--                     -> Debug.Trace.traceShow (rank shrB, rank shrS) $ 
--                       LS shrB (multidim shrB $ Prelude.take (rank shrB - rank shrS) (multidim' shrB shB) ++ multidim' shrS shS) 
--                           -- (flipShape shrB . multidim shrB $ multidim' shrS shS ++ drop (rank shrS) (multidim' shrB shB)) 
--                           -- False
--                   _ -> error "huh"
--     where flipShape x y = y

    -- error "todo: take the known indices from the smaller True one, and the rest from the larger False one, call the result False"

instance EvalOp (JustAccumulator NativeOp) where
  type EvalMonad (JustAccumulator NativeOp) = StateT (Accumulated, Loopsizes) (CodeGen Native)
  type Index (JustAccumulator NativeOp) = ()
  type Embed' (JustAccumulator NativeOp) = Both TypeR Operands
  type EnvF (JustAccumulator NativeOp) = GroundOperand

  unit = Both TupRunit OP_Unit
  embed = error "not needed"
  indexsh  vars gamma = pure $ Both (mapTupR varType $ unsafeToExpVars vars) (aprjParameters (unsafeToExpVars vars) gamma)
  indexsh' vars gamma = pure $ Both (mapTupR varType vars) (aprjParameters vars gamma)

  subtup SubTupRskip _ = Both TupRunit OP_Unit
  subtup SubTupRkeep x = x
  subtup (SubTupRpair a b) (Both (TupRpair x y) (OP_Pair x' y')) = case (subtup @(JustAccumulator NativeOp) a (Both x x'), subtup @(JustAccumulator NativeOp) b (Both y y')) of
    (Both l l', Both r r') -> Both (TupRpair l r) (OP_Pair l' r')
  subtup _ _ = error "subtup-pair with non-pair TypeR"

  readInput _ _ _ _ (BCA2JA IsUnit) _ = pure $ Both TupRunit OP_Unit
  readInput ty sh _ gamma (BCA2JA (BCAN2 Nothing               _)) _ = StateT $ \(acc,ls) -> pure (Both (TupRsingle ty) (zeroes $ TupRsingle ty), (acc, merge ls sh gamma))
  readInput ty _ _  gamma (BCA2JA (BCAN2 (Just (BP _ _ _ ls')) _)) _ = StateT $ \(acc,ls) -> pure (Both (TupRsingle ty) (zeroes $ TupRsingle ty), (acc, merge ls ls' gamma))

  writeOutput _ sh _ gamma _ _ = StateT $ \(acc,ls) -> pure ((), (acc, merge ls sh gamma))

  evalOp () l (JA (NScan1 LeftToRight)) _ (Push (Push _ (BAE (Value' (Both ty x) sh) _)) (BAE _ _))
    = StateT $ \(acc,ls) -> do
        let thing = zeroes ty
        pure (Push Env.Empty $ FromArg (Value' (Both ty x) sh), (M.insert l (Exists thing, Exists ty) acc, ls))
  evalOp () _ (JA NFold) _ _ = undefined
  evalOp () l (JA NFold1) _ (Push (Push _ (BAE (Value' (Both ty x) (Shape' (ShapeRsnoc shr) sh)) _)) (BAE _ _))
    = StateT $ \(acc,ls) -> do
        let thing = zeroes ty
        pure (Push Env.Empty $ FromArg (Value' (Both ty x) (Shape' shr (case sh of Both (TupRpair x _) (OP_Pair x' _) -> Both x x'))), (M.insert l (Exists thing, Exists ty) acc, ls))
  evalOp () _ (JA NMap) _ (Push (Push (Push Env.Empty (BAE _ _)) (BAE (Value' _ (Shape' shr sh)) _)) (BAE f _))
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' (Both (getOutputType f) (zeroes (getOutputType f))) (Shape' shr sh)
  evalOp () _ (JA NBackpermute) _ (Push (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE (Value' x _) _)) _)
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' x $ Shape' shr sh
  evalOp () _ (JA NGenerate) _ (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE f _))
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' (Both (getOutputType f) (zeroes (getOutputType f))) (Shape' shr sh)
  evalOp _ _ (JA NPermute) _ (Push (Push (Push (Push Env.Empty (BAE (Value' _ (Shape' shr (Both _ sh))) _)) _) _) _)
    = StateT $ \(acc,ls) -> pure (Env.Empty, (acc, combine ls $ LS shr sh))
  evalOp _ _ (JA NPermute') _ (Push (Push Env.Empty (BAE (Value' _ (Shape' shr (Both _ sh))) _)) _)
    = StateT $ \(acc,ls) -> pure (Env.Empty, (acc, combine ls $ LS shr sh))
  evalOp _ _ _ _ _ = error "missing"

getOutputType :: Fun env (i -> o) -> TypeR o
getOutputType (Lam _ (Body e)) = expType e
getOutputType _ = error "nope"

instance MakesILP op => MakesILP (JustAccumulator op) where
  type BackendVar (JustAccumulator op) = BackendVar op
  type BackendArg (JustAccumulator op) = BackendArg op
  newtype BackendClusterArg (JustAccumulator op) a = BCAJA (BackendClusterArg op a)
  mkGraph (JA _) = undefined -- do not want to run the ILP solver again!
  finalize = undefined
  labelLabelledArg = undefined
  getClusterArg = undefined
  encodeBackendClusterArg = undefined
  combineBackendClusterArg = undefined
  defaultBA = undefined
  -- probably just never running anything here
  -- this is really just here because MakesILP is a superclass


instance (StaticClusterAnalysis op, EnvF (JustAccumulator op) ~ EnvF op) => StaticClusterAnalysis (JustAccumulator op) where
  newtype BackendClusterArg2 (JustAccumulator op) x y = BCA2JA (BackendClusterArg2 op x y)
  onOp a b c d   = coerce @(BackendArgs        op _ _) @(BackendArgs        (JustAccumulator op) _ _) $ onOp (coerce a) (coerce b) (coerce c) d
  def      x y z = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ def x y (coerce z)
  valueToIn    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ valueToIn $ coerce x
  valueToOut   x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ valueToOut $ coerce x
  inToValue    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ inToValue $ coerce x
  inToVar      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ inToVar $ coerce x
  outToValue   x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ outToValue $ coerce x
  outToSh      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ outToSh $ coerce x
  shToOut      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ shToOut $ coerce x
  shToValue    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ shToValue $ coerce x
  varToValue   x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ varToValue $ coerce x
  varToSh      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ varToSh $ coerce x
  outToVar     x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ outToVar $ coerce x
  shToVar      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ shToVar $ coerce x
  shrinkOrGrow a b x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ shrinkOrGrow a b $ coerce x
  addTup       x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ addTup $ coerce x
  unitToVar    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ unitToVar $ coerce x
  varToUnit    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ varToUnit $ coerce x
  pairinfo a x y = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ pairinfo a (coerce x) (coerce y)
  bcaid        x = coerce @(BackendClusterArg op _)    @(BackendClusterArg (JustAccumulator op) _)    $ bcaid $ coerce x
  

deriving instance (Eq (BackendClusterArg2 op x y)) => Eq (BackendClusterArg2 (JustAccumulator op) x y)
deriving instance (Show (BackendClusterArg2 op x y)) => Show (BackendClusterArg2 (JustAccumulator op) x y)
deriving instance (ShrinkArg (BackendClusterArg op)) => ShrinkArg (BackendClusterArg (JustAccumulator op))


toOnlyAcc :: Cluster op args -> Cluster (JustAccumulator op) args
toOnlyAcc (Fused f l r) = Fused f (toOnlyAcc l) (toOnlyAcc r)
toOnlyAcc (SingleOp (Single op opArgs) l) = SingleOp (Single (JA op) opArgs) l

pattern CJ :: f a -> Compose Maybe f a
pattern CJ x = Compose (Just x)
pattern CN :: Compose Maybe f a
pattern CN = Compose Nothing
{-# COMPLETE CJ,CN #-}

varsContainsThisShape :: Vars f x sh -> ShapeR sh' -> Maybe (sh :~: sh')
varsContainsThisShape vs shr
  | isAtDepth vs (rank shr) = unsafeCoerce $ Just Refl
  | otherwise = Nothing

-- Does this Vars contain exactly `x` variables, i.e., is `sh` `x`-dimensional?
isAtDepth :: Vars f x sh -> Int -> Bool
isAtDepth vs x = x == depth vs
  where
    depth :: Vars x y z -> Int
    depth TupRunit = 0
    depth (TupRpair l r) = depth l + depth r
    depth TupRsingle{} = 1

isAtDepth' :: ShapeR sh -> Int -> Bool
isAtDepth' vs x = x == rank vs


zeroes :: TypeR a -> Operands a
zeroes TupRunit = OP_Unit
zeroes (TupRpair l r) = OP_Pair (zeroes l) (zeroes r)
zeroes ty@(TupRsingle t) = case t of
  VectorScalarType _ -> error "todo"
  SingleScalarType (NumSingleType t) -> case t of
    IntegralNumType t -> case t of
      TypeInt    -> constant ty 0
      TypeInt8   -> constant ty 0
      TypeInt16  -> constant ty 0
      TypeInt32  -> constant ty 0
      TypeInt64  -> constant ty 0
      TypeWord   -> constant ty 0
      TypeWord8  -> constant ty 0
      TypeWord16 -> constant ty 0
      TypeWord32 -> constant ty 0
      TypeWord64 -> constant ty 0
    FloatingNumType t -> case t of
      TypeHalf   -> constant ty 0
      TypeFloat  -> constant ty 0
      TypeDouble -> constant ty 0

gvarsToShapeR :: Vars GroundR x sh -> ShapeR sh
gvarsToShapeR TupRunit = ShapeRz
gvarsToShapeR (TupRpair sh (TupRsingle x)) = case x of
  Var (GroundRscalar (SingleScalarType (NumSingleType (IntegralNumType TypeInt)))) _ -> ShapeRsnoc $ gvarsToShapeR sh
  _ -> error "not a shape"
gvarsToShapeR _ = error "not a shape"
