{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Foreign
-- Copyright   : [2016..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Foreign
  where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Lowering
import Data.Array.Accelerate.Trafo.Operation.Substitution
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Sugar.Foreign                          as A

import Data.Array.Accelerate.LLVM.CodeGen.Sugar

-- | Interface for backends to provide foreign function implementations for
-- scalar expressions.
--
-- FFI for array computation operates via mkForeign in type class LowerAcc.
--
class CompileForeignExp arch where
  foreignExp :: A.Foreign asm
             => asm (x -> y)
             -> Maybe (IRFun1 arch (x -> y))
  foreignExp _ = Nothing

-- | Call a foreign function that takes one input array and produces one output
-- array of the same size.
foreignCallMaplike
  :: ShapeR sh
  -> TypeR e
  -> TypeR e'
  -> IsFusible b
  -> op b (In sh e -> Out sh e' -> ())
  -> GroundVars env (LoweredArrays (Array sh e))
  -> OperationAcc op env (LoweredArrays (Array sh e'))
foreignCallMaplike shr tpIn tpOut fusible op = \case
  sh `TupRpair` buffersIn
    | DeclareVars lhs k value <- declareVars $ buffersR tpOut
    , buffersOut <- value weakenId
    , sh' <- mapTupR (weaken k) sh
    , buffersIn' <- mapTupR (weaken k) buffersIn ->
      aletUnique lhs (lowerAlloc (ArrayR shr tpOut) $ groundToExpVar (shapeType shr) sh) $
        Alet LeftHandSideUnit TupRunit (Exec (ExecOp fusible op) $
          ArgArray In (ArrayR shr tpIn) sh' buffersIn'
          :>: ArgArray Out (ArrayR shr tpOut) sh' buffersOut
          :>: ArgsNil)
        $ Return $ TupRpair sh' buffersOut
  TupRsingle v -> pairImpossible $ varType v
