{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Monad
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Monad (

  CodeGen,
  codeGenFunction,
  liftCodeGen,

  -- codegen context
  getLLVMversion,

  -- declarations
  fresh, freshLocalName, freshGlobalName,
  declareGlobalVar,
  declareExternFunc,
  typedef,
  intrinsic,

  -- basic blocks
  Block,
  newBlock, newBlockNamed, setBlock, getBlock, beginBlock, createBlocks,

  -- instructions
  instr, instr', instrMD, instrMD', do_, return_, retval_, br, cbr, cbrMD, switch,
  phi, phi', phi1, hoistAlloca,
  instr_,

  -- metadata
  addNamedMetadata, addMetadata,

) where

import Data.Array.Accelerate.Error
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Intrinsic
import Data.Array.Accelerate.LLVM.State                             ( LLVM )
import Data.Array.Accelerate.LLVM.Target
import Data.Array.Accelerate.Representation.Tag
import Data.Array.Accelerate.Representation.Type
import qualified Data.Array.Accelerate.Debug.Internal               as Debug
import Data.Array.Accelerate.LLVM.Compile.Cache                     ( UID )

import LLVM.AST.Type.Constant
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Metadata
import LLVM.AST.Type.Module
import LLVM.AST.Type.Function
import LLVM.AST.Type.Global
import LLVM.AST.Type.Name
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation
import LLVM.AST.Type.Terminator
import qualified Text.LLVM                                          as LP
import qualified Text.LLVM.PP                                       as LP
import qualified Text.LLVM.Triple.Parse                             as LP

import Control.Applicative
import Control.Monad
import Control.Monad.Reader                                         ( ReaderT, MonadReader, runReaderT, ask, asks )
import Control.Monad.State
import Data.ByteString.Short                                        ( ShortByteString )
import qualified Data.ByteString.Short.Char8                        as SBS8
import Data.Function
import Data.HashMap.Strict                                          ( HashMap )
import Data.Sequence                                                ( Seq )
import Data.String
import Data.Text.Lazy.Builder                                       ( Builder )
import Formatting
import Prelude
import qualified Data.Foldable                                      as F
import qualified Data.HashMap.Strict                                as HashMap
import qualified Data.Map.Strict                                    as Map
import qualified Data.Sequence                                      as Seq
import qualified Data.ByteString.Short                              as B
import qualified Debug.Trace


-- Code generation
-- ===============

-- | The code generation state for scalar functions and expressions.
--
-- We use two records: one to hold all the code generation state as it walks the
-- AST, and one for each of the basic blocks that are generated during the walk.
--
data CodeGenState = CodeGenState
  { blockChain          :: Seq Block                                      -- blocks for this function
  , globalvarTable      :: HashMap Label LP.Global                        -- global variable definitions
  , fundeclTable        :: HashMap Label LP.Declare                       -- global (external) function declarations
  , typedefTable        :: HashMap Label LP.Type                          -- global type definitions
  , namedMetadataTable  :: HashMap ShortByteString (Seq [Maybe Metadata]) -- module metadata to be collected
  , metadataTable       :: Seq [Maybe Metadata]                           -- module metadata with numbers as keys
  , intrinsicTable      :: HashMap ShortByteString Label                  -- standard math intrinsic functions
  , local               :: {-# UNPACK #-} !Word                           -- a name supply
  , global              :: {-# UNPACK #-} !Word                           -- a name supply for global variables
  , allocaIndex         :: {-# UNPACK #-} !Word                           -- a name supply for hoisted allocas
  , blocksAllocated     :: Int                                            -- number of blocks generated
  }

data Block = Block
  { blockLabel          :: {-# UNPACK #-} !Label -- block label
  , instructions        :: Seq LP.Stmt           -- stack of instructions
  , terminator          :: LP.Stmt               -- block terminator
  }
instance Show Block where
  show (Block l i _) = "Block " <> show l <> "instructions: {" <> show i <> "}"

-- | Code generation context: read-only additional context of the compilation.
--
-- This contains the LLVM version.
data CodeGenContext = CodeGenContext
  { codegenLLVMversion :: LP.LLVMVer }

newtype CodeGen target a = CodeGen
  { runCodeGen :: ReaderT CodeGenContext (StateT CodeGenState (LLVM target)) a }
  deriving (Functor, Applicative, Monad, MonadReader CodeGenContext, MonadState CodeGenState)

liftCodeGen :: LLVM arch a -> CodeGen arch a
liftCodeGen = CodeGen . lift . lift

getLLVMversion :: CodeGen arch LP.LLVMVer
getLLVMversion = asks codegenLLVMversion

codeGenFunction
  :: forall arch f t a. (HasCallStack, Target arch, Intrinsic arch, Result f ~ t, Result t ~ t)
  => String
  -> Type t
  -> (GlobalFunctionDefinition t -> GlobalFunctionDefinition f)
  -> CodeGen arch a
  -> LLVM arch (a, Module f)
codeGenFunction name returnTp bind body = do
  llvmver <- ask
  let context = CodeGenContext
        { codegenLLVMversion = llvmver }
  -- Execute the CodeGen monad and retrieve the code of the function and final state.
  ((a, code), st) <- runStateT
    ( runReaderT
      ( runCodeGen $ do
        -- For tracy, we should emit this:
        -- zone <- zone_begin_alloc 0 [] (S8.unpack sbs) [] 0
        a <- body
        -- _    <- zone_end zone
        blocks <- createBlocks
        pure (a, blocks)
      )
      context
    )
    $ CodeGenState
        { blockChain         = initBlockChain
        , globalvarTable     = HashMap.empty
        , fundeclTable       = HashMap.empty
        , typedefTable       = HashMap.empty
        , namedMetadataTable = HashMap.empty
        , metadataTable      = Seq.Empty
        , intrinsicTable     = intrinsicForTarget @arch
        , local              = 0
        , global             = 0
        , allocaIndex        = 0
        , blocksAllocated    = 0
        }

  let
    typeDefs = map (\(n,t) -> LP.TypeDecl (labelToPrettyI n) t) $ HashMap.toList $ typedefTable st
    globals = HashMap.elems (globalvarTable st)
    declares = HashMap.elems (fundeclTable st)
    
    unnamedMd1 = createMetadata (metadataTable st)
    (namedMd, unnamedMd2) = createNamedMetadata (length $ metadataTable st) (namedMetadataTable st)

  return 
    ( a
    , Module
      { moduleName             = name
      , moduleDataLayout       = [] -- TODO: Something with targetDataLayout @arch; this will be important for PTX
      , moduleTargetTriple     = case targetTriple @arch of
          Just s -> LP.parseTriple (SBS8.unpack s)
          Nothing -> error "TODO: module target triple"
      , moduleMain             = bind $ Body returnTp Nothing (GlobalFunctionBody (Label $ fromString name) code)
      , moduleTypes            = typeDefs
      , moduleGlobals          = globals
      , moduleDeclares         = declares
      , moduleNamedMd          = namedMd
      , moduleUnnamedMd        = (unnamedMd1 ++ unnamedMd2)
      }
    )

-- Basic Blocks
-- ============

-- | An initial block chain
--
initBlockChain :: HasCallStack => Seq Block
initBlockChain
  = Seq.singleton
  $ Block "entry" Seq.empty (internalError "block has no terminator")


-- | Create a new basic block, but don't yet add it to the block chain. You need
-- to call 'setBlock' to append it to the chain, so that subsequent instructions
-- are added to this block.
--
-- Note: [Basic blocks]
--
-- The names of basic blocks are generated based on the base name provided to
-- the 'newBlock' function, as well as the current state (length) of the block
-- stream. By not immediately adding new blocks to the stream, we have the
-- advantage that:
--
--   1. Instructions are generated "in order", and are always appended to the
--      stream. There is no need to search the stream for a block of the right
--      name.
--
--   2. Blocks are named in groups, which helps readability. For example, the
--      blocks for the then and else branches of a conditional, created at the
--      same time, will be named similarly: 'if4.then' and 'if4.else', etc.
--
-- However, this leads to a slight awkwardness when walking the AST. Since a new
-- naming group scheme is only applied *after* a call to 'setBlock',
-- encountering (say) nested conditionals in the walk will generate logically
-- distinct blocks that happen to have the same name. This means that
-- instructions might be added to the wrong blocks, or the first set of blocks
-- will be emitted empty and/or without a terminator.
--
-- To fix this, we now use the 'blocksAllocated' counter rather than the size of the chain
--
newBlock :: HasCallStack => String -> CodeGen arch Block
newBlock nm =
  state $ \s ->
    let idx     = blocksAllocated s
        label   = let (h,t) = break (== '.') nm in (h ++ shows idx t)
        next    = Block (fromString label) Seq.empty err
        err     = internalError ("block `" % string % "' has no terminator") label
    in
    ( next, s { blocksAllocated = 1 + idx } )

-- Variant of newBlock, where the caller should assure that the name is unique
newBlockNamed :: HasCallStack => String -> Block
newBlockNamed label = Block (fromString label) Seq.empty err
  where
    err = internalError ("block `" % string % "' has no terminator") label

-- | Add this block to the block stream. Any instructions pushed onto the stream
-- by 'instr' and friends will now apply to this block.
--
setBlock :: Block -> CodeGen arch ()
setBlock next =
  modify $ \s -> s { blockChain = blockChain s Seq.|> next }

getBlock :: CodeGen arch Block
getBlock = state $ \s -> case Seq.viewr (blockChain s) of
  Seq.EmptyR -> internalError "empty block chain"
  _ Seq.:> b -> ( b, s )

-- | Generate a new block and branch unconditionally to it.
--
beginBlock :: HasCallStack => String -> CodeGen arch Block
beginBlock nm = do
  next <- newBlock nm
  _    <- br next
  setBlock next
  return next


-- | Extract the block state and construct the basic blocks that form a function
-- body. The block stream is re-initialised, but module-level state such as the
-- global symbol table is left intact.
--
createBlocks :: HasCallStack => CodeGen arch [LP.BasicBlock]
createBlocks
  = state
  $ \s -> let s'     = s { blockChain = initBlockChain, local = 0 }
              blocks = makeBlock `fmap` blockChain s
              m      = Seq.length (blockChain s)
              n      = F.foldl' (\i b -> i + Seq.length (instructions b)) 0 (blockChain s)
          in
          trace (bformat ("generated " % int % " instructions in " % int % " blocks") (n+m) m) ( F.toList blocks , s' )
  where
    makeBlock Block{..} =
      LP.BasicBlock (Just (labelToPrettyBL blockLabel)) (F.toList instructions ++ [terminator])


-- Instructions
-- ------------

-- | Generate a fresh local reference
--
fresh :: TypeR a -> CodeGen arch (Operands a)
fresh TupRunit         = return OP_Unit
fresh (TupRpair t2 t1) = OP_Pair <$> fresh t2 <*> fresh t1
fresh (TupRsingle t)   = ir t . LocalReference (PrimType (ScalarPrimType t)) <$> freshLocalName

-- | Generate a fresh local (un)name
--
freshLocalName :: CodeGen arch (Name a)
freshLocalName = state $ \s@CodeGenState{..} -> ( UnName local, s { local = local + 1 } )

-- | Generate a fresh global (un)name
--
freshGlobalName :: CodeGen arch (Name a)
freshGlobalName = state $ \s@CodeGenState{..} -> ( UnName global, s { global = global + 1 } )

-- | Generate a fresh local name for a hoisted alloca
--
freshAllocaName :: CodeGen arch (Name a)
freshAllocaName = state $ \s@CodeGenState{..} -> ( Name $ fromString $ "alloca." ++ show allocaIndex, s { allocaIndex = allocaIndex + 1 } )

-- | Add an instruction to the state of the currently active block so that it is
-- computed, and return the operand (LocalReference) that can be used to later
-- refer to it.
--
instr :: HasCallStack => Instruction a -> CodeGen arch (Operands a)
instr ins = ir (typeOf ins) <$> instr' ins

instr' :: HasCallStack => Instruction a -> CodeGen arch (Operand a)
instr' ins = instrMD' ins []

-- | The MD variants of instr and instr' also take metadata of the instruction.
instrMD :: HasCallStack => Instruction a -> InstructionMetadata -> CodeGen arch (Operands a)
instrMD ins md = ir (typeOf ins) <$> instrMD' ins md

instrMD' :: HasCallStack => Instruction a -> InstructionMetadata -> CodeGen arch (Operand a)
instrMD' ins md =
  -- LLVM-5 does not allow instructions of type void to have a name.
  case typeOf ins of
    VoidType -> do
      instr_ $ LP.Effect (downcast ins) (downcastInstructionMetadata md)
      return $ LocalReference VoidType (Name B.empty)
    --
    ty -> do
      name <- freshLocalName
      instr_ $ LP.Result (nameToPrettyI name) (downcast ins) (downcastInstructionMetadata md)
      return $ LocalReference ty name

-- | Execute an unnamed instruction
--
do_ :: HasCallStack => Instruction () -> CodeGen arch ()
do_ ins = instr_ $ LP.Effect (downcast ins) []

-- | Add raw assembly instructions to the execution stream
--
instr_ :: HasCallStack => LP.Stmt -> CodeGen arch ()
instr_ ins =
  modify $ \s ->
    case Seq.viewr (blockChain s) of
      Seq.EmptyR  -> internalError "empty block chain"
      bs Seq.:> b -> s { blockChain = bs Seq.|> b { instructions = instructions b Seq.|> ins } }


-- | Return void from a basic block
--
return_ :: HasCallStack => CodeGen arch ()
return_ = void $ terminate Ret

-- | Return a value from a basic block
--
retval_ :: HasCallStack => Operand a -> CodeGen arch ()
retval_ x = void $ terminate (RetVal x)


-- | Unconditional branch. Return the name of the block that was branched from.
--
br :: HasCallStack => Block -> CodeGen arch Block
br target = terminate $ Br (blockLabel target)


-- | Conditional branch. Return the name of the block that was branched from.
--
cbr :: HasCallStack => Operands Bool -> Block -> Block -> CodeGen arch Block
cbr (OP_Bool cond) t f = terminate $ CondBr cond (blockLabel t) (blockLabel f)

cbrMD :: HasCallStack => Operands Bool -> Block -> Block -> InstructionMetadata -> CodeGen arch Block
cbrMD (OP_Bool cond) t f md = terminateMD (CondBr cond (blockLabel t) (blockLabel f)) md

-- | Switch statement. Return the name of the block that was branched from.
--
switch :: forall arch tag. (HasCallStack, IsIntegral tag) => Operands tag -> Block -> [(tag, Block)] -> CodeGen arch Block
switch tag def eqs = terminate $ Switch (op tp tag) (blockLabel def) [(ScalarConstant tp t, blockLabel b) | (t,b) <- eqs]
  where
    tp :: ScalarType tag
    tp = SingleScalarType $ NumSingleType $ IntegralNumType integralType

-- | Add a phi node to the top of the current block
--
phi :: forall arch a. HasCallStack => TypeR a -> [(Operands a, Block)] -> CodeGen arch (Operands a)
phi tp incoming = do
  crit  <- fresh tp
  block <- getBlock
  phi' tp block crit incoming

phi' :: HasCallStack => TypeR a -> Block -> Operands a -> [(Operands a, Block)] -> CodeGen arch (Operands a)
phi' tp target = go tp
  where
    go :: TypeR t -> Operands t -> [(Operands t, Block)] -> CodeGen arch (Operands t)
    go TupRunit OP_Unit _
      = return OP_Unit
    go (TupRpair t2 t1) (OP_Pair n2 n1) inc
      = OP_Pair <$> go t2 n2 [ (x, b) | (OP_Pair x _, b) <- inc ]
                <*> go t1 n1 [ (y, b) | (OP_Pair _ y, b) <- inc ]
    go (TupRsingle t) tup inc
      | LocalReference _ v <- op t tup = ir t <$> phi1 target v [ (op t x, b) | (x, b) <- inc ]
      | otherwise                      = internalError "expected critical variable to be local reference"


phi1 :: HasCallStack => Block -> Name a -> [(Operand a, Block)] -> CodeGen arch (Operand a)
phi1 target crit incoming =
  let cmp       = (==) `on` blockLabel
      update b  = b { instructions = LP.Result (nameToPrettyI crit) (downcast $ Phi t [ (p,blockLabel) | (p,Block{..}) <- incoming ]) [] Seq.<| instructions b }
      t         = case incoming of
                    []        -> internalError "no incoming values specified"
                    (o,_):_   -> case typeOf o of
                                   VoidType    -> internalError "operand has void type"
                                   PrimType x  -> x
  in
  state $ \s ->
    case Seq.findIndexR (cmp target) (blockChain s) of
      Nothing -> internalError "unknown basic block"
      Just i  -> ( LocalReference (PrimType t) crit
                 , s { blockChain = Seq.adjust update i (blockChain s) } )

hoistAlloca :: PrimType t -> CodeGen arch (Operand (Ptr t))
hoistAlloca tp = do
  name <- freshAllocaName
  let update = \b -> b { instructions =
    (LP.Result (nameToPrettyI name) (downcast $ Alloca tp) []) Seq.<| instructions b }

  state $ \s ->
    case Seq.findIndexR (\b -> blockLabel b == "entry") (blockChain s) of
      Nothing -> internalError "could not find entry block"
      Just i  -> ( LocalReference (PrimType $ PtrPrimType tp defaultAddrSpace) name
                 , s { blockChain = Seq.adjust update i (blockChain s) } )

-- | Add a termination condition to the current instruction stream. Also return
-- the block that was just terminated.
--
terminate :: HasCallStack => Terminator a -> CodeGen arch Block
terminate term = terminateMD term []

terminateMD :: HasCallStack => Terminator a -> InstructionMetadata -> CodeGen arch Block
terminateMD term md =
  state $ \s ->
    case Seq.viewr (blockChain s) of
      Seq.EmptyR  -> internalError "empty block chain"
      bs Seq.:> b -> ( b, s { blockChain = bs Seq.|> b { terminator = LP.Effect (downcast term) (downcastInstructionMetadata md) } } )

-- | Add a global variable declaration to the module
--
declareGlobalVar :: HasCallStack => LP.Global -> CodeGen arch ()
declareGlobalVar g =
  let unique (Just q) | g /= q    = internalError "duplicate symbol"
                      | otherwise = Just g
      unique _                    = Just g

      name = case LP.globalSym g of
               LP.Symbol n -> Label (fromString n)
  in
  modify (\s -> s { globalvarTable = HashMap.alter unique name (globalvarTable s) })


-- | Add an external function declaration to the module
--
declareExternFunc :: HasCallStack => LP.Declare -> CodeGen arch ()
declareExternFunc g =
  let unique (Just q) | g /= q    = internalError "duplicate symbol"
                      | otherwise = Just g
      unique _                    = Just g

      name = case LP.decName g of
               LP.Symbol n -> Label (fromString n)
  in
  modify (\s -> s { fundeclTable = HashMap.alter unique name (fundeclTable s) })


-- | Add a global type definition
--
typedef :: HasCallStack => Label -> LP.Type -> CodeGen arch ()
typedef name t =
  let unique (Just s) | t /= s    = internalError "duplicate typedef"
                      | otherwise = Just t
      unique _                    = Just t
  in
  modify (\s -> s { typedefTable = HashMap.alter unique name (typedefTable s) })


-- | Get name of the corresponding intrinsic function implementing a given C
-- function. If there is no mapping, the C function name is used.
--
intrinsic :: ShortByteString -> CodeGen arch Label
intrinsic key =
  state $ \s ->
    let name = HashMap.lookupDefault (Label key) key (intrinsicTable s)
    in  (name, s)



-- Metadata
-- ========

-- | Insert a metadata key/value pair into the current module.
--
addNamedMetadata :: ShortByteString -> [Maybe Metadata] -> CodeGen arch ()
addNamedMetadata key val =
  modify $ \s ->
    s { namedMetadataTable = HashMap.insertWith (flip (Seq.><)) key (Seq.singleton val) (namedMetadataTable s) }

addMetadata :: (MetadataNodeID -> [Maybe Metadata]) -> CodeGen arch MetadataNodeID
addMetadata val =
  state $ \s ->
    let index = fromIntegral $ Seq.length $ metadataTable s
    in (index, s{ metadataTable = metadataTable s Seq.:|> val index })


-- | Generate the metadata definitions for the file. Every key in the map
-- represents a named metadata definition. The values associated with that key
-- represent the metadata node definitions that will be attached to that
-- definition.
--
createNamedMetadata :: Int -> HashMap ShortByteString (Seq [Maybe Metadata]) -> ([LP.NamedMd], [LP.UnnamedMd])
createNamedMetadata offset md = go (HashMap.toList md) (Seq.empty, Seq.empty)
  where
    go :: [(ShortByteString, Seq [Maybe Metadata])]
       -> (Seq LP.NamedMd, Seq LP.UnnamedMd) -- accumulator of (names, metadata)
       -> ([LP.NamedMd], [LP.UnnamedMd])
    go []     (k,d) = (F.toList k, F.toList d)
    go (x:xs) (k,d) =
      let (k',d') = meta (offset + Seq.length d) x
      in  go xs (k Seq.|> k', d Seq.>< d')

    meta :: Int                                         -- number of metadata node definitions so far
         -> (ShortByteString, Seq [Maybe Metadata])     -- current assoc of the metadata map
         -> (LP.NamedMd, Seq LP.UnnamedMd)
    meta n (key, vals)
      = let node i      = i + n
            nodes       = Seq.mapWithIndex (\i x -> LP.UnnamedMd (node i) (LP.ValMdNode (downcast (F.toList x))) False) vals
            name        = LP.NamedMd (SBS8.unpack key) [ node i | i <- [0 .. Seq.length vals - 1] ]
        in
        (name, nodes)

createMetadata :: Seq [Maybe Metadata] -> [LP.UnnamedMd]
createMetadata md = zipWith convert [0..] $ F.toList md
  where
    convert :: Int -> [Maybe Metadata] -> LP.UnnamedMd
    -- TODO: Currently we never mark metadata as distinct,
    -- should we allow marking it as distinct?
    convert idx vals = LP.UnnamedMd idx (downcast vals) False


-- Debug
-- =====

{-# INLINE trace #-}
trace :: Builder -> a -> a
trace msg = Debug.trace Debug.dump_cc ("llvm: " <> msg)

