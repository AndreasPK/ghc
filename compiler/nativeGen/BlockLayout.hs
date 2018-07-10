{-# LANGUAGE TypeFamilies, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fprof-auto #-}

module BlockLayout
    ( sequenceTop )
where

import GhcPrelude

import Instruction
import NCGMonad
import CFG

import BlockId
import Cmm
import Hoopl.Collections
import Hoopl.Label
import Hoopl.Block

import UniqFM
import Util
import Unique

import Digraph
import Outputable
import Maybes

-- DEBUGGING ONLY
--import Debug
--import OrdList
--import Debug.Trace
import PprCmm ()

import Data.List
import Data.Foldable
import Hoopl.Graph

import qualified Data.Sequence as Seq
import qualified Data.Set as Set

dropJumps :: forall a i. Instruction i => LabelMap a -> [GenBasicBlock i]
          -> [GenBasicBlock i]
dropJumps _    [] = []
dropJumps info ((BasicBlock lbl ins):todo)
    | not . null $ ins
    , [dest] <- jumpDestsOfInstr (last ins)
    , ((BasicBlock nextLbl _) : _) <- todo
    , not (mapMember dest info)
    , nextLbl == dest
    = BasicBlock lbl (init ins) : dropJumps info todo
    | otherwise
    = BasicBlock lbl ins : dropJumps info todo


-- -----------------------------------------------------------------------------
-- Sequencing the basic blocks

-- Cmm BasicBlocks are self-contained entities: they always end in a
-- jump, either non-local or to another basic block in the same proc.
-- In this phase, we attempt to place the basic blocks in a sequence
-- such that as many of the local jumps as possible turn into
-- fallthroughs.

sequenceTop
    :: (Instruction instr, Outputable instr)
    => Bool --Use new layout code
    -> NcgImpl statics instr jumpDest -> CFG
    -> NatCmmDecl statics instr -> NatCmmDecl statics instr

sequenceTop _     _       _           top@(CmmData _ _) = top
--Use old algorithm
sequenceTop False ncgImpl edgeWeights
            (CmmProc info lbl live (ListGraph blocks)) =
  CmmProc info lbl live (ListGraph $ ncgMakeFarBranches ncgImpl info $
                         sequenceBlocks False edgeWeights info blocks)
sequenceTop True ncgImpl edgeWeights
            (CmmProc info lbl live (ListGraph blocks)) =
  CmmProc info lbl live (ListGraph $ ncgMakeFarBranches ncgImpl info $
                         sequenceBlocks False edgeWeights info blocks)



-- The algorithm is very simple (and stupid): we make a graph out of
-- the blocks where there is an edge from one block to another iff the
-- first block ends by jumping to the second.  Then we topologically
-- sort this graph.  Then traverse the list: for each block, we first
-- output the block, then if it has an out edge, we move the
-- destination of the out edge to the front of the list, and continue.

-- FYI, the classic layout for basic blocks uses postorder DFS; this
-- algorithm is implemented in Hoopl.

sequenceBlocks
        :: Instruction instr
        => Bool -> CFG -> LabelMap i
        -> [NatBasicBlock instr]
        -> [NatBasicBlock instr]

sequenceBlocks _ edgeWeights _ [] = []
sequenceBlocks useWeights edgeWeights infos (entry:blocks) =
    let entryNode = mkNode useWeights edgeWeights entry
        bodyNodes = reverse
                    (flattenSCCs (sccBlocks useWeights edgeWeights blocks))
        seqAlgo
          | useWeights = dropJumps infos . seqBlocks infos
          | otherwise = dropJumps infos . seqBlocksOld infos
    in seqAlgo ( entryNode : bodyNodes)
  -- the first block is the entry point ==> it must remain at the start.


sccBlocks
        :: Instruction instr
        => Bool -> CFG -> [NatBasicBlock instr]
        -> [SCC (Node BlockId (NatBasicBlock instr))]
sccBlocks useWeights edgeWeights blocks = stronglyConnCompFromEdgedVerticesUniqR (map (mkNode useWeights edgeWeights) blocks)

mkNode :: (Instruction t)
       => Bool -> CFG -> GenBasicBlock t
       -> Node BlockId (GenBasicBlock t)
mkNode useWeights edgeWeights block@(BasicBlock id instrs) =
    DigraphNode block id (getOutEdges instrs)
  where
    getOutEdges :: Instruction instr
                => [instr] -> [BlockId]
    getOutEdges instrs
      | useWeights
      = let targets = getOutgoingEdges edgeWeights id
      in case targets of
            [] -> []
            (target,weight):_ | length targets < 3 -> [target]
                              | otherwise -> []
    -- we're only interested in the last instruction of
    -- the block, and only if it has a single destination.
      | otherwise
      = case jumpDestsOfInstr (last instrs) of
            [one] -> [one]
            _many -> []

seqBlocks :: LabelMap i -> [Node BlockId (GenBasicBlock t1)]
                        -> [GenBasicBlock t1]
seqBlocks infos blocks = placeNext pullable0 todo0
  where
    -- pullable: Blocks that are not yet placed
    -- todo:     Original order of blocks, to be followed if we have no good
    --           reason not to;
    --           may include blocks that have already been placed, but then
    --           these are not in pullable
    pullable0 = listToUFM [ (i,(b,n)) | DigraphNode b i n <- blocks ]
    todo0     = map node_key blocks

    placeNext _ [] = []
    placeNext pullable (i:rest)
        | Just (block, pullable') <- lookupDeleteUFM pullable i
        = place pullable' rest block
        | otherwise
        -- We already placed this block, so ignore
        = placeNext pullable rest

    place pullable todo (block,[])
                          = block : placeNext pullable todo
    place pullable todo (block@(BasicBlock id instrs),[next])
        | Just (nextBlock, pullable') <- lookupDeleteUFM pullable next
        = BasicBlock id instrs : place pullable' todo nextBlock
        | otherwise
        = block : placeNext pullable todo
    place _ _ (_,tooManyNextNodes)
        = pprPanic "seqBlocks" (ppr tooManyNextNodes)

seqBlocksOld :: LabelMap i -> [Node BlockId (GenBasicBlock t1)]
                        -> [GenBasicBlock t1]
seqBlocksOld infos blocks = placeNext pullable0 todo0
  where
    -- pullable: Blocks that are not yet placed
    -- todo:     Original order of blocks, to be followed if we have no good
    --           reason not to;
    --           may include blocks that have already been placed, but then
    --           these are not in pullable
    pullable0 = listToUFM [ (i,(b,n)) | DigraphNode b i n <- blocks ]
    todo0     = map node_key blocks

    placeNext _ [] = []
    placeNext pullable (i:rest)
        | Just (block, pullable') <- lookupDeleteUFM pullable i
        = place pullable' rest block
        | otherwise
        -- We already placed this block, so ignore
        = placeNext pullable rest

    place pullable todo (block,[])
                          = block : placeNext pullable todo
    place pullable todo (block@(BasicBlock id instrs),[next])
        | mapMember next infos
        = block : placeNext pullable todo
        | Just (nextBlock, pullable') <- lookupDeleteUFM pullable next
        = BasicBlock id (init instrs) : place pullable' todo nextBlock
        | otherwise
        = block : placeNext pullable todo
    place _ _ (_,tooManyNextNodes)
        = pprPanic "seqBlocks" (ppr tooManyNextNodes)


lookupDeleteUFM :: Uniquable key => UniqFM elt -> key
                -> Maybe (elt, UniqFM elt)
lookupDeleteUFM m k = do -- Maybe monad
    v <- lookupUFM m k
    return (v, delFromUFM m k)
