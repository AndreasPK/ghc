{-# LANGUAGE TypeFamilies, ScopedTypeVariables #-}
-- {-# OPTIONS_GHC -fprof-auto #-}

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

-- | Size of a block before it no longer is inlined in a
--   triangle shaped control flow. See Note [Chain based CFG serialization]
maxTriangleSize :: Int
maxTriangleSize = 1

-- | Look at X number of blocks in two chains to determine
--   if they are "neighbours".
neighbourOverlapp :: Int
neighbourOverlapp = 2

-- | Only edges heavier than this are considered for neighbourhood checks.
minNeighbourPriority :: Int
minNeighbourPriority = 0

-- | Only edges heavier than this are considered
--   for combining into a single chain.
minChainLinkWeight :: Int
minChainLinkWeight = 0





-- | A non empty ordered sequence of basic blocks.
--   It is suitable for serialization in this order.
data BlockChain i
    = BlockChain
    { chainMembers :: LabelSet
    , chainBlocks :: (Seq.Seq (GenBasicBlock i))
    }

instance Eq (BlockChain i) where
    (BlockChain _ blks1) == (BlockChain _ blks2)
        = fmap blockId blks1 == fmap blockId blks2

--instance Ord (BlockChain i) where
--    (BlockChain lbls1 _) `compare` (BlockChain lbls2 _)
--        = lbls1 `compare` lbls2

instance Outputable (BlockChain i) where
    ppr (BlockChain _ blks) =
        parens (text "Chain:" <+> ppr (map blockId . toList $ blks) )

inFront :: BlockId -> BlockChain i -> Bool
inFront bid chain
  | BasicBlock lbl _ <- (Seq.index (chainBlocks chain) 0)
  = lbl == bid
  | otherwise = panic "Empty Chain"

atEnd :: BlockId -> BlockChain i -> Bool
atEnd bid chain
  | _ Seq.:> (BasicBlock lbl _) <- Seq.viewr (chainBlocks chain)
  = lbl == bid
  | otherwise = panic "empty chain"

--lastId :: BlockChain i -> BlockId
--lastId (BlockChain _ blks)
--  | _ Seq.:> (BasicBlock lbl _) <- Seq.viewr blks
--  = lbl

--firstId :: BlockChain i -> BlockId
--firstId (BlockChain _ blks)
--  | (BasicBlock lbl _) Seq.:< _ <- Seq.viewl blks
--  = lbl

chainMember :: BlockId -> BlockChain i -> Bool
chainMember bid chain
  = setMember bid . chainMembers $ chain

chainSingleton :: GenBasicBlock i -> BlockChain i
chainSingleton b@(BasicBlock lbl _)
    = BlockChain (setSingleton lbl) (Seq.singleton b)

chainCons :: forall i. GenBasicBlock i -> BlockChain i -> BlockChain i
chainCons blk@(BasicBlock lbl _) (BlockChain lbls blks)
  = BlockChain (setInsert lbl lbls) (blk Seq.<| blks)

chainSnoc :: forall i. BlockChain i -> GenBasicBlock i -> BlockChain i
chainSnoc (BlockChain lbls blks) blk@(BasicBlock lbl _)
  = BlockChain (setInsert lbl lbls) (blks Seq.|> blk)

chainConcat :: forall i. BlockChain i -> BlockChain i -> BlockChain i
chainConcat (BlockChain lbls1 blks1) (BlockChain lbls2 blks2)
  = BlockChain (setUnion lbls1 lbls2) (blks1 Seq.>< blks2)

chainToBlocks :: BlockChain i -> [GenBasicBlock i]
chainToBlocks (BlockChain _ blks) = toList blks

chainFromBlocks :: [GenBasicBlock i] -> BlockChain i
chainFromBlocks blocks
    = BlockChain (setFromList . map blockId $ blocks) (Seq.fromList blocks)

-- | Given the Chain A -> B -> C -> D and we break at C
--   we get the two Chains (A -> B, C -> D) as result.
breakChainAt :: forall i. BlockId -> BlockChain i
             -> (BlockChain i,BlockChain i)
breakChainAt bid (BlockChain lbls blks)
    | not (setMember bid lbls)
    = panic "Block not in chain"
    | otherwise
    = let (lblks, rblks) = Seq.breakl (\(BasicBlock lbl _) -> lbl == bid) blks
          --lblSet :: [GenBasicBlock i] -> BlockChain i
          lblSet blks =
            setFromList
                (map (\(BasicBlock lbl _) -> lbl) $ toList blks)
      in
      (BlockChain (lblSet lblks) lblks, BlockChain (lblSet rblks) rblks)

-- | Get the block following `bid` in the chain.
--chainSucc :: forall i. BlockId -> BlockChain i -> Maybe BlockId
--chainSucc bid (BlockChain _ blks)
--    = snd <$> (find ((==bid) . fst ) . zip blkList $ tail blkList)
--    where
--        blkList = map blockId . toList $ blks

-- | Get the block before `bid` in the chain.
chainPred :: forall i. BlockId -> BlockChain i -> Maybe BlockId
chainPred bid (BlockChain _ blks)
    = fst <$> (find ((==bid) . snd ) . zip blkList $ tail blkList)
    where
        blkList = map blockId . toList $ blks

takeR :: forall i. Int -> BlockChain i -> [GenBasicBlock i]
takeR n (BlockChain _ blks) =
    take n . toList . Seq.reverse $ blks

takeL :: forall i. Int -> BlockChain i -> [GenBasicBlock i]
takeL n (BlockChain _ blks) =
    take n . toList $ blks

-- | For a given list of chains try to combine chains with strong
--   edges between them into a single chain.
combineChains :: forall i. CFG -> CFG
              -> [BlockChain i] -> [BlockChain i]
combineChains weights _ chains
    = applyEdges prioEdges chains
    where
        applyEdges :: [(BlockId,BlockId,Int)] -> [BlockChain i]
                   -> [BlockChain i]
        applyEdges [] chains = chains
        applyEdges ((from,to,w):edges) chains
            | w <= minChainLinkWeight
            = chains
            | [c1,c2] <- candidates
            , atEnd from c1 && inFront to c2
            = applyEdges edges $ combine c1 c2 : rest
            | otherwise
            = applyEdges edges chains
          where
            combine c1 c2
              | atEnd from c1
              = chainConcat c1 c2
              | otherwise
              = chainConcat c2 c1
            (candidates,rest) =
                partition (\c -> chainMember from c || chainMember to c) chains
        prioEdges = sortOn (\(_,_,z) -> -z) $ edgeList weights

-- See also Note [Chain based CFG serialization]
-- We have the chains ABCD and EF.
-- There is a indirect link C->E between them.
--
-- So we want to place them next to each other even if we can't merge them.
--
--   A -> B -> C -> D
--             v
--             - -> E -> F ...
--
-- Simple heuristic:
--   * Check if the ends of a chain contain a edge if so merge them.
--   * Process edges in descending priority.

-- | For a given list of chains try to combine chains with strong
--   edges between them into a single chain.
combineNeighbourhood :: forall i. CFG -> [BlockChain i] -> [BlockChain i]
combineNeighbourhood weights chains
    = applyEdges prioEdges chains
    where
        prioEdges = sortOn (\(_,_,z) -> -z) $ edgeList weights

        applyEdges :: [(BlockId,BlockId,Int)] -> [BlockChain i]
                   -> [BlockChain i]
        applyEdges [] chains = chains
        applyEdges ((from,to,w):edges) chains
            | w <= minNeighbourPriority
            = chains

            | [c1,c2] <- candidates
            = applyEdges edges $ (combine c1 c2) : rest

            | otherwise
            = applyEdges edges chains
          where
            combine c1 c2
              | chainMember from c1
              = chainConcat c1 c2
              | otherwise
              = chainConcat c2 c1
              where
            (candidates,rest) =
                partition (\c -> atEnd from c || atBeginning to c) chains

            atBeginning bid c =
              chainMember bid c &&
              (elem bid . map blockId . takeL neighbourOverlapp $ c)
            atEnd bid c =
              chainMember bid c &&
              (elem bid . map blockId . takeR neighbourOverlapp $ c)

{-
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  ~~~ Note [Chain based CFG serialization]
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  We have a CFG with edge weights based on which we try to place blocks next to
  each other.

  Edge weights not only represent likelyhood of control transfer between blocks
  but also how much a block would benefit from being placed sequentially after
  it's predecessor.
  For example blocks which are preceeded by an info table are more likely to end
  up in a different cache line than their predecessor. So there is less benefit
  in placing them sequentially.

  For example consider this example:

  A:  ...
      jmp cond D (weak successor)
      jmp B
  B:  ...
      jmp C
  C:  ...
      jmp X
  D:  ...
      jmp B (weak successor)

  We determine a block layout by building up chunks (calling them chains) of
  possible control flows for which blocks will be placed sequentially.

  Eg for our example we might end up with two chains like:
  [A->B->C->X],[D]. Blocks inside chains will always be placed sequentially.
  However there is no particular order in which chains are placed since
  (hopefully) the blocks for which sequentially is important have already
  been placed in the same chain.

  -----------------------------------------------------------------------------
      First try to create a lists of good chains.
  -----------------------------------------------------------------------------

  We do so by taking a block not yet placed in a chain and
  looking at these cases:

  *)  (Evaluation) Triangle:
      The following subgraph is VERY common for generated code:
        A
        |\
        | B
        |/
        C

      This is a common result of:
        A: Check if an argument is evaluated.
        B: If not: Evaluate the argument.
        C: Do something with the argument.

      Usually B is a single instruction. A indirect jump to a register.
      So instead of moving B out of the way we want to keep it between A
      and C so we check for this special case.

      However we only apply this if B is a small block.

  *)  Check if the best predecessor of the block is at the end of a chain.
      If so add the current block to the end of that chain.

      Eg if we look at block C and already have the chain [A -> B]
      then we extend the chain to [A -> B -> C].

      Combined with the fact that we process blocks in reverse post order
      this means loop bodies often end up as a single chain.

  *)  Otherwise we create a singleton chain from the block we are looking at.
      Eg if we have [A->B] alread and look at D we create the chain [D].

  -----------------------------------------------------------------------------
      We then try to combine chains.
  -----------------------------------------------------------------------------

  There are edge cases which result in two chains being created which trivially
  represent linear control flow. For example [A,B,C] [D,E] with an cfg triangle:

      A----->C->D->E
       \->B-/

  For this reason we try to combine chains which follow each other.

  We do so by looking at the list of edges sorted by weight.
  Given the edge (C -> D) we try to find two chains such that:
      * C is at the end of chain one.
      * D is in front of chain two.
      * If two such chains exist we merge them.
  We then remove the edge and repeat the process for the rest of the edges.

  After having done so for all edges we serialize the cfg by placing the
  blocks in each chain in sequence, doing so for each chain.

  -----------------------------------------------------------------------------
      Place indirect successors (neighbours) after each other
  -----------------------------------------------------------------------------

  We might have chains [A,B,C,X],[E] in a CFG of the sort:

    A ---> B ---> C --------> X(exit)
                   \- ->E- -/

  While E does not follow X it's still beneficial to place them near each other.
  This can be advantageous if eg C,X,E will end up in the same cache line.

-}
buildChains :: forall a i. (Instruction i, Outputable i) => LabelMap a
            -> CFG -> CFG -> LabelMap (GenBasicBlock i)
            -> LabelSet -> [BlockChain i] -> [GenBasicBlock i]
            -> [BlockChain i]
buildChains _    _           _           _        _      chains [] = chains
buildChains info succWeights predWeights blockMap placed chains (block:todo)
  | setMember lbl placed
  = buildChains info succWeights predWeights blockMap placed chains todo
  | otherwise =
        let (newBlocks,chains') = findChain
        in  buildChains info succWeights predWeights blockMap
                (foldl' (flip setInsert) placed newBlocks)
                chains'
                todo
  where
    findChain :: ([BlockId],[BlockChain i])
    findChain
      --
      | Just (b,c) <- isTriangle
      , all (not . alreadyPlaced) [b,c]
      , Just (BasicBlock _ ins) <- mapLookup b blockMap
      , length ins < maxTriangleSize --label;any;jmp;
      = --pprTrace "Triangle" (ppr (lbl,b,c)) $
        ( [lbl,b,c]
        , ( chainFromBlocks .
            map (\b -> expectJust "block should exist" . mapLookup b $ blockMap) $
            [lbl,b,c]
          ):chains )
--{-
    -- B) place block at end of existing chain if
    -- there is no better block left to append.
      | (pred:_) <- preds
      , alreadyPlaced pred
      , ([predChain],chains') <- partition (atEnd pred) chains
      , (best:_) <- filter (not . alreadyPlaced) $ getSuccs pred
      , best == lbl
      , Just w <- getEdgeWeight pred lbl succWeights
      , w > 0
      = --pprTrace "B.2)" (ppr (pred,lbl)) $
        ( [lbl]
        , (chainSnoc predChain block) : chains')
---}
--{-
    -- C.1 current block replaces existing (worse) predecessor
      | (succ:_) <- succs
      , alreadyPlaced succ
      , ([succChain],rest) <- partition (chainMember succ) chains
      , Just pred <- chainPred succ succChain
      , linkWeight <- getEdgeWeight pred succ succWeights
      , newWeight <- getEdgeWeight lbl succ succWeights
      , linkWeight < newWeight
      , (lc, sc) <- breakChainAt succ succChain
      = --pprTrace "C.1)" (
        --    ppr (lbl,pred,succ) <+> ppr ((chainCons block sc) : lc : rest)) $
        ( [lbl]
        , (chainCons block sc) : lc : rest )
---}
      | otherwise
      = ([lbl], (chainSingleton block):chains)
        where
          alreadyPlaced blkId
            = (setMember blkId placed)

    isTriangle :: Maybe (BlockId,BlockId)
    isTriangle
      | [b,c] <- succs
      = case getEdgeWeight b c succWeights of
        Just _  -> Just (b,c)
        _       ->
            case getEdgeWeight c b succWeights of
                Just _ -> Just (c,b)
                _      -> Nothing
      | otherwise = Nothing

    BasicBlock lbl _ins = block
    getSuccs = map fst . getSortedEdges succWeights
    succs = map fst $ getSortedEdges succWeights lbl
    preds = map fst $ getSortedEdges predWeights lbl

-- We make the CFG a Hoopl Graph, so we can reuse revPostOrder.
newtype BlockNode i e x = BN (GenBasicBlock i,[BlockId])
instance NonLocal (BlockNode i) where
  entryLabel (BN (BasicBlock lbl _,_))   = lbl
  successors (BN (_,succs)) = succs

fromNode :: BlockNode i C C -> GenBasicBlock i
fromNode (BN x) = fst x

sequenceChain :: forall a i. (Instruction i, Outputable i) => LabelMap a -> CFG
            -> [GenBasicBlock i] -> [GenBasicBlock i]
sequenceChain _info _weights [] = []
sequenceChain _info _weights [x] = [x]
sequenceChain  info  weights blocks@((BasicBlock entry _):_) =
    let blockMap :: LabelMap (GenBasicBlock i)
        blockMap
            = foldl' (\m blk@(BasicBlock lbl _ins) ->
                        mapInsert lbl blk m)
                     mapEmpty blocks

        toNode :: GenBasicBlock i -> BlockNode i C C
        toNode x@(BasicBlock bid _) =
            -- sort such that heavier successors come first.
            BN (x,map fst . sortWith (snd) . getBlockTargets weights $ bid)

        orderedBlocks :: [GenBasicBlock i]
        orderedBlocks
            = --pprTraceIt "blockOrder" .
              map fromNode $
              revPostorderFrom (fmap toNode blockMap) entry

        --For efficiency we also create the map to look up predecessors here
        predWeights = reverseEdges weights

        chains
            = {-# SCC "buildChains" #-}
            --pprTraceIt "generatedChains" $
              buildChains
                info weights predWeights blockMap
                setEmpty [] orderedBlocks

        combinedChains
            = {-# SCC "combineChains" #-}
              --pprTraceIt "CombinedChains" $
              combineChains weights predWeights chains

        neighbourChains
            = {-# SCC "groupNeighbourChains" #-}
            --pprTraceIt "ResultChains" .
              combineNeighbourhood weights combinedChains

        ([entryChain],chains')
            = partition (chainMember entry) neighbourChains
        (entryChain':entryRest)
            | inFront entry entryChain = [entryChain]
            | (rest,entry) <- breakChainAt entry entryChain
            = [entry,rest]
            | otherwise = pprPanic "Entry point eliminated" $
                            ppr ([entryChain],chains')

        prepedChains
            = entryChain':(entryRest++chains')
        blockList
            = (concatMap chainToBlocks prepedChains)
    in  {-
        (   if (length blockList > 2)
                then pprTrace "combinedChains" (ppr prepedChains)
                else id)
        -}
        dropJumps info blockList




dropJumps :: forall a i. Instruction i => LabelMap a -> [GenBasicBlock i]
          -> [GenBasicBlock i]
dropJumps _    [] = []
dropJumps info ((BasicBlock lbl ins):todo)
    | [dest] <- jumpDestsOfInstr (last ins)
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
sequenceTop False ncgImpl _edgeWeights
            (CmmProc info lbl live (ListGraph blocks)) =
  CmmProc info lbl live (ListGraph $ ncgMakeFarBranches ncgImpl info $
                         sequenceBlocks info blocks)
--Use chain based algorithm
sequenceTop True ncgImpl edgeWeights
            (CmmProc info lbl live (ListGraph blocks)) =
  CmmProc info lbl live (ListGraph $ ncgMakeFarBranches ncgImpl info $
                         sequenceChain info edgeWeights blocks )


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
        => LabelMap i
        -> [NatBasicBlock instr]
        -> [NatBasicBlock instr]

sequenceBlocks _ [] = []
sequenceBlocks infos (entry:blocks) =
  seqBlocks infos (mkNode entry : reverse (flattenSCCs (sccBlocks blocks)))
  -- the first block is the entry point ==> it must remain at the start.


sccBlocks
        :: Instruction instr
        => [NatBasicBlock instr]
        -> [SCC (Node BlockId (NatBasicBlock instr))]

sccBlocks blocks = stronglyConnCompFromEdgedVerticesUniqR (map mkNode blocks)

-- we're only interested in the last instruction of
-- the block, and only if it has a single destination.
getOutEdges
        :: Instruction instr
        => [instr] -> [BlockId]

getOutEdges instrs
        = case jumpDestsOfInstr (last instrs) of
                [one] -> [one]
                _many -> []

mkNode :: (Instruction t)
       => GenBasicBlock t
       -> Node BlockId (GenBasicBlock t)
mkNode block@(BasicBlock id instrs) = DigraphNode block id (getOutEdges instrs)

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
