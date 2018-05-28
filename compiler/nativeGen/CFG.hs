{-# LANGUAGE TypeFamilies, ScopedTypeVariables #-}
-- {-# OPTIONS_GHC -fprof-auto #-}

module CFG
    ( CFG, CfgEdge, addWeightEdge, delEdge, edgeList
    , shortcutWeightMap, getBlockTargets, addImmediateSuccessor
    , getEdgeWeight, getSortedEdges, reverseEdges
    , getCFG, addNodeBetween, pprEdgeWeights, getCfgNodes, sanityCheckCfg )
where

import GhcPrelude

import BlockId
import Cmm
import CmmUtils
import CmmSwitch
import Hoopl.Collections
import Hoopl.Label
import Hoopl.Block

import Util

import Outputable
-- DEBUGGING ONLY
--import Debug
--import OrdList
--import Debug.Trace
import PprCmm ()

import Data.List
import Hoopl.Graph

import qualified Data.Map.Strict as M



type CfgEdge = (BlockId, BlockId, Maybe Int)
type EdgeWeightMap edgeInfo = M.Map Label (M.Map Label edgeInfo)
type CFG = EdgeWeightMap (Int)

getCfgNodes :: CFG -> [BlockId]
getCfgNodes m = M.keys m ++ concat (M.elems . M.map M.keys $ m)

-- | Check if the nodes in the cfg and the list of labels match up.
sanityCheckCfg :: CFG -> [BlockId] -> SDoc -> Bool
sanityCheckCfg m blocks msg
    | setNull diff = True
    | otherwise =
        pprPanic "Block list and cfg nodes don't match" (
            text "difference:" <+> ppr diff $$
            text "blocks:" <+> ppr blocks $$
            text "cfg:" <+> ppr m $$
            msg )
            False
    where
      cfgNodes = setFromList $ getCfgNodes m :: LabelSet
      blockSet = setFromList blocks :: LabelSet
      diff = setDifference cfgNodes blockSet :: LabelSet




--If we shortcut to a non-block we simply remove the edge.
--It's not perfect but works for most cases. I'm only aware
--of that happening without tables_next_to_code anyway.

{-
During shortcutting if we shortcut A -> B -> C to A -> C:
* We delete A -> B and B -> C
* We add A -> C

This means for each entry B -> C we delete the edge.
For each entry A -> B we map B to C.

B -> C can't have had a interesting weight since
it's a single jmp ins in a block.

We preserve the weight from A -> B so that's fine too.

If we shortcut to a immediate (Nothing):
    A -> B => A -> IMM 
we remove the edge A -> B. We can also delete the node B
as all jumps to it will be replaced by jumps to the immediate.

See Note [What is shortcutting] in the control flow optimization
for a explanation on shortcutting.
-}
shortcutWeightMap :: CFG -> LabelMap (Maybe BlockId) -> CFG
shortcutWeightMap m cuts =
  foldl' applyMapping m $ mapToList cuts
    where     -- B -> C
      applyMapping :: CFG -> (BlockId,Maybe BlockId) -> CFG
      applyMapping m (from, Nothing) =
        M.delete from . 
        fmap (M.delete from) $ m
      applyMapping m (from, Just to) =
        let updatedMap
              = fmap (M.mapKeys (updateKey (from,to))) $
                M.delete from m
        in case mapLookup to cuts of
            Nothing -> updatedMap
            Just dest -> applyMapping updatedMap (to, dest)
      updateKey :: (BlockId, BlockId) -> BlockId -> BlockId
      updateKey (from, to) k
        | k == from = to
        | otherwise = k

-- | Sometimes we insert a block which should unconditionally be executed
--   after a given block. This function updates the CFG for these cases.
addImmediateSuccessor :: BlockId -> BlockId -> CFG -> CFG
addImmediateSuccessor node follower m
    = updateEdges . addWeightEdge node follower 100 $ m
    where
        successors = map fst targets :: [BlockId]
        targets = getBlockTargets m node
        updateEdges = addNewSuccs . remOldSuccs
        remOldSuccs m = foldl' (flip (delEdge node)) m successors
        addNewSuccs m = foldl' (\m (t,w) -> addWeightEdge follower t w m) m targets

addWeightEdge :: BlockId -> BlockId -> Int -> CFG -> CFG
addWeightEdge from to weight m =
    M.alter addDest from m
    where
        addDest Nothing = Just $ M.singleton to weight
        addDest (Just wm) = Just $ M.insert to weight wm

delEdge :: BlockId -> BlockId -> CFG -> CFG
delEdge from to m =
    M.alter remDest from m
    where
        remDest Nothing = Nothing
        remDest (Just wm) = Just $ M.delete to wm

-- | Destinations from bid ordered by weight
getSortedEdges :: CFG -> BlockId -> [(Label,Int)]
getSortedEdges m bid =
    let destMap = M.findWithDefault M.empty bid m
        edges = M.toList destMap
        sortedEdges = sortWith (negate . snd) edges
    in  --pprTrace "getSortedEdges" (ppr bid <+> text "map:" <+> ppr m)
        sortedEdges

getEdgeWeight :: BlockId -> BlockId -> CFG -> Maybe Int
getEdgeWeight from to m
    | Just wm <- M.lookup from m
    , Just w <- M.lookup to wm
    = Just w
    | otherwise
    = Nothing

reverseEdges :: CFG -> CFG
reverseEdges m = foldr add M.empty flatElems
    where
        elems = M.toList $ fmap M.toList m :: [(BlockId,[(BlockId,Int)])]
        flatElems =
            concatMap (\(from,ws) -> map (\(to,w) -> (to,from,w)) ws ) elems
        add (to,from,w) m = addWeightEdge to from w m

edgeList :: CFG -> [(BlockId,BlockId,Int)]
edgeList m =
    let lists = M.toList $ fmap M.toList m
    in concatMap
        (\(from, tos) -> map (\(to,weight) -> (from,to,weight)) tos )
        lists

getBlockTargets :: CFG -> BlockId -> [(BlockId,Int)]
getBlockTargets m bid
    | Just wm <- M.lookup bid m
    = M.toList wm
    | otherwise = []

pprEdgeWeights :: CFG -> SDoc
pprEdgeWeights m =
    let edges = sortOn (\(_,_,z) -> z) $ edgeList m
        printEdge (from,to,weight)
            = text "\t" <> ppr from <+> text "->" <+> ppr to <>
              text "[label=\"" <> ppr weight <> text "\",weight=\"" <>
              ppr weight <> text "\"];\n"
        --for the case that there are no edges from/to this node.
        printNode node
            = text "\t" <> ppr node <> text ";\n"
    in
    text "digraph {\n" <>
        (foldl' (<>) empty (map printEdge edges)) <>
        (foldl' (<>) empty (map printNode $ M.keys m)) <>
    text "}\n"


-- | Update entries based of info:
--   (A,B,C)
--   A -> C: Old arc
--   A -> B -> C : New Arc
-- It's possible that a block generates two arcs in the assembly code.
-- We ignore that edge case but give some info info if it leads to issues.
addNodeBetween :: CFG -> [(BlockId,BlockId,BlockId)] -> CFG
addNodeBetween m updates =
  -- Nub
  foldl' updateWeight m $ ordNub weightedUpdates
    where
      -- We might add two edges A -> B -> C, A -> D -> C
      -- in this case after applying the first update the weight
      -- is no longer available. So we calculate future weights before updates.
      weightedUpdates = map getWeight updates
      getWeight :: (BlockId,BlockId,BlockId) -> (BlockId,BlockId,BlockId,Int)
      getWeight (from,between,old)
        | Just w <- getEdgeWeight from old m
        = (from,between,old,w)
        | otherwise
        = pprTraceDebug "Can't find weight for edge that should have one" (
            text "triple" <+> ppr (from,between,old) $$
            text "updates" <+> ppr updates )
            (from,between,old, 0)
      updateWeight m (from,between,old,w)
        = addWeightEdge from between w $
          addWeightEdge between old w $
          delEdge from old m

-- | Generate weights for a Cmm proc based on some simple heuristics.
getCFG :: RawCmmDecl -> CFG
getCFG (CmmData {}) = M.empty
getCFG (CmmProc info _lab _live graph) =
  foldl' insertEdge nodes $ concatMap weightedEdges blocks
  where
    nodes = M.fromList $ zip (map entryLabel blocks) (repeat M.empty)
    insertEdge :: CFG -> ((Label,Label),Int) -> CFG
    insertEdge m ((from,to),weight) =
      M.alter f from m
        where
          f :: Maybe (M.Map Label Int) -> Maybe (M.Map Label Int)
          f Nothing = Just $ M.singleton to weight
          f (Just destMap) = Just $ M.insert to weight destMap
    weightedEdges :: CmmBlock -> [((Label,Label),Int)]
    weightedEdges block =
      case branch of
        CmmBranch dest
          --Penalize info tables since they prevent eliminating
          --the jump
          | mapMember dest info -> [((bid,dest),60)]
          | otherwise           -> [((bid,dest),100)]
        CmmCondBranch _c t f l
          -- Prefer false branch to keep in line with old
          -- layout algorithm.
          | l == Nothing -> [((bid,f),51),((bid,t),49)]
          | l == Just True -> [((bid,f),10),((bid,t),90)]
          | l == Just False -> [((bid,t),10),((bid,f),90)]
        (CmmSwitch _e ids) -> map (\x -> ((bid,x),5)) $ switchTargetsToList ids
        --Calls naturally break control flow, so don't try and keep
        --the return address in sequence
        (CmmCall { cml_cont = Just cont})  -> [((bid,cont),0)]
        (CmmForeignCall {Cmm.succ = cont}) -> [((bid,cont),0)]
        (CmmCall { cml_cont = Nothing })  -> []
        other ->
            --pprTrace "Unkown successor cause:"
            --    (ppr branch <+> text "=>" <> ppr (successors other)) $
            map (\x -> ((bid,x),5)) $ successors other
      where
        branch = lastNode block :: CmmNode O C
        bid = entryLabel block

    blocks = revPostorder graph :: [CmmBlock]
