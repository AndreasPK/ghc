{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module CmmContFlowOpt
    ( cmmCfgOpts
    , cmmCfgOptsProc
    , removeUnreachableBlocksProc
    , replaceLabels
    , predInfoMap
    )
where

import GhcPrelude hiding (succ, unzip, zip)

import Hoopl.Block
import Hoopl.Collections
import Hoopl.Graph
import Hoopl.Label
import BlockId
import Cmm
import CmmUtils
import CmmSwitch (mapSwitchTargets)
import PprCmm ()
import Maybes
import Panic
import Outputable
import Util

import Control.Monad
import Data.List
import Data.Foldable
import Data.Bifunctor

import System.IO
import System.IO.Unsafe


-- Note [What is shortcutting]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Consider this Cmm code:
--
-- L1: ...
--     goto L2;
-- L2: goto L3;
-- L3: ...
--
-- Here L2 is an empty block and contains only an unconditional branch
-- to L3. In this situation any block that jumps to L2 can jump
-- directly to L3:
--
-- L1: ...
--     goto L3;
-- L2: goto L3;
-- L3: ...
--
-- In this situation we say that we shortcut L2 to L3. One of
-- consequences of shortcutting is that some blocks of code may become
-- unreachable (in the example above this is true for L2).


-- Note [Control-flow optimisations]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- This optimisation does three things:
--
--   - If a block finishes in an unconditional branch to another block
--     and that is the only jump to that block we concatenate the
--     destination block at the end of the current one.
--
--   - If a block finishes in a call whose continuation block is a
--     goto, then we can shortcut the destination, making the
--     continuation block the destination of the goto - but see Note
--     [Shortcut call returns].
--
--   - For any block that is not a call we try to shortcut the
--     destination(s). Additionally, if a block ends with a
--     conditional branch we try to invert the condition.
--
-- Blocks are processed using postorder DFS traversal. A side effect
-- of determining traversal order with a graph search is elimination
-- of any blocks that are unreachable.
--
-- Transformations are improved by working from the end of the graph
-- towards the beginning, because we may be able to perform many
-- shortcuts in one go.


-- Note [Shortcut call returns]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We are going to maintain the "current" graph (LabelMap CmmBlock) as
-- we go, and also a mapping from BlockId to BlockId, representing
-- continuation labels that we have renamed.  This latter mapping is
-- important because we might shortcut a CmmCall continuation.  For
-- example:
--
--    Sp[0] = L
--    call g returns to L
--    L: goto M
--    M: ...
--
-- So when we shortcut the L block, we need to replace not only
-- the continuation of the call, but also references to L in the
-- code (e.g. the assignment Sp[0] = L):
--
--    Sp[0] = M
--    call g returns to M
--    M: ...
--
-- So we keep track of which labels we have renamed and apply the mapping
-- at the end with replaceLabels.


-- Note [Shortcut call returns and proc-points]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Consider this code that you might get from a recursive
-- let-no-escape:
--
--       goto L1
--      L1:
--       if (Hp > HpLim) then L2 else L3
--      L2:
--       call stg_gc_noregs returns to L4
--      L4:
--       goto L1
--      L3:
--       ...
--       goto L1
--
-- Then the control-flow optimiser shortcuts L4.  But that turns L1
-- into the call-return proc point, and every iteration of the loop
-- has to shuffle variables to and from the stack.  So we must *not*
-- shortcut L4.
--
-- Moreover not shortcutting call returns is probably fine.  If L4 can
-- concat with its branch target then it will still do so.  And we
-- save some compile time because we don't have to traverse all the
-- code in replaceLabels.
--
-- However, we probably do want to do this if we are splitting proc
-- points, because L1 will be a proc-point anyway, so merging it with
-- L4 reduces the number of proc points.  Unfortunately recursive
-- let-no-escapes won't generate very good code with proc-point
-- splitting on - we should probably compile them to explicitly use
-- the native calling convention instead.

cmmCfgOpts :: Bool -> CmmGraph -> CmmGraph
cmmCfgOpts split g = fst (blockConcat split Nothing g)

cmmCfgOptsProc :: Bool -> CmmDecl -> CmmDecl
cmmCfgOptsProc split (CmmProc info lbl live g) = CmmProc info' lbl live g'
    where (g', env) = blockConcat split (Just info) g
          info' = info{ info_tbls = new_info_tbls }
          new_info_tbls = mapFromList (map upd_info (mapToList (info_tbls info)))

          -- If we changed any labels, then we have to update the info tables
          -- too, except for the top-level info table because that might be
          -- referred to by other procs.
          upd_info (k,info)
             | Just k' <- mapLookup k env
             = (k', if k' == g_entry g'
                       then info
                       else info{ cit_lbl = infoTblLbl k' })
             | otherwise
             = (k,info)
cmmCfgOptsProc _ top@(CmmData {}) = top


blockConcat :: Bool -> Maybe CmmTopInfo -> CmmGraph -> (CmmGraph, LabelMap BlockId)
blockConcat splitting_procs info g@CmmGraph { g_entry = entry_id }
  = --pprTrace "Concat"
    --  (ppr g $$ ppr splitting_procs $$
    --   if (null shortcut_map')
    --        then text "empty"
    --        else (text "hasMap" <+> ppr shortcut_map'))
    (replaceLabels shortcut_map $ ofBlockMap new_entry new_blocks, shortcut_map')
  where
    -- We might be able to shortcut the entry BlockId itself.
    -- Remember to update the shortcut_map, since we also have to
    -- update the info_tbls mapping now.
    (new_entry, shortcut_map')
      | Just entry_blk <- mapLookup entry_id new_blocks
      , Just dest      <- canShortcut entry_blk
      = (dest, mapInsert entry_id dest shortcut_map)
      | otherwise
      = (entry_id, shortcut_map)

     -- blocks are sorted in reverse postorder, but we want to go from the exit
    -- towards beginning, so we use foldr below.
    blocks = revPostorder g
    blockmap = foldl' (flip addBlock) emptyBody blocks

    -- Accumulator contains three components:
    --  * map of blocks in a graph
    --  * map of shortcut labels. See Note [Shortcut call returns]
    --  * map containing number of predecessors for each block. We discard
    --    it after we process all blocks.
    (new_blocks, shortcut_map, _) =
        foldr maybe_concat (blockmap, mapEmpty, initialBackEdges) blocks

    -- Map of predecessors for initial graph. We add the entry block
    -- as predecessors for itself to denote that it is a target of a
    -- jump, even if no block in the current graph jumps to it.

    initialBackEdges = predInfoMap blocks :: LabelMap LabelSet

    maybe_concat :: CmmBlock
                -> (LabelMap CmmBlock, LabelMap BlockId, LabelMap LabelSet)
                -> (LabelMap CmmBlock, LabelMap BlockId, LabelMap LabelSet)
    maybe_concat block (!blocks, !shortcut_map, !backEdges)

      -- If:
      --   (1) current block ends with unconditional branch to b' and
      --   (2) it has exactly one predecessor (namely, current block)
      --
      -- Then:
      --   (1) append b' block at the end of current block
      --   (2) remove b' from the map of blocks
      --   (3) remove information about b' from predecessors map
      --
      -- Since we know that the block has only one predecessor we call
      -- mapDelete directly instead of calling decPreds.
      --
      -- Note that we always maintain an up-to-date list of predecessors, so
      -- we can ignore the contents of shortcut_map
      | CmmBranch b' <- last
      , hasOnePredecessor b'
      , Just blk' <- mapLookup b' blocks
      , entryLabel block /= b'
      = let bid' = entryLabel blk'
        in  --pprTrace "branch" (ppr $ mapDelete bid' $ mapInsert bid (splice head blk') blocks)
            ( mapDelete bid' $ mapInsert bid (splice head blk') blocks
            , shortcut_map
            , foldl' (\m s -> cut bid bid' s m) backEdges (successors blk')
            )

      -- If:
      --   (1) we are splitting proc points (see Note
      --       [Shortcut call returns and proc-points]) and
      --   (2) current block is a CmmCall or CmmForeignCall with
      --       continuation b' and
      --   (3) we can shortcut that continuation to dest
      -- Then:
      --   (1) we change continuation to point to b'
      --   (2) create mapping from b' to dest
      --   (3) increase number of predecessors of dest by 1
      --   (4) decrease number of predecessors of b' by 1
      --
      -- Later we will use replaceLabels to substitute all occurrences of b'
      -- with dest.
      | splitting_procs
      , Just b'   <- callContinuation_maybe last
      , Just blk' <- mapLookup b' blocks
      , Just dest <- canShortcut blk'
      = ( mapInsert bid (blockJoinTail head (update_cont dest)) blocks
        , mapInsert b' dest shortcut_map
        , cut bid b' dest backEdges
        )

      -- If:
      --   (1) a block does not end with a call
      -- Then:
      --   (1) if it ends with a conditional attempt to invert the
      --       conditional
      --   (2) attempt to shortcut all destination blocks
      --   (3) if new successors of a block are different from the old ones
      --       update the of predecessors accordingly
      --
      -- A special case of this is a situation when a block ends with an
      -- unconditional jump to a block that can be shortcut.
      | Nothing <- callContinuation_maybe last
      = let oldSuccs = successors last
            (last', predMap') = shortcut_last
            swappedLast = rewrite_last last'
            newSuccs = successors swappedLast
        in ( mapInsert bid (blockJoinTail head swappedLast) blocks
            , shortcut_map
            , if oldSuccs == newSuccs
              then backEdges
              else
                foldr (\newSuc -> addPred newSuc bid)
                  (foldr (\oldSuc -> delPred oldSuc bid) backEdges oldSuccs)
                  newSuccs
            )

      -- Otherwise don't do anything
      | otherwise
      = ( blocks, shortcut_map, backEdges )
      where
        (head, last) = blockSplitTail block
        bid = entryLabel block

        -- Changes continuation of a call to a specified label
        update_cont :: Label -> CmmNode O C
        update_cont dest =
            case last of
              CmmCall{}        -> last { cml_cont = Just dest }
              CmmForeignCall{} -> last { succ = dest }
              _                -> panic "Can't shortcut continuation."

        -- See Note [Invert Cmm conditionals]
        rewrite_last :: CmmNode O C -> CmmNode O C
        rewrite_last last
          --Only take apart Conditional Branches
          | case last of
            CmmCondBranch {} -> False
            _ -> True
          = last

          -- Sometimes we can get rid of the conditional completely.
          | t == f
          = CmmBranch t
          -- Case A & B
          | -- inverting will make t a fallthrough
            trueSuitableFallthrough && not (reqInfoTable t)
          -- false branch is a bad candidate for fallthrough.
          , likelyTrue l || not falseSuitableFallthrough || reqInfoTable f
          , Just cond' <- maybeInvertCmmExpr cond
          = CmmCondBranch cond' f t (invertLikeliness l)

          -- Case C
          | likelyTrue l
          , numPreds f <= 3
          , Just cond' <- maybeInvertCmmExpr cond
          --, trace ("SwapInfo;1;"++show swapInfo) $ mflash True
          = CmmCondBranch cond' f t (invertLikeliness l)

          | l == Nothing
          , numPreds f > numPreds t
          , Just cond' <- maybeInvertCmmExpr cond
          --, trace ("SwapInfo;1;"++show swapInfo) $ mflash True
          = CmmCondBranch cond' f t (invertLikeliness l)



          -- | l == Just False
          --, trueSuitableFallthrough
          --, not falseSuitableFallthrough || reqInfoTable f --TODO:
          -- TODO: If we have other good fallthrough candidates AND a info table, it might be worth to invert?
          --, Just cond' <- maybeInvertCmmExpr cond
          --, trace ("SwapInfo;2;"++show swapInfo) $ mflash True
          -- = CmmCondBranch cond' f t (invertLikeliness l)

          | --trace ("SwapInfo;0;"++show swapInfo) $ mflash
            False
          = undefined
          | otherwise
          = last
          where
            (CmmCondBranch cond t f l) = last
            {-
            swapInfo =
              ( hasOnePredecessor t && (likelyTrue l || numPreds f > 1)
              , numPreds f
              , numPreds t
              , reqInfoTable f
              , reqInfoTable t
              , showSDocUnsafe (ppr bid)
              ) -}
            reqInfoTable :: Label -> Bool
            reqInfoTable lbl
              | Just infoBlocks <- info
              =  mapMember lbl (info_tbls infoBlocks)
              | entry_id == lbl
              = True
              | otherwise
              = any nodeCausesInfoTabel . mapMaybe getBlockTail .
                getPreds $ lbl

            --True if no other preds of the f/t targets can fall through.
            --The currently processed block always can fall through since we know it's a conditional.
            trueSuitableFallthrough = {-
              pprTrace "trueGood" (
                let nodes = mapMaybe (`getBlockTail` t) . filter (/= bid) $ getPreds t :: [CmmNode O C]
                    results = map (couldFallThrough t) nodes :: [Bool]
                in
                ppr results $$
                ppr nodes
              ) $ -}
              not $ any (couldFallThrough t) .
                mapMaybe getBlockTail . filter (/= bid) $ getPreds t
            falseSuitableFallthrough = {-
              pprTrace "falseGood" (
                let nodes = mapMaybe (`getBlockTail` f) . filter (/= bid) $ getPreds f :: [CmmNode O C]
                    results = map (couldFallThrough f) nodes :: [Bool]
                in
                ppr results $$
                ppr nodes
              ) $ -}
              not $ any (couldFallThrough f) .
                mapMaybe getBlockTail . filter (/= bid) $ getPreds f

            getBlockTail :: Label -> Maybe (CmmNode O C)
            getBlockTail from = snd . blockSplitTail <$> entryBlock
              where
                entryBlock :: Maybe CmmBlock
                entryBlock
                  | mapMember from blocks
                  = mapLookup from blocks
                  | otherwise
                  = pprTrace "Warning: Block not found" (ppr from) Nothing

            getPreds :: Label -> [Label]
            getPreds blkLbl
              = setElems $
                (mapLookup blkLbl backEdges `orElse` setEmpty)

        shortcut_last :: (CmmNode O C, LabelMap LabelSet)
        shortcut_last = second update_map shortcut_last'
          where
            update_map =
              foldl (\m (between,to) -> cut bid between to m) backEdges .
                catMaybes

        --shortedSuccs = mapFromList . catMaybes . snd $ shortcut_last'

        -- Attempts to shortcut successors of last node
        -- TODO: Update predecessor map.
        -- The tuple is (oldLabel, NewLabel)
        -- ... L1 ...
        -- L1: goto L2
        -- L2: .....
        -- -> Just (L1, L2)
        shortcut_last' :: (CmmNode O C, [Maybe (Label, Label)])
        shortcut_last' = mapCollectSuccessors shortcut last
          where
            shortcut l =
                case mapLookup l blocks of
                  Just b | Just dest <- canShortcut b
                        -> (dest, Just (l,dest))
                  _otherwise -> (l,Nothing)

        likelyTrue (Just True)   = True
        likelyTrue _             = False

        invertLikeliness :: Maybe Bool -> Maybe Bool
        invertLikeliness         = fmap not

        -- Number of predecessors for a block
        numPreds bid
          | bid == entry_id
          = predCount + 1
          | otherwise
          = predCount
          where
            predCount = (setSize <$> mapLookup bid backEdges) `orElse` 0

        hasOnePredecessor b = numPreds b == 1

-- | Shutcut
--  from:     goto between
--  between:  goto to --remove this
--  to:       ...
cut :: Label -> Label -> Label -> LabelMap LabelSet -> LabelMap LabelSet
cut from between to predMap =
  mapAdjust (setDelete between . setInsert from) to .
  mapDelete between $ predMap

mflash :: a -> a
mflash = seq (unsafePerformIO $ hFlush stdout >> hFlush stderr)

{- Note [Good Fallthroughs]
  We want to make one branch of conditionals a fallthrough if possible.
  However we also want to generate as many fallthroughs as possible.

  If multiple blocks jump into a block L3 then we ideally want to make
  at least one of these a fallthrough.

  For this purpose we use couldFallThrough to check if any of the
  predecessors already will cause a fallthrough to be generated.

  A simple check is if to check if they have only one predecessor.
  However this falls short if a predecessor:
  a) is a call of some sort which always returns via jmp.
  b) is on a cold codepath.

  This check covers a) completely and partially covers b)

  We take a conservative approach and only report guaranteed good
  fallthroughs.

  This means a good fallthrough is:
  * A direct jump
  * The false branch of a conditional if it's likely to be taken
    or in absence of likelyhood information.

  --TODO: Check

  Any other constellation should end up as a jump to the
  target block so concating it does not improve performance.


-}



{-
  Note [Invert Cmm conditionals]
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  The native code generator always produces jumps to the true branch.
  Falling through to the false branch is however faster. So we try to
  arrange for that to happen.

  This also has the secondary advantage that the hot code will be placed next
  to each other.

  This means we should invert the condition if:
  * Case A: (Not implemented)
      We are optimizing for size and we are fairly confident inverting
      will turn the true branch into a fallthrough.
  * Case B:
      We have no likelyhood information and we are fairly confident inverting
      will turn the true branch into a fallthrough, while the false branch
      would not end up as fallthrough.
  * Case C:
      Make the likely branch the false branch.
      We only make an exception if there are already a lot of branches
      leading to the false branch.

  A is obvious. It removes a jump instruction in the generated code.
  It's also the only case where we consider info tables. If a target
  label is likely preceeded by a info table this requires a jump
  instruction.

  B is analog to A, all else being equal smaller code is faster code.

  C has more complex reasoning. During code layout we try to place blocks
  following each other next to each other. However for code like
  B1: if cond then goto BT; else goto BF;
  there is a priority for a layout of [B1, BF, .., BT]. If we always jump to
  BT from B1 this makes for bad performance since we might miss the
  instruction cache. Hence for speed we default to turning the likely branch
  into the false branch.


  In some cases it's faster to avoid inverting when the false branch is likely.
  However determining when that is the case is neither easy nor cheap so for
  now we always invert as this produces smaller binaries and code that is
  equally fast on average. (On an i7-6700K)

  TODO:
  There is also the edge case when both branches have multiple predecessors.
  In this case we could assume that we will end up with a jump for BOTH
  branches. In this case it might be best to put the likely path in the true
  branch especially if there are large numbers of predecessors as this saves
  us the jump thats not taken. However I haven't tested this and as of early
  2018 we almost never generate cmm where this would apply.
-}

-- Functions for updating of predecessors. If

-- Invariant: if a block has no predecessors it should be dropped from the
-- graph because it is unreachable. maybe_concat is constructed to maintain
-- that invariant, but calling replaceLabels may introduce unreachable blocks.
-- We rely on subsequent passes in the Cmm pipeline to remove unreachable
-- blocks.
addPred, delPred :: Label -> Label -> LabelMap LabelSet -> LabelMap LabelSet
addPred bid pred edges
  = mapInsertWith setUnion bid (setSingleton pred) edges
delPred bid oldPred edges
  = mapAdjust (setDelete oldPred) bid edges

-- Checks if a block consists only of "goto dest". If it does than we return
-- "Just dest" label. See Note [What is shortcutting]
canShortcut :: CmmBlock -> Maybe BlockId
canShortcut block
    | (_, middle, CmmBranch dest) <- blockSplit block
    , all dont_care $ blockToList middle
    , entryLabel block /= dest
    = Just dest
    | otherwise
    = Nothing
    where dont_care CmmComment{} = True
          dont_care CmmTick{}    = True
          dont_care _other       = False

-- | Check if the given Node is a good candidate for falling through
-- to the given label.
-- See Note [Good Fallthroughs]
-- The given label HAS to be the block we want to fall through to.
couldFallThrough :: Label -> CmmNode O C -> Bool
couldFallThrough _ (CmmBranch {}) = True
couldFallThrough bid (CmmCondBranch _e _t f l)
  | bid == f
  = (l == Nothing || l == Just False)
  | otherwise = False
couldFallThrough _ (CmmCall {}) = False
couldFallThrough _ (CmmForeignCall {}) = False
couldFallThrough _ (CmmSwitch {}) = False
couldFallThrough _ n = pprPanic "Unchecked block end" (ppr n)

-- Concatenates two blocks. First one is assumed to be open on exit, the second
-- is assumed to be closed on entry (i.e. it has a label attached to it, which
-- the splice function removes by calling snd on result of blockSplitHead).
splice :: Block CmmNode C O -> CmmBlock -> CmmBlock
splice head rest = entry `blockJoinHead` code0 `blockAppend` code1
  where (CmmEntry lbl sc0, code0) = blockSplitHead head
        (CmmEntry _   sc1, code1) = blockSplitHead rest
        entry = CmmEntry lbl (combineTickScopes sc0 sc1)

-- If node is a call with continuation call return Just label of that
-- continuation. Otherwise return Nothing.
callContinuation_maybe :: CmmNode O C -> Maybe BlockId
callContinuation_maybe (CmmCall { cml_cont = Just b }) = Just b
callContinuation_maybe (CmmForeignCall { succ = b })   = Just b
callContinuation_maybe _ = Nothing


-- Map over the CmmGraph, replacing each label with its mapping in the
-- supplied LabelMap.
replaceLabels :: LabelMap BlockId -> CmmGraph -> CmmGraph
replaceLabels env g
  | mapNull env = g
  | otherwise   = replace_eid $ mapGraphNodes1 txnode g
   where
     replace_eid g = g {g_entry = lookup (g_entry g)}
     lookup id = mapLookup id env `orElse` id

     txnode :: CmmNode e x -> CmmNode e x
     txnode (CmmBranch bid) = CmmBranch (lookup bid)
     txnode (CmmCondBranch p t f l) =
       mkCmmCondBranch (exp p) (lookup t) (lookup f) l
     txnode (CmmSwitch e ids) =
       CmmSwitch (exp e) (mapSwitchTargets lookup ids)
     txnode (CmmCall t k rg a res r) =
       CmmCall (exp t) (liftM lookup k) rg a res r
     txnode fc@CmmForeignCall{} =
       fc{ args = map exp (args fc), succ = lookup (succ fc) }
     txnode other = mapExpDeep exp other

     exp :: CmmExpr -> CmmExpr
     exp (CmmLit (CmmBlock bid))                = CmmLit (CmmBlock (lookup bid))
     exp (CmmStackSlot (Young id) i) = CmmStackSlot (Young (lookup id)) i
     exp e                                      = e

mkCmmCondBranch :: CmmExpr -> Label -> Label -> Maybe Bool -> CmmNode O C
mkCmmCondBranch p t f l =
  if t == f then CmmBranch t else CmmCondBranch p t f l

-- | When we jump from the given block into another one a
-- info table is required in the successor.
nodeCausesInfoTabel :: CmmNode O C -> Bool
nodeCausesInfoTabel (CmmBranch {}) = False
nodeCausesInfoTabel (CmmCondBranch {}) = False
nodeCausesInfoTabel (CmmCall {}) = True
nodeCausesInfoTabel (CmmForeignCall {}) = True
nodeCausesInfoTabel (CmmSwitch {}) = False
nodeCausesInfoTabel n = pprPanic "Impossible block end" (ppr n)

-- Build a map which records for each block the predecessors.
predInfoMap :: [CmmBlock] -> LabelMap LabelSet
predInfoMap blocks = foldl' (flip insertPred) mapEmpty succPairs
    where
        insertPred :: (Label, Label) -> LabelMap LabelSet -> LabelMap LabelSet
        insertPred (l,pred) predMap = mapInsertWith setUnion l (setSingleton pred) predMap
        getPairs :: Label -> [Label] -> [(Label, Label)]
        getPairs l succ = map (\s -> (s,l)) succ
        succPairs :: [(Label, Label)]
        succPairs =
            foldMap (\b -> getPairs (entryLabel b) (successors b)) blocks

-- Removing unreachable blocks
removeUnreachableBlocksProc :: CmmDecl -> CmmDecl
removeUnreachableBlocksProc proc@(CmmProc info lbl live g)
   | used_blocks `lengthLessThan` mapSize (toBlockMap g)
   = CmmProc info' lbl live g'
   | otherwise
   = proc
   where
     g'    = ofBlockList (g_entry g) used_blocks
     info' = info { info_tbls = keep_used (info_tbls info) }
             -- Remove any info_tbls for unreachable

     keep_used :: LabelMap CmmInfoTable -> LabelMap CmmInfoTable
     keep_used bs = mapFoldlWithKey keep mapEmpty bs

     keep :: LabelMap CmmInfoTable -> Label -> CmmInfoTable -> LabelMap CmmInfoTable
     keep env l i | l `setMember` used_lbls = mapInsert l i env
                  | otherwise               = env

     used_blocks :: [CmmBlock]
     used_blocks = revPostorder g

     used_lbls :: LabelSet
     used_lbls = setFromList $ map entryLabel used_blocks
