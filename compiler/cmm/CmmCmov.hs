{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, InstanceSigs #-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module CmmCmov
    (BranchInfo(..), cmmIfToCmov)
where

import GhcPrelude hiding (succ, unzip, zip)

import Hoopl.Block
import Hoopl.Collections
import Hoopl.Graph
import Hoopl.Label
import BlockId
import Cmm
import CmmUtils
--import CmmSwitch (mapSwitchTargets)
import DynFlags
import Maybes
import Panic
--import Util
import UniqSupply

import Control.Monad
import Data.List
import Data.Foldable (toList)
--import Data.Bifunctor (bimap)

import PprCmm ()
import FastString
import Outputable
--import Maybes
import Data.Bifunctor (second)

import qualified Data.Set as S

{-
The big picture:

We look at two branches of an if/else code path.
We split the two paths into a common pre/suffix and differing middle.
We check if the differing instructions consist only of assignments.
If yes -> Try to turn them into conditional moves:

    * Match them in assignments to the same destination,
      keep relative order of assignments.
    * Try to turn each pair into a cmov.

    Tricky:
    If there is only one assignment then generate a "partial" cmov.
    Catch! Floats are special in many ways. If we would need to invert
    a floating point condition just give up instead.

    * Dependencies ruin everything:
        We ensure later assignments don't depend on earlier ones,
        that way we can evaluate all expressions independent of each other.

        While this isn't very hard to check it will rule out some valid
        oppertunities.



-}


cmmIfToCmov :: DynFlags -> CmmDecl -> UniqSM CmmDecl
--cmmIfToCmov dflags proc@(CmmProc info lbl live graph) = return proc
cmmIfToCmov dflags (CmmProc info lbl live graph) = do

    --Try to combine split control flow using cmov
    cmovResults <-
        (foldM (\m bid ->
                    pure (mapInsert bid :: a -> LabelMap a -> LabelMap a ) <*>
                    getCmov bid <*> pure m)
                mapEmpty
                (diamonds ++ triangles))

    let cmovUpdates = fmap fromJust . mapFilter (isJust) $ cmovResults

    let cmovBlocks = mapElems cmovUpdates

    let updateBlock :: CmmBlock -> CmmBlock
        updateBlock block
          | Just blk <- mapLookup tipLbl cmovUpdates
          , cmovLbl <- entryLabel blk
          = replaceLastNode block (CmmBranch cmovLbl)
          | otherwise = block
          where
            tipLbl = (entryLabel block)

    let tipBlocks = fmap (updateBlock . getBlock) diamonds


    let graph' = ofBlockMap entry $
                 foldl' (\m b ->
                            mapInsert (entryLabel b) b m :: LabelMap CmmBlock)
                        (toBlockMap graph)
                        (cmovBlocks ++ tipBlocks)

    return $ CmmProc info lbl live graph'
    where
        --hasInfoTable bid = mapMember bid info
        entry = g_entry graph
        blocks = toBlockList graph
        blockMap = toBlockMap graph
        getBlock :: BlockId -> CmmBlock
        getBlock b = expectJust "Foo" $ mapLookup b blockMap

        diamonds :: [BlockId]
        diamonds = filter (isDiamondTip blockMap) . map entryLabel $ blocks

        triangles :: [BlockId]
        triangles = filter (isJust . getTriangle blockMap) .
                    map entryLabel $ blocks

        getBranches :: Label -> BranchInfo CmmBlock
        getBranches b
            | [f,t] <- map getBlock . successors . getBlock $ b
            = BranchBoth t f
            | Just branch <- getTriangle blockMap b
            = fmap getBlock branch
            | otherwise
            = panic "Can't get branches to construct cmov"

        getCondition :: (BlockId) -> CmmExpr
        getCondition blk
            | lst <- lastNode . getBlock $ blk
            , CmmCondBranch cond _ _ _ <- lst
            = cond
            | otherwise
            = pprPanic "TODO:Get cond from" (ppr blk)


        getCmov bid = canApplyCmov dflags cond branches
            where
                cond = getCondition bid
                branches = getBranches bid


cmmIfToCmov _ top = return top

-- | Look at two blocks and check if they can be replaced by one using conditional moves
canApplyCmov ::  DynFlags -> CmmExpr -> BranchInfo CmmBlock
             -> UniqSM (Maybe CmmBlock)
canApplyCmov dflags cond branches =
    let (prefix, stmtsLeft, stmtsRight, suffix) = splitMiddle midTrue midFalse
    in do
    when (dopt Opt_D_dump_cmm_cmov dflags) $
        pprTraceM "cmovAnalysis" (
            text "blocks" <+>
                ppr (entryLabel <$> (getTrueInfo branches),
                    entryLabel <$> (getFalseInfo branches)) $$
            text "prefix" <+> ppr prefix $$
            text "diff true" <+> ppr stmtsLeft $$
            text "diff false" <+> ppr stmtsRight $$
            text "suffix" <+> ppr suffix)

    cmovRes <- mkCmov dflags cond stmtsLeft stmtsRight

    let instrs :: Either FastString [CmmNode O O]
        instrs = case cmovRes of
            Right cmov  -> Right (prefix ++ [cmov] ++ suffix)
            Left reason -> Left reason

    lbl <- mkBlockId <$> getUniqueM

    let cmovBlock = (\ins -> BlockCC (CmmEntry lbl tickScope)
                                        (blockFromList ins)
                                        lastInstr) <$> instrs

    when (dopt Opt_D_dump_cmm_cmov dflags) $
        pprTraceM "Cmov" (ppr cmovBlock)

    return $ either (const Nothing) (Just) cmovBlock
    where
        lastInstr :: CmmNode O C
        lastInstr = lastNode . head . toList $ branches
        tickScope = (\(CmmEntry _ ts) -> ts) .
                    firstNode . head . toList $ branches
        branchNodes :: BranchInfo [CmmNode O O]
        branchNodes = fmap (blockToList . middleBlock) branches
        midTrue
            = maybe [] id (getTrueInfo  branchNodes)
        midFalse
            = maybe [] id (getFalseInfo branchNodes)


        --Get the common prefix and the two remaining parts of the lists.
        getPrefix n1s  [] = ([],n1s,[])
        getPrefix []  n2s = ([],[],n2s)
        getPrefix (n1:n1s) (n2:n2s)
            | n1 == n2 || (dont_care n1 && dont_care n2)
            = let (prefix, restTrue, restFalse) = getPrefix n1s n2s
            in  (n1:prefix, restTrue, restFalse)
            | otherwise = ([], (n1:n1s),(n2:n2s))

        getSuffix ts fs =
            let (suffix, diffLeft, diffRight) = getPrefix (reverse ts)
                                                            (reverse fs)
            in (reverse suffix, reverse diffLeft, reverse diffRight)

        splitMiddle :: [CmmNode O O] -> [CmmNode O O]
                    -> ([CmmNode O O], [CmmNode O O], [CmmNode O O], [CmmNode O O])
        splitMiddle middle1 middle2 =
            let (pre, tailLeft, tailRight) = getPrefix middle1 middle2
                (suf, diffLeft, diffRight) = getSuffix tailLeft tailRight
            in (pre, diffLeft, diffRight, suf)

mkCmov :: DynFlags -> CmmExpr -> [CmmNode O O] -> [CmmNode O O]
       -> UniqSM (Either FastString  (CmmNode O O))
mkCmov dflags cond true' false' = do
        when (dopt Opt_D_dump_cmm_cmov dflags) $
            pprTraceM "StatementPairings" (ppr cmovData)
        return $ fmap (\assignments -> CmmCondAssign cond assignments) cmovData
    where
        trueStmts  = filter (not . dont_care) true'
        falseStmts = filter (not . dont_care) false'

        compatibleStmt :: CmmNode O O -> CmmNode O O -> Bool
        compatibleStmt (CmmAssign t1 _) (CmmAssign t2 _) = t1 == t2
        compatibleStmt (CmmStore t1 _) (CmmStore t2 _) = t1 == t2
        compatibleStmt x y = x == y

        cmovData :: Either FastString [(CmmReg, BranchInfo CmmExpr)]
        cmovData = second (const (map getAssignmentInfo pairs))
                        (checkDependencies dflags cond pairs)


        --List of matched up assignments
        pairs :: [BranchInfo (CmmNode O O)]
        pairs = (if (dopt Opt_D_dump_cmm_cmov dflags)
                    then (pprTraceIt "CmovPairs")
                    else id) $
                matchPairs compatibleStmt trueStmts falseStmts

        getAssignmentInfo :: BranchInfo (CmmNode O O)
                          -> (CmmReg, BranchInfo CmmExpr)
        getAssignmentInfo (BranchBoth (CmmAssign r eTrue) (CmmAssign _ eFalse))
            = (r,BranchBoth eTrue eFalse)
        getAssignmentInfo (BranchTrue (CmmAssign r eTrue))
            = (r,BranchTrue eTrue)
        getAssignmentInfo (BranchFalse (CmmAssign r eFalse))
            = (r,BranchFalse eFalse)
        getAssignmentInfo info
            = pprPanic "cmov assignment info not supported for " $ ppr info

data CmovCheckInfo
    = CheckInfo
    { localRegs :: !(RegSet LocalReg)
    , globalRegs :: !(RegSet GlobalReg)
    , estimatedCost :: !Int
    } deriving (Eq)

-- | Check the pairings
-- We rule out true dependencies between the assignments when executed in order
-- as well as between the assignments and the condition.
-- We also filter out cases with too expensive expressions or assignments to memory
checkDependencies :: DynFlags -> CmmExpr -> [BranchInfo (CmmNode O O)]
                  -> Either FastString ()
checkDependencies dflags cond pairs
    = go pairs (CheckInfo S.empty S.empty 0)
  where
    maxCost = maxCmovCost dflags
    condLocalRegs = foldRegsUsed dflags extendRegSet emptyRegSet cond
    condGlobalRegs = foldRegsUsed dflags extendRegSet emptyRegSet cond

    go :: [BranchInfo (CmmNode O O)] -> CmovCheckInfo
       -> Either FastString ()
    go [] (CheckInfo localAss globalAss cost)
      | condConflict = Left $ fsLit "Assignment <-> Cond conflict"
      | cost > maxCost = Left $ fsLit "Expression cost too high"
      | otherwise = Right ()
      where
        setsConflict s1 s2 = not . nullRegSet $ timesRegSet s1 s2
        condConflict = setsConflict condLocalRegs localAss ||
                       setsConflict condGlobalRegs globalAss

    go (mr : ms) (CheckInfo localAss globalAss cost)
      | not (all isAssign mr)
      = Left $ fsLit "Store"
      | any floatType mr
      = Left $ fsLit "Float"
      | globalConflict
      = Left $ fsLit "Global Register Dependency"
      | localConflict
      = Left $ fsLit "Local Variable Dependency"
      | cost > maxCost
      = Left $ fsLit "Expression cost too high"
      | otherwise
      = go ms (CheckInfo (plusRegSet localDefd localAss)
                         (plusRegSet globalDefd globalAss) (cost + biCost))

      where
        localConflict = not . nullRegSet $ timesRegSet localAss localRead
        globalConflict = not . nullRegSet $ timesRegSet globalAss globalRead

        (localDefd :: LocalRegSet)
          = foldLocalRegsDefd dflags extendRegSet emptyRegSet mr
        (globalDefd :: GlobalRegSet)
          = foldRegsDefd dflags extendRegSet emptyRegSet mr

        (localRead :: LocalRegSet)
          = foldLocalRegsUsed dflags extendRegSet emptyRegSet mr
        (globalRead :: GlobalRegSet)
          = foldRegsUsed dflags extendRegSet emptyRegSet mr
        biCost = foldl' (\r n -> r + nodeCost n) 0 mr
        nodeCost :: CmmNode O O -> Int
        nodeCost (CmmAssign _to expr) = exprCost expr
        nodeCost (CmmStore to expr) = 5 + exprCost to + exprCost expr
        nodeCost n = pprPanic "Invalid node:" (ppr n)

    floatType :: CmmNode O O -> Bool
    floatType (CmmAssign r _e)  =
      isFloatType . cmmRegType dflags $ r
    floatType (CmmStore _a e)   =
      isFloatType . cmmExprType dflags $ e
    floatType _other          = False

    --isStore :: CmmNode O O -> Bool
    --isStore (CmmStore {})   = True
    --isStore _other          = False

    isAssign :: CmmNode O O -> Bool
    isAssign (CmmAssign {})   = True
    isAssign _other          = False

-- | An estimate of the overhead caused by unneccesary
--   evaluation of the expression at the CPU level.
exprCost :: CmmExpr -> Int
exprCost (CmmLit {}) = 1
exprCost (CmmLoad e _) = 3 + exprCost e -- Can increase cache pressure
exprCost (CmmReg {}) = 1
exprCost (CmmStackSlot {}) = 1
exprCost (CmmRegOff {}) = 2
exprCost (CmmMachOp mo exprs) =
    mcost mo + (sum . map exprCost $ exprs)
  where
    mcost (MO_Add {}) = 1
    mcost (MO_Sub {}) = 1
    mcost (MO_Eq {}) = 1
    mcost (MO_Ne {}) = 1
    mcost (MO_Mul {}) = 3

    mcost (MO_S_MulMayOflo {}) = 3
    mcost (MO_S_Neg {}) = 1

    mcost (MO_S_Ge {}) = 1
    mcost (MO_S_Le {}) = 1
    mcost (MO_S_Gt {}) = 1
    mcost (MO_S_Lt {}) = 1
    mcost (MO_U_Ge {}) = 1
    mcost (MO_U_Le {}) = 1
    mcost (MO_U_Gt {}) = 1
    mcost (MO_U_Lt {}) = 1

    mcost (MO_F_Add {}) = 2
    mcost (MO_F_Sub {}) = 2
    mcost (MO_F_Neg {}) = 1
    mcost (MO_F_Mul {}) = 5

    mcost (MO_F_Eq {}) = 2
    mcost (MO_F_Ne {}) = 2
    mcost (MO_F_Ge {}) = 2
    mcost (MO_F_Le {}) = 2
    mcost (MO_F_Gt {}) = 2
    mcost (MO_F_Lt {}) = 2

    mcost (MO_And {}) = 1
    mcost (MO_Or {}) = 1
    mcost (MO_Xor {}) = 1
    mcost (MO_Not {}) = 1
    mcost (MO_Shl {}) = 1
    mcost (MO_U_Shr {}) = 1
    mcost (MO_S_Shr {}) = 1
    mcost (MO_SF_Conv {}) = 1
    mcost (MO_FS_Conv {}) = 1
    mcost (MO_SS_Conv {}) = 0
    mcost (MO_UU_Conv {}) = 0
    mcost (MO_FF_Conv {}) = 0

    --Expensive things
    mcost _ = 1000


-- We have list of stores/assignments we try to match up based on their
-- destination. We don't reorder statements in their own branch so if
-- there is a mtch we can find it in two lists xs,ys if we:
--      check the heads
--      check for x and y how many assignments from the other branch we have
--      to remove to match them up.
--      Pop one element from the branch where we can match up faster
matchPairs :: (a -> a -> Bool) -> [a] -> [a] -> [BranchInfo a]
matchPairs _ [] [] = []
matchPairs p (x:xs) [] = BranchTrue x : matchPairs p xs []
matchPairs p [] (y:ys) = BranchFalse y : matchPairs p [] ys
matchPairs p (x:xs) (y:ys)
    --Matching pair
    | p x y
    = BranchBoth x y : matchPairs p xs ys

    --If a head has no match advance it's branch
    | minDist == Nothing
    = BranchTrue x : BranchFalse y : matchPairs p xs ys
    | distX == Nothing
    = BranchFalse y : matchPairs p (x:xs) (ys)
    | distY == Nothing
    = BranchTrue x : matchPairs p (xs) (y:ys)

    --Otherwise advance the branch where we have to do fewer onesided
    --statements before finding a match.
    | distX < distY
    = BranchTrue x : matchPairs p (xs) (y:ys)
    | distX >= distY
    = BranchFalse y : matchPairs p (x:xs) (ys)
    | otherwise
    = panic "Impossible"

    where
      --Negate to make the order of Nothing/Just match up with distance.
      distX = findIndex (`p` y) (x:xs)
      distY = findIndex (p x) (y:ys)
      minDist = min distX distY

dont_care :: CmmNode e x -> Bool
dont_care CmmComment{} = True
dont_care CmmTick{}    = True
dont_care _other       = False

-- if a then ... goto b else goto b
getTriangle :: LabelMap CmmBlock -> BlockId -> Maybe (BranchInfo BlockId)
getTriangle blockMap lbl
    | Just [b,c] <- successors <$> mapLookup lbl blockMap
    = isTriangle (b,c)
    | otherwise
    = Nothing
    where
        isTriangle :: (BlockId,BlockId) -> Maybe (BranchInfo BlockId)
        isTriangle (t,f)
            = case lastNode <$> mapLookup t blockMap of
                Just (CmmBranch dest)
                    | dest == f -> Just $ BranchTrue t
                _ -> case lastNode <$> mapLookup f blockMap of
                        Just (CmmBranch dest)
                            | dest == t -> Just $ BranchFalse f
                        _       -> Nothing

isDiamondTip :: LabelMap CmmBlock -> BlockId -> Bool
isDiamondTip blockMap lbl
    | Just [b,c] <- successors <$> mapLookup lbl blockMap
    , Just dl <- lastNode <$> mapLookup b blockMap
    , Just dr <- lastNode <$> mapLookup c blockMap
    , dl == dr
    , CmmBranch _ <- dl
    = True
    | otherwise = False
