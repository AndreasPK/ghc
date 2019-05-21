--
-- Copyright (c) 2019 Andreas Klebinger
--

{-# LANGUAGE CPP, TypeFamilies, RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs, TupleSections #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}

{-# OPTIONS_GHC -O0 #-}

-- (findTags, nodesTopBinds)
module StgTraceTags.Analyze (findTags, FlowNode(..), NodeId(..), hasOuterTag) where

#include "HsVersions.h"

import GhcPrelude

import DataCon
import Data.Bifunctor
import Id
import StgSyn
import StgUtil
import Outputable
-- import VarEnv
import CoreSyn (AltCon(..))
-- import Data.List (mapAccumL)
import Data.Maybe (fromMaybe)

import VarSet
-- import UniqMap

import TyCon (tyConDataCons_maybe, PrimRep(..), tyConDataCons)
import Type -- (tyConAppTyCon, isUnliftedType, Type)
import Hoopl.Collections
-- import PrimOp
import UniqSupply
import StgCmmClosure (idPrimRep)
import RepType
import StgUtil

import Name
import PrelNames
-- import OccName
import SrcLoc
import FastString

import Control.Monad
-- import Data.Maybe
import qualified Data.List as L

import Unique
import UniqFM
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Util
import Data.Ord (comparing)

import State
import Maybes
import Data.Foldable
import Control.Applicative

import StgSubst

data AppEnterMapping = AppEnterMapping

class Lattice a where
    bot :: a
    glb :: a -> a -> a
    lub :: a -> a -> a
    top :: a


-- | Enterinfo for a binding IF IT USED AS AN UNAPPLIED ATOM.
--   In particular for
--     case food<NoEnter> ingredients of ...
--   we WILL need to evaluate food either way.
-- However if an id is determined to be NeverEnter we can say
-- that we can put it directly in strict fields without violating
-- the tagging invariant as well as casing on it as data without entering
-- eg the code:
-- case burger<NoEnter> of
--     CheeseBurger -> e1
--     Regular -> e2
-- does not require us to emite code to enter burger to branch on it's value.
data EnterInfo
    = BotEnterInfo      -- ^ No information
    | UndetEnterInfo    -- ^ Not yet determined, happens for rhsCon if we don't
                        --   know if the strict fields are already tagged.
    | NeedsEnter        -- ^ WILL need to be entered
    | MaybeEnter        -- ^ Could be either
    | NeverEnter        -- ^ Does NOT need to be entered.
    deriving (Eq,Show)

instance Outputable EnterInfo where
    ppr BotEnterInfo   = text "_|_"
    ppr UndetEnterInfo    = char '?'
    ppr NeedsEnter    = char 'u'
    ppr MaybeEnter  = char 'm'
    ppr NeverEnter      = char 't'

{- |
              MaybeEnter
             /    |    \
      NeedsEnter  |   NeverEnter
             \    |    /
            UndetEnterInfo
                  |
            BotEnterInfo


    BotEnterInfo
-}
instance Lattice EnterInfo where
    bot = BotEnterInfo
    top = MaybeEnter

    glb = panic "glb not used"

    lub BotEnterInfo x = x
    lub x BotEnterInfo = x

    lub UndetEnterInfo x = x
    lub x UndetEnterInfo = x

    lub NeedsEnter NeverEnter = MaybeEnter
    lub NeverEnter NeedsEnter  = MaybeEnter

    lub NeedsEnter NeedsEnter = NeedsEnter
    lub NeverEnter NeverEnter = NeverEnter

    lub MaybeEnter _ = MaybeEnter
    lub _ MaybeEnter = MaybeEnter




-- Pointwise instances, but with a twist:
-- Namely we assume bot == [] == replicate n bot
-- Only valid between domains of the same dimensions
instance Lattice a => Lattice [a] where
    top = panic "Not reasonable"
    bot = []

    glb [] ys = map (const bot) ys
    glb xs [] = map (const bot) xs
    glb xs ys = zipWithEqual "Pointwise lattice" glb xs ys

    lub [] ys = ys
    lub xs [] = xs
    lub xs ys = zipWithEqual "Pointwise lattice" lub xs ys

instance (Lattice a1, Lattice a2) => Lattice (a1,a2) where
    glb (l1,r1) (l2,r2) = (glb l1 l2, glb r1 r2)
    lub (l1,r1) (l2,r2) = (lub l1 l2, lub r1 r2)
    bot = (bot,bot)
    top = (top,top)

data SumInfo
    = NoSumInfo -- ^ Default
    | SumInfo !DataCon [EnterLattice] -- ^ A constructor application
    | TopSumInfo -- ^ Result could be different constructors
    deriving (Eq)

instance Outputable SumInfo where
    ppr NoSumInfo = text "_|_"
    ppr (SumInfo con fields) = char '<' <> ppr con <> char '>' <> ppr fields
    ppr TopSumInfo = char 'T'

instance Lattice SumInfo where
    bot = NoSumInfo
    top = TopSumInfo

    glb TopSumInfo x = x
    glb x TopSumInfo = x
    glb (SumInfo con1 lat1) (SumInfo con2 lat2)
        | con1 == con2
        = SumInfo con1 (glb lat1 lat2)
        | otherwise = NoSumInfo
    glb NoSumInfo _ = NoSumInfo
    glb _ NoSumInfo = NoSumInfo

    lub NoSumInfo x = x
    lub x NoSumInfo = x
    lub TopSumInfo _ = TopSumInfo
    lub _ TopSumInfo = TopSumInfo
    lub (SumInfo con1 lat1) (SumInfo con2 lat2)
        | con1 == con2
        = SumInfo con1 (lub lat1 lat2)
        | otherwise = TopSumInfo

data ProdInfo = BotProdInfo | FieldProdInfo [EnterLattice] | TopProdInfo deriving Eq

instance Lattice ProdInfo where
    bot = BotProdInfo
    top = TopProdInfo

    glb = panic "Not used"

    lub BotProdInfo x = x
    lub x BotProdInfo = x
    lub (FieldProdInfo fields1) (FieldProdInfo fields2)
        = FieldProdInfo (zipWith lub fields1 fields2)
    lub TopProdInfo _ = TopProdInfo
    lub _ TopProdInfo = TopProdInfo

instance Outputable ProdInfo where
    ppr BotProdInfo = text "p _|_"
    ppr TopProdInfo = text "p  T "
    ppr (FieldProdInfo fields) = text "p" <+> ppr fields

{- |

Lattice of roughly this shape:

              Top
               |
           LatUnknown
           |        |
          / \       |
    LatProd LatSum  |
         |   |      |
       LatUndet    /
               \  /
                Bot

LatUnknown represents things over which we can't know anything but their enter behaviour.
LatUndet represents cases where we haven't been able to compute field information yet.

Prod/Sum tell us something about the values returned.

LatUndet/Unknown allows us to differentiate between lack of
information about returned values from "uncomputeable" field information.



-- TODO:

f x = case x of
    C1 _ -> e1
    C2 p -> f p
    C3 _ -> e3

The information for f is determined by [f] = lub [e1] [f] [e3]

-}


data EnterLattice
    = Bot -- Things we can't say anything about (yet)

    -- | At most we can say something about the tag of the value itself.
    --   The fields are obscured (eg imported ids).
    | LatUnknown !EnterInfo

    -- | We know something about the value itself, and we can find out more
    -- about it's return values as well.
    | LatUndet !EnterInfo

    | LatProd !EnterInfo !ProdInfo
    -- ^ This cross product allows us to represent all but sum types
    -- * For things without contents (eg Bool) we have @LatProd tag [].
    -- * For things for which we care not about the outer tag (unboxed tuples)
    --   we ignore it.
    -- * For things where we care about both (tag and fields)
    --   like:  y = True; x = Just y
    --   we get for x:
    --   LatProd NeverEnter [LatProd NeverEnter []]

    | LatSum !EnterInfo !SumInfo

    | Top
                deriving (Eq)

-- | Get the (outer) EnterInfo value
getOuter :: EnterLattice -> EnterInfo
getOuter Bot = bot
getOuter (LatUndet x) = x
getOuter (LatUnknown x) = x
getOuter (LatProd x _) = x
getOuter (LatSum x  _) = x
getOuter Top = top



instance Outputable EnterLattice where
    ppr Bot = text "_|_"
    ppr Top = text "T"
    ppr (LatUnknown outer) = ppr outer
    ppr (LatUndet   outer) = ppr outer <+> text "undet"
    ppr (LatProd outer inner) =
        ppr outer <+> (ppr inner)
    ppr (LatSum outer inner) =
        ppr outer <+> (ppr inner)

instance Lattice EnterLattice where
    bot = Bot
    top = Top

    glb = panic "glb not implemented"


    lub Top _ = Top
    lub _ Top = Top
    lub Bot y = y
    lub x Bot = x

    -- Compare LatUnknown to remaining constructors
    lub (LatUnknown outer1) (LatProd outer2 _)
        = LatUnknown (lub outer1 outer2)
    lub (LatProd outer1 _) (LatUnknown outer2)
        = LatUnknown (lub outer1 outer2)

    lub (LatUnknown outer1) (LatSum outer2 _)
        = LatUnknown (lub outer1 outer2)
    lub (LatSum outer1 _) (LatUnknown outer2)
        = LatUnknown (lub outer1 outer2)

    lub (LatUnknown o1) (LatUnknown o2)
        = LatUnknown (lub o1 o2)

    lub (LatUnknown o1) (LatUndet o2) = LatUnknown (lub o1 o2)
    lub (LatUndet o1) (LatUnknown o2) = LatUnknown (lub o1 o2)

    -- Compare LatUndet to remaining constructors
    lub (LatUndet o1) (LatUndet o2)
        = LatUndet (lub o1 o2)

    lub (LatUndet o1) (LatSum o2 fs1) = LatSum (lub o1 o2) (fs1)
    lub (LatSum o1 fs1) (LatUndet o2)  = LatSum (lub o1 o2) (fs1)

    lub (LatUndet o1) (LatProd o2 fs1) = LatProd (lub o1 o2) (fs1)
    lub (LatProd o1 fs1) (LatUndet o2)  = LatProd (lub o1 o2) (fs1)

    -- Compare LatProd/LatSum
    lub (LatProd outer1 inner1) (LatProd outer2 inner2) =
        LatProd (lub outer1 outer2) (lub inner1 inner2)

    lub (LatSum outer1 fields1) (LatSum outer2 fields2)
        = LatSum (lub outer1 outer2) (lub fields1 fields2)

    lub (LatProd o1 _ ) (LatSum o2 _) =
        LatUnknown (lub o1 o2)
        -- TODO: This should only occure because of shadowing
        -- which we can work around.
        -- panic "Comparing sum with prod type"
    lub (LatSum o1 _) (LatProd o2 _ ) =
        LatUnknown (lub o1 o2)
        -- panic "Comparing sum with prod type"

flatLattice :: EnterInfo -> EnterLattice
flatLattice x = LatUnknown x

setOuterInfo :: EnterLattice -> EnterInfo -> EnterLattice
setOuterInfo lat info =
    case lat of
        Bot ->  LatUndet info
        LatUndet _ ->  LatUndet info
        LatUnknown _ -> LatUnknown info
        LatProd _ fields -> LatProd info fields
        LatSum  _ fields -> LatSum info fields
        Top -> Top

setFieldsToTop :: EnterLattice -> EnterLattice
setFieldsToTop Bot = top
setFieldsToTop (LatUndet x) = LatUnknown x
setFieldsToTop (LatProd x _) = LatUnknown x
setFieldsToTop (LatSum x _) = LatUnknown x
setFieldsToTop (LatUnknown x) = LatUnknown x
setFieldsToTop Top = Top

-- Lookup field info, defaulting towards bot
indexField :: EnterLattice -> Int -> EnterLattice
indexField Bot _ = bot
indexField (LatUndet _) _ = bot
indexField (LatProd _ (FieldProdInfo fields)) n =
    case drop n fields of
        [] -> bot
        (x:_xs) -> x
indexField (LatProd _ BotProdInfo) _ = bot
indexField (LatProd _ TopProdInfo) _ = top

indexField (LatSum _ sum) n
    | SumInfo _con fields <- sum
    = case drop n fields of
        [] -> bot
        (x:_xs) -> x
    | otherwise = bot
indexField Top _ = top
indexField LatUnknown {} _ = top

hasOuterTag :: EnterLattice -> Bool
hasOuterTag (LatUnknown NeverEnter) = True
hasOuterTag (LatProd NeverEnter _) = True
hasOuterTag (LatSum NeverEnter _) = True
hasOuterTag _ = False

-- TODO: Rewrite for early termination.
nestingLevelOver :: EnterLattice -> Int -> Bool
nestingLevelOver _ 0 = True
nestingLevelOver (LatProd _ (FieldProdInfo fields)) n
    = any (`nestingLevelOver` (n-1)) fields
nestingLevelOver (LatSum _ (SumInfo _ fields)) n
    = any (`nestingLevelOver` (n-1)) fields
nestingLevelOver _ _ = False

-- Constraints we aim to resolve.
{-

    Assumptions made:
        * StgApp is always fully applied
        * Now shadowing - currently not guaranted will fix later.

    Binds, top level and otherwise are implemented by nodeBind
    ========================================================
    [NonRec x rhs]
        => tag[x] = tag[rhs]

    Rec [(x1,rhs1), (x2,rhs2), ... ]]
        => tag[x1] = tag[rhs1]
           tag[x2] = tag[rhs2]
           ...

    Rhss are implemented by nodeRhs
    ========================================================

    -- This is the general case for constructors without
    -- strict fields. They will always be tagged.

    rhs@[RhsCon con args], noneMarkedStrict args
        => tag[rhs] = (NeverEnter, map tag args)

    -- The special case for constructors with strict fields.
    -- This works fine, but it requires us to reliable detect
    -- non-tagged cases in the arguments, or we might infer
    -- SP !x !x; .. SP <undet> <tagged> as tagged.

    rhs@[RhsCon con args], strictLub@(strictArgs args)
        => tag[rhs] = (strictLub, map tag args)

    -- Closures always need to be entered. Their nested enterInfo
    -- is determined by the closure body.
    rhs@[RhsClosure args body]
        => tag[rhs] = (NeedsEnter, fieldsOf(tag body))

    -- Not implemented:
    -- We can mark closures with arity > 1 as NeverEnter.
    -- If they are not applied to arguments they in fact are never entered.
    -- We just have to be sure to properly deal with the applied case.

    Expressions:
    ========================================================

    -- Unsure, but likely doesn't matter
    [StgOpApp]
        => (MayEnter, top)

    -- Proper STG doesn't contain lambdas.
    [StgLam]
        => panic

    -- Let's just flow along
    [StgLet bnd body]
        => tag[body]

    -- Let's just flow along
    [StgLetNoEscape bnd body]
        => tag[body]

    -- Literal expressions never require entering.
    [StgLit]
        => tag[StgLit] = (NeverEnter, top)

    Function application
    --------------------------------------------------------

    -- AppAbsent
    -- The result does not need to be entered if it's an application of
    -- absentError
    app@[StgApp f _], f == absentError
        => tag[app] = (NeverEnter, top)

    -- AppRec:
    -- In the recursive case, the app gives us no new information,
    -- but does not constrain us either.
    app@[StgApp f _], hasEnv[letrec f = @rhs(... app ...)]
        => tag[app] = tag[rhs]

    AppDefault
    -- If f represents a constructor we want to avoid entering,
    -- but we need to force entering if it's not. However this
    -- is already set in the rhs rules so we just pass it along.
    app@[StgApp f []]
        => tag[app] = tag f

    -- The result is tagged if the function returns a tagged arguments.
    [StgApp f []]
        => fun_out[ [StgApp f []] ] = tag[f]

    conApp@[StgConApp con args]
        => tag[conApp] = (NeedsEnter, map tag args)

    -- This constraint is currently disabled.
    conApp@[StgConApp con [arg1,arg2,argi,... argn], hasCtxt[letrec argi = ...]
        => tag[argi] = (enterInfo arg1, top)

    Subparts of case expressions
    --------------------------------------------------------

    -- Cases are one of the harder parts.
    -- The lower bound of the alts determine the expressions tag
    case@[StgCase scrut bndr alts]
        => tag[case] = lub alts

    -- The case binder is never entered
    [StgCase scrut bndr alts]
        => tag [bndr] = (NeverEnter, fields scrut)

    -- Alternative results are determined from their rhs
    alt@[StgAlt con bnds expr]
        => tag[alt] = tag expr

    -- Strict fields are tagged and as such need not be entered.
    alt@[StgAlt con [b1,b2,..bn] expr], strictField bi, hasEnv[case scrut of ... alt, ...]
            => tag[bi] = (NeverEnter, fields scrut !! i)

------------------------------------------------------

Implementation considerations:
We want to create a data flow graph for all of the above.

* We only care about results of let-bound ids
* This means we can map all outputs we care about via a map over Id
* We do however have other graph nodes
* We can map these via Uniques so we can update them.

Each flow node carries:
* Input dependencies
* It's id
* It's result (Or should it be put in a seperate map?)

We generate the flow graph by traversing over the Stg code (once)
and building up the nodes.

Then we calculate the fixpoint.

In the last step we transfer back the information gained from the analysis.

For now generate one node per rule.
We could common up some of these though for performance.

-}

-- | Nodes identified by their id have the result mapped back the STG
--   all other nodes get an unique and are only there for the analysis.
--   We also map certain ids to uniqe based id's if they might be shadowed.
data NodeId
    = BoundId !Id
    | UniqId  !Unique
    | ConstId !Int
    deriving (Eq)

instance Ord NodeId where
    compare = comparing comparingHelper

instance Outputable NodeId where
    ppr (BoundId i) = char 'v' <-> ppr i
    ppr (UniqId  i) = char 'u' <-> ppr i
    ppr (ConstId i) = char 'c' <-> ppr i


comparingHelper :: NodeId -> (Int,Int)
comparingHelper (ConstId i) = (1, i)
comparingHelper (BoundId id) = (2,getKey $ getUnique  id)
comparingHelper (UniqId u) = (3,getKey u)

data FlowState
    = FlowState
    { fs_iteration :: !Int -- ^ Current iteration
    , fs_us :: !UniqSupply
    , fs_idNodeMap :: !(UniqFM FlowNode) -- ^ Map from let bounds ids to their defining node
    , fs_uqNodeMap :: !(UniqFM FlowNode) -- ^ Transient results
    , fs_constNodeMap :: !(IM.IntMap FlowNode) -- ^ Non-updating nodes
    , fs_doneNodes :: !(M.Map NodeId FlowNode) -- ^ We can be sure these will no longer change.
    }

-- getNodeIdMap :: FlowState -> NodeId -> UniqFM FlowNode
-- getNodeIdMap s (Left uq) = fs_uqNodeMap s
-- getNodeIdMap s (Right v) = fs_idNodeMap v

-- putNodeIdMap :: NodeId -> UniqFM FlowNode -> FlowState
-- putNodeIdMap (Left uq) map = s {fs_uqNodeMap = map}
-- putNodeIdMap (Right v) map = s {fs_idNodeMap = map}


type AM = State FlowState

instance MonadUnique AM where
    getUniqueSupplyM = do
        s <- get
        let (us1,us2) = splitUniqSupply $ fs_us s
        put $ s {fs_us = us1}
        return us2
    getUniqueM = do
        s <- get
        let (u,us) = takeUniqFromSupply $ fs_us s
        put $! s {fs_us = us}
        return u

addNode :: FlowNode -> AM ()
addNode node = do
    s <- get
    -- TODO: Assert node doesn't exist
    let s' = case node_id node of
                UniqId uq -> s { fs_uqNodeMap = addToUFM (fs_uqNodeMap s) uq node }
                BoundId v -> s { fs_idNodeMap = addToUFM (fs_idNodeMap s) v  node }
                ConstId i -> s { fs_constNodeMap = IM.insert i node (fs_constNodeMap s) }
    put s'

-- | Move the node from the updateable to the finished set
markDone :: FlowNode -> AM ()
markDone node = do
    case node_id node of
        ConstId id -> do
            s <- get
            let s' = s  { fs_constNodeMap = IM.insert id node (fs_constNodeMap s) }
            put s'
        BoundId id -> do
            s <- get
            let s' = s  { fs_idNodeMap = delFromUFM (fs_idNodeMap s) id
                        , fs_doneNodes = M.insert (BoundId id) node (fs_doneNodes s) }
            put s'
        UniqId uq -> do
            s <- get
            let s' = s  { fs_uqNodeMap = delFromUFM (fs_uqNodeMap s) uq
                        , fs_doneNodes = M.insert (UniqId uq) node (fs_doneNodes s) }
            put s'

isMarkedDone :: NodeId -> AM Bool
isMarkedDone (ConstId _) = return True
isMarkedDone id = M.member id . fs_doneNodes <$> get

updateNode :: NodeId -> EnterLattice -> AM ()
updateNode id !result = do
    -- TODO: Assert node is not done yet
    node <- getNode id
    addNode $! node {node_result = result}


getNode :: NodeId -> AM FlowNode
getNode node_id = do
    s <- get
    let m_done = M.lookup node_id (fs_doneNodes s)

    case m_done of
        Just node -> return $ node
        Nothing -> return $ case node_id of
                        UniqId uq -> fromMaybe (panic "getNodeUq"       $ ppr node_id) $ lookupUFM  (fs_uqNodeMap s) uq
                        BoundId v -> fromMaybe (pprPanic "getNodeId"    $ ppr node_id) $ lookupUFM  (fs_idNodeMap s) v
                        ConstId i -> fromMaybe (pprPanic "getNodeConst" $ ppr node_id) $ IM.lookup  i (fs_constNodeMap s)

-- | Loke node_result <$> getNode but defaults to bot
-- for non-existing nodes
lookupNodeResult :: NodeId -> AM EnterLattice
lookupNodeResult node_id = do
    s <- get
    let result = (M.lookup node_id (fs_doneNodes s)) <|>
                 (lookupNode s node_id)
    case result of
        Just r  -> return $ node_result r
        Nothing -> pprPanic "No node created for " (ppr node_id)
                   --return $ top -- We know we know nothing
    where
        lookupNode :: FlowState -> NodeId -> (Maybe FlowNode)
        lookupNode s node_id =
                case node_id of
                    UniqId uq -> lookupUFM  (fs_uqNodeMap s) uq
                    BoundId v -> lookupUFM  (fs_idNodeMap s) v
                    ConstId i -> IM.lookup  i (fs_constNodeMap s)

getArgNodeId :: [SynContext] -> StgArg -> NodeId
getArgNodeId _    (StgLitArg _ ) = litNodeId
getArgNodeId ctxt (StgVarArg v ) = mkIdNodeId ctxt v

-- -- | Creates a node which takes the result of id
-- -- if available, a default value otherwise.
-- mkIndDefaultNode :: NodeId -> AM NodeId
-- mkIndDefaultNode indirectee = do
--     node_id <- mkUniqueId

--     let updater = do
--             result <- lookupNodeResult indirectee
--             updateNode node_id result
--             return result

--     addNode FlowNode
--         { node_id = node_id, node_inputs = [indirectee]
--         , node_result = Bot, node_update = updater
--         , node_desc = text "ind" }

--     return node_id





data FlowNode
    = FlowNode
    { node_id :: !NodeId -- ^ Node id
    , node_inputs :: [NodeId]  -- ^ Input dependencies
    , node_result :: !(EnterLattice) -- ^ Cached result
    , node_update :: (AM EnterLattice) -- ^ Calculates a new value for the node
                                       -- AND updates the environment with it.
    -- , node_updated :: Int -- ^ Latest iteration in which the node was updated.
    --                       -- ^ Zero implies it never was
    , node_desc :: !SDoc -- ^ Debugging purposes
    -- ^ Calculate result, update node in environment.
    }

instance Outputable FlowNode where
    ppr node =
        text "node_" <> (node_desc node) <> char '_' <>
            pprId node <> (ppr $ node_inputs node) <>
            parens (ppr (node_result node)  )
      where
        pprId node =
            case node_id node of
                UniqId uq -> text "u_" <> ppr uq
                BoundId v -> text "v_" <> ppr v
                ConstId i -> text "c_" <> ppr i

data SynContext
    = CLetRec [Id]
    | CClosure [(Id,NodeId)] -- Args of the closure mapped to nodes
    | CTopLevel
    | CNone -- ^ No Context given
    deriving Eq

hasLetRecId :: [SynContext] -> Id -> Bool
hasLetRecId ctxt id =
        findLetRec ctxt
    where
        findLetRec [] = False
        findLetRec ((CLetRec ids):todo)
            | id `elem` ids = True
        findLetRec (_:todo) = findLetRec todo


-- | Lub between all input node
mkLubNode :: [NodeId] -> AM NodeId
mkLubNode inputs = do
    node_id <- mkUniqueId

    let updater = do
            input_results <- mapM lookupNodeResult inputs
            let result = foldl1 lub input_results
            updateNode node_id result
            return result

    addNode $ FlowNode { node_id = node_id, node_result = bot
                       , node_inputs = inputs
                       , node_update = updater, node_desc = text "lub" }
    return node_id

-- | Take a lattice argument per constructor argument to simplify things.
mkConLattice :: DataCon -> EnterInfo -> [EnterLattice] -> EnterLattice
mkConLattice con outer fields
    | conCount == 1 = LatProd outer (FieldProdInfo fields)
    | conCount > 1
    = LatSum outer (SumInfo con fields)
    | otherwise = panic "mkConLattice"
  where
    conCount = length (tyConDataCons $ dataConTyCon con)

{-# NOINLINE findTags #-}
findTags :: UniqSupply -> [StgTopBinding] -> ([StgTopBinding], UniqFM FlowNode)
findTags us binds =
    let state = FlowState 0 us emptyUFM emptyUFM mempty mempty
    -- Run the analysis, extract only info about id-bound nodes
        result = (flip runState) state $ do
            -- pprTraceM "FindTags" empty
            addConstantNodes
            nodesTopBinds binds
            nodes <- solveConstraints
            -- mapM_ (pprTraceM "res:" . ppr) nodes
            -- pprTraceM "Result nodes" $ vcat (map ppr nodes)
            return $ binds
    in second fs_idNodeMap result

-- Constant mappings
addConstantNodes :: AM ()
addConstantNodes = do
    addNode $ mkConstNode taggedBotNodeId (flatLattice NeverEnter)
    addNode litNode
    markDone $ mkConstNode botNodeId Bot
    addNode $ mkConstNode topNodeId Top

mkConstNode :: NodeId -> EnterLattice -> FlowNode
mkConstNode id val = FlowNode id [] val (return $ val) (text "const")

-- We don't realy do anything with literals, but for a uniform approach we
-- map them to (NeverEnter x Bot)
taggedBotNodeId, litNodeId :: NodeId
taggedBotNodeId = ConstId 1
litNodeId       = ConstId 2
botNodeId       = ConstId 3 -- Always returns bot
topNodeId       = ConstId 4

litNode :: FlowNode
litNode = (mkConstNode litNodeId (flatLattice NeverEnter)) { node_desc = text "lit" }

{-# NOINLINE nodesTopBinds #-}
nodesTopBinds :: [StgTopBinding] -> AM [StgTopBinding]
nodesTopBinds binds = mapM (nodesTop) binds

nodesTop :: StgTopBinding -> AM StgTopBinding
-- Always "tagged"
nodesTop bind@(StgTopStringLit v _str) = do
    let node = mkConstNode (mkIdNodeId [CTopLevel] v) (flatLattice NeverEnter)
    markDone node
    return $ bind
nodesTop      (StgTopLifted bind)  = do
    nodesBind [CTopLevel] bind
    return $ (StgTopLifted bind)

nodesBind :: [SynContext] -> StgBinding -> AM ()
nodesBind ctxt (StgNonRec v rhs) = do
    nodeBind ctxt v rhs
nodesBind ctxt (StgRec binds) = do
    let boundIds = map fst binds
    let ctxt' = (CLetRec boundIds) : ctxt
    mapM_ (uncurry (nodeBind ctxt')) binds

nodeBind :: [SynContext] -> Id -> StgRhs -> AM ()
nodeBind ctxt id rhs = do
    nodeRhs ctxt id rhs

-- | This adds nodes with information we can figure out about imported ids.
--   Mimics what we do in StgCmmClosure.hs:mkLFImported
addImportedNode :: Id -> AM ()
addImportedNode id = do
    idMap <- fs_idNodeMap <$> get
    case lookupUFM idMap id of
        Just _ -> return ()
        Nothing
            | not (isGlobalId id)
            -> return ()

            -- Functions are tagged with arity and never entered as atoms
            | idFunRepArity id > 0
            -> markDone $ mkConstNode node_id (flatLattice NeverEnter)

            -- Known Nullarry constructors are also never entered
            | Just con <- (isDataConWorkId_maybe id)
            , isNullaryRepDataCon con
            -> markDone $ mkConstNode node_id (flatLattice NeverEnter)

            -- May or may not be entered.
            | otherwise
            -> markDone $ mkConstNode node_id (flatLattice MaybeEnter)


  where
    node_id = (mkIdNodeId [CNone] id)




-- | When dealing with a let bound rhs passing the id in allows us the shortcut the
--  the rule for the rhs tag to flow to the id
nodeRhs :: [SynContext] -> Id -> StgRhs -> AM ()
nodeRhs ctxt binding (StgRhsCon _ccs con args)  = do
    mapM addImportedNode [v | StgVarArg v <- args]
    let node_id = mkIdNodeId ctxt binding
    let node = FlowNode { node_id = node_id
                        , node_inputs = node_inputs
                        , node_result = bot
                        , node_update = node_update node_id
                        , node_desc   = text "rhsCon"
                        }
    if null args
        then markDone node
        else addNode node
  where
    node_inputs = map (getArgNodeId ctxt) args :: [NodeId]
    banged_inputs = getStrictConArgs con node_inputs
    node_update this_id = do
        fieldResults <- zip node_inputs <$> mapM lookupNodeResult node_inputs
        let strictResults = map snd $ getStrictConArgs con fieldResults
        let strictFieldLub = foldl' lub bot $ map getOuter strictResults
        -- foldl' lub bot strictResults
        -- pprTraceM "RhsCon" (ppr con <+> ppr this_id <+> ppr fieldResults)
        -- Rule 2
        let outerTag
                | null banged_inputs
                = NeverEnter
                -- If any of the inputs are undetermined so is the output,
                -- if any of the inputs require entering or can't be reasoned
                -- about well then the same is true about this con.
                | otherwise
                = strictFieldLub

        let result = mkConLattice con outerTag (map snd fieldResults)
        updateNode this_id result
        return $ result

nodeRhs ctxt binding (StgRhsClosure _ext _ccs _flag args body) = do
    let arg_nodes = zip args (repeat topNodeId) :: [(Id, NodeId)]
    let ctxt' = (CClosure arg_nodes):ctxt
    -- TODO: Take into acount args somehow
    body_id <- nodeExpr ctxt' body

    let node_id = mkIdNodeId ctxt binding
    let node_inputs = body_id : (map snd arg_nodes)
    let node = FlowNode { node_id = node_id
                        , node_inputs = node_inputs
                        , node_result = bot
                        , node_update = node_update node_id body_id
                        , node_desc   = text "rhsClosure"
                        }
    addNode node

    return ()


  where
    node_update this_id body_id= do
        -- pprTraceM "UpdateClosure1" $ ppr body_id

        -- In case we have:
        -- f x = x we end up without a node for the argument
        bodyInfo <- lookupNodeResult body_id
        -- pprTraceM "UpdateClosure2" $ ppr body_id

        let result = setOuterInfo bodyInfo NeedsEnter
        updateNode this_id result
        return result

-- If the id is the argument of a closure we
-- set it to top as we don't analyze closure arguments currently.
mkIdNodeId :: [SynContext] -> Id -> NodeId
mkIdNodeId ctxt id = -- BoundId id
        findMapping ctxt
    where
        findMapping [] = BoundId id
        findMapping ((CClosure args):todo)
            -- While traversing the AST when we enter a closure
            -- with arguments we map the arguments to dummy nodes already.
            -- We look these up here.
            | Just uid <- lookup id args = uid
        findMapping (_:todo) = findMapping todo


mkUniqueId :: AM NodeId
mkUniqueId = UniqId <$> getUniqueM

nodeExpr :: [SynContext] -> StgExpr -> AM NodeId
nodeExpr ctxt (e@StgCase {})          = nodeCase ctxt e
nodeExpr ctxt (e@StgLet {})           = nodeLet ctxt e
nodeExpr ctxt (e@StgLetNoEscape {})   = nodeLetNoEscape ctxt e
nodeExpr ctxt (StgTick t e)           = nodeExpr ctxt e
nodeExpr ctxt e@(StgConApp _con _args _tys) = nodeConApp ctxt e

nodeExpr ctxt e@(StgApp _ f args)      = do
    mapM addImportedNode [v | StgVarArg v <- args]
    addImportedNode f
    nodeStgApp ctxt e
nodeExpr ctxt e@(StgLit _lit)            = nodeLit ctxt e
nodeExpr ctxt e@(StgOpApp _op _args _ty) = nodeOpApp ctxt e
nodeExpr ctxt  (StgLam {}) = error "Invariant violated: No lambdas in STG representation."

nodeCase ctxt (StgCase scrut bndr alt_type alts) = do
    -- pprTraceM "NodeCase" $ ppr bndr
    scrutNodeId <- nodeExpr ctxt scrut

    altNodeIds <- mapM (nodeAlt ctxt scrutNodeId) alts

    mkCaseBndrNode scrutNodeId bndr

    altsId <- mkLubNode altNodeIds

    -- pprTraceM "Scrut, alts, rhss" $ ppr (scrut, scrutNodeId, altNodeIds, altsId)

    return altsId

  where
    mkCaseBndrNode scrutNodeId bndr = do
        let node_inputs = [scrutNodeId]
        addNode $ FlowNode  { node_id = bndrId, node_inputs = [scrutNodeId]
                            , node_result = bot, node_update = updater
                            , node_desc = text "caseBndr" }
      where
        bndrId = mkIdNodeId ctxt bndr
        -- Take the result of the scrutinee and throw an other tag on it.
        updater = do
            -- We don't create nodes for closure arguments, so they might
            -- be undefined
            scrutResult <- lookupNodeResult scrutNodeId
            let result = setOuterInfo scrutResult NeverEnter
            updateNode bndrId result
            return result

    node_update this_id = do
        let result = flatLattice UndetEnterInfo
        updateNode this_id result
        return result
nodeCase _ _ = panic "Impossible: nodeCase"

-- TODO: Shadowing is possible here for the alt bndrs
nodeAlt :: [SynContext] -> NodeId -> StgAlt -> AM NodeId
nodeAlt ctxt scrutNodeId (altCon, bndrs, rhs)
  | otherwise = do
    zipWithM mkAltBndrNode [0..] bndrs

    rhs_id <- nodeExpr ctxt rhs
    return rhs_id

    where
        -- TODO: These are always tagged
        strictBnds
          | DataAlt con <- altCon
          = getStrictConFields con bndrs
          | otherwise = []

        mkAltBndrNode n bndr
          | isUnliftedType bndrTy
          , not (isUnboxedTupleType bndrTy)
          , not (isUnboxedSumType bndrTy)
          = do
                let node_id = mkIdNodeId ctxt bndr
                addNode litNode { node_id = node_id }
                return node_id
          | otherwise = do
                let node_id = mkIdNodeId ctxt bndr
                let updater = do
                        scrut_res <- lookupNodeResult scrutNodeId
                        let res
                                | elem bndr strictBnds
                                -- Tag things coming out of strict binds
                                = setOuterInfo (indexField scrut_res n) NeverEnter
                                | otherwise = indexField scrut_res n

                        updateNode node_id res
                        return res
                addNode FlowNode
                    { node_id = node_id
                    , node_result = bot
                    , node_inputs = [scrutNodeId]
                    , node_update = updater
                    , node_desc = text "altBndr" <-> ppr altCon <-> ppr strictBnds }
                return node_id
            where
                bndrTy = idType bndr

(<->) :: SDoc -> SDoc -> SDoc
(<->) a b = a <> char '_' <> b

nodeLet :: [SynContext] -> StgExpr -> State FlowState NodeId
nodeLet ctxt (StgLet _ bind expr) = do
    nodesBind ctxt bind
    nodeExpr ctxt expr

nodeLetNoEscape ctxt (StgLetNoEscape _ bind expr) = do
    nodesBind ctxt bind
    nodeExpr ctxt expr

nodeConApp ctxt (StgConApp con args tys) = do
    -- pprTraceM "ConApp" $ ppr con <+> ppr args
    mapM_ addImportedNode [v | StgVarArg v <- args]
    node_id <- mkUniqueId
    let inputs = map (getArgNodeId ctxt) args :: [NodeId]
    -- let recInputs = map (getArgNodeId ctxt . StgVarArg) .
    --                 filter (ctxt `hasLetRecId`) $
    --                 [v | StgVarArg v <- args]

    let updater = do
            fields <- mapM getField inputs :: AM [EnterLattice]
            -- Todo: When an *expression* returns a value the outer tag
            --       is not really defined.
            let result = mkConLattice con top fields
            -- pprTraceM "Update conApp" $ ppr (con, args, fields, result)
            updateNode node_id result
            return result
                where
                    getField input_id
                        -- | elem input_id recInputs
                        -- , pprTrace "recCon" (ppr input_id) True
                        -- = setFieldsToTop <$> lookupNodeResult input_id
                        | otherwise = lookupNodeResult input_id

    addNode FlowNode
        { node_id = node_id, node_result = bot
        , node_inputs = inputs
        , node_update = updater
        , node_desc = text "conApp"
        }

    return node_id

nodeStgApp ctxt (StgApp _ f args) = do
    -- pprTraceM "App" $ ppr f <+> ppr args
    node_id <- mkUniqueId
    let function_id = mkIdNodeId ctxt f

    let updater = do
            -- Try to peek into the function
            result <-
                case () of
                    _   -- Rule AppAbsent
                        | (idUnique f == absentErrorIdKey)
                        -> return $ flatLattice NeverEnter

                        -- Rule AppRec
                        | isRecursiveCall ctxt -> lookupNodeResult function_id

                        -- AppDefault
                        | otherwise -> do
                            lookupNodeResult function_id
            -- pprTraceM "AppFields" $ ppr (f, func_lat)
            -- let result = setOuterInfo func_lat BotEnterInfo
            when (nestingLevelOver result 5) $ do
                pprTraceM "Limiting nesting for " (ppr node_id)
                node <- getNode node_id
                addNode $ node { node_update = return result }
            updateNode node_id result
            return result

    addNode FlowNode
        { node_id = node_id, node_result = Bot
        , node_inputs = [function_id]
        , node_update = updater
        , node_desc = text "app"
        }

    return node_id
    where
        isRecursiveCall [] = False
        isRecursiveCall ((CLetRec ids) : todo) | f `elem` ids = True
        isRecursiveCall (_ : todo) = isRecursiveCall todo


-- Do we need rules here?
nodeLit ctxt (StgLit lit) = return $ litNodeId

nodeOpApp ctxt (StgOpApp op args res_ty) = do
    -- pprTraceM "OpApp" $ ppr args
    return $ topNodeId







solveConstraints :: AM [FlowNode]
solveConstraints = do
        iterate 1
        idList <- map snd . nonDetUFMToList . fs_idNodeMap <$> get
        uqList <- map snd . nonDetUFMToList . fs_uqNodeMap <$> get
        doneList <- map snd . M.toList . fs_doneNodes <$> get

        pprTraceM "ListLengthsFinal" $ ppr (length idList, length uqList, length doneList)
        return $ idList ++ uqList ++ doneList
  where
    iterate :: Int -> AM ()
    iterate n = do
        pprTraceM "iterate - pass " (ppr n)
        idList <- map snd . nonDetUFMToList . fs_idNodeMap <$> get
        uqList <- map snd . nonDetUFMToList . fs_uqNodeMap <$> get

        doneList <- map snd . M.toList . fs_doneNodes <$> get
        pprTraceM "ListLengthsPass" $ ppr (length idList, length uqList, length doneList)

        progress <- liftM2 (||) (update n idList False) (update n uqList False)
        if (not progress)
            then return ()
            else if (n > 5)
                then pprTraceM "Warning:" (text "Aborting at" <+> ppr n <+> text "iterations")
                else iterate (n+1)

    update :: Int -> [FlowNode] -> Bool -> AM Bool
    update n []           progress = return $ progress
    update n (node:todo)  progress = do
        -- pprTraceM "update:" $ ppr (node_id node) <+> (node_desc node)
        let old_result = node_result node
        -- node_update also updates the environment
        result <- node_update node
        if (result == old_result)
            -- Nothing to do this round
            then update n todo progress
            else do
                done <- and <$> (mapM isMarkedDone (node_inputs node))
                when done (markDone (node { node_result = result }))
                -- pprTraceM "Updated:" (ppr node)
                -- pprTraceM "Updated:" (text "old:" <> ppr old_result <+> ppr node)
                -- pprTraceM "Updated:" (ppr (node_id node) <+> (node_desc node))
                when (mod n     1000 == 0) $ pprTraceM "Node:" (ppr node)
                update n todo True


