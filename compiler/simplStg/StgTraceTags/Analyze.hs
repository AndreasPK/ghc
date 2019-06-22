--
-- Copyright (c) 2019 Andreas Klebinger
--

{-# LANGUAGE CPP, TypeFamilies, RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs, TupleSections #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}

{-# OPTIONS_GHC -O -fprof-auto #-}

-- (findTags, nodesTopBinds)
module StgTraceTags.Analyze (findTags, FlowNode(..), NodeId(..), hasOuterTag) where

#include "HsVersions.h"

import GhcPrelude

import BasicTypes
import DataCon
import Data.Bifunctor
import Id
import StgSyn hiding (AlwaysEnter)
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

import Module
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
import qualified EnumSet as ES
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Util
import MonadUtils (whenM)
import Data.Ord (comparing)

import State
import Maybes
import Data.Foldable
import Control.Applicative hiding (empty)

import StgSubst

data RecursionKind
    = SimpleRecursion
    -- ^ Simple direction recursion of the (syntactic) form
    --   let f x = ... if cond then e' else f x'

    | OtherRecursion
    -- ^ All other kinds
    | NoRecursion
    deriving Eq

isSimpleRecursion SimpleRecursion   = True
isSimpleRecursion _                 = False

{- Note [Dealing with function arguments]

Given a closure which returns it's argument
or whos return value depends on it's argument how should we proceed?

For example consider these functions:
    f1 x y =
        ... -> (x,y)

    f2 x =
        case x of
            C a1 a2 -> (a1,a2)

We approach this by creating (potentially) multiple nodes per closure.
Each node assumes a certain tag info about it's arguments.

At call sites we then try to look up the appropriate node, defaulting
towards top for missing variants.

This allows performance tuning in a few ways:
a) We can limit us to a single node for closures with a lot of arguments.
b) We can make this dependent on optimization flags.
c) We can limit this to exploring the arguments which are likely to matter.

-}

class Lattice a where
    bot :: a
    glb :: a -> a -> a
    lub :: a -> a -> a
    top :: a


-- | Enterinfo for a binding IF IT USED AS AN UNAPPLIED ATOM.
--   In particular for
--     case (food<NoEnter> ingredients) of ...
--   we WILL need to evaluate food either way.
-- However if an id is determined to be NeverEnter we can say
-- that we can put it directly in strict fields without violating
-- the tagging invariant as well as casing on it as data without entering
-- eg the code:
-- case determineBurger<NoEnter> of
--     CheeseBurger -> e1
--     Regular -> e2
-- does not require us to emite code for entering determineBurger to branch on it's value.
data EnterInfo
    = UndetEnterInfo    -- ^ Not yet determined, happens for rhsCon if we don't
                        --   know if the strict fields are already tagged.
    | AlwaysEnter        -- ^ WILL need to be entered
    | MaybeEnter        -- ^ Could be either
    | NeverEnter        -- ^ Does NOT need to be entered.
    deriving (Eq,Ord,Show,Enum)

instance Outputable EnterInfo where
    ppr UndetEnterInfo    = char '?'
    ppr AlwaysEnter    = text "ent"
    ppr MaybeEnter  = char 'm'
    ppr NeverEnter      = char 't'

{- |
              MaybeEnter
             /    |    \
      AlwaysEnter  |   NeverEnter
             \    |    /
            UndetEnterInfo

-}
instance Lattice EnterInfo where
    bot = UndetEnterInfo
    top = MaybeEnter

    glb = panic "glb not used"

    lub UndetEnterInfo x = x
    lub x UndetEnterInfo = x

    lub AlwaysEnter NeverEnter = MaybeEnter
    lub NeverEnter AlwaysEnter  = MaybeEnter

    lub AlwaysEnter AlwaysEnter = AlwaysEnter
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

instance Ord SumInfo where
    -- TODO: Define comparing for efficiency
    NoSumInfo <= _ = True
    _ <= TopSumInfo = True
    SumInfo con1 lat1 <= SumInfo con2 lat2
        = (dataConTag con1, lat1) <= (dataConTag con2, lat2)

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

data ProdInfo
    = BotProdInfo
    | FieldProdInfo [EnterLattice]
    | TopProdInfo
    deriving (Eq, Ord)

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

-- data FieldInfo
--     = BotFieldInfo | TopFieldInfo
--     | SumF


{- |

Lattice of roughly this shape:

           LatUnknown
           |        |
          / \       |
    LatProd LatSum  |
          |    |    |
           \   |   /
           LatUndet

LatUnknown represents things over which we can't know anything except their enter behaviour.
LatUndet represents cases where we haven't been able to compute field information yet.

Prod/Sum tell us something about the values returned.

LatUndet/Unknown allows us to differentiate between lack of
information about returned values and "uncomputeable" field information.



-- TODO:

f x = case x of
    C1 _ -> e1
    C2 p -> f p
    C3 _ -> e3

The information for f is determined by [f] = lub [e1] [f] [e3]

-}

data EnterLattice
    -- | At most we can say something about the tag of the value itself.
    --   The fields are not yet known.
    --   Semantically: EnterInfo x bot(fields)
    = LatUnknown !EnterInfo

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
    deriving (Eq, Ord)

-- | Get the (outer) EnterInfo value
getOuter :: EnterLattice -> EnterInfo
getOuter (LatUndet x) = x
getOuter (LatUnknown x) = x
getOuter (LatProd x _) = x
getOuter (LatSum x  _) = x



instance Outputable EnterLattice where
    ppr (LatUnknown outer) = ppr outer
    ppr (LatUndet   outer) = ppr outer <+> text "undet"
    ppr (LatProd outer inner) =
        ppr outer <+> (ppr inner)
    ppr (LatSum outer inner) =
        ppr outer <+> (ppr inner)

instance Lattice EnterLattice where
    bot = LatUndet UndetEnterInfo
    top = LatUnknown MaybeEnter

    glb = panic "glb not implemented"

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

-- Lattice when we only know the outer layer.
flatLattice :: EnterInfo -> EnterLattice
flatLattice x = LatUnknown x

undetLattice :: EnterInfo -> EnterLattice
undetLattice = LatUndet

setOuterInfo :: EnterLattice -> EnterInfo -> EnterLattice
setOuterInfo lat info =
    case lat of
        LatUndet _ ->  LatUndet info
        LatUnknown _ -> LatUnknown info
        LatProd _ fields -> LatProd info fields
        LatSum  _ fields -> LatSum info fields

setFieldsToTop :: EnterLattice -> EnterLattice
setFieldsToTop (LatUndet x) = LatUnknown x
setFieldsToTop (LatProd x _) = LatUnknown x
setFieldsToTop (LatSum x _) = LatUnknown x
setFieldsToTop (LatUnknown x) = LatUnknown x

-- Lookup field info, defaulting towards bot
indexField :: EnterLattice -> Int -> EnterLattice
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
indexField LatUnknown {} _ = bot

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

-- Note [Constraints/Rules for tag/enter information]
{-

    Assumptions made:
        * StgApp is always fully applied
        * Now shadowing - currently not guaranted will fix later.

    We use a pseudo syntax allowing both haskell functions and rule info.
    In general:

    * These rules are meant for reference and understanding and reference.
      So please apply common sense when reading them and if they don't match the implementation
      please update them accordingly.
      If you feel inclined to make these more formal then please do so!

    * info[name] = e
        => assign for the node name the value of evaluating e to it's info field.

    * We play loose with expressions but in general they are haskell pseudocode.

    * For each assignment pattern of "<foo>[node]"" we use "foo node" in expressions
      to mean the value foo of node that was assigned in the last iteration.

    * We use 3 main elements of information: info, tag, fields
      * tag says something about the entering behaviour of the node itself
        when cased on.
      * fields says something about the entering behaviour of fields of the node
        when they are bound to case binders.
      * info, for convenience is the tuple of (tag x fields).

    * In the premises of the rules:
        * Generally @ gives AST nodes names.
        * Arguments to ADT constructors are often ommited if not relevant.

    * In some cases syntax is a bit ... ad hoc, but hopefully should be understandable
      from the context.

    * In general rules are not exclusive, so more than one rule might match some
      AST element/node. If in doubt if a rule is exclusive check the implementation.
      (sorry).


    Binds, top level and otherwise are implemented by nodeBind
    ========================================================
    [NonRec x rhs]
        => info[x] = info rhs

    Rec [(x1,rhs1), (x2,rhs2), ... ]]
        => info[x1] = info rhs1
           info[x2] = info rhs2
           ...

    Rhss are implemented by nodeRhs
    ========================================================

    Allocating constructors
    --------------------------------------------------------

    -- This is the general case for constructors without
    -- strict fields. They will always be tagged.

    rhs@[RhsCon con args], noneMarkedStrict args
        => info[rhs] = (NeverEnter, map info args)

    -- The special case for constructors with strict fields.
    -- This works fine, but it requires us to reliable detect
    -- non-tagged cases in the arguments, or we might infer
    -- SP !x !x; .. SP <undet> <tagged> as tagged.

    -- This means we have to take great care  to assign unknown
    -- bindings MaybeEnter.

    rhs@[RhsCon con args], sargs@(strictArgs args)
        => info[rhs] = (lub Tagged sargs, map info args)

    Functions/Closures
    --------------------------------------------------------

    -- Closures always need to be entered. Their nested enterInfo
    -- is determined by the closure body. However we CAN mark them
    -- as no-enter if they take arguments. Because function
    -- applications are always entered when applied to arguments.

    rhs@[RhsClosure args body], null args
        => info[rhs] = (AlwaysEnter, fieldsOf(info body))

    rhs@[RhsClosure args body], not (null args)
        => info[rhs] = (NeverEnter, fieldsOf(info body))


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
        => info body

    -- Let's just flow along
    [StgLetNoEscape bnd body]
        => info body

    -- Literal expressions never require entering.
    [StgLit]
        => info[StgLit] = (NeverEnter, top)

    Function application
    --------------------------------------------------------

    -- AppAbsent
    -- The result does not need to be entered if it's an application of
    -- absentError
    app@[StgApp f _], f == absentError
        => info[app] = (NeverEnter, top)

    -- AppRec:
    -- In the recursive case, the app gives us no new information,
    -- but does not constrain us either.
    app@[StgApp f _], hasEnv[letrec f = @rhs(... app ...)]
        => info[app] = info[rhs]

    AppDefault
    -- We just pass it along.
    app@[StgApp f []]
        => info[app] = info f

    -- The result is tagged if the function returns a tagged arguments.
    [StgApp f []]
        => fun_out[ [StgApp f []] ] = info[f]

    conApp@[StgConApp con args]
        => info[conApp] = (AlwaysEnter, map info args)

    -- This constraint is currently disabled.
    conApp@[StgConApp con [arg1,arg2,argi,... argn], hasCtxt[letrec argi = ...]
        => info[argi] = (enterInfo argi, top)

    Subparts of case expressions
    --------------------------------------------------------

    -- Cases are one of the harder parts.
    -- The lower bound of the alts determine the expressions tag
    case@[StgCase scrut bndr alts]
        => info[case] = lub alts

    -- The case binder is never entered
    [StgCase scrut bndr alts]
        => info [bndr] = (NeverEnter, fields scrut)

    -- Alternative results are determined from their rhs
    alt@[StgAlt con bnds expr]
        => info[alt] = info expr

    -- Strict fields are tagged and as such need not be entered.
    alt@[StgAlt con [b1,b2,..bn] expr], strictField bi, hasEnv[case scrut of ... alt, ...]
            => info[bi] = (NeverEnter, fields scrut !! i)

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
    { fs_mod :: !Module
    , fs_iteration :: !Int -- ^ Current iteration
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

-- | Loke node_result <$> getNode but defaults to bot
-- for non-existing nodes
lookupNodeResultOuter :: NodeId -> AM EnterLattice
lookupNodeResultOuter node_id = do
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

-- | If we use a *function* as an unapplied argument to a constructor we throw
-- away nested information and make do with NeverEnter Top for now.
getConArgNodeId :: [SynContext] -> StgArg -> NodeId
getConArgNodeId _    (StgLitArg _ ) = litNodeId
getConArgNodeId ctxt (StgVarArg v )
    -- | pprTrace "getArgNodeId"
    --     (   ppr v <+>
    --         text "arity" <+>
    --         ppr (idArity v) <+>
    --         text "type" <+>
    --         ppr (idType v)
    --     )
    --     False
    -- = undefined
    | isFunTy (unwrapType $ idType v)
    = neverNodeId
    | otherwise
    = mkIdNodeId ctxt v

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
        hang
            (text "node_" <> (node_desc node) <> char '_' <> pprId node)
            2
            ( (ppr $ node_inputs node) <> parens (ppr $ node_result node) )
      where
        pprId node =
            case node_id node of
                UniqId uq -> text "u_" <> ppr uq
                BoundId v -> text "v_" <> ppr v
                ConstId i -> text "c_" <> ppr i

data SynContext
    = CLetRec [Id] -- These id's are in the same recursive group.
    | CClosureBody
        { cid_map :: [(Id,NodeId)] -- ^ Args of a closure mapped to nodes in the body
        }
    -- | Around rhs of case alternative, with alternative binders mapped to nodes.
    | CAlt { cid_map :: [(Id,NodeId)] }
    | CTopLevel
    | CNone -- ^ No Context given
    deriving Eq

instance Outputable SynContext where
    ppr CNone = text "CNone"
    ppr (CTopLevel) = text "CTop"
    ppr (CAlt map) = text "CAlt" <> ppr map
    ppr (CClosureBody map) = text "CClosure" <> ppr map
    ppr (CLetRec ids) = text "CLetRec" <> ppr ids


idMappedInCtxt :: Id -> [SynContext] -> Maybe NodeId
idMappedInCtxt id ctxt
    = go ctxt
  where
    go ((CClosureBody argMap):todo)
        | Just node <- lookup id argMap
        = Just node
    go ((CAlt argMap):todo)
        | Just node <- lookup id argMap
        = Just node
    go (_:todo) = go todo
    go [] = Nothing

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
findTags :: Module -> UniqSupply -> [StgTopBinding] -> ([StgTopBinding], [FlowNode])
findTags this_mod us binds =
    pprTrace "findTags" (ppr this_mod) $
    let state = FlowState this_mod 0 us emptyUFM emptyUFM mempty mempty
    -- Run the analysis, extract only info about id-bound nodes
        (!binds', !s) = (flip runState) state $ do
            -- pprTraceM "FindTags" empty
            addConstantNodes
            nodesTopBinds binds
            nodes <- solveConstraints
            -- mapM_ (pprTraceM "res:" . ppr) nodes
            -- pprTraceM "Result nodes" $ vcat (map ppr nodes)
            return $ binds
        !idNodes = (eltsUFM $ fs_idNodeMap s)
        !doneIdNodes = [n | (BoundId _, n) <- (M.toList $ fs_doneNodes s) ]

    in (binds', idNodes ++ doneIdNodes)

-- Constant mappings
addConstantNodes :: AM ()
addConstantNodes = do
    addNode $ mkConstNode taggedBotNodeId (flatLattice NeverEnter)
    addNode litNode
    markDone $ mkConstNode botNodeId bot
    addNode $ mkConstNode topNodeId top
    addNode $ mkConstNode neverNodeId (flatLattice NeverEnter)
    addNode $ mkConstNode alwaysNodeId (flatLattice AlwaysEnter)


mkConstNode :: NodeId -> EnterLattice -> FlowNode
mkConstNode id val = FlowNode id [] val (return $ val) (text "const")

-- We don't realy do anything with literals, but for a uniform approach we
-- map them to (NeverEnter x Bot)
taggedBotNodeId, litNodeId :: NodeId
taggedBotNodeId = ConstId 1
litNodeId       = ConstId 2
botNodeId       = ConstId 3 -- Always returns bot
topNodeId       = ConstId 4 -- No information possible (MaybeEnter)
neverNodeId     = ConstId 5 -- No information possible (MaybeEnter)
alwaysNodeId    = ConstId 6 -- No information possible (MaybeEnter)


litNode :: FlowNode
litNode = (mkConstNode litNodeId (flatLattice NeverEnter)) { node_desc = text "lit" }

{-# NOINLINE nodesTopBinds #-}
nodesTopBinds :: [StgTopBinding] -> AM [StgTopBinding]
nodesTopBinds binds = mapM (nodesTop) binds

nodesTop :: StgTopBinding -> AM StgTopBinding
-- Always "tagged"
nodesTop bind@(StgTopStringLit v _str) = do
    pprTraceM "TopString" (ppr v)
    let node = mkConstNode (mkIdNodeId [CTopLevel] v)
                           (flatLattice NeverEnter)
    markDone $ node { node_desc = text "c_str" }
    return $ bind
nodesTop      (StgTopLifted bind)  = do
    nodesBind [CTopLevel] TopLevel bind
    return $ (StgTopLifted bind)

nodesBind :: [SynContext] -> TopLevelFlag -> StgBinding -> AM ()
nodesBind ctxt top (StgNonRec v rhs) = do
    void $ nodeBind ctxt top v rhs
nodesBind ctxt top (StgRec binds) = do
    let boundIds = map fst binds
    let ctxt' = (CLetRec boundIds) : ctxt
    void $ mapM (uncurry (nodeBind ctxt' top )) binds

nodeBind :: [SynContext] -> TopLevelFlag -> Id -> StgRhs -> AM NodeId
nodeBind ctxt top id rhs = do
    nodeRhs ctxt top id rhs

-- | This adds nodes with information we can figure out about imported ids into the env.
--   Mimics somewhat what we do in StgCmmClosure.hs:mkLFImported
addImportedNode :: Id -> AM ()
addImportedNode id = do
    s <- get
    let doneNodes = fs_doneNodes s
    let idNodes =   fs_idNodeMap s
    case lookupUFM idNodes id <|> M.lookup (BoundId id) doneNodes of
        Just _ -> return ()
        Nothing
            | nameIsLocalOrFrom (fs_mod s) (idName id)
            -> return ()

            -- Functions are tagged with arity and never entered as atoms
            | idFunRepArity id > 0
            -> markDone $ (mkConstNode node_id (flatLattice NeverEnter))
                            { node_desc = text "ext_func" }

            -- Known Nullarry constructors are also never entered
            | Just con <- (isDataConWorkId_maybe id)
            , isNullaryRepDataCon con
            -> markDone $ (mkConstNode node_id (flatLattice NeverEnter))
                            { node_desc = text "ext_nullCon" }

            -- May or may not be entered.
            | otherwise
            -> markDone $ (mkConstNode node_id (flatLattice MaybeEnter))
                            { node_desc = text "ext_unknown" }

  where
    node_id = (mkIdNodeId [CNone] id)

importedFuncNode :: Module -> Id -> Maybe NodeId
importedFuncNode this_mod id
    -- Not an imported function
    | nameIsLocalOrFrom this_mod (idName id)
    = Nothing
    | Just con <- (isDataConWorkId_maybe id)
    , isNullaryRepDataCon con
    = Just $ neverNodeId
    | otherwise
    = Just $ alwaysNodeId



-- | When dealing with a let bound rhs passing the id in allows us the shortcut the
--  the rule for the rhs tag to flow to the id
nodeRhs :: [SynContext] -> TopLevelFlag -> Id -> StgRhs -> AM NodeId
nodeRhs ctxt _ binding (StgRhsCon _ccs con args)
  | pprTrace "nodeRhsCon" (ppr binding) False = undefined
  | null args = do
        let node_id = mkIdNodeId ctxt binding
        let node = mkConstNode node_id (flatLattice NeverEnter)
        markDone $ node { node_desc = text "rhsCon" }
        return node_id
  | otherwise = do
        mapM addImportedNode [v | StgVarArg v <- args]
        let node_id = mkIdNodeId ctxt binding
        let node = FlowNode { node_id = node_id
                            , node_inputs = node_inputs
                            , node_result = bot
                            , node_update = node_update node_id
                            , node_desc   = text "rhsCon"
                            }
        addNode node
        return node_id
  where
    node_inputs = map (getConArgNodeId ctxt) args :: [NodeId]
    banged_inputs = getStrictConArgs con node_inputs
    node_update this_id = do
        fieldResults <- zip node_inputs <$> mapM (lookupNodeResult) node_inputs
        let strictResults = map snd $ getStrictConArgs con fieldResults
        let strictFieldLub = foldl' lub NeverEnter $ map getOuter strictResults
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


{- Functions are a pain.

We do NOT create their nodes here, instead we create a generator function
which creates needed nodes on the fly.

WHY we do this is that it allows us to instantiate closure nodes with
actual information of their arguments. If we have for example:

let fst x = case x of (a,_) -> a
in
    let foo = (C1 <constArgs> ,C2)
    let bar = fst foo
    in ... e ...

    we instantiate the function fst with it's arguments
    and as a consequence know the tag info of bar which gives
    us better information about e as well.

-}
nodeRhs ctxt topFlag binding (StgRhsClosure _ext _ccs _flag args body)
    | pprTrace "nodeRhs" (ppr binding <+> text "args:" <> ppr args) False
    = undefined
    -- Nullary thunks
    | null args
    = do
        let ctxt' = (CClosureBody []):ctxt
        body_id <- nodeExpr ctxt' body
        let node_id = mkIdNodeId ctxt binding
        let node = FlowNode { node_id = node_id
                            , node_inputs = [body_id]
                            -- ^ We might infer things about nested fields once evaluated.
                            , node_result = LatUndet AlwaysEnter
                            , node_update = node_update node_id body_id
                            , node_desc   = text "rhsThunk"
                            }
        addNode node
        return node_id

    -- Functions
    | otherwise = do
        let node_id = mkIdNodeId ctxt binding
        let ctxt' = (CClosureBody (zip args (replicate arity topNodeId)):ctxt)
        body_id <- nodeExpr ctxt' body

        let node = FlowNode { node_id = node_id
                            , node_inputs = [body_id]
                            -- ^ We might infer things about nested fields once evaluated.
                            , node_result = bot
                            , node_update = node_update node_id body_id
                            , node_desc   = text "rhsFunc"
                            }

        addNode $ node
        return node_id

  where
    arity = length args
    node_update this_id body_id= do

        bodyInfo <- lookupNodeResult body_id

        let enterInfo
                | null args = AlwaysEnter
                | otherwise = NeverEnter -- Thunks with arity > 0
                                         -- are only entered when applied.
        let result = setOuterInfo bodyInfo enterInfo
        updateNode this_id result
        return result

-- If the id is the argument of a closure we
-- do a little dance in findMapping to find the appropriate node.

mkIdNodeId :: [SynContext] -> Id -> NodeId
mkIdNodeId ctxt id
    | Just node <- idMappedInCtxt id ctxt
    = node
    | otherwise = BoundId id

mkUniqueId :: AM NodeId
mkUniqueId = UniqId <$> getUniqueM

nodeExpr :: [SynContext] -> StgExpr -> AM NodeId
nodeExpr ctxt (e@StgCase {})          = nodeCase ctxt e
nodeExpr ctxt (e@StgLet {})           = nodeLet ctxt e
nodeExpr ctxt (e@StgLetNoEscape {})   = nodeLetNoEscape ctxt e
nodeExpr ctxt (StgTick t e)           = nodeExpr ctxt e
nodeExpr ctxt e@(StgConApp _con _args _tys) = nodeConApp ctxt e

nodeExpr ctxt e@(StgApp _ f args)      = do
    mapM_ addImportedNode [v | StgVarArg v <- args]
    addImportedNode f
    nodeApp ctxt e
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
    bndrMappings <- zipWithM mkAltBndrNode [0..] bndrs
    let ctxt' = (CAlt bndrMappings):ctxt
    rhs_id <- nodeExpr ctxt' rhs
    return rhs_id

    where
        -- TODO: These are always tagged
        strictBnds
          | DataAlt con <- altCon
          = getStrictConFields con bndrs
          | otherwise = []

        mkAltBndrNode :: Int -> Id -> AM (Id,NodeId)
        mkAltBndrNode n bndr
          | isUnliftedType bndrTy
          , not (isUnboxedTupleType bndrTy)
          , not (isUnboxedSumType bndrTy)
          = do
                let node_id = mkIdNodeId ctxt bndr
                addNode litNode { node_id = node_id }
                return (bndr,node_id)
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
                return (bndr,node_id)
            where
                bndrTy = idType bndr

(<->) :: SDoc -> SDoc -> SDoc
(<->) a b = a <> char '_' <> b

nodeLet :: [SynContext] -> StgExpr -> State FlowState NodeId
nodeLet ctxt (StgLet _ bind expr) = do
    nodesBind ctxt NotTopLevel bind
    nodeExpr ctxt expr

nodeLetNoEscape ctxt (StgLetNoEscape _ bind expr) = do
    nodesBind ctxt NotTopLevel bind
    nodeExpr ctxt expr

nodeConApp ctxt (StgConApp con args tys) = do
    -- pprTraceM "ConApp" $ ppr con <+> ppr args
    mapM_ addImportedNode [v | StgVarArg v <- args]
    node_id <- mkUniqueId
    let inputs = map (getConArgNodeId ctxt) args :: [NodeId]
    -- let recInputs = map (getConArgNodeId ctxt . StgVarArg) .
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

-- | Todo: Higher order functions?
getFunctionNode :: [SynContext] -> Id -> [EnterLattice] -> AM NodeId
getFunctionNode ctxt id _arg_lats
    | Just node <- isArgFunction ctxt
    = return node
    | otherwise
    = return (mkIdNodeId ctxt id)
  where
    isArgFunction ((CClosureBody argMap):todo)
        | Just node <- lookup id argMap
        = Just node
    isArgFunction ((CAlt argMap):todo)
        | Just node <- lookup id argMap
        = Just node
    isArgFunction [] = Nothing
    isArgFunction (_:todo) = isArgFunction todo

{-
    * A recursive call won't produce any new information.
    * Neither will imported functions


    -- TODO: Mutual recursion
-}
nodeApp :: [SynContext] -> StgExpr -> AM NodeId
nodeApp ctxt (StgApp _ f args) = do
        s <- get
        let this_mod = fs_mod s
        pprTraceM "App1" $ ppr f <+> ppr args

        case () of
          _
            | Just nodeId <- importedFuncNode this_mod f
            -> return nodeId
            | otherwise -> do

                node_id <- mkUniqueId
                pprTraceM "App" $ ppr f <+> ppr args <+> ppr node_id
                let arg_ids = map (getConArgNodeId ctxt) args
                let updater = do
                        -- Argument handling:
                        arg_latts <- mapM lookupNodeResult arg_ids :: AM [EnterLattice]
                        -- Try to peek into the function
                        result <-
                            case () of
                                _   -- Rule AppAbsent
                                    | (idUnique f == absentErrorIdKey)
                                    -> return $ flatLattice NeverEnter

                                    -- Rule AppRec
                                    | SimpleRecursion <- recursionKind ctxt
                                    -> do
                                        func_node <- return $ mkIdNodeId ctxt f
                                            --getFunctionNode ctxt f arg_latts
                                        lookupNodeResult func_node

                                    | OtherRecursion <- recursionKind ctxt
                                    -- We don't even try to inspect mutual recursion currently.
                                    -> pprTrace "mutRec" (Outputable.empty) $ return top

                                    -- AppDefault
                                    | isFunTy (unwrapType $ idType f) -> do
                                        -- pprTraceM "updateStgApp:func" (
                                        --     text "type" <+> ppr (unwrapType $ idType f) $$
                                        --     text "func" <+> ppr f $$
                                        --     text "args" <+> ppr args $$
                                        --     text "context" <+> vcat (map ppr ctxt)
                                        --     )
                                        func_node <- getFunctionNode ctxt f arg_latts
                                        lookupNodeResult func_node
                                    | otherwise -> do
                                        -- pprTraceM "updateStgApp:other" (
                                        --     text "type" <+> ppr (unwrapType $ idType f) $$
                                        --     text "func" <+> ppr f $$
                                        --     text "args" <+> ppr args $$
                                        --     text "context" <+> vcat (map ppr ctxt)
                                        --     )
                                        lookupNodeResult (mkIdNodeId ctxt f)
                        -- pprTraceM "AppFields" $ ppr (f, func_lat)
                        when (nestingLevelOver result 10) $ do
                            pprTraceM "Limiting nesting for " (ppr node_id)
                            node <- getNode node_id
                            addNode $ node { node_update = return result }
                        updateNode node_id result
                        return result

                inputs <- if ( isSimpleRecursion $ recursionKind ctxt )
                    then do
                        return (mkIdNodeId ctxt f  : arg_ids)
                    else return arg_ids

                addNode $ FlowNode
                    { node_id = node_id, node_result = bot
                    , node_inputs = inputs
                    , node_update = updater
                    , node_desc = text "app" <-> ppr f <> ppr args
                    }

                return node_id
    where
        arg_ids = map (getConArgNodeId ctxt) args
        recursionKind [] = NoRecursion
        recursionKind ((CLetRec ids) : todo) | f `elem` ids =
            if length ids == 1 then SimpleRecursion else OtherRecursion
        recursionKind (_ : todo) = recursionKind todo
        arity = idFunRepArity f


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
        pprTraceM "Result nodes" (vcat $ map ppr (idList ++ uqList ++ doneList))
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
            else if (n > 10)
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
                let node' = node { node_result = result }
                done <- and <$> (mapM isMarkedDone (node_inputs node))
                when (done || nestingLevelOver result 10) (markDone node')

                -- pprTraceM "Updated:" (ppr node)
                -- pprTraceM "Updated:" (text "old:" <> ppr old_result <+> ppr node)
                -- pprTraceM "Updated:" (ppr (node_id node) <+> (node_desc node))
                when (mod n     1000 == 0) $ pprTraceM "Node:" (ppr node)
                update n todo True


