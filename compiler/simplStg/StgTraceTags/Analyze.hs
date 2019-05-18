--
-- Copyright (c) 2019 Andreas Klebinger
--

{-# LANGUAGE CPP, TypeFamilies, RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs, TupleSections #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}

-- (findTags, nodesTopBinds)
module StgTraceTags.Analyze  where

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
import Util

import State
import Maybes
import Data.Foldable

import StgSubst

class Lattice a where
    bot :: a
    glb :: a -> a -> a
    lub :: a -> a -> a
    top :: a

-- Currently not suitable to model knowledge that something is definitely not tagged!
-- Since the glb of Untagged, Tagged == Untagged.
data TagInfo
    = NoTagInfo     -- ^ No information
    | UndetTag      -- ^ Not yet determined
    | Untagged      -- ^ WILL NOT be tagged
    | UnknownTag    -- ^ Could be either
    | Tagged        -- ^ WILL be tagged
    | TopTagInfo    -- ^ We know we don't know anything
    deriving (Eq,Show)

instance Outputable TagInfo where
    ppr NoTagInfo   = text "_|_"
    ppr UndetTag    = char '?'
    ppr Untagged    = char 'u'
    ppr UnknownTag  = char 'm'
    ppr Tagged      = char 't'
    ppr TopTagInfo  = char 'T'

{- |
             TopTagInfo
              /   |   \
       Untagged Tagged UnknownTag
              \   |   /
               UndetTag
                  |
              NoTagInfo


    NoTagInfo
-}
instance Lattice TagInfo where
    bot = NoTagInfo
    top = TopTagInfo

    glb NoTagInfo x = NoTagInfo
    glb x NoTagInfo = NoTagInfo
    glb UndetTag x = UndetTag
    glb x UndetTag = UndetTag
    glb x y = if x == y then x else TopTagInfo

    lub NoTagInfo x = x
    lub x NoTagInfo = x
    lub UndetTag x = x
    lub x UndetTag = x
    lub TopTagInfo x = TopTagInfo
    lub x TopTagInfo = TopTagInfo

    -- This should not happen, we should only ever INCREASE information
    -- or we risk non-termination
    lub x y = if x == y then x else panic "Regressing Taginfo" -- UndetTag


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
    | SumInfo DataCon [TagLattice] -- ^ A constructor application
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

{- |

Lattice of roughly this shape:

          Top
          / \
    LatProd LatSum
         |   |
       LatUnknown
           |
          Bot

LatUnknown represents things over which we can't know anything but their tag.

Prod/Sum refine this knowledge and extend it to the fields of a returned value.

-}
data TagLattice
    = Bot -- Things we can't say anything about (yet)
    | LatUnknown !TagInfo

    | LatProd !TagInfo [TagLattice]
    -- ^ This cross product allows us to represent all but sum types
    -- * For things without contents (eg Bool) we have @LatProd tag [].
    -- * For things for which we care not about the outer tag (unboxed tuples)
    --   we ignore it.
    -- * For things where we care about both (tag and fields)
    --   like:  y = True; x = Just y
    --   we get for x:
    --   LatProd Tagged [LatProd Tagged []]

    | LatSum !TagInfo SumInfo

    | Top
                deriving (Eq)

getOuter :: TagLattice -> Maybe TagInfo
getOuter (LatUnknown x) = Just x
getOuter (LatProd x _) = Just x
getOuter (LatSum x  _) = Just x
getOuter _ = Nothing



instance Outputable TagLattice where
    ppr Bot = text "_|_"
    ppr Top = text "T"
    ppr (LatUnknown outer) = ppr outer
    ppr (LatProd outer inner) =
        ppr outer <+> (ppr inner)
    ppr (LatSum outer inner) =
        ppr outer <+> (ppr inner)

instance Lattice TagLattice where
    bot = Bot
    top = Top

    glb Bot _ = Bot
    glb _ Bot = Bot
    glb Top y = y
    glb x Top = x

    glb (LatUnknown outer1) x
        = LatUnknown (glb outer1 (expectJust "glb:TagLattice1" $ getOuter x))
    glb x (LatUnknown outer1)
        = LatUnknown (glb outer1 (expectJust "glb:TagLattice2" $ getOuter x))

    glb (LatProd outer1 inner1) (LatProd outer2 inner2) =
        LatProd (glb outer1 outer2) (glb inner1 inner2)

    glb (LatSum outer1 fields1) (LatSum outer2 fields2)
        = LatSum (glb outer1 outer2) (glb fields1 fields2)
    -- While from the lattice perspectice this makes sense,
    -- we error here as it implies a binding takes a value
    -- both from a sum and a product type which can't happen
    -- unless it's polymorphic.
    -- But then the result must come from the functions argument
    -- something currently not analyzed.
    glb (LatProd _ _ ) (LatSum _ _) =
        panic "Comparing sum with prod type"

    lub Top _ = Top
    lub _ Top = Top
    lub Bot y = y
    lub x Bot = x
    lub (LatUnknown outer1) x
        = setOuterInfo x outer1
    lub x (LatUnknown outer1)
        = setOuterInfo x outer1

    lub (LatProd outer1 inner1) (LatProd outer2 inner2) =
        LatProd (lub outer1 outer2) (lub inner1 inner2)

    lub (LatSum outer1 fields1) (LatSum outer2 fields2)
        = LatSum (lub outer1 outer2) (lub fields1 fields2)

    lub (LatProd _ _ ) (LatSum _ _) =
        panic "Comparing sum with prod type"


flatLattice x = LatUnknown x

setOuterInfo :: TagLattice -> TagInfo -> TagLattice
setOuterInfo lat info =
    case lat of
        Bot -> LatUnknown info
        LatUnknown _ -> LatUnknown info
        LatProd _ fields -> LatProd info fields
        LatSum  _ fields -> LatSum info fields
        Top -> Top


-- Lookup field info, defaulting towards bot
indexField :: TagLattice -> Int -> TagLattice
indexField Bot _ = Bot
indexField Top _ = Top
indexField LatUnknown {} _ = Bot
indexField (LatProd _ fields) n =
    case drop n fields of
        [] -> bot
        (x:_xs) -> x
indexField (LatSum _ sum) n
    | SumInfo _con fields <- sum
    = case drop n fields of
        [] -> bot
        (x:_xs) -> x
    | otherwise = bot

hasOuterTag :: TagLattice -> Bool
hasOuterTag (LatUnknown Tagged) = True
hasOuterTag (LatProd Tagged _) = True
hasOuterTag (LatSum Tagged _) = True
hasOuterTag _ = False

-- Outdated Rules for 0CAF
{-

    Assumptions made:
        * StgApp is always fully applied
        * Now shadowing - currently not guaranted will fix later.

    Build the domain for a constructor:

    Tag Lattice for expression results, not listed are the common bot/top elements

    Nullary results | n-Product/Unboxed n-Tuple:

    Tagged              [TagInfo x] (TagInfo^n)
      |
    Maybe
      |
    Untagged



    Syntax:
    tag[e] -> Tagness info of e

    e[expr]


    Binds, top level and otherwise.
    =======================================================
    [NonRec x rhs]
        => fun_out[x] = tag[rhs]
        => tag[x] = tag[rhs]

    Rec [(x1,rhs1), (x2,rhs2), ... ]]
        => fun_out[x1] = tag[rhs1]
           tag[x1] = tag[rhs1]
           ...


    Expressions:
    =======================================================

    -- The result is tagged if the function returns a tagged arguments.
    [StgApp f args]
        => tag[StgApp f args] = fun_out[f]

    -- The result is tagged if the function returns a tagged arguments.
    [StgApp f []]
        => fun_out[ [StgApp f []] ] = tag[f]

    -- Always "tagged" (not represented by a pointer)
    [StgLit]
        => tag[StgLit] = Tagged

    -- Always returns a tagged pointer
    [StgConApp args]
        => fields[StgConApp] = tags(args)

    -- Unsure, but likely doesn't matter
    [StgOpApp]
        => Untagged

    -- Proper STG doesn't contain lambdas.
    [StgLam]
        => panic -

    --
    [StgLet bnd body]
        => tag[body]

    --
    [StgLetNoEscape bnd body]
        => tag[body]

    -- Cases are one of the harder parts.
    -- The lower bound of the alts determine the expressions tag
    [StgCase scrut bndr alts]
        => tag[StgCase scrut bndr alts] = glb alts

    -- The case binder is always tagged
    [StgCase scrut bndr alts]
        => tag [bndr] = Tagged

    -- Alternative results are determined from their rhs
    [StgAlt con bnds expr]
        => tag[StgAlt con bnds expr] = tag[expr]

    -- Strict fields are always at least tagged
    -- tagOuter tells transforms the tagInfo in one that
    -- represents a tagged pointer, without touching information about
    -- inner fields. This is monotonic!
    [StgAlt con [b1,b2,..bn] expr], strictField bi
            => tag[bi] = tagOuter(tag[bi])

    -- Function return values flowing into alternative binders.
    [StgCase scrut bndr [alt0, ..., alti, ..., altn]],
    alti@[StgAlt con [b1, b2, .., bi, .., bn] rhs]
        => tag[b1] = extractFieldTag(1,fun_out(scrut))

        If eg f returns a unboxed n-tuple then it's domain will be TagInfo^n.
        extractFieldTag(i,tagInfo) gives us the info about the ith field.


    GenStgRhs:
    =======================================================

    [StgRhsClosure], arity > 0
        => Tagged

    [StgRhsClosure], arity == 0
        => Untagged

    -- Will be tagged on the outer level, inner depends on the arguments
    [StgRhsCon cc con args], lazyCon rhs
        => mkTag(TagOuter, con, args)

        eg: Just [a1]
        => Tagged x tag(a1)


    e[StgRhsCon], all (\arg -> e[arg] == Tagged) strictArgs rhs
        => mkTag(TagOuter, con, args)

    e[StgRhsCon], any (\arg -> e[arg] == Untagged) strictArgs rhs
        => mkTag(UntaggedOuter, con, args)

    e[StgRhsCon], otherwise
        => mkTag(UndetTagOuter, con, args)


    -- Slightly less outdated considerations:

    Rule AppRec:
    -- TODO: Should we make it (Prod/Sum Untagged Top) instead?
    app@(StgApp _ f args), let f = ... app ...
        => [app] = [f]

    Rule2:
    -- If a banged field is not guaranteed tagged then we have to
    -- turn this into a closure loosing the tag :(
    con@(StgRhsCon con args), isMarkedStrict arg -> tag[arg]
        => outer[con] = Tagged

    Rule AppAbsent:
    -- We have to treat applications of absentError as tagged,
    -- otherwise we might enter them when forcing strict fields
    -- even though otherwise the demand analyser guarantees the
    -- content will not be used.
    app@(StgApp _ f args), f = absentError
        => outer[app] = Tagged


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
type NodeId = Either Unique Id

data FlowState
    = FlowState
    { fs_us :: UniqSupply
    , fs_idNodeMap :: UniqFM FlowNode -- ^ Map from let bounds ids to their defining node
    , fs_uqNodeMap :: UniqFM FlowNode -- ^ Transient results
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

addNode :: FlowNode -> AM ()
addNode node = do
    s <- get
    let s' = case node_id node of
                Left uq -> s { fs_uqNodeMap = addToUFM (fs_uqNodeMap s) uq node }
                Right v -> s { fs_idNodeMap = addToUFM (fs_idNodeMap s) v  node }
    put s'

updateNode :: NodeId -> TagLattice -> AM ()
updateNode id result = do
    node <- getNode id
    addNode $ node {node_result = result}



getNode :: NodeId -> AM FlowNode
getNode node_id = do
    s <- get
    return $ case node_id of
        Left uq -> fromMaybe (panic "getNodeUq" $ ppr node_id) $ lookupUFM  (fs_uqNodeMap s) uq
        Right v -> fromMaybe (pprPanic "getNodeId" $ ppr node_id) $ lookupUFM  (fs_idNodeMap s) v

-- | Loke node_result <$> getNode but defaults to bot
-- for non-existing nodes
lookupNodeResult :: NodeId -> AM TagLattice
lookupNodeResult node_id = do
    s <- get
    let result =
            case node_id of
                Left uq -> lookupUFM  (fs_uqNodeMap s) uq
                Right v -> lookupUFM  (fs_idNodeMap s) v
    case result of
        Just r  -> return $ node_result r
        Nothing -> return top -- We know we know nothing

getArgNodeId :: StgArg -> NodeId
getArgNodeId (StgLitArg _ ) = taggedBotNodeId
getArgNodeId (StgVarArg v ) = Right v

-- | Creates a node which takes the result of id
-- if available, a default value otherwise.
mkIndDefaultNode :: NodeId -> AM NodeId
mkIndDefaultNode indirectee = do
    node_id <- mkUniqueId

    let updater = do
            result <- lookupNodeResult indirectee
            updateNode node_id result
            return result

    addNode FlowNode
        { node_id = node_id, node_inputs = [indirectee]
        , node_result = Bot, node_update = updater
        , node_desc = text "ind" }

    return node_id





data FlowNode
    = FlowNode
    { node_id :: NodeId -- ^ Node id
    , node_inputs :: [NodeId]  -- ^ Input dependencies
    , node_result :: (TagLattice) -- ^ Cached result
    , node_update :: (AM TagLattice)
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
                Left uq -> text "u_" <> ppr uq
                Right v -> text "v_" <> ppr v

data SynContext
    = CLetRec [Id]
    | CTopLevel
    deriving Eq


-- | Lub between all input node
mkLubNode :: [NodeId] -> AM NodeId
mkLubNode inputs = do
    node_id <- mkUniqueId

    let updater = do
            input_results <- mapM (\id -> node_result <$> getNode id) inputs
            let result = foldl1 lub input_results
            updateNode node_id result
            return result

    addNode $ FlowNode { node_id = node_id, node_result = Bot, node_inputs = inputs
                       , node_update = updater, node_desc = text "lub" }
    return node_id

-- | Take a lattice argument per constructor argument to simplify things.
mkConLattice :: DataCon -> TagInfo -> [TagLattice] -> TagLattice
mkConLattice con outer fields
    | conCount == 1 = LatProd outer fields
    | conCount > 1
    = LatSum outer (SumInfo con fields)
    | otherwise = panic "mkConLattice"
  where
    conCount = length (tyConDataCons $ dataConTyCon con)

{-# NOINLINE findTags #-}
findTags :: UniqSupply -> [StgTopBinding] -> ([StgTopBinding], UniqFM FlowNode)
findTags us binds =
    let state = FlowState us emptyUFM emptyUFM
    -- Run the analysis, extract only info about id-bound nodes
        result = (flip runState) state $ do
            -- pprTraceM "FindTags" empty
            addConstantNodes
            nodesTopBinds binds
            nodes <- solveConstraints
            -- pprTraceM "Result nodes" $ vcat (map ppr nodes)
            return $ binds
    in second fs_idNodeMap result

-- Constant mappings
addConstantNodes :: AM ()
addConstantNodes = do
    addNode $ mkConstNode taggedBotNodeId (flatLattice Tagged)
    addNode $ mkConstNode litNodeId (flatLattice Tagged)
    addNode $ mkConstNode botNodeId Bot
    addNode $ mkConstNode topNodeId Top

mkConstNode :: NodeId -> TagLattice -> FlowNode
mkConstNode id val = FlowNode id [] val (return $ val) (text "const")

-- We don't realy do anything with literals, but for a uniform approach we
-- map them to (Tagged x Bot)
taggedBotNodeId, litNodeId :: NodeId
taggedBotNodeId = Left $ mkUnique 'c' 1
litNodeId       = Left $ mkUnique 'c' 2
botNodeId       = Left $ mkUnique 'c' 3 -- Always returns bot
topNodeId       = Left $ mkUnique 'c' 4


{-# NOINLINE nodesTopBinds #-}
nodesTopBinds :: [StgTopBinding] -> AM [StgTopBinding]
nodesTopBinds binds = mapM (nodesTop) binds

nodesTop :: StgTopBinding -> AM StgTopBinding
-- Always "tagged"
nodesTop bind@(StgTopStringLit v _str) = do
    let node = mkConstNode (mkIdNodeId v) (flatLattice Tagged)
    addNode node
    return $ bind
nodesTop      (StgTopLifted bind)  = do
    nodesBind [CTopLevel] bind
    return $ (StgTopLifted bind)

-- | Converts RhsCon into RhsClosure if it's required to uphold the tagging
-- invariant.
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

            -- Functions are tagged with arity
            | idFunRepArity id > 0
            -> addNode $ mkConstNode node_id (LatProd Tagged bot)

            -- Known Nullarry constructor
            | Just con <- (isDataConWorkId_maybe id)
            , isNullaryRepDataCon con
            -> addNode $ mkConstNode node_id (LatProd Tagged [])

            | otherwise
            -> addNode $ mkConstNode node_id Bot


  where
    node_id = (mkIdNodeId id)




-- | When dealing with a let bound rhs passing the id in allows us the shortcut the
--  the rule for the rhs tag to flow to the id
nodeRhs :: [SynContext] -> Id -> StgRhs -> AM ()
nodeRhs ctxt binding (StgRhsCon _ccs con args)  = do
    mapM addImportedNode [v | StgVarArg v <- args]
    let node_id = mkIdNodeId binding
    let node = FlowNode { node_id = node_id
                        , node_inputs = node_inputs
                        , node_result = Bot
                        , node_update = node_update node_id
                        , node_desc   = text "rhsCon"
                        }
    addNode node
  where
    node_inputs = map getArgNodeId args :: [NodeId]
    banged_inputs = getStrictConArgs con node_inputs
    node_update this_id = do
        -- Get input nodes
        -- Map their lattices to arguments
        -- use mkConLattice to generate final lattice
        -- mkConLattice con outer fields
        fieldResults <- zip node_inputs <$> mapM lookupNodeResult node_inputs
        -- pprTraceM "RhsCon" (ppr con <+> ppr this_id <+> ppr fieldResults)
        -- lookupNodeResult is kinda expensive so instead here we go
        -- Rule 2
        let outerTag
                | all
                    (\(id,lat) -> hasOuterTag lat || not (elem id banged_inputs))
                    fieldResults
                = -- pprTrace "Rule2" (ppr this_id)
                    Tagged
                | otherwise = UndetTag

        let result = mkConLattice con outerTag (map snd fieldResults)
        updateNode this_id result
        return $ result

nodeRhs ctxt binding (StgRhsClosure _ext _ccs _flag args body) = do
    -- TODO: Take into acount args somehow
    mapM addImportedNode args
    body_id <- nodeExpr ctxt body

    let node_id = mkIdNodeId binding
    let node_inputs = [body_id] -- : (map mkIdNodeId args)
    let node = FlowNode { node_id = node_id
                        , node_inputs = node_inputs
                        , node_result = Bot
                        , node_update = node_update node_id body_id
                        , node_desc   = text "rhsClosure"
                        }
    addNode node

    return ()


  where
    node_update this_id body_id= do
        -- Get input nodes
        -- Map their lattices to arguments
        -- use mkConLattice to generate final lattice
        -- mkConLattice con outer fields
        -- pprTraceM "UpdateClosure1" $ ppr body_id

        -- In case we have:
        -- f x = x we end up without a node for the argument
        bodyInfo <- lookupNodeResult body_id
        -- pprTraceM "UpdateClosure2" $ ppr body_id

        let result = setOuterInfo bodyInfo UndetTag
        updateNode this_id result
        return result

mkIdNodeId :: Id -> NodeId
mkIdNodeId = Right

mkUniqueId :: AM NodeId
mkUniqueId = Left <$> getUniqueM

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
                            , node_result = Bot, node_update = updater
                            , node_desc = text "caseBndr" }
      where
        bndrId = mkIdNodeId bndr
        -- Take the result of the scrutinee and throw an other tag on it.
        updater = do
            -- We don't create nodes for closure arguments, so they might
            -- be undefined
            scrutResult <- lookupNodeResult scrutNodeId
            let result = setOuterInfo scrutResult Tagged
            updateNode bndrId result
            return result

    node_update this_id = do
        let result = flatLattice UndetTag
        updateNode this_id result
        return result
nodeCase _ _ = panic "Impossible: nodeCase"

nodeAlt ctxt scrutNodeId (altcon, bndrs, rhs)
  | otherwise = do
    zipWithM mkAltBndrNode [0..] bndrs

    rhs_id <- nodeExpr ctxt rhs
    return rhs_id

    where
        -- TODO: These are always tagged
        strictBnds
          | DataAlt con <- altcon
          = getStrictConFields con bndrs
          | otherwise = []

        mkAltBndrNode n bndr
          | isUnliftedType bndrTy
          , not (isUnboxedTupleType bndrTy)
          , not (isUnboxedSumType bndrTy)
          = return litNodeId
          | otherwise = do
                let node_id = mkIdNodeId bndr
                let updater = do
                        scrut_res <- lookupNodeResult scrutNodeId
                        let res
                                | elem bndr strictBnds
                                -- Tag things coming out of strict binds
                                = setOuterInfo (indexField scrut_res n) Tagged
                                | otherwise = indexField scrut_res n

                        updateNode node_id res
                        return res
                addNode FlowNode
                    { node_id = node_id
                    , node_result = Bot
                    , node_inputs = [scrutNodeId]
                    , node_update = updater
                    , node_desc = text "altBndr" }
                return node_id
            where
                bndrTy = idType bndr

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
    let inputs = map getArgNodeId args :: [NodeId]

    let updater = do
            fields <- mapM lookupNodeResult inputs :: AM [TagLattice]
            -- Todo: When an *expression* returns a value the outer tag
            --       is not really defined.
            let result = mkConLattice con bot fields
            -- pprTraceM "Update conApp" $ ppr (con, args, fields, result)
            updateNode node_id result
            return result

    addNode FlowNode
        { node_id = node_id, node_result = Bot
        , node_inputs = inputs
        , node_update = updater
        , node_desc = text "conApp"
        }

    return node_id

-- nodeStgApp ctxt (StgApp _ f []) = do
--     -- The important case!
--     -- The tag info from f flows to the use site of the expression
--     -- TODO: Avoiding the indirection when we know we will get a node
--     --       for the id
--     -- pprTraceM "ind" $ ppr f
--     mkIndDefaultNode $ mkIdNodeId f



nodeStgApp ctxt (StgApp _ f args) = do
    pprTraceM "App" $ ppr f <+> ppr args
    node_id <- mkUniqueId

    let updater = do
            -- Try to peek into the function
            func_lat <-
                case () of
                    _
                        | (idUnique f == absentErrorIdKey)
                        -> return $ flatLattice Tagged -- Rule AppAbsent
                        -- Rule AppRec
                        | isRecursiveCall ctxt -> lookupNodeResult (mkIdNodeId f)
                        | otherwise -> lookupNodeResult (mkIdNodeId f)
            -- pprTraceM "AppFields" $ ppr (f, func_lat)
            let result = setOuterInfo func_lat NoTagInfo
            updateNode node_id result
            return result

    addNode FlowNode
        { node_id = node_id, node_result = Bot
        , node_inputs = [mkIdNodeId f]
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
    return $ botNodeId







solveConstraints :: AM [FlowNode]
solveConstraints = do
        iterate 1
        idList <- map snd . nonDetUFMToList . fs_idNodeMap <$> get
        uqList <- map snd . nonDetUFMToList . fs_uqNodeMap <$> get
        return $ idList ++ uqList
  where
    iterate :: Int -> AM ()
    iterate n = do
        pprTraceM "iterate - pass " (ppr n)
        idList <- map snd . nonDetUFMToList . fs_idNodeMap <$> get
        uqList <- map snd . nonDetUFMToList . fs_uqNodeMap <$> get

        progress <- liftM2 (||) (update idList False) (update uqList False)
        when progress $ iterate (n+1)

    update :: [FlowNode] -> Bool -> AM Bool
    update []           progress = return $ progress
    update (node:todo)  progress = do
        let old_result = node_result node
        -- node_update also updates the environment
        result <- node_update node
        if (result == old_result)
            then update todo progress
            else update todo True


