--
-- Copyright (c) 2019 Andreas Klebinger
--

{-# LANGUAGE CPP, TypeFamilies, RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs, TupleSections #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}

module StgTraceTags.Analyze (findTags, nodesTopBinds) where

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

class Lattice a where
    bot :: a
    glb :: a -> a -> a
    lub :: a -> a -> a
    top :: a

-- Currently not suitable to model knowledge that something is definitely not tagged!
-- Since the glb of Untagged, Tagged == Untagged.
data TagInfo = NoInfo | Untagged | MaybeTagged | Tagged deriving (Eq,Ord,Show)

instance Outputable TagInfo where
    ppr NoInfo = char '?'
    ppr Untagged = char 'u'
    ppr MaybeTagged = char 'm'
    ppr Tagged = char 't'


instance Lattice TagInfo where
    glb x y = min x y
    lub x y = max x y
    bot = NoInfo
    top = Tagged

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



data TagLattice = Bot
                | Lat !TagInfo [TagLattice]
                -- ^ This cross product allows us to represent all but sum types
                -- * For things without contents (eg Bool) we have @Lat tag [].
                -- * For things for which we care not about the outer tag (unboxed tuples)
                --   we ignore it.
                -- * For things we care about both like: y = True; x = Just y we get
                --   for x: Lat Tagged [Lat Tagged []]
                | Top
                deriving (Eq)

instance Outputable TagLattice where
    ppr Bot = text "_|_"
    ppr Top = text "T"
    ppr (Lat outer inner) =
        ppr outer <+> (ppr inner)

instance Lattice TagLattice where
    bot = Bot
    top = Top
    glb Bot _ = Bot
    glb _ Bot = Bot
    glb Top y = y
    glb x Top = x
    glb (Lat outer1 inner1) (Lat outer2 inner2) =
        Lat (glb outer1 outer2) (glb inner1 inner2)


    -- glb (Flat x) (Flat y) = Flat $ glb x y
    -- glb (UnboxedTuple x) (UnboxedTuple y) = UnboxedTuple $ glb x y
    -- glb (ProdTag x xfs) (ProdTag y yfs) = ProdTag (glb x y) (glb xfs yfs)
    -- glb (SumTag x) (SumTag y) = SumTag $ glb x y
    -- glb _ _ = Bot -- Other cases are not comparable

    lub Bot y = y
    lub x Bot = x
    lub Top _ = Top
    lub _ Top = Top
    lub (Lat outer1 inner1) (Lat outer2 inner2) =
        Lat (lub outer1 outer2) (lub inner1 inner2)

    -- lub (Flat x) (Flat y) = Flat $ lub x y
    -- lub (UnboxedTuple x) (UnboxedTuple y) = UnboxedTuple $ lub x y
    -- lub (ProdTag x xfs) (ProdTag y yfs) = ProdTag (lub x y) (lub xfs yfs)
    -- lub (SumTag x) (SumTag y) = SumTag $ lub x y
    -- lub _ _ = Top -- Other cases are not comparable

flatLattice x = Lat x []

withOuterInfo :: TagLattice -> TagInfo -> TagLattice
withOuterInfo lat info =
    case lat of
        Bot -> Lat info []
        Top -> Top
        Lat _ fields -> Lat info fields

indexField :: TagLattice -> Int -> TagLattice
indexField Bot _ = Bot
indexField Top _ = Top
indexField (Lat _ fields) n =
    case drop n fields of
        [] -> bot
        (x:_xs) -> x

hasOuterTag :: TagLattice -> Bool
hasOuterTag (Lat Tagged _) = True
hasOuterTag _ = False

-- Rules for 0CAF
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
        => mkTag(MaybeTaggedOuter, con, args)


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
        Nothing -> return Bot

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
        , node_result = Bot, node_update = updater }

    return node_id





data FlowNode
    = FlowNode
    { node_id :: NodeId -- ^ Node id
    , node_inputs :: [NodeId]  -- ^ Input dependencies
    , node_result :: (TagLattice) -- ^ Cached result
    , node_update :: (AM TagLattice)
    -- ^ Calculate result, update node in environment.
    }

instance Outputable FlowNode where
    ppr node =
        text "node_" <> pprId node <> (ppr $ node_inputs node) <>
            parens (ppr (node_result node)  )
      where
        pprId node =
            case node_id node of
                Left uq -> text "u_" <> ppr uq
                Right v -> text "v_" <> ppr v



-- | Lowest bound between all input node
mkGlbNode :: [NodeId] -> AM NodeId
mkGlbNode inputs = do
    node_id <- mkUniqueId

    let updater = do
            input_results <- mapM (\id -> node_result <$> getNode id) inputs
            let result = foldl1 glb input_results
            updateNode node_id result
            return result

    addNode $ FlowNode { node_id = node_id, node_result = Bot, node_inputs = inputs
                       , node_update = updater }
    return node_id

-- TODO: For performance reasons we really should only have ONE node
--       per constant result. Or at least for Bot and (OuterInfo x Bot)

-- | Stub that never gives information
mkUselessTODONode :: AM NodeId
mkUselessTODONode = do
    node_id <- mkUniqueId

    addNode $ FlowNode
        { node_id = node_id
        , node_result = Bot
        , node_inputs = []
        , node_update = return $ Bot}
    return node_id

-- | Take a lattice argument per constructor argument to simplify things.
mkConFieldLattice :: DataCon -> TagInfo -> [TagLattice] -> TagLattice
mkConFieldLattice con outer fields
    | conCount /= 1
    = Lat outer []
    | otherwise = Lat outer fields
  where
    conCount = length (tyConDataCons $ dataConTyCon con)

{-# NOINLINE findTags #-}
findTags :: UniqSupply -> [StgTopBinding] -> [StgTopBinding]
findTags us binds =
    let state = FlowState us emptyUFM emptyUFM
    in (flip evalState) state $ do
        pprTraceM "FindTags" empty
        addConstantNodes
        nodesTopBinds binds
        nodes <- solveConstraints
        pprTraceM "Result nodes" $ vcat (map ppr nodes)
        return $ binds

-- Constant mappings
addConstantNodes :: AM ()
addConstantNodes = do
    addNode $ mkConstNode taggedBotNodeId (Lat Tagged [])
    addNode $ mkConstNode botNodeId Bot
    addNode $ mkConstNode topNodeId Top

mkConstNode :: NodeId -> TagLattice -> FlowNode
mkConstNode id val = FlowNode id [] val (return $ val)

-- We don't realy do anything with literals, but for a uniform approach we
-- map them to (Tagged x Bot)
taggedBotNodeId, litNodeId :: NodeId
taggedBotNodeId = Left $ mkUnique 'c' 1
litNodeId       = Left $ mkUnique 'c' 1
botNodeId       = Left $ mkUnique 'c' 2 -- Always returns bot
topNodeId       = Left $ mkUnique 'c' 3


{-# NOINLINE nodesTopBinds #-}
nodesTopBinds :: [StgTopBinding] -> AM [StgTopBinding]
nodesTopBinds binds = mapM (nodesTop) binds

nodesTop :: StgTopBinding -> AM StgTopBinding
-- Always "tagged"
nodesTop bind@(StgTopStringLit v _str) = do
    let node = FlowNode (Right v) [] (flatLattice Tagged) (return $ flatLattice Tagged)
    addNode node
    return $ bind
nodesTop      (StgTopLifted bind)  = do
    nodesBind bind
    return $ (StgTopLifted bind)

-- | Converts RhsCon into RhsClosure if it's required to uphold the tagging
-- invariant.
nodesBind :: StgBinding -> AM ()
nodesBind (StgNonRec v rhs) = do
    nodeBind v rhs
nodesBind (StgRec binds) = do
    mapM_ (uncurry nodeBind) binds

nodeBind :: Id -> StgRhs -> AM ()
nodeBind id rhs = do
    nodeRhs id rhs

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
            -> addNode $ mkConstNode node_id (Lat Tagged bot)

            -- Known Nullarry constructor
            | Just con <- (isDataConWorkId_maybe id)
            , isNullaryRepDataCon con
            -> addNode $ mkConstNode node_id (Lat Tagged [])

            | otherwise
            -> addNode $ mkConstNode node_id Bot


  where
    node_id = (mkIdNodeId id)




-- | When dealing with a let bound rhs passing the id in allows us the shortcut the
--  the rule for the rhs tag to flow to the id
nodeRhs :: Id -> StgRhs -> AM ()
nodeRhs binding (StgRhsCon _ccs con args)  = do
    mapM addImportedNode [v | StgVarArg v <- args]
    let node_id = mkIdNodeId binding
    let node = FlowNode { node_id = node_id
                        , node_inputs = node_inputs
                        , node_result = Bot
                        , node_update = node_update node_id
                        }
    addNode node
  where
    strictArgs = getStrictConArgs con args
    node_inputs = map getArgNodeId args :: [NodeId]
    node_update this_id = do
        -- Get input nodes
        -- Map their lattices to arguments
        -- use mkConFieldLattice to generate final lattice
        -- mkConFieldLattice con outer fields
        fields <- mapM lookupNodeResult node_inputs

        let outerTag
                | null strictArgs = Tagged
                | otherwise = MaybeTagged

        let result = Lat outerTag fields
        updateNode this_id result
        return $ result

nodeRhs m_binding (StgRhsClosure _ext _ccs _flag args body) = do
    mapM addImportedNode args
    body_id <- nodeExpr body

    let node_id = mkIdNodeId m_binding
    let node_inputs = map Right args
    let node = FlowNode { node_id = node_id
                        , node_inputs = node_inputs
                        , node_result = Bot
                        , node_update = node_update node_id body_id
                        }
    addNode node

    return ()


  where
    node_update this_id body_id= do
        -- Get input nodes
        -- Map their lattices to arguments
        -- use mkConFieldLattice to generate final lattice
        -- mkConFieldLattice con outer fields
        bodyInfo <- node_result <$> getNode body_id

        let result = withOuterInfo bodyInfo MaybeTagged
        updateNode this_id result
        return result

mkIdNodeId :: Id -> NodeId
mkIdNodeId = Right

mkUniqueId :: AM NodeId
mkUniqueId = Left <$> getUniqueM

nodeExpr :: StgExpr -> AM NodeId
nodeExpr (e@StgCase {})          = nodeCase e
nodeExpr (e@StgLet {})           = nodeLet e
nodeExpr (e@StgLetNoEscape {})   = nodeLetNoEscape e
nodeExpr (StgTick t e)           = nodeExpr e
nodeExpr e@(StgConApp _con _args _tys) = nodeConApp e

nodeExpr e@(StgApp _ f args)      = do
    mapM addImportedNode [v | StgVarArg v <- args]
    addImportedNode f
    nodeStgApp e
nodeExpr e@(StgLit _lit)            = nodeLit e
nodeExpr e@(StgOpApp _op _args _ty) = nodeOpApp e
nodeExpr   (StgLam {}) = error "Invariant violated: No lambdas in STG representation."

nodeCase (StgCase scrut bndr alt_type alts) = do
    -- pprTraceM "NodeCase" $ ppr bndr
    scrutNodeId <- nodeExpr scrut

    altNodeIds <- mapM (nodeAlt scrutNodeId) alts

    mkCaseBndrNode scrutNodeId bndr

    altsId <- mkGlbNode altNodeIds

    pprTraceM "Scrut, alts, rhss" $ ppr (scrut, scrutNodeId, altNodeIds, altsId)

    return altsId

  where
    mkCaseBndrNode scrutNodeId bndr = do
        let node_id = mkIdNodeId bndr
        let node_inputs = [scrutNodeId]
        addNode $ FlowNode  { node_id = node_id, node_inputs = [scrutNodeId]
                            , node_result = Bot, node_update = updater node_id }
      where
        -- Take the result of the scrutinee and throw an other tag on it.
        updater this_id = do
            scrutNode <- getNode scrutNodeId
            let result = withOuterInfo (node_result scrutNode) Tagged
            updateNode this_id result
            return result

    node_update this_id = do
        let result = flatLattice MaybeTagged
        updateNode this_id result
        return result



nodeCase _ = panic "Impossible: nodeCase"

nodeAlt scrutNodeId (altcon, bndrs, rhs)
--   | (Right f) <- scrutNodeId
--   , StgApp _ fRhs _ <- stgUntickExpr rhs
--   , fRhs == fRhs
--   = do
--     addImportedNode f
--     return topNodeId

  | otherwise = do
    zipWithM mkAltBndrNode [0..] bndrs

    rhs_id <- nodeExpr rhs
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
                                = withOuterInfo (indexField scrut_res n) Tagged
                                | otherwise = indexField scrut_res n

                        updateNode node_id res
                        return res
                addNode FlowNode
                    { node_id = node_id
                    , node_result = Bot
                    , node_inputs = [scrutNodeId]
                    , node_update = updater }
                return node_id
            where
                bndrTy = idType bndr

nodeLet (StgLet _ bind expr) = do
    nodesBind bind
    nodeExpr expr

nodeLetNoEscape (StgLetNoEscape _ bind expr) = do
    nodesBind bind
    nodeExpr expr

nodeConApp (StgConApp con args tys) = do
    mapM_ addImportedNode [v | StgVarArg v <- args]
    node_id <- mkUniqueId
    let inputs = map getArgNodeId args :: [NodeId]

    let updater = do
            fields <- mapM lookupNodeResult inputs :: AM [TagLattice]
            -- Todo: When an *expression* returns a value the outer tag
            --       is not really defined.
            let result = Lat bot fields
            -- pprTraceM "Update conApp" $ ppr (con, args, fields, result)
            updateNode node_id result
            return result

    addNode FlowNode
        { node_id = node_id, node_result = Bot
        , node_inputs = inputs
        , node_update = updater
        }

    return node_id

nodeStgApp (StgApp _ f []) = do
    -- The important case!
    -- The tag info from f flows to the use site of the expression
    -- TODO: Avoiding the indirection when we know we will get a node
    --       for the id
    -- pprTraceM "ind" $ ppr f
    -- mkIndDefaultNode (Right f)

    mkIndDefaultNode (Right f)
    return $ mkIdNodeId f


nodeStgApp (StgApp _ f args) = do
    -- TODO: If f is imported we can make this a constant node
    node_id <- mkUniqueId
    -- let inputs = map getArgNodeId args :: [NodeId]

    let updater = do
            -- Try to peek into the function
            func_lat <- lookupNodeResult (Right f)
            -- Todo: When an *expression* returns a value the outer tag
            --       is not really defined.
            let result = withOuterInfo func_lat Untagged
            updateNode node_id result
            return result

    addNode FlowNode
        { node_id = node_id, node_result = Bot
        , node_inputs = [Right f]
        , node_update = updater
        }

    return node_id

-- Do we need rules here?
nodeLit (StgLit lit) = return $ litNodeId

nodeOpApp (StgOpApp op args res_ty) = return $ botNodeId







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


