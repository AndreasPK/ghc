--
-- Copyright (c) 2019 Andreas Klebinger
--

{-# LANGUAGE TypeFamilies, RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs, TupleSections #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fprof-auto #-}

{-|

    Note [CSR for Stg]
    ~~~~~~~~~~~~~~~~~~

    This module implements a primitive version of CSR (Constructed Strict Returns).

    The basic idea is to determine bindings which have already have been evaluated.
    If they are then we can:
        * Skip generating code to enter their closure.
        * Avoid the code checking for evaluatedness.

    So we win both in terms of code size as well as in actual work (instructions)
    executed.

    Currently this is done in multiple top down pass over STG functions.
    The first pass looks at top level bindings and determines if they are
    tagged.
    The second and third pass traverses the whole program and adds cases when allocating
    constructors if they have strict fields which might be untagged otherwise.

    They keep a set of evaluated bindings and tag Applications with their
    evaluatedness status.

    We add to our set of evaluated bindings the following:
    * Case binders:
        (case e of bndr) => bndr:evaluatedBinds
    * Strict fields of constructors.
        data T = Foo !Int
        case scrut of _ {
            Foo bndr -> e => bndr for e's environment.

    Then if we happen on a case scrutinizing one of these binders we tag
    it as evaluated.

    This could be done on the case itself but currently the tag is on the
    actual application.

    StgCase (StgApp _ v []) {} => StgCase (StgApp <evaluated> v []) {}

    We don't HAVE to put the tag on StgApp but it's easier with how CodeGen is
    organized.

    During the Stg -> Cmm CodeGen we use this information to omit the code
    associated with entering a closure.

    Note [Scrutinees can't be tagged as evaluated]
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    Note that in code like this:

    case foo of _ {
        ...
            case foo of _ {
                C1 x y -> e1
                ...
            }
    }

    We CAN'T mark foo strict in the second case.

    The reason is in hindsight quite obvious:

    foo starts of as a pointer to a thunk,
    which is overwritten with an indirection.
    It doesn't matter if the indirection is tagged,
    if we treat is as evaluated closure
    we will assign x & y to a memory offset from the indirection
    instead to the actual field.

    I currently don't see a way around this. When generating code
    for the first case we don't overwrite the actual foo pointer.
    We only overwrite the closure (with an indirection).

    But CSR relies on the fact that we know a binding refers to the
    actual evaluated closure, not an indirection to an evaluated closure.

    In the end this is of little consequence. If anything it's easier to
    optimize the above into using a case binder and the whole problem
    goes away.

-----------------------------------------------------------
    Note [STagged Things]
-----------------------------------------------------------

    For some things we can guarantee they will have been tagged
    and we don't need to enter them.

    1)  Let bound StgRhsCons.

        They encode in the most direct way an allocated constructor.

        However we have to be careful since some of those will be
        turned into Closures in order to ensure all strict fields
        are tagged, in which case we HAVE to enter them.

    2)  Closures which are applications to absentError.

        absentError applications encode the fact that an value
        will NOT be entered even if it's put into an strict field.

        So we make sure we avoid entering these as well by pretending
        they are tagged.

    3)  (Imported) Nullary Constructors.

        Since they have no arguments they can't technically be unevaluated.

    4)  (Imported) Thunks of arity > 0

        Thunks of arity > 0 are functions and as such will be tagged
        with their arity. This means entering these would also be pointless
        and afaik a no-op.

-}

module StgAnal (tagTop) where

import GhcPrelude

import DataCon
import Data.Bifunctor
import Id
import StgSyn
import Outputable
-- import VarEnv
import CoreSyn (AltCon(..))
-- import Data.List (mapAccumL)
import Data.Maybe (fromMaybe)

import VarSet
-- import UniqMap

import TyCon (tyConDataCons_maybe, PrimRep(..))
import Type (tyConAppTyCon, isUnliftedType, Type)
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

import UniqFM

import Module

import StgTraceTags.Analyze

------------------------------------------------------------
--  Environment tellin us about the state of tagging of ids.
------------------------------------------------------------

-- We turn some RhsCons into RhsClosure, this informs us if the type of
-- the RHS might still change.
data RhsForm = FinalRhs | IntermediateRhs deriving Eq

data SimpleTagInfo = STagged
                -- ^ STagged values are guaranteed to be tagged by codegen.
             | SMaybeTagged [Id]
                -- ^ Might be tagged depending on other bindings taggedness
             | SUntagged
                -- ^ Can reasonably be assumed to be untagged.
             deriving Eq

instance Outputable SimpleTagInfo where
    ppr STagged = char '!'
    ppr SUntagged = char '~'
    ppr (SMaybeTagged deps) = char 'v' <> parens (ppr deps)

type AnaEnv = UniqFM SimpleTagInfo

emptyEnv :: AnaEnv
emptyEnv = emptyUFM

-- | A pesimistic predicate on weither or not an Id is tagged.
--   If isTagged == True then it's guaranteed to be tagged.
isTagged :: AnaEnv -> Id -> Bool
isTagged env id =
    not (liftedId id) || -- (pprTrace "IdRep:" (ppr (id, idPrimRep id)) (idPrimRep id)) /= LiftedRep ||
    -- We know it's already tagged. (Cased on, absentId, ...)
    (lookupUFM env id == Just STagged) ||
    -- Nullary data cons are always represented by a tagged pointer.
    (isNullaryCon id) ||
    -- Thunks with Arity > 0 are also always tagged
    (idFunRepArity id > 0)

  where
    -- True guarantees a lifted rep, but False could be any rep.
    liftedId id
        | [rep] <- typePrimRep (idType id)
        = rep == LiftedRep
        | otherwise = False
    isNullaryCon id
        | Just con <- (isDataConWorkId_maybe id)
        = isNullaryRepDataCon con
        | otherwise = False

-- | Id is definitely not tagged
isUntagged :: AnaEnv -> Id -> Bool
isUntagged env id =
    (lookupUFM env id == Just SUntagged)

tag :: AnaEnv -> Id -> AnaEnv
tag env id = addToUFM env id STagged

untag :: AnaEnv -> Id -> AnaEnv
untag env id = addToUFM env id SUntagged

tagMany :: AnaEnv -> [Id] -> AnaEnv
tagMany env ids = addListToUFM env (zip ids $ repeat STagged)


------------------------------------------------------------
------------------------------------------------------------





------------------------------------------------------------
--  The actual analysis.
------------------------------------------------------------

{-  Note [Top level and recursive binds]

    Consider the following code:

        data Foo = Foo Int Int

        foo = Foo 1 2
        bar = (foo, 1)

    Here bar depends on foo, but they are NOT in a recursive group.
    For local binds this would result in code of the form:

    let foo = ...; in
        let bar = ... in
            e

    However for top level bindings there is no indication that bar
    contains a reference to foo, so we traverse all top level bindings.
    During this traversal we collect info about ids which will be tagged
    by codegen in a global environment which is then used as initial environment
    for going over the body of all top level bindings.

    We use the same approach also for recursive binds. With the major difference
    that we only have to do a pass over the recursive group.
-}

{-# NOINLINE tagTop #-}
tagTop :: Module -> [StgTopBinding] -> UniqSM [StgTopBinding]
-- tagTop binds = return binds

tagTop this_mod binds = do
    -- Experimental stuff:
    us <- getUniqueSupplyM
    let (_binds, idResults) = findTags this_mod us binds
    -- let (_binds, idMap) = (undefined, mempty)

    -- pprTraceM "map" $ ppr idMap

    let env' = fromIdMap env idResults
    -- let env' = env
    -- Proven but too simplistic approach:
    rbinds <- (mapM (tagTopBind env') binds)

    return $ rbinds



    where
        -- See Note [Top level and recursive binds]
        -- env = topEnv binds
        env = topEnv binds

        fromIdMap :: AnaEnv -> [FlowNode] -> AnaEnv
        fromIdMap env =
            foldl' maybeTagNode env
            where
                maybeTagNode env node
                    | BoundId id <- node_id node
                    , hasOuterTag (node_result node)
                    = pprTrace "Tagging:" (ppr $ node_id node) $
                      tag env id
                    | otherwise = env

-- Is the top level binding evaluated, or can be treated as such.
topEnv :: [StgTopBinding] -> AnaEnv
topEnv binds =
    -- pprTraceIt "Evaled (or absent) top binds:" $
    resolveMaybeTagged emptyEnv $ concatMap (evaldTopBind) binds
  where

    evaldTopBind :: StgTopBinding -> [(Id, SimpleTagInfo)]
    evaldTopBind (StgTopStringLit _v _) = [] -- Unlifted - not tagged.
    evaldTopBind (StgTopLifted bind)    =
        taggedByBind emptyEnv False bind

rhsTagInfo :: AnaEnv -> StgRhs -> SimpleTagInfo
rhsTagInfo env rhs = evaldRhs rhs
  where
    evaldRhs (StgRhsClosure _ _ _ args body)
        -- *Not tagged* but guaranteed to never be entered by
        -- the strictness analyzer.
        | StgApp _ func _ <- body
        , idUnique func == absentErrorIdKey
        = STagged
        -- Function tagged with arity.
        | not (null args)
        = STagged
        -- Thunk - untagged
        | otherwise = SUntagged
    evaldRhs (StgRhsCon _ccs con args)
        -- If the constructor has no strict fields,
        -- or the args are already tagged then it we known
        -- it won't become a thunk and will be tagged.
        | null untaggedIds
        = -- pprTrace "taggedBind - nonstrictCon" (ppr con)
          STagged

        -- If all args are tagged a RhsCon will always be tagged.
        | otherwise
        = SMaybeTagged untaggedIds
      where
        strictArgs = (getStrictConArgs con args) :: [StgArg]
        untaggedIds = [v | StgVarArg v <- strictArgs
                         , not (isTagged env v)]

-- | Out of a recursive binding we get the info if a bind is:
-- * STagged
-- * SUntagged
-- * SMaybeTagged deps - This means the binding is tagged if all deps are tagged.

-- We check all SimpleTagInfos, update the environment based on them
-- and check if we can decide the taggedness of any SMaybeTagged bindings based on that.

-- This is at worst n². But this is only an issue if we have:
-- * Many ConRhss
-- * with strict fields
-- * which depend on each other.
-- So in practice not an issue.

resolveMaybeTagged :: AnaEnv -> [(Id,SimpleTagInfo)] -> (AnaEnv)
resolveMaybeTagged env infos =
    decidedTagged env infos [] False
  where
    decidedTagged :: AnaEnv -> [(Id,SimpleTagInfo)] -> [(Id,SimpleTagInfo)] -> Bool -> AnaEnv
    -- Iterate as long as we make progress
    decidedTagged env [] maybes True = decidedTagged env maybes [] False
    -- If we made no progress then there is nothing left that could turn
    -- untagged into tagged bindings, so we mark them untagged.
    decidedTagged env [] maybes False = foldl' untag env $ map fst maybes
    decidedTagged env (orig@(v, SMaybeTagged deps):todo) maybes progress
        | any (isUntagged env) deps = decidedTagged (untag env v) todo maybes True
        | all (isTagged env) deps   = decidedTagged (tag env v)   todo maybes True
        | otherwise                 = decidedTagged env           todo (orig:maybes)
                                                                        progress
    decidedTagged env ((v, STagged):todo) maybes progress
                                    = decidedTagged (tag env v)   todo maybes True
    decidedTagged env ((v, SUntagged):todo) maybes progress
                                    = decidedTagged (untag env v) todo maybes True
    decidedTagged env [] [] _ = env


-- Check if for a binding binding @v@ we can expect references to be tagged.
-- IsFinal tells us if a later pass might change the form of the binding.
-- This happens for example if we turn a RhsCon into a function in order
-- to make sure that strict fields are tagged.

taggedByBind :: AnaEnv -> Bool -> StgBinding -> [(Id, SimpleTagInfo)]
-- TODO: This should be done iteratively.
-- Consider these binds, with ! marking strict fields:
-- val = Int 1
-- foo = Con1 !x
-- bar = Con2 !foo
-- In the current single pass scheme we don't recognize foo/bar as tagged
-- since that depends on the knowledge that val/foo will be tagged.
taggedByBind env isFinal bnd
    | (StgNonRec v rhs) <- bnd
    = [(v, evaldRhs rhs)]
    | (StgRec binds) <- bnd
    = map (second evaldRhs) binds
  where
    evaldRhs :: StgRhs -> SimpleTagInfo
    evaldRhs (StgRhsClosure _ _ _ _ body)
        | StgApp _ func _ <- body
        , idUnique func == absentErrorIdKey
        = STagged
    evaldRhs (StgRhsCon _ccs con args)
        -- Final let bound constructors always get a proper tag.
        | isFinal
        = -- pprTrace "taggedBind - FinalCon" (ppr con)
          STagged

        -- If the constructor has no strict fields,
        -- or the args are already tagged then it we known
        -- it won't become a thunk and will be tagged.
        | null untaggedIds
        = -- pprTrace "taggedBind - nonstrictCon" (ppr con)
          STagged

        -- If all args are tagged a RhsCon will always be tagged.
        | not (isFinal)
        = SMaybeTagged untaggedIds
      where
        strictArgs = (getStrictConArgs con args) :: [StgArg]
        untaggedIds = [v | StgVarArg v <- strictArgs
                         , not (isTagged env v)]
    evaldRhs _ = SUntagged

-- The tagFoo functions enforce the invariant that all
-- members of strict fields have been tagged.

tagTopBind :: AnaEnv -> StgTopBinding -> UniqSM StgTopBinding
tagTopBind _env bind@(StgTopStringLit {}) = return $ bind
tagTopBind env       (StgTopLifted bind)  =
    StgTopLifted <$> tagBind env bind

-- TODO: Shadowing is allows so eventually we also have to remove untagged
--       binds introduced from the map to be save.

-- | Converts RhsCon into RhsClosure if it's required to uphold the tagging
-- invariant.
tagBind :: AnaEnv -> StgBinding -> UniqSM StgBinding
tagBind env (StgNonRec v rhs) = do
    -- pprTraceM "tagBind" (ppr v)
    StgNonRec v <$> tagRhs env rhs
tagBind env (StgRec binds) = tagRecBinds env binds

tagRecBinds :: AnaEnv -> [(Id, StgRhs)] -> UniqSM StgBinding
tagRecBinds env binds = do
    let tagInfos = map (\(v,rhs) -> (v,rhsTagInfo env rhs)) binds
    let env' = resolveMaybeTagged env tagInfos
    binds' <- mapM (\(v,rhs) -> (v,) <$> (tagRhs env' rhs)) binds
    return $ StgRec binds'

-- Note [Bottoming bindings in strict fields]
--
-- This is a fun one. GHC puts bottoming bindings into
-- strict fields (without evaluating them).

-- This is dicy but valid in the absence of bugs.
-- In particular it habens with "absent argument" errors.
-- These are placed there by the worker/wrapper pass if we determine
-- that a field will not be used.
-- This means we will also never case on the fields so we can simply treat
-- it as evaluated even if it's not.

-- TODO:
-- How do we check for this condition? We don't (currently).
-- Instead we simply trust the codeGen to tag all local bindings properly and
-- pray that the worker and the absent error thunk stay within the same module.
--

-- | This turns certain StgRhsCon intp StgRhsClosure if we can't
-- ensure that strict fields would get a tagged pointer.
-- Turning a Con into a Closure is terrible! Really terrible!
-- So we go to some lengths to avoid it.

-- TODO: If there
tagRhs :: AnaEnv -> StgRhs -> UniqSM StgRhs
tagRhs env (StgRhsClosure _ext _ccs _flag _args body)
    = StgRhsClosure _ext _ccs _flag _args <$> tagExpr env body
tagRhs env (StgRhsCon ccs con args)
  | null possiblyUntagged
  = return $ (StgRhsCon ccs con args)
  -- Make sure everything we put into strict fields is also tagged.
  | otherwise
  = pprTraceM "tagRhs: Creating Closure for" (ppr (con, args)) >>
    -- pprTrace "SUntagged args:"
--             (   ppr possiblyUntagged $$
--                 text "allArgs" <+> ppr args $$
--                 text "strictness" <+> ppr conReps $$
--                 text "Constructor:" <+> ppr con
--             )
    mkTopConEval possiblyUntagged (StgRhsCon ccs con args)

  | otherwise
  = return $ (StgRhsCon ccs con args)
  where
    strictArgs = getStrictConArgs con args
    possiblyUntagged =  [ v | (StgVarArg v) <- strictArgs
                            , not (isTagged env v)
                        ]


-- We keep a set of already evaluated ids.
tagExpr :: AnaEnv -> StgExpr -> UniqSM StgExpr
tagExpr env (e@StgCase {})          = tagCase env e
tagExpr env (e@StgLet {})           = tagLet env e
tagExpr env (e@StgLetNoEscape {})   = tagLetNoEscape env e
tagExpr env (StgTick t e)           = StgTick t <$> tagExpr env e
tagExpr env e@(StgConApp _con _args _tys) = tagConApp env e

tagExpr _env e@(StgApp _ _f _args)      = return $ e
tagExpr _env e@(StgLit _lit)            = return $ e
tagExpr _env e@(StgOpApp _op _args _ty) = return $ e
tagExpr _env   (StgLam {}) = error "Invariant violated: No lambdas in finalized STG representation."

tagConApp :: AnaEnv -> StgExpr -> UniqSM StgExpr
tagConApp env e@(StgConApp con args tys)
    | null possiblyUntagged = return e
    | otherwise = do
        mkSeqs possiblyUntagged con args tys
  where
    strictArgs = getStrictConArgs con args
    possiblyUntagged =  [ v | (StgVarArg v) <- strictArgs
                            , not (isTagged env v)
                        ]
tagConApp _ _ = panic "Impossible"


tagCase :: AnaEnv -> StgExpr -> UniqSM StgExpr
tagCase env (StgCase scrut bndr ty alts) = do
    -- pprTrace "tagCase:" (text "scrut" <+> ppr scrut $$ text "env'" <+> ppr env' $$
    --     text "env" <+> ppr env $$ text "redundant" <+> ppr redundantEvaled) $
    scrut' <- tagScrut
    alts' <- mapM (tagAlt env') alts
    return (StgCase scrut' bndr ty alts')
  where
    tagScrut
        | StgApp _ v [] <- scrut
        , isTagged env v
        =
            -- pprTrace "Marking:" (ppr v) $
            return $ StgApp NoEnter v []
        | otherwise
            = tagExpr env scrut
    env'
      -- After unaris (where we are) unboxed tuples binders are never in scope
      | stgCaseBndrInScope ty True = tag env bndr
      | otherwise = env

tagCase _ _ = error "Not a case"

tagAlt :: AnaEnv -> StgAlt -> UniqSM StgAlt
tagAlt env (con@(DataAlt dcon), binds, rhs)
    | (not . null) strictBinds
    -- Extract strictness information for dcon.
    =
    --   pprTrace "strictDataConBinds" (
    --         ppr con <+> ppr (strictBinds)
    --         ) $
            (con, binds,) <$> tagExpr (env') rhs
  where
    env' = tagMany env (strictBinds)
    strictBinds = getStrictConFields dcon binds
tagAlt env (con, binds, rhs) = (con, binds,) <$> (tagExpr env rhs)

-- TODO: Theoretically we could have code of the form:
-- let x = Con in case x of ... e ...
-- However I haven't seen this occure in all of nofib, so omitting checking
-- for this case at this time.
tagLet :: AnaEnv -> StgExpr -> UniqSM StgExpr
tagLet env (StgLet ext bind body) = do
    bind' <- tagBind env bind
    let tagged = map fst .
                 filter (\(_v,info) -> info == STagged) $
                 taggedByBind env True bind'
    let env' = tagMany env tagged
    body' <- tagExpr env' body
    return $ StgLet ext bind' body'

tagLet _ _ = panic "Not a Let"

-- Let no escapes are glorified gotos,
-- we don't have to worry about their taggedness.
tagLetNoEscape :: AnaEnv -> StgExpr -> UniqSM StgExpr
tagLetNoEscape env (StgLetNoEscape ext bind body)
    = liftM2 (StgLetNoEscape ext) (tagBind env bind) (tagExpr env body)
tagLetNoEscape _ _
    = panic "Not a LetNoEscape"





mkLocalArgId :: Id -> UniqSM (Id)
mkLocalArgId id = do
    u <- getUniqueM
    -- TODO: Also reflect this in the idName?
    return $ setIdUnique (localiseId id) u

mkSeq :: Id -> Id -> StgExpr -> StgExpr
mkSeq id bndr expr =
    -- TODO: Is PolyAlt the right one?
    -- pprTraceIt "mkSeq" $
    let altTy = mkStgAltType bndr [(DEFAULT, [], panic "Not used")]
    in
    StgCase (StgApp MayEnter id []) bndr altTy [(DEFAULT, [], expr)]

-- Create a ConApp which is guaranteed to evaluate the given ids.
mkSeqs :: [Id] -> DataCon -> [StgArg] -> [Type] -> UniqSM StgExpr
mkSeqs untaggedIds con args tys = do
    argMap <- mapM (\arg -> (arg,) <$> mkLocalArgId arg ) untaggedIds :: UniqSM [(InId, OutId)]
    -- mapM_ (pprTraceM "Forcing strict args:" . ppr) argMap
    let taggedArgs
            = map   (\v -> case v of
                        StgVarArg v' -> StgVarArg $ fromMaybe v' $ lookup v' argMap
                        lit -> lit)
                    args

    let conBody = StgConApp con taggedArgs tys
    let body = foldr (\(v,bndr) expr -> mkSeq v bndr expr) conBody argMap
    return body

mkTopConEval :: [Id] -> StgRhs -> UniqSM StgRhs
mkTopConEval _          StgRhsClosure {} = panic "Impossible"
mkTopConEval needsEval (StgRhsCon ccs con args)
  = do
    -- pprTraceM "mkTopConEval" ( empty
    --     -- $$ text "evalStrictnesses" <+> ppr (map idStrictness needsEval)
    --     -- $$ text "argIdInfos - useage" <+> ppr (map idStrictness possiblyUntagged)
    --     )

    -- We don't need to pass the [Type] as top level binds are never unlifted
    -- tuples and it's the only case where they are used.
    body <- mkSeqs needsEval con args []
    return $ (StgRhsClosure noExtSilent ccs ReEntrant [] body)












