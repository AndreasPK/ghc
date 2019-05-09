--
-- Copyright (c) 2019 Andreas Klebinger
--

{-# LANGUAGE TypeFamilies, RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs, TupleSections #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

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
    Note [Tagged Things]
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

module StgAnal (stgAna, tagTop) where

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
-- import Hoopl.Collections
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

newtype RhsForm = RhsForm Bool

finalRhs = RhsForm True
intermediateRhs = RhsForm False

------------------------------------------------------------
--  Utility functions
------------------------------------------------------------

-- | Given a DataCon and list of args passed to it, return the ids we expect to be strict.
-- We use this to determine which of these require evaluation
getStrictConArgs :: DataCon -> [StgArg] -> [StgArg]
getStrictConArgs con args =
    strictArgs
  where
    conReps = dataConRepStrictness con
    strictArgs = map snd $ filter (\(s,_v) -> isMarkedStrict s) $ zip conReps args

-- | When given a list of ids this con binds, returns the list of ids coming
-- from strict fields.
getStrictConFields :: DataCon -> [Id] -> [Id]
getStrictConFields con binds =
    strictBinds
  where
    conReps = dataConRepStrictness con
    strictBinds = map snd $ filter (\(s,_v) -> isMarkedStrict s) $ zip conReps binds

emptyEnv :: IdSet
emptyEnv = emptyVarSet


------------------------------------------------------------
------------------------------------------------------------








------------------------------------------------------------
--  The actual analysis.
------------------------------------------------------------

{-# NOINLINE tagTop #-}
tagTop :: [StgTopBinding] -> UniqSM [StgTopBinding]
-- tagTop binds = return binds
tagTop binds = mapM (tagTopBind env) binds
    where
        env = mkVarSet $ evaldTopBinds binds

-- TODO: This mess here:
-- All explicit constructors should likely be marked evaluated.

-- Is the top level absence error.
evaldTopBinds :: [StgTopBinding] -> [Id]
evaldTopBinds binds =
    let result = concatMap (evaldTopBind) binds
    in if null result then []
    else pprTrace "Evaled (absent) top binds:" (ppr result) result


  where
    evaldTopBind :: StgTopBinding -> [Id]
    evaldTopBind (StgTopStringLit _v _) = [] -- TODO
    evaldTopBind (StgTopLifted bind)    =
        taggedByBind False bind

-- Check if for a binding binding @v@ we can expect references to be tagged.
-- IsFinal tells us if a later pass might change the form of the binding.
-- This happens for example if we turn a RhsCon into a function in order
-- to make sure that strict fields are tagged.
taggedByBind :: Bool -> GenStgBinding p -> [BinderP p]
taggedByBind isFinal bnd
    | (StgNonRec v rhs) <- bnd
    = if evaldRhs rhs then [v] else []
    | (StgRec binds) <- bnd
    = map fst $ filter (evaldRhs . snd) binds
  where
    evaldRhs :: GenStgRhs p -> Bool
    evaldRhs (StgRhsClosure _ _ _ _ body)
        | StgApp _ func _ <- body
        , idUnique func == absentErrorIdKey
        = True
    evaldRhs (StgRhsCon _ccs con args)
        -- Final let bound constructors always get a proper tag.
        | isFinal
        = pprTrace "taggedBind - FinalCon" (ppr con)
          True
        -- If the constructor has no strict fields
        -- we never turn it into a closure
        | null (getStrictConArgs con args)
        = pprTrace "taggedBind - nonstrictCon" (ppr con)
          True
    evaldRhs _ = False

-- The tagFoo functions enforce the invariant that all
-- members of strict fields have been tagged.

tagTopBind :: IdSet -> StgTopBinding -> UniqSM StgTopBinding
tagTopBind _env bind@(StgTopStringLit {}) = return $ bind
tagTopBind env       (StgTopLifted bind)  =
    StgTopLifted <$> tagBind env bind

tagBind :: IdSet -> StgBinding -> UniqSM StgBinding
tagBind env (StgNonRec v rhs) = do
    -- pprTraceM "tagBind" (ppr v)
    StgNonRec v <$> tagRhs env rhs
tagBind env (StgRec binds) = do
    -- pprTraceM "tagBinds" (ppr $ map fst binds)
    binds' <- mapM (\(v,rhs) -> (v,) <$> (tagRhs env rhs)) binds
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
tagRhs :: IdSet -> StgRhs -> UniqSM StgRhs
tagRhs env (StgRhsClosure _ext _ccs _flag _args body)
    = StgRhsClosure _ext _ccs _flag _args <$> tagExpr env body
tagRhs env (StgRhsCon ccs con args)
  | null possiblyUntagged
  = return $ (StgRhsCon ccs con args)
  -- Make sure everything we put into strict fields is also tagged.
  | otherwise
  = pprTraceM "tagRhs: Creating Closure for" (ppr (con, args)) >>
    -- pprTrace "Untagged args:"
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
    possiblyUntagged =  [ v | arg@(StgVarArg v) <- strictArgs
                            , not (isTagged env v)
                        ]

-- | A pesimistic predicate on weither or not an Id is tagged.
--   If isTagged == True then it's guaranteed to be tagged.
isTagged :: IdSet -> Id -> Bool
isTagged env id =
    not (liftedId id) || -- (pprTrace "IdRep:" (ppr (id, idPrimRep id)) (idPrimRep id)) /= LiftedRep ||
    -- We know it's already tagged. (Cased on, absentId, ...)
    (elemVarSet id env) ||
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


-- We keep a set of already evaluated ids.
tagExpr :: IdSet -> StgExpr -> UniqSM StgExpr
tagExpr env (e@StgCase {})          = tagCase env e
tagExpr env (e@StgLet {})           = tagLet env e
tagExpr env (e@StgLetNoEscape {})   = tagLetNoEscape env e
tagExpr env (StgTick t e)           = StgTick t <$> tagExpr env e
tagExpr env e@(StgConApp _con _args _tys) = tagConApp env e

tagExpr _env e@(StgApp _ _f _args)      = return $ e
tagExpr _env e@(StgLit _lit)            = return $ e
tagExpr _env e@(StgOpApp _op _args _ty) = return $ e
tagExpr _env   (StgLam {}) = error "Invariant violated: No lambdas in finalized STG representation."

tagConApp :: IdSet -> StgExpr -> UniqSM StgExpr
tagConApp env e@(StgConApp con args tys)
    | null possiblyUntagged = return e
    | otherwise = do
        mkSeqs possiblyUntagged con args tys
  where
    strictArgs = getStrictConArgs con args
    possiblyUntagged =  [ v | arg@(StgVarArg v) <- strictArgs
                            , not (isTagged env v)
                        ]
tagConApp _ _ = panic "Impossible"


tagCase :: IdSet -> StgExpr -> UniqSM StgExpr
tagCase env (StgCase scrut bndr ty alts) = do
    -- pprTrace "tagCase:" (text "scrut" <+> ppr scrut $$ text "env'" <+> ppr env' $$
    --     text "env" <+> ppr env $$ text "redundant" <+> ppr redundantEvaled) $
    scrut' <- tagExpr env scrut
    alts' <- mapM (tagAlt env') alts
    return (StgCase scrut' bndr ty alts')
  where
    env'
      -- After unaris (where we are) unboxed tuples binders are never in scope
      | stgCaseBndrInScope ty True = extendVarSet env bndr
      | otherwise = env

tagCase _ _ = error "Not a case"

tagAlt :: IdSet -> StgAlt -> UniqSM StgAlt
tagAlt env (con@(DataAlt dcon), binds, rhs)
    | (not . null) strictBinds
    -- Extract strictness information for dcon.
    =
    --   pprTrace "strictDataConBinds" (
    --         ppr con <+> ppr (strictBinds)
    --         ) $
            (con, binds,) <$> tagExpr (env') rhs
  where
    env' = extendVarSetList env (strictBinds)
    strictBinds = getStrictConFields dcon binds
tagAlt env (con, binds, rhs) = (con, binds,) <$> (tagExpr env rhs)

-- TODO: Theoretically we could have code of the form:
-- let x = Con in case x of ... e ...
-- However I haven't seen this occure in all of nofib, so omitting checking
-- for this case at this time.
tagLet :: IdSet -> StgExpr -> UniqSM StgExpr
tagLet env (StgLet ext bind body) = do
    bind' <- tagBind env bind
    let tagged = taggedByBind True bind'
    let env' = extendVarSetList env tagged
    body' <- tagExpr env' body
    return $ StgLet ext bind' body'

tagLet _ _ = panic "Not a Let"

tagLetNoEscape :: IdSet -> StgExpr -> UniqSM StgExpr
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
    StgCase (StgApp noExtSilent id []) bndr altTy [(DEFAULT, [], expr)]

-- Create a ConApp which is guaranteed to evaluate the given ids.
mkSeqs :: [Id] -> DataCon -> [StgArg] -> [Type] -> UniqSM StgExpr
mkSeqs untaggedIds con args tys = do
    argMap <- mapM (\arg -> (arg,) <$> mkLocalArgId arg ) untaggedIds :: UniqSM [(InId, OutId)]
    -- pprTraceM "Forcing strict args:" (ppr argMap)
    mapM (pprTraceM "Forcing strict args:" . ppr) argMap
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
    pprTraceM "mkTopConEval" ( empty
        -- $$ text "evalStrictnesses" <+> ppr (map idStrictness needsEval)
        -- $$ text "argIdInfos - useage" <+> ppr (map idStrictness possiblyUntagged)
        )

    -- We don't need to pass the [Type] as top level binds are never unlifted
    -- tuples and it's the only case where they are used.
    body <- mkSeqs needsEval con args []
    return $ (StgRhsClosure noExtSilent ccs ReEntrant [] body)

















{-# NOINLINE stgAna #-}
stgAna :: [CgStgTopBinding] -> [CgStgTopBinding]
stgAna = map anaTopBind

anaTopBind :: CgStgTopBinding -> CgStgTopBinding
anaTopBind lit@StgTopStringLit {} = lit
anaTopBind (StgTopLifted bind) =
    StgTopLifted $ anaBind emptyEnv bind

anaBind :: IdSet -> CgStgBinding -> CgStgBinding
anaBind env (StgNonRec v rhs) =
    StgNonRec v $ anaRhs env rhs
anaBind env (StgRec binds) =
    StgRec $ map (second (anaRhs env)) binds

anaRhs :: IdSet -> CgStgRhs -> CgStgRhs
anaRhs _env e@(StgRhsCon {}) = e -- TODO: Strict fields
anaRhs env (StgRhsClosure _ext _ccs _flag _args body)
    = StgRhsClosure _ext _ccs _flag _args $
        anaExpr env body

-- We keep a set of already evaluated ids.
anaExpr :: IdSet -> CgStgExpr -> CgStgExpr
anaExpr env (e@StgCase {})          = anaCase env e
anaExpr env (e@StgLet {})           = anaLet env e
anaExpr env (e@StgLetNoEscape {})   = anaLetNoEscape env e
anaExpr env (StgTick t e)           = StgTick t $ anaExpr env e

anaExpr _env e@(StgApp _ _f _args)          = e
anaExpr _env e@(StgLit _lit)                = e
anaExpr _env e@(StgConApp _con _args _tys)  = e
anaExpr _env e@(StgOpApp _op _args _ty)     = e
anaExpr _env   (StgLam {}) = error "Invariant violated: No lambdas in finalized STG representation."


anaCase :: IdSet -> CgStgExpr -> CgStgExpr
anaCase env (StgCase scrut bndr ty alts) =
    -- pprTrace "anaCase:" (text "scrut" <+> ppr scrut $$ text "env'" <+> ppr env' $$
    --     text "env" <+> ppr env $$ text "redundant" <+> ppr redundantEvaled) $
    (StgCase scrut' bndr ty alts')
  where
    scrut'
        | StgApp _ v [] <- scrut
        , isTagged env v
        =
            pprTrace "Marking:" (ppr v) $
            StgApp MarkedStrict v []
        | otherwise
            = anaExpr env scrut
    alts' = map (anaAlt env') alts
    env'
      -- After unaris (where we are) unboxed tuples binders are never in scope
      | stgCaseBndrInScope ty True = extendVarSet env bndr
      | otherwise = env

anaCase _ _ = error "Not a case"

anaAlt :: IdSet -> CgStgAlt -> CgStgAlt
anaAlt env (con@(DataAlt dcon), binds, rhs)
    | (not . null) strictBinds
    -- Extract strictness information for dcon.
    =
        -- pprTrace "strictDataConBinds" (
        --     ppr con <+> ppr (strictBinds)
        --     ) $
            (con, binds, anaExpr (env') rhs)
    | otherwise = (con, binds, anaExpr env rhs)
  where
    env' = extendVarSetList env (strictBinds)

    -- zip binds types
    -- tyConDataCons_maybe = mapMaybe tyConDataCons_maybe tyCons

    -- smallFamily = dataConRepArgTys
    strictSigs = dataConRepStrictness dcon
    strictBinds = map snd $ filter (\(s,_v) -> isMarkedStrict s) $ zip strictSigs binds
anaAlt env (con, binds, rhs) = (con, binds, anaExpr env rhs)

-- TODO: Theoretically we could have code of the form:
-- let x = Con in case x of ... e ...
-- However I haven't seen this occure in all of nofib, so omitting checking
-- for this case at this time.
anaLet :: IdSet -> CgStgExpr -> CgStgExpr
anaLet env (StgLet ext bind body)
    = let tagged = taggedByBind True bind
          env'   = extendVarSetList env tagged
      in  StgLet ext (anaBind env bind) (anaExpr env' body)
anaLet _ _ = panic "Not a Let"

anaLetNoEscape :: IdSet -> CgStgExpr -> CgStgExpr
anaLetNoEscape env (StgLetNoEscape ext bind body)
    = StgLetNoEscape ext (anaBind env bind) (anaExpr env body)
anaLetNoEscape _ _
    = panic "Not a LetNoEscape"


