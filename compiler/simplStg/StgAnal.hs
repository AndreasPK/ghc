--
-- Copyright (c) 2019 Andreas Klebinger
--

{-# LANGUAGE TypeFamilies, RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs #-}

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

    Currently this is done in a single top down pass over STG functions.
    We keep a set of evaluated bindings and tag Applications with their
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
-}

module StgAnal (stgAna) where

import GhcPrelude

import DataCon
import Data.Bifunctor
import Id
import StgSyn
import Outputable
import VarEnv
import CoreSyn (AltCon(..))
import Data.List (mapAccumL)
import Data.Maybe (fromMaybe)
import CoreMap
import NameEnv
import Control.Monad( (>=>) )
import VarSet

import Hoopl.Collections
import PrimOp

emptyEnv :: IdSet
emptyEnv = emptyVarSet

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
anaExpr env (e@StgCase {}) = anaCase env e
anaExpr env (e@StgLet {}) = anaLet env e
anaExpr env (e@StgLetNoEscape {}) = anaLetNoEscape env e
anaExpr env (StgTick t e) = StgTick t $ anaExpr env e

anaExpr _env e@(StgApp _ _f _args) = e
anaExpr _env e@(StgLit _lit) = e
anaExpr _env e@(StgConApp _con _args _tys) = e
anaExpr _env e@(StgOpApp _op _args _ty) = e
anaExpr _env e@(StgLam {}) = error "Invariant violated: No lambdas in finalized STG representation."


anaCase :: IdSet -> CgStgExpr -> CgStgExpr
anaCase env (StgCase scrut bndr _ty alts) =
    -- pprTrace "anaCase:" (text "scrut" <+> ppr scrut $$ text "env'" <+> ppr env' $$
    --     text "env" <+> ppr env $$ text "redundant" <+> ppr redundantEvaled) $
    (StgCase scrut' bndr _ty alts')
  where
    alts' = map (anaAlt env') alts
    -- Tag already evaluated bindings
    scrut'
        | StgApp _ v [] <- scrut
        , elemVarSet v env
        =
            -- pprTrace "Marking:" (ppr v) $
            StgApp MarkedStrict v []
        | otherwise = scrut

    env' = extendVarSet env bndr

anaCase _ _ = error "Not a case"

anaAlt :: IdSet -> CgStgAlt -> CgStgAlt
anaAlt env (con, binds, rhs)
    | DataAlt dcon <- con
    -- Extract strictness information for dcon.
    = let   strictSigs = dataConRepStrictness dcon
            strictBinds = filterWith isMarkedStrict binds strictSigs
            env' = extendVarSetList env strictBinds
      in (con, binds, anaExpr env' rhs)
    | otherwise = (con, binds, anaExpr env rhs)

-- TODO: Theoretically we could have code of the form:
-- let x = Con in case x of ... e ...
-- However I haven't seen this occure in all of nofib, so omitting checking
-- for this case at this time.
anaLet env (StgLet ext bind body)
    = StgLet ext (anaBind env bind) (anaExpr env body)
anaLet _ _ = panic "Not a Let"

anaLetNoEscape env (StgLetNoEscape ext bind body)
    = StgLetNoEscape ext (anaBind env bind) (anaExpr env body)
anaLetNoEscape _ _
    = panic "Not a LetNoEscape"

-- | Keep elements from a if f returns true for the matching element in bs
filterWith :: (b -> Bool) -> [a] -> [b] -> [a]
filterWith f xs ys = map fst . filter (f . snd) $ zip xs ys
