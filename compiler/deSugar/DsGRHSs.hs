{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998


Matching guarded right-hand-sides (GRHSs)
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

module DsGRHSs ( dsGuarded, dsGRHSs, dsGRHS, isTrueLHsExpr ) where

#include "HsVersions.h"

import GhcPrelude
import Control.Monad (when, liftM2)

import {-# SOURCE #-} DsExpr  ( dsLExpr, dsLocalBinds )
import {-# SOURCE #-} Match   ( matchSinglePatVar )

import HsSyn
import MkCore
import CoreSyn
import CoreUtils (bindNonRec)

import BasicTypes (BranchWeight(..), combineWeightsMaybe, neverFreq)
import BasicTypes
import Data.Maybe (listToMaybe, catMaybes)
import Check (genCaseTmCs2)
import DsMonad
import DsUtils
import Type   ( Type )
import Name
import Util
import SrcLoc
import Outputable

{-
@dsGuarded@ is used for pattern bindings.
It desugars:
\begin{verbatim}
        | g1 -> e1
        ...
        | gn -> en
        where binds
\end{verbatim}
producing an expression with a runtime error in the corner if
necessary.  The type argument gives the type of the @ei@.
-}

{- Note [Matching weighted guards]
When desugaring guards of the form:
foo x
  | cond1 =     { -# LIKELY w1 #- } e1
  | cond2 =     { -# LIKELY w2 #- } e2
  ...
  | otherwise = { -# LIKELY wn #- } eother

We translate this such that we get
if (cond1)
  then { -# LIKELY w1 #- } e1
  else { -# LIKELY w2 + w3 + .. + wn #- }
    if (cond2) ...
      else { -# LIKELY w3 + .. + wn #- }
      ...

We also assume guards are always exhaustive. Why?
Consider the following code:

  foo x
    | cond1 ...
  foo (Just x)
    | cond2 ...
    | cond3 ...

When desugaring the first guarded RHS we currently have no way
to know what weight to use for failure of the first guard.

We could restructure the compiler code to make this work two ways:
* Each function that produces a potentially failing @MatchResult@ takes
  a weight to use for the failure case.
  Then proceed desugaring "back to front" passing weights along as we do
  so.
* Change MatchResult to take a (optional) BranchWeight argument.
  So instead of producing a result of `Expr -> DsM Expr` we get results
  in the form of `(Maybe Weight,Expr) -> DsM Expr`

For now I've gone with the former. Pattern matches which make heavy use of
backtracking and would benefit from the later more are also of the kind to
have non-trivial desugarings. Might still worth revesiting later.

-}

dsGuarded :: GRHSs GhcTc (LHsExpr GhcTc) -> Type -> DsM CoreExpr
dsGuarded grhss rhs_ty = do
    --single alternative case, so weight not important
    (match_result,_weight) <- dsGRHSs PatBindRhs grhss rhs_ty
    error_expr <- mkErrorAppDs nON_EXHAUSTIVE_GUARDS_ERROR_ID rhs_ty empty
    extractMatchResult match_result error_expr
  where

-- In contrast, @dsGRHSs@ produces a @MatchResult@,
-- as well the total weight of all guarded expressions.
dsGRHSs :: HsMatchContext Name
        -> GRHSs GhcTc (LHsExpr GhcTc)          -- Guarded RHSs
        -> Type                                 -- Type of RHS
        -> DsM (MatchResult, Maybe BranchWeight)
dsGRHSs hs_ctx guarded@(GRHSs _ grhss binds) rhs_ty
  = ASSERT( notNull grhss ) do
      -- let totalWeight = getGRHSsWeight guarded
      (match_result,totalWeight) <- dsGuardedAlts grhss
      let match_result2 = adjustMatchResultDs (dsLocalBinds binds) match_result
                          -- NB: nested dsLet inside matchResult
      return (match_result2, totalWeight )
  where
    dsGuardedAlts :: [LGRHS GhcTc (LHsExpr GhcTc)] -> DsM (MatchResult, Maybe BranchWeight)
    dsGuardedAlts [] = return (alwaysFailMatchResult,Nothing)
    -- dsGuardedAlts [] = return (alwaysFailMatchResult,Just alwaysFreq)
    dsGuardedAlts (g:grhss) = do
      (mr_rest,w_rest) <- dsGuardedAlts grhss
      (mr,w) <- dsGRHS hs_ctx rhs_ty g w_rest
      return (combineMatchResults mr mr_rest, combineWeightsMaybe w w_rest)
dsGRHSs _ (XGRHSs _) _ = panic "dsGRHSs"

-- | Turn a @GHRS@ into a MatchResult
-- @ | gexps = e@        =>      @\fail -> case gexp of {True -> e; False -> fail}@
dsGRHS :: HsMatchContext Name -> Type -> LGRHS GhcTc (LHsExpr GhcTc)
       -> Maybe BranchWeight -- ^ Weight for the failure case relative to this grhs.
       -> DsM (MatchResult, Maybe BranchWeight)
dsGRHS hs_ctx rhs_ty (dL->L _ (GRHS _ guards rhs weight)) fail_weight
  = do let gweights = liftM2 (,) weight fail_weight :: Maybe (BranchWeight, BranchWeight)
       match_result <- matchGuards (map unLoc guards) (PatGuard hs_ctx)
                       rhs rhs_ty gweights
       return (match_result, weight)
dsGRHS _ _ (dL->L _ (XGRHS _)) _ = panic "dsGRHS"
dsGRHS _ _ _ _ = panic "dsGRHS: Impossible Match" -- due to #15884

{-
************************************************************************
*                                                                      *
*  matchGuard : make a MatchResult from a guarded RHS                  *
*                                                                      *
************************************************************************
-}

matchGuards :: [GuardStmt GhcTc]     -- Guard
            -> HsStmtContext Name    -- Context
            -> LHsExpr GhcTc         -- RHS
            -> Type                  -- Type of RHS of guard
            -> Maybe (BranchWeight,BranchWeight) -- ^ Weight for current/remaining guards.
            -> DsM MatchResult

-- See comments with HsExpr.Stmt re what a BodyStmt means
-- Here we must be in a guard context (not do-expression, nor list-comp)

matchGuards [] _ rhs _ _
  = do  { core_rhs <- dsLExpr rhs
        ; return (cantFailMatchResult core_rhs) }

        -- BodyStmts must be guards
        -- Turn an "otherwise" guard is a no-op.  This ensures that
        -- you don't get a "non-exhaustive eqns" message when the guards
        -- finish in "otherwise".
        -- NB:  The success of this clause depends on the typechecker not
        --      wrapping the 'otherwise' in empty HsTyApp or HsWrap constructors
        --      If it does, you'll get bogus overlap warnings
matchGuards (BodyStmt _ e _ _ : stmts) ctx rhs rhs_ty weights
  | Just addTicks <- isTrueLHsExpr e = do
    match_result <- matchGuards stmts ctx rhs rhs_ty weights
    return (adjustMatchResultDs addTicks match_result)
matchGuards (BodyStmt _ expr _ _ : stmts) ctx rhs rhs_ty weights = do
    match_result <- matchGuards stmts ctx rhs rhs_ty weights
    pred_expr <- dsLExpr expr
    return (mkGuardedMatchResult pred_expr match_result weights)

matchGuards (LetStmt _ binds : stmts) ctx rhs rhs_ty weights = do
    match_result <- matchGuards stmts ctx rhs rhs_ty  weights
    return (adjustMatchResultDs (dsLocalBinds binds) match_result)
        -- NB the dsLet occurs inside the match_result
        -- Reason: dsLet takes the body expression as its argument
        --         so we can't desugar the bindings without the
        --         body expression in hand

matchGuards (BindStmt _ pat bind_rhs _ _ : stmts) ctx rhs rhs_ty weights = do
    let upat = unLoc pat
        dicts = collectEvVarsPat upat
    match_var <- selectMatchVar upat
    tm_cs <- genCaseTmCs2 (Just bind_rhs) [upat] [match_var]
    match_result <- addDictsDs dicts $
                    addTmCsDs tm_cs  $
                      -- See Note [Type and Term Equality Propagation] in Check
                    matchGuards stmts ctx rhs rhs_ty weights
    core_rhs <- dsLExpr bind_rhs
    match_result' <- matchSinglePatVar match_var (StmtCtxt ctx) pat rhs_ty
                                       match_result (fst <$> weights) (snd <$> weights)
    pure $ adjustMatchResult (bindNonRec match_var core_rhs) match_result'

matchGuards (LastStmt  {} : _) _ _ _ _ = panic "matchGuards LastStmt"
matchGuards (ParStmt   {} : _) _ _ _ _ = panic "matchGuards ParStmt"
matchGuards (TransStmt {} : _) _ _ _ _ = panic "matchGuards TransStmt"
matchGuards (RecStmt   {} : _) _ _ _ _ = panic "matchGuards RecStmt"
matchGuards (ApplicativeStmt {} : _) _ _ _ _ =
  panic "matchGuards ApplicativeLastStmt"
matchGuards (XStmtLR {} : _) _ _ _ _ =
  panic "matchGuards XStmtLR"

{-
Should {\em fail} if @e@ returns @D@
\begin{verbatim}
f x | p <- e', let C y# = e, f y# = r1
    | otherwise          = r2
\end{verbatim}
-}
