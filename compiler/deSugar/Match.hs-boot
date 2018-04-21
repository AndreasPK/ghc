module Match where

import GhcPrelude
import Var      ( Id )
import TcType   ( Type )
import DsMonad  ( DsM, EquationInfo, MatchResult )
import CoreSyn  ( CoreExpr )
import HsSyn    ( LPat, HsMatchContext, MatchGroup, LHsExpr, GhcTc )
import HsPat    ( Pat )
import Name     ( Name )
-- import HsExtension ( Id )
import Util (HasCallStack)

match   :: HasCallStack => [Id]
        -> Type
        -> [EquationInfo]
        -> DsM MatchResult

matchWrapper :: HasCallStack
             => HsMatchContext Name    -- For shadowing warning messages
             -> Maybe (LHsExpr GhcTc)  -- The scrutinee, if we check a case expr
             -> MatchGroup GhcTc (LHsExpr GhcTc)   -- Matches being desugared
             -> DsM ([Id], CoreExpr)   -- Results

matchSimply
        :: HasCallStack
        => CoreExpr
        -> HsMatchContext Name
        -> LPat GhcTc
        -> CoreExpr
        -> CoreExpr
        -> DsM CoreExpr

matchSinglePat
        :: HasCallStack
        => CoreExpr
        -> HsMatchContext Name
        -> LPat GhcTc
        -> Type
        -> MatchResult
        -> DsM MatchResult
