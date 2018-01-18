module Match where

import GhcPrelude
import BasicTypes (BranchWeight)
import Var      ( Id )
import TcType   ( Type )
import DsMonad  ( DsM, EquationInfo, MatchResult )
import CoreSyn  ( CoreExpr )
import HsSyn    ( LPat, HsMatchContext, MatchGroup, LHsExpr )
import Name     ( Name )
import HsExtension ( GhcTc )

match   :: [Id]
        -> Type
        -> [EquationInfo]
        -> Maybe BranchWeight
        -> DsM (MatchResult, Maybe BranchWeight)

matchWrapper
        :: HsMatchContext Name
        -> Maybe (LHsExpr GhcTc)
        -> MatchGroup GhcTc (LHsExpr GhcTc)
        -> DsM ([Id], CoreExpr)

matchSimply
        :: CoreExpr
        -> HsMatchContext Name
        -> LPat GhcTc
        -> CoreExpr
        -> CoreExpr
        -> Maybe (BranchWeight, BranchWeight)
        -> DsM CoreExpr

matchSinglePatVar
        :: Id
        -> HsMatchContext Name
        -> LPat GhcTc
        -> Type
        -> MatchResult
        -> Maybe BranchWeight
        -> Maybe BranchWeight
        -> DsM MatchResult
