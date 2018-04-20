module Match where

import GhcPrelude
import Var      ( Id )
import TcType   ( Type )
import DsMonad  ( DsM, EquationInfo, MatchResult )
import CoreSyn  ( CoreExpr )
import HsSyn    ( LPat, HsMatchContext, MatchGroup, LHsExpr )
import HsPat    ( Pat )
import Name     ( Name )
-- import HsExtension ( Id )
import Util (HasCallStack)

match   :: HasCallStack => [Id]
        -> Type
        -> [EquationInfo]
        -> DsM MatchResult

matchWrapper
        :: HasCallStack
        => HsMatchContext Name
        -> Maybe (LHsExpr Id)
        -> MatchGroup Id (LHsExpr Id)
        -> DsM ([Id], CoreExpr)

matchSimply
        :: HasCallStack
        => CoreExpr
        -> HsMatchContext Name
        -> LPat Id
        -> CoreExpr
        -> CoreExpr
        -> DsM CoreExpr

matchSinglePat
        :: HasCallStack
        => CoreExpr
        -> HsMatchContext Name
        -> LPat Id
        -> Type
        -> MatchResult
        -> DsM MatchResult
