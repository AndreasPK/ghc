-- | Smart constructors for EvTerm
-- (those who have too heavy dependencies for TcEvidence)
module TcEvTerm
    ( evDelayedError, evLit, evCallStack, evTypeable)

where

import GhcPrelude

import FastString
import Type
import CoreSyn
import MkCore ( tYPE_ERROR_ID, mkStringExprFS, mkNaturalExpr )
import Literal ( Literal(..) )
import TcEvidence
import HscTypes

-- Used with Opt_DeferTypeErrors
-- See Note [Deferring coercion errors to runtime]
-- in TcSimplify
evDelayedError :: Type -> FastString -> EvTerm
evDelayedError ty msg
  = Var errorId `mkTyApps` [getRuntimeRep ty, ty] `mkApps` [litMsg]
  where
    errorId = tYPE_ERROR_ID
    litMsg  = Lit (MachStr (fastStringToByteString msg))

-- Dictionary for KnownNat and KnownSymbol classes.
-- Note [KnownNat & KnownSymbol and EvLit]
evLit :: MonadThings m => EvLit -> m EvTerm
evLit (EvNum n) = mkNaturalExpr n
evLit (EvStr n) = mkStringExprFS n

-- Dictionary for CallStack implicit parameters
evCallStack :: EvCallStack -> EvTerm
evCallStack = undefined

-- Dictionary for (Typeable ty)
evTypeable :: Type -> EvTypeable -> EvTerm
evTypeable = undefined
