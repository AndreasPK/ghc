-- | Smart constructors for EvTerm
-- (those who have too heavy dependencies for TcEvidence)
module TcEvTerm
    ( evDelayedError, evLit, evCallStack, evTypeable)

where

import GhcPrelude

import FastString
import Var
import Type
import CoreSyn
import CoreUtils
import Class ( classSCSelId )
import Id ( isEvVar )
import CoreFVs ( exprSomeFreeVars )
import MkCore ( tYPE_ERROR_ID )
import Literal ( Literal(..) )
import TcEvidence

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
evLit :: EvLit -> EvTerm
evLit = undefined

-- Dictionary for CallStack implicit parameters
evCallStack :: EvCallStack -> EvTerm
evCallStack = undefined

-- Dictionary for (Typeable ty)
evTypeable :: Type -> EvTypeable -> EvTerm
evTypeable = undefined
