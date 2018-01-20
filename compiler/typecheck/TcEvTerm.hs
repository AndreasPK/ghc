-- | Smart constructors for EvTerm
-- (those who have too heavy dependencies for TcEvidence)
module TcEvTerm
    ( evDelayedError, evCallStack, evTypeable)

where

import GhcPrelude

import FastString
import Type
import CoreSyn
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

-- Dictionary for CallStack implicit parameters
evCallStack :: EvCallStack -> EvTerm
evCallStack = undefined

-- Dictionary for (Typeable ty)
evTypeable :: Type -> EvTypeable -> EvTerm
evTypeable = undefined
