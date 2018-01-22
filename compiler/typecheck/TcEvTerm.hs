
-- (those who have too heavy dependencies for TcEvidence)
module TcEvTerm
    ( evDelayedError )
where

import GhcPrelude

import FastString
import Type
import CoreSyn
import MkCore
import Literal ( Literal(..) )
import TcEvidence
import HscTypes
import DynFlags
import Name
import Module
import CoreUtils
import PrelNames
import SrcLoc

-- Used with Opt_DeferTypeErrors
-- See Note [Deferring coercion errors to runtime]
-- in TcSimplify
evDelayedError :: Type -> FastString -> EvTerm
evDelayedError ty msg
  = EvExpr $ Var errorId `mkTyApps` [getRuntimeRep ty, ty] `mkApps` [litMsg]
  where
    errorId = tYPE_ERROR_ID
    litMsg  = Lit (MachStr (fastStringToByteString msg))
