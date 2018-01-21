
-- (those who have too heavy dependencies for TcEvidence)
module TcEvTerm
    ( evDelayedError, evCallStack, evTypeable)

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
import TyCon
import Outputable
import MkId
import TysWiredIn
import Control.Monad (zipWithM)

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
evCallStack :: (MonadThings m, HasModule m, HasDynFlags m) =>
    EvCallStack -> m CoreExpr
-- See Note [Overview of implicit CallStacks] in TcEvidence.hs
evCallStack cs = do
  df            <- getDynFlags
  m             <- getModule
  srcLocDataCon <- lookupDataCon srcLocDataConName
  let mkSrcLoc l = mkCoreConApps srcLocDataCon <$>
               sequence [ mkStringExprFS (unitIdFS $ moduleUnitId m)
                        , mkStringExprFS (moduleNameFS $ moduleName m)
                        , mkStringExprFS (srcSpanFile l)
                        , return $ mkIntExprInt df (srcSpanStartLine l)
                        , return $ mkIntExprInt df (srcSpanStartCol l)
                        , return $ mkIntExprInt df (srcSpanEndLine l)
                        , return $ mkIntExprInt df (srcSpanEndCol l)
                        ]

  emptyCS <- Var <$> lookupId emptyCallStackName

  pushCSVar <- lookupId pushCallStackName
  let pushCS name loc rest =
        mkCoreApps (Var pushCSVar) [mkCoreTup [name, loc], rest]

  let mkPush name loc tm = do
        nameExpr <- mkStringExprFS name
        locExpr <- mkSrcLoc loc
        -- at this point tm :: IP sym CallStack
        -- but we need the actual CallStack to pass to pushCS,
        -- so we use unwrapIP to strip the dictionary wrapper
        -- See Note [Overview of implicit CallStacks]
        let ip_co = unwrapIP (exprType tm)
        return (pushCS nameExpr locExpr (Cast tm ip_co))

  case cs of
    EvCsPushCall name loc tm -> mkPush (occNameFS $ getOccName name) loc tm
    EvCsEmpty -> return emptyCS

evTypeable :: MonadThings m => Type -> EvTypeable -> m CoreExpr
-- Return a CoreExpr :: Typeable ty
-- This code is tightly coupled to the representation
-- of TypeRep, in base library Data.Typeable.Internals
evTypeable ty ev
  = do { tyCl <- lookupTyCon typeableClassName    -- Typeable
       ; let kind = typeKind ty
             Just typeable_data_con
                 = tyConSingleDataCon_maybe tyCl    -- "Data constructor"
                                                    -- for Typeable

       ; rep_expr <- ds_ev_typeable ty ev           -- :: TypeRep a

       -- Package up the method as `Typeable` dictionary
       ; return $ mkConApp typeable_data_con [Type kind, Type ty, rep_expr] }

type TypeRepExpr = CoreExpr

-- | Returns a @CoreExpr :: TypeRep ty@
ds_ev_typeable :: MonadThings m => Type -> EvTypeable -> m CoreExpr
ds_ev_typeable ty (EvTypeableTyCon tc kind_ev)
  = do { mkTrCon <- lookupId mkTrConName
                    -- mkTrCon :: forall k (a :: k). TyCon -> TypeRep k -> TypeRep a
       ; someTypeRepTyCon <- lookupTyCon someTypeRepTyConName
       ; someTypeRepDataCon <- lookupDataCon someTypeRepDataConName
                    -- SomeTypeRep :: forall k (a :: k). TypeRep a -> SomeTypeRep

       ; tc_rep <- tyConRep tc                      -- :: TyCon
       ; let ks = tyConAppArgs ty
             -- Construct a SomeTypeRep
             toSomeTypeRep :: MonadThings m => Type -> EvTerm -> m CoreExpr
             toSomeTypeRep t ev = do
                 rep <- getRep ev t
                 return $ mkCoreConApps someTypeRepDataCon [Type (typeKind t), Type t, rep]
       ; kind_arg_reps <- zipWithM toSomeTypeRep ks kind_ev   -- :: TypeRep t
       ; let -- :: [SomeTypeRep]
             kind_args = mkListExpr (mkTyConTy someTypeRepTyCon) kind_arg_reps

         -- Note that we use the kind of the type, not the TyCon from which it
         -- is constructed since the latter may be kind polymorphic whereas the
         -- former we know is not (we checked in the solver).
       ; let expr = mkApps (Var mkTrCon) [ Type (typeKind ty)
                                         , Type ty
                                         , tc_rep
                                         , kind_args ]
       -- ; pprRuntimeTrace "Trace mkTrTyCon" (ppr expr) expr
       ; return expr
       }

ds_ev_typeable ty (EvTypeableTyApp ev1 ev2)
  | Just (t1,t2) <- splitAppTy_maybe ty
  = do { e1  <- getRep ev1 t1
       ; e2  <- getRep ev2 t2
       ; mkTrApp <- lookupId mkTrAppName
                    -- mkTrApp :: forall k1 k2 (a :: k1 -> k2) (b :: k1).
                    --            TypeRep a -> TypeRep b -> TypeRep (a b)
       ; let (k1, k2) = splitFunTy (typeKind t1)
       ; let expr =  mkApps (mkTyApps (Var mkTrApp) [ k1, k2, t1, t2 ])
                            [ e1, e2 ]
       -- ; pprRuntimeTrace "Trace mkTrApp" (ppr expr) expr
       ; return expr
       }

ds_ev_typeable ty (EvTypeableTrFun ev1 ev2)
  | Just (t1,t2) <- splitFunTy_maybe ty
  = do { e1 <- getRep ev1 t1
       ; e2 <- getRep ev2 t2
       ; mkTrFun <- lookupId mkTrFunName
                    -- mkTrFun :: forall r1 r2 (a :: TYPE r1) (b :: TYPE r2).
                    --            TypeRep a -> TypeRep b -> TypeRep (a -> b)
       ; let r1 = getRuntimeRep t1
             r2 = getRuntimeRep t2
       ; return $ mkApps (mkTyApps (Var mkTrFun) [r1, r2, t1, t2])
                         [ e1, e2 ]
       }

ds_ev_typeable ty (EvTypeableTyLit dict)
  = do { fun  <- lookupId tr_fun
       ; let proxy = mkTyApps (Var proxyHashId) [ty_kind, ty]
       ; return (mkApps (mkTyApps (Var fun) [ty]) [ dict, proxy ]) }
  where
    ty_kind = typeKind ty

    -- tr_fun is the Name of
    --       typeNatTypeRep    :: KnownNat    a => Proxy# a -> TypeRep a
    -- of    typeSymbolTypeRep :: KnownSymbol a => Proxy# a -> TypeRep a
    tr_fun | ty_kind `eqType` typeNatKind    = typeNatTypeRepName
           | ty_kind `eqType` typeSymbolKind = typeSymbolTypeRepName
           | otherwise = panic "dsEvTypeable: unknown type lit kind"

ds_ev_typeable ty ev
  = pprPanic "dsEvTypeable" (ppr ty $$ ppr ev)

getRep :: MonadThings m
       => EvTerm          -- ^ EvTerm for @Typeable ty@
       -> Type            -- ^ The type @ty@
       -> m TypeRepExpr -- ^ Return @CoreExpr :: TypeRep ty@
                          -- namely @typeRep# dict@
-- Remember that
--   typeRep# :: forall k (a::k). Typeable k a -> TypeRep a
getRep ev ty
  = do { typeRepId     <- lookupId typeRepIdName
       ; let ty_args = [typeKind ty, ty]
       ; return (mkApps (mkTyApps (Var typeRepId) ty_args) [ ev ]) }

tyConRep :: MonadThings m => TyCon -> m CoreExpr
-- Returns CoreExpr :: TyCon
tyConRep tc
  | Just tc_rep_nm <- tyConRepName_maybe tc
  = do { tc_rep_id <- lookupId tc_rep_nm
       ; return (Var tc_rep_id) }
  | otherwise
  = pprPanic "tyConRep" (ppr tc)
