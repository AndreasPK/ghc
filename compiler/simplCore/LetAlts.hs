module LetAlts ( letAlts ) where

import GhcPrelude

import CoreSubst
import Var              ( Var )
import VarEnv           ( elemInScopeSet, mkInScopeSet )
import Id               ( Id, idType, idInlineActivation, isDeadBinder
                        , zapIdOccInfo, zapIdUsageInfo, idInlinePragma
                        , isJoinId

                        , mkSysLocalOrCoVar )
import CoreUtils        ( mkAltExpr, eqExpr
                        , exprIsTickedString
                        , stripTicksE, stripTicksT, mkTicks )
import CoreFVs          ( exprFreeVars )
import Type             ( tyConAppArgs )
import CoreSyn
import Outputable
import BasicTypes       ( TopLevelFlag(..), isTopLevel
                        , isAlwaysActive, isAnyInlinePragma,
                          inlinePragmaSpec, noUserInlineSpec )
import TrieMap
import Util             ( filterOut, third3 )
import Data.List        ( mapAccumL )

import System.IO.Unsafe (unsafePerformIO)
import Unique (Unique, getUnique)
import Type (Type)
import FastString (fsLit)

import CoreFVs( exprFreeVarsDSet )
import CoreSyn
import CoreUtils
import MkCore
import CoreArity        ( etaExpand )
import CoreMonad        ( FloatOutSwitches(..) )

import DynFlags
import ErrUtils         ( dumpIfSet_dyn )
import Id               ( Id, idArity, idType, isBottomingId,
                          isJoinId, isJoinId_maybe )
import SetLevels
import UniqSupply       ( UniqSupply, initUs, UniqSM, getUniqueM )
import Bag
import Util
import Maybes
import Outputable
import Type
import qualified Data.IntMap as M

import Data.List        ( partition )

import VarSet
import UniqSet
import UniqDSet
import CoreOpt
import Debug.Trace
import OccurAnal
import CSE
import CoreOpt
import Id
import BasicTypes
import CallArity
import IdInfo
import CoreStats
import CoreArity

letAlts :: DynFlags -> UniqSupply -> CoreProgram -> CoreProgram --, UniqSupply)
letAlts dflags us pgm =
    pgm
    -- fst . initUs us $ do
    --     res <- mapM lettifyTop pgm
    --     return $ --pprTrace "letAlts" (ppr res)
    --         res


lettifyTop :: CoreBind -> UniqSM OutBind
lettifyTop idRes@(NonRec v rhs) = do
    (rhs', bnds) <- lettifyExpr rhs
    --pprTraceM ("letRHS:") $ ppr rhs'
    let rhs'' =
            -- occurAnalyseExpr .
            -- simpleOptExpr .
            -- occurAnalyseExpr .
            callArityRHS .
            occurAnalyseExpr .
            --simpleOptExpr .
            cseOneExpr .
            occurAnalyseExpr .
            callArityRHS .
            mkCoreLets bnds $ rhs'

    pprTraceM "topRHS" $ ppr rhs''
    pprTraceM "topArities" $ getLamArity rhs''
    let ids = (getIds rhs'')
    pprTraceM "ids" $ ( ppr ids $$
                        text "tailCalled" <+> ppr (map (isAlwaysTailCalled . idOccInfo) ids) $$
                        text "idDetails" <+> ppr (map (idDetails) ids)
                        )

    return (NonRec v rhs'')

getIds :: CoreExpr -> [Id]
getIds expr =
    catMaybes $ mapExpr f expr
  where
    f (Var v) = Just v
    f _ = Nothing

getLamArity :: CoreExpr -> SDoc
getLamArity expr =
    ppr pairs
  where
    pairs = zipWith (\id expr -> (id, joinRhsArity expr)) ids rhss
    ids = bindersOfBinds binds
    rhss = concatMap (rhssOfBind) binds
    binds = catMaybes $ mapExpr f expr
    f (Let b body) = Just b
    f _ = Nothing



lettifyExpr :: InExpr -> UniqSM (OutExpr, [CoreBind])
lettifyExpr expr =
    case expr of
        Var id ->
            return (expr, [])
        Lit lit ->
            return (expr, [])
        App e1 e2 -> do
            (e1' , b1) <- lettifyExpr e1
            (e2', b2)  <- lettifyExpr e2
            return (App e1' e2', b1 ++ b2)
        Lam b e -> do
            (e', b1) <- lettifyExpr e
            return (Lam b e', b1)
        Let bndr body -> do
            (body', b1) <- lettifyExpr body
            (bndr', b2) <- lettifyBind bndr
            return (Let bndr' body', b1 ++ b2)
        Case scrut v ty alts -> lettifyCase scrut v ty alts
        Cast e co -> do
            (e', b1) <- lettifyExpr e
            return (Cast e co, b1)
        Tick tick e -> do
            (e', b1) <- lettifyExpr e
            return (Tick tick e', b1)
        Type t -> return (Type t, [])
        Coercion co -> return (expr, [])

lettifyCase :: InExpr -> InVar -> Type -> [InAlt] -> UniqSM (OutExpr, [CoreBind])
lettifyCase scrut bnd ty alts = do

    (alts,binds) <- unzip <$> mapM (wrapAlt ty) alts

    return (Case scrut bnd ty alts, concat binds)

wrapAlt :: Type -> InAlt -> UniqSM (OutAlt, [OutBind])
wrapAlt ty alt@(con, args, expr)
  | exprIsTrivial expr = do
        (expr', bnds') <- lettifyExpr expr
        return (alt, [])
  | otherwise = do
    (expr', bnds') <- lettifyExpr expr
    let vars = uniqDSetToList $ exprFreeVarsDSet expr :: [Var]
    unq <- getUniqueM
    --pprTraceM "vars:" (ppr vars)
    let bndTy = mkLamTypes vars ty
    pprTraceM "lamTy:" (ppr bndTy)
    let id' = mkSysLocalOrCoVar (fsLit "cseAlts_") unq bndTy
    let id = if exprSize expr' > 600
                then modifyIdInfo (`setInlinePragInfo` neverInlinePragma) id'
                else id'
    --pprTraceM "id:" (ppr id)
    let lam = mkCoreLams vars expr'
    --pprTraceM "lam:" (ppr lam)
    --pprTraceM "lamJoinArity" (ppr $ joinRhsArity lam)
    let bind = NonRec id lam
    --pprTraceM "bind" (ppr bind)
    let altExpr = mkCoreApps (Var id) (map Var vars)
    --pprTraceM "rhs" (ppr altExpr)
    --pprTraceM "maybeJoin" (ppr $ joinPointBinding_maybe id lam)
    return ((con,args,altExpr), bnds' ++ [bind])



lettifyBind :: InBind -> UniqSM (OutBind, [CoreBind])
lettifyBind bnd = return (bnd, [])

mapExpr :: (CoreExpr -> a) -> CoreExpr -> [a]
mapExpr f expr =
    go expr
  where
    go e@(Var id) = [f e]
    go e@(Lit id) = [f e]
    go e@(App e1 e2) = [f e] ++ go e1 ++ go e2
    go e@(Lam b e1) = f e : go e1
    go e@(Let bndr body) = f e : (concatMap go (rhssOfBind bndr) ++ go body)
    go e@(Case e1 _ _ alts) = (f e) : (go e1 ++ concatMap go (rhssOfAlts alts))
    go e@(Cast e1 _) = f e : go e1
    go e@(Type _) = [f e]
    go e@(Coercion _) = [f e]