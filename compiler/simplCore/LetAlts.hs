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
import Unique           ( Unique, getUnique )
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
import Var
import Data.Foldable

{-
Current issues:
* The code fails when the let can't be made a join point, as we might try to jump
  into a join point from a different closure.
*
-}

letAlts :: DynFlags -> UniqSupply -> CoreProgram -> CoreProgram --, UniqSupply)
letAlts dflags us pgm =
    pgm
    -- -- (pgm,us)
    -- fst . initUs us $ do
    --     res <- mapM lettifyTop pgm
    --     return $ --pprTrace "letAlts" (ppr res)
    --         res

lettifyTopBind :: Id -> CoreExpr -> UniqSM (Id,CoreExpr)
lettifyTopBind v rhs = do
    (rhs', bnds) <- lettifyExpr rhs
    --pprTraceM ("letRHS:") $ ppr rhs'
    let rhs'' =
            -- occurAnalyseExpr .
            -- simpleOptExpr .
            -- occurAnalyseExpr .
            -- callArityRHS .
            -- occurAnalyseExpr .
            -- cseOneExpr .
            --simpleOptExpr .
            -- cseOneExpr .
            occurAnalyseExpr .
            callArityRHS .
            mkCoreLets bnds $ rhs'

    -- pprTraceM "topRHS" $ ppr rhs''
    let ids = (getIds rhs'')
    -- pprTraceM "ids" $ ( ppr ids $$
    --                     text "tailCalled" <+> ppr (map (isAlwaysTailCalled . idOccInfo) ids) $$
    --                     text "idDetails" <+> ppr (map (idDetails) ids)
    --                     )

    return (v, rhs'')

lettifyTop :: CoreBind -> UniqSM OutBind
lettifyTop (NonRec v rhs) = do
    (v',rhs') <- lettifyTopBind v rhs
    return $ NonRec v' rhs'
lettifyTop (Rec binds) = do
    binds' <- mapM (uncurry lettifyTopBind) binds
    return $ Rec binds'

getIds :: CoreExpr -> [Id]
getIds expr =
    catMaybes $ mapExpr f expr
  where
    f (Var v) = Just v
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


    return $ (mkCoreLets (concat binds) (Case scrut bnd ty alts), [])

wrapAlt :: Type -> InAlt -> UniqSM (OutAlt, [OutBind])
wrapAlt ty alt@(con, args, expr)
  | exprIsTrivial expr = do
        (expr', bnds') <- lettifyExpr expr
        return (alt, [])
  | otherwise = do
    (expr', bnds') <- lettifyExpr expr
    let vars = filter abstractVar . uniqDSetToList $ exprFreeVarsDSet expr :: [Var]
    --pprTraceM "vars:" (ppr vars)
    let bndTy = mkLamTypes vars ty
    --pprTraceM "lamTy:" (ppr bndTy)
    id' <- mkSysLocalOrCoVarM (fsLit "cseAlts") bndTy
    let id = if exprSize expr' > 50
                then id' --modifyIdInfo (`setInlinePragInfo` neverInlinePragma) id'
                else id'
    --pprTraceM "id:" (ppr id)

    lamVars <- mapM (mkSysLocalOrCoVarM (fsLit "lamVar") . varType) vars
    let free = nonDetEltsUniqSet  $ exprFreeVars expr'
    let subst = extendInScopeList emptySubst free
    -- pprTraceM "vars" (ppr vars $$ ppr lamVars)
    let subst' = foldl' (uncurry . extendSubstWithVar) subst $ zip vars lamVars
    let expr'' = substExpr (text "lamSub") subst' expr'

    let lam = mkCoreLams lamVars expr''
    --pprTraceM "lam:" (ppr lam)
    let bind = NonRec id lam
    --pprTraceM "bind" (ppr bind)
    let altExpr = mkCoreApps (Var id) (map Var vars)
    let altExpr' = mkCoreLets (bnds' ++ [bind]) altExpr
    return ((con,args,altExpr'), [])
  where
    abstractVar x
        | isTyVar x = False
        | isCoVar x = False
        | isJoinId x = False
        | isExportedId x = False
        | isGlobalId x = False
        | otherwise = True



lettifyBind :: InBind -> UniqSM (OutBind, [CoreBind])
lettifyBind (NonRec v expr) = do
    (expr',binds) <- lettifyExpr expr
    return (NonRec v expr', binds)
lettifyBind x@(Rec _binds) = do
    return (x, [])

pprTraceM :: Monad m => String -> SDoc -> m ()
pprTraceM s o = pprTrace s o (return ())

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