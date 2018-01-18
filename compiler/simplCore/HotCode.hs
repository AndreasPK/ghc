module HotCode
  ( likelyRecursion, likelyRecursionBndr, likelyRecursionPgm
  , unlikelyBottomsPgm
  ) where

import GhcPrelude

import BasicTypes (multiplyWeight, neverFreq)
import CoreSyn
import CoreArity
-- import CoreMonad
import IdInfo
import Id

import UniqSet
import CoreMonad
import HscTypes

import Outputable

-- import Data.Foldable
import Data.Bifunctor
-- import Util (thdOf3)
-- import Outputable

-- import Debug.Trace

unlikelyBottomsPgm :: ModGuts -> CoreM ModGuts
unlikelyBottomsPgm guts = return $ guts { mg_binds = map unlikelyBottomsBndr (mg_binds guts) }

unlikelyBottomsBndr :: CoreBind -> CoreBind
unlikelyBottomsBndr (NonRec bind expr) =
  NonRec bind (unlikelyBottomsExpr expr)
unlikelyBottomsBndr (Rec bnds) =
  Rec [(b,unlikelyBottomsExpr expr) | (b,expr) <- bnds]

{- We check the termination of case alternatives,
   if they are known to be bottom we assume they
   are unlikely to be entered.
-}
unlikelyBottomsExpr :: CoreExpr -> CoreExpr
unlikelyBottomsExpr expr@(Case scrut b ty alternatives) =
  --pprTrace "CaseHot?:" (text "scrut-" <> ppr scrut) $
  Case (unlikelyBottomsExpr scrut) b ty (map updateAlt alternatives)
  where
    updateAlt :: CoreAlt -> CoreAlt
    updateAlt alt@(con, bndrs, rhs)
      | Just s@(arr, sig) <- exprBotStrictness_maybe rhs
      = --pprTrace "Sig:" (ppr $ (s,rhs)) $
        --pprTraceIt "Alt:"
        (setAltConWeight con neverFreq, bndrs, rhs)
      | otherwise
      = (con, bndrs, unlikelyBottomsExpr rhs)
unlikelyBottomsExpr e@(Var v) = e
unlikelyBottomsExpr _e@(Let binds body)
  = Let (unlikelyBottomsBndr binds) (unlikelyBottomsExpr body)
unlikelyBottomsExpr expr@(Lit {}) = expr
unlikelyBottomsExpr (App expr arg) = App (unlikelyBottomsExpr expr) (unlikelyBottomsExpr arg)
unlikelyBottomsExpr (Lam b expr) = Lam b (unlikelyBottomsExpr expr)
unlikelyBottomsExpr (Cast expr co) = Cast (unlikelyBottomsExpr expr) co
unlikelyBottomsExpr (Tick t expr) = Tick t (unlikelyBottomsExpr expr)
unlikelyBottomsExpr expr@Type {} = expr
unlikelyBottomsExpr expr@Coercion {} = expr







{-
  Note [Likely Recursion]
 ~~~~~~~~~~~~~~~~~~~~~~~

  It's obvious that for recursive functions the base case is less likely
  to be selected. Eg the x <= 0 branch will only taken once per call to
  fac below.

    fac x
      | x <= 0 = 1
      | otherwise = x * fac(x-1)

  This happens often enough that we want to optimize for the common case
  of recursion. We do this by marking all branches which lead to the
  recursive call as more likely.

  While for a human this is reasonable easy to tell it's
  harder to recognize this pattern automatically.

  This is how we go about this:
    * We collect potential recursive function binders from binders while
      stepping into the expression
    * If we find the usage of the binders we record this.
    * When stepping out of the expresion whenever we hit a case statement:
      ° We check how many usages of binders we recorded for the alts.
      ° We simply assume alts with more binder usages are more likely
        to be selected.

  This is far from perfect given that:
    * We might consider bindings as candidates which are no indication of
      recursion like join points.
    * The alternative with the most occurences might not be a recursive case.

-}

likelyRecursionPgm :: ModGuts -> CoreM ModGuts
likelyRecursionPgm guts =
  let binds' = map likelyRecursionBndr (mg_binds guts)
  in return $ guts {mg_binds = binds'}


likelyRecursionBndr :: CoreBind -> CoreBind
likelyRecursionBndr (NonRec b expr) =
--  pprTrace "NonRec recursion?"
--    (text "binder" <+> ppr b $$ text "body" <+> ppr expr)
    (NonRec b expr')
  where (_ids', expr') = if isRecCandidate False b then annotateExpr (unitUniqSet b) expr else annotateExpr mempty expr
likelyRecursionBndr (Rec binders)
  = {-pprTrace "Annotation result"
      (ppr binders $$ text "annotated" $$ ppr (zip bs exprs') $$
       text "recCalled" $$ ppr bs' $$
       text "idsFound" $$ ppr ids' $$
       text "occInfo" $$ ppr (map idDetails bs) $$
       text "bs" $$ ppr bs $$
       text "bs" $$ ppr (map idOccInfo bs) $$
       text "rec" $$ ppr (Rec binders) $$
       text "binders" $$ ppr (binders) $$
       text "head" $$ ppr (head binders)
      ) -}
      Rec (zip bs exprs')
  where
    (bs, exprs) = unzip binders
    bs' = filter (isRecCandidate True) bs
    (_ids', exprs') = unzip $ map (annotateExpr $ mkUniqSet bs') exprs

type IdSet = UniqSet Id

likelyRecursion :: CoreExpr -> CoreExpr
likelyRecursion = snd . annotateExpr mempty

{- |Check for recursion and mark the recursive case as likely.

    Given code of the form:
    func x =
        ...
          case e of
            alt1 -> baseCase
            alt2 -> f x'}

    It's reasonably that we will select the recursive case more often than
    the base case.

    We calculate this info by collecting recursively all binders which might
    be tailcalled and counting their occurences for all branches.

    If a branch does not contain tailcalled ids we assume it's unlikely to be
    selected.
-}
annotateExpr :: IdSet -> CoreExpr -> (IdSet, CoreExpr)
annotateExpr ids (Var v)
  | elementOfUniqSet v ids = (unitUniqSet v, Var v)
  | otherwise = (mempty, Var v)

--TODO: Remove sanity check
annotateExpr ids _e@(Let binder@(NonRec b _expr) body)
  | isRecCandidate False b
  = let (ids', body') = annotateExpr (addOneToUniqSet ids b) body
  in (ids', Let binder body')
  | otherwise =
  let (ids', body') = annotateExpr ids body
  in (filterUniqSet (/= b) ids', Let binder body')

annotateExpr ids (Let _binder@(Rec bindings) body) =
  --TODO: Also anotate bound expressions & check their logic
  let (binderIds, _binderExprs) = unzip bindings
      newIdList = mappend ids $ mkUniqSet (filter (isRecCandidate True) $ binderIds) :: IdSet
      (ids', body') = annotateExpr newIdList body
      bindings' = map (second (snd . annotateExpr newIdList)) bindings
  in
  (filterUniqSet (\b -> not ( b `elem` binderIds)) ids',
   Let (Rec bindings') body')

--TODO: This should be written cleaner
annotateExpr ids expr@(Case scrut b ty alternatives) =
  let (cons, bdrs, alts) = unzip3 alternatives
      (altOccs, altExprs) = unzip $ map (annotateExpr ids) alts :: ([IdSet], [CoreExpr])

      allTheSame = all (== (head altOccs)) altOccs

      (scrutOccs, scrut') = annotateExpr ids scrut

      offset = minimum $ map sizeUniqSet altOccs

      ids' = unionManyUniqSets (scrutOccs:altOccs)
      alts' = zip3 cons bdrs altExprs

      setLikelyhood :: IdSet -> CoreAlt -> CoreAlt
      setLikelyhood xs alt@(con,bdrs,altExpr)
        | isEmptyUniqSet xs = alt
        | otherwise = --pprTrace "recursionLikelyHoodSet" (ppr con) $
          let weightFactor = 1 + sizeUniqSet xs - offset
              oldWeight = altConWeight con
              con' = setAltConWeight con $ multiplyWeight oldWeight weightFactor
          in (con',bdrs,altExpr)

      newCase
        | all isEmptyUniqSet altOccs = expr
        | allTheSame = Case scrut' b ty alts'
        | otherwise = Case scrut' b ty (zipWith setLikelyhood altOccs alts')
  in (ids', newCase)

annotateExpr _ids expr@(Lit {})
  = (mempty, expr)
annotateExpr ids (App expr arg)
  = let (eids, expr') = annotateExpr ids expr
        (aids, arg') = annotateExpr ids arg
        ids' = unionUniqSets eids aids
  in (ids', App expr' arg')
annotateExpr ids (Lam b expr)
  = let (ids', expr') = annotateExpr ids expr
  in (ids', Lam b expr')
annotateExpr ids (Cast expr co)
  = let (ids', expr') = annotateExpr ids expr
  in (ids', Cast expr' co)
annotateExpr ids (Tick t expr)
  = let (ids', expr') = annotateExpr ids expr
  in (ids', Tick t expr')
annotateExpr _ids expr@Type {}
  = (mempty, expr)
annotateExpr _ids expr@Coercion {}
  = (mempty, expr)

-- | Given a id determine if it is likely used in a recursive fashion.
--   For now we simply consider all recursive lets
isRecCandidate :: Bool -> Id -> Bool
isRecCandidate isRec v
  | isAlwaysTailCalled . idOccInfo $ v = True
  | isRec = True
  | otherwise = False





{-
data Expr b
  = Var   Id
  | Lit   Literal
  | App   (Expr b) (Arg b)
  | Lam   b (Expr b)
  | Let   (Bind b) (Expr b)
  | Case  (Expr b) b Type [Alt b]       -- See #case_invariants#
  | Cast  (Expr b) Coercion
  | Tick  (Tickish Id) (Expr b)
  | Type  Type
  | Coercion Coercion
  deriving Data
  -}
