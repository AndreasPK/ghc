module HotCode ( likelyRecursion, likelyRecursionBndr ) where

import GhcPrelude

import BasicTypes (BranchWeight(..), defFreq, multiplyWeight)
import CoreSyn
import CoreMonad
import IdInfo
import Id

import UniqDSet
import Data.Foldable
import Data.Bifunctor
import Util (thdOf3)
import Outputable

import Debug.Trace

likelyRecursionBndr :: CoreBind -> CoreBind
likelyRecursionBndr (NonRec b expr)
  | elem b ids'
  , pprTrace "NonRec recursion?"
    (text "binder" <+> ppr b $$ text "body" <+> ppr expr) False = undefined
  | otherwise = NonRec b expr'
  where (ids', expr') = annotateExpr [b] expr

--TODO: Why
likelyRecursionBndr (Rec binders)
  = pprTrace "Annotation result"
      (ppr binders $$ text "annotated" $$ ppr (zip bs exprs') $$
       text "recCalled" $$ ppr bs' $$
       text "idsFound" $$ ppr ids' $$
       text "occInfo" $$ ppr (map idDetails bs) $$
       text "bs" $$ ppr bs $$
       text "bs" $$ ppr (map idOccInfo bs) $$
       text "rec" $$ ppr (Rec binders) $$
       text "binders" $$ ppr (binders) $$
       text "head" $$ ppr (head binders)
      )
      Rec (zip bs exprs')
  where
    (bs, exprs) = unzip binders
    bs' = filter (isAlwaysTailCalled . idOccInfo) bs
    (ids', exprs') = unzip $ map (annotateExpr bs) exprs



likelyRecursion :: CoreExpr -> CoreExpr
likelyRecursion = snd . annotateExpr []

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
annotateExpr :: [Id] -> CoreExpr -> ([Id], CoreExpr)
annotateExpr ids (Var v)
  | elem v ids = ([v], Var v)
  | otherwise = ([], Var v)

--TODO: Remove sanity check
annotateExpr ids e@(Let binder@(NonRec b expr) body)
  | AlwaysTailCalled {} <- tailCallInfo . idOccInfo $ b
  , pprTrace "NonRec tailcalled" (ppr e) True
  = let (ids', body') = annotateExpr (b:ids) body
  in (ids', Let binder body')
  | otherwise =
  let (ids', body') = annotateExpr ids body
  in (ids', Let binder body')

annotateExpr ids (Let binder@(Rec bindings) body) =
  --TODO: Also anotate bound expressions & check their logic
  let newIdList = ids ++ (filter (isAlwaysTailCalled . idOccInfo) . map fst $ bindings)
      (ids', body') = annotateExpr newIdList body
      bindings' = map (second (snd . annotateExpr newIdList)) bindings
  in
  (ids', Let (Rec bindings') body')

--TODO: This should be written cleaner
annotateExpr ids expr@(Case scrut b ty alternatives) =
  let (cons, bdrs, alts) = unzip3 alternatives
      (altOccs, altExprs) = unzip $ map (annotateExpr ids) alts :: ([[Id]], [CoreExpr])

      allTheSame = all (== (head altOccs)) altOccs

      (scrutOccs, scrut') = annotateExpr ids scrut

      offset = minimum $ map length altOccs

      ids' = uniqDSetToList . unionManyUniqDSets $ map mkUniqDSet (scrutOccs : altOccs)
      alts' = zip3 cons bdrs altExprs

      setLikelyhood :: [Id] -> CoreAlt -> CoreAlt
      setLikelyhood [] alt = alt
      setLikelyhood xs (con,bdrs,altExpr) =
        let weightFactor = 1 + length xs - offset
            hint = WeightHint $ multiplyWeight defFreq weightFactor
        in (con,bdrs,Tick hint altExpr)

      newCase
        | all null altOccs = expr
        | allTheSame = Case scrut' b ty alts'
        | otherwise = Case scrut' b ty (zipWith setLikelyhood altOccs alts')
  in (ids', newCase)

annotateExpr ids expr@(Lit {})
  = ([], expr)
--TODO: Arg should never really trigger as it won't be tail called.
annotateExpr ids (App expr arg)
  = let (eids, expr') = annotateExpr ids expr
        (aids, arg') = annotateExpr ids arg
        ids' = uniqDSetToList . unionManyUniqDSets . map mkUniqDSet $ [eids, aids]
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
annotateExpr ids expr@Type {}
  = ([], expr)
annotateExpr ids expr@Coercion {}
  = ([], expr)






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