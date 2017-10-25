{-# LANGUAGE CPP, ScopedTypeVariables #-}

module MatchTree where

--import {- -#SOURCE#-} DsExpr (dsLExpr, dsSyntaxExpr)

#include "HsVersions.h"

import DsExpr
import DynFlags
import HsSyn
import TcHsSyn
import TcEvidence
import TcRnMonad
import Check
import CoreSyn
import Literal
import CoreUtils
import MkCore
import DsMonad
import DsBinds
import DsGRHSs
import DsUtils
import Id
import ConLike
import DataCon
import PatSyn
import MatchCon
import MatchLit
import Type
import Coercion ( eqCoercion )
import TcType ( toTcTypeBag )
import TyCon( isNewTyCon )
import TysWiredIn
import ListSetOps
import SrcLoc
import Maybes
import Util
import Name
import Outputable
import BasicTypes ( isGenerated, fl_value )
import FastString
import Unique
import UniqDFM

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map(..))
import qualified Data.Sequence as Seq
import Data.Sequence  as Seq ( Seq(..), (|>) )
import qualified Data.List as L
import Control.Monad 


--import Pattern.SimplePatterns
--import TL.Language
import Data.Foldable as F
import Prelude as P hiding (pred)
import Data.Bifunctor as BF
import Data.Foldable as F


type MatchId = Id   -- See Note [Match Ids]
type Occurrence = MatchId

{-
Our system is such that:
A condition represents that a occurence must be one of
    * evaluated (Nothing)
    * matches a constructor (Right tag)
    * doesn't match it (Left tag)

Conditions are always conjunctive and represents the
    conditions that must be met before we can select a rhs.
A constraint is a list of conditions as described above.

Constraints are the sum of all constraints applicable to a rhs.

-}

--Represents knowledge about the given occurence.
--Left => Constructors which the Occurence does not match.
--Right Tag => Occurence matches the constructor.
type Evidence = (Occurrence, (Either [ConTag] ConTag))

--Represents a condition on the given occurence. Nothing represents evaluation.
--Left Tag => Occurence does not match the constructor
--Right Tag => Occurence matches the constructor.
--We only use the right variant atm, gruft and stuff
type Condition = (Occurrence, Maybe (Either ConTag ConTag))
type Conditions = [Condition]

type Constraint = Conditions
type Constraints = [Constraint]

type CPM = PM MatchId MatrixRHS
{--
 Set of all occurences and the constructor it was evaluated to.
 We generate no knowledge for default branches
-}
type DecompositionKnowledge = Map Occurrence (Either [ConTag] ConTag)

type Heuristic = CPM -> Maybe Int

--
type EqMatrix = PM MatchId MatrixRHS

type MatrixRHS = ((DsWrapper, Expr MatchId), Constraints)







match :: [MatchId]        -- Variables rep\'ing the exprs we\'re matching with
                          -- See Note [Match Ids]
      -> Type             -- Type of the case expression
      -> [EquationInfo]   -- Info about patterns, etc. (type synonym below)
      -> DsM MatchResult  -- Desugared result!

-- | Goes through the RHSs
match [] ty eqns
  = ASSERT2( not (null eqns), ppr ty )
    return (foldr1 combineMatchResults match_results)
  where
    match_results = [ ASSERT( null (eqn_pats eqn) )
                      eqn_rhs eqn
                    | eqn <- eqns ]

match vars ty eqns = undefined


toPatternMatrix :: [EquationInfo] -> DsM EqMatrix
toPatternMatrix eqs = do
    rows <- mapM toMatrixRow eqs
    return $ Seq.fromList rows

toMatrixRow :: EquationInfo -> DsM (PatternEquation MatchId MatrixRHS)
toMatrixRow eq = undefined


tidyEntry :: Entry Occurrence -> DsM (DsWrapper, Entry MatchId)
tidyEntry (pat, occ) = undefined

















tidy1 :: Id                  -- The Id being scrutinised
      -> Pat GhcTc           -- The pattern against which it is to be matched
      -> DsM (DsWrapper,     -- Extra bindings to do before the match
              Pat GhcTc)     -- Equivalent pattern

-------------------------------------------------------
--      (pat', mr') = tidy1 v pat mr
-- tidies the *outer level only* of pat, giving pat'
-- It eliminates many pattern forms (as-patterns, variable patterns,
-- list patterns, etc) yielding one of:
--      WildPat
--      ConPatOut
--      LitPat
--      NPat
--      NPlusKPat

{------------------------------------

         Vanilla tidying code

-------------------------------------}



tidy1 v (ParPat pat)      = tidy1 v (unLoc pat)
tidy1 v (SigPatOut pat _) = tidy1 v (unLoc pat)
tidy1 _ (WildPat ty)      = return (idDsWrapper, WildPat ty)
tidy1 v (BangPat (L l p)) = tidy_bang_pat v l p

        -- case v of { x -> mr[] }
        -- = case v of { _ -> let x=v in mr[] }
tidy1 v (VarPat (L _ var))
  = return (wrapBind var v, WildPat (idType var))

        -- case v of { x@p -> mr[] }
        -- = case v of { p -> let x=v in mr[] }
tidy1 v (AsPat (L _ var) pat)
  = do  { (wrap, pat') <- tidy1 v (unLoc pat)
        ; return (wrapBind var v . wrap, pat') }

{- now, here we handle lazy patterns:
    tidy1 v ~p bs = (v, v1 = case v of p -> v1 :
                        v2 = case v of p -> v2 : ... : bs )

    where the v_i's are the binders in the pattern.

    ToDo: in "v_i = ... -> v_i", are the v_i's really the same thing?

    The case expr for v_i is just: match [v] [(p, [], \ x -> Var v_i)] any_expr
-}

tidy1 v (LazyPat pat)
    -- This is a convenient place to check for unlifted types under a lazy pattern.
    -- Doing this check during type-checking is unsatisfactory because we may
    -- not fully know the zonked types yet. We sure do here.
  = do  { let unlifted_bndrs = filter (isUnliftedType . idType) (collectPatBinders pat)
        ; unless (null unlifted_bndrs) $
          putSrcSpanDs (getLoc pat) $
          errDs (hang (text "A lazy (~) pattern cannot bind variables of unlifted type." $$
                       text "Unlifted variables:")
                    2 (vcat (map (\id -> ppr id <+> dcolon <+> ppr (idType id))
                                 unlifted_bndrs)))

        ; (_,sel_prs) <- mkSelectorBinds [] pat (Var v)
        ; let sel_binds =  [NonRec b rhs | (b,rhs) <- sel_prs]
        ; return (mkCoreLets sel_binds, WildPat (idType v)) }

tidy1 _ (ListPat pats ty Nothing)
  = return (idDsWrapper, unLoc list_ConPat)
  where
    list_ConPat = foldr (\ x y -> mkPrefixConPat consDataCon [x, y] [ty])
                        (mkNilPat ty)
                        pats

-- Introduce fake parallel array constructors to be able to handle parallel
-- arrays with the existing machinery for constructor pattern
tidy1 _ (PArrPat pats ty)
  = return (idDsWrapper, unLoc parrConPat)
  where
    arity      = length pats
    parrConPat = mkPrefixConPat (parrFakeCon arity) pats [ty]

tidy1 _ (TuplePat pats boxity tys)
  = return (idDsWrapper, unLoc tuple_ConPat)
  where
    arity = length pats
    tuple_ConPat = mkPrefixConPat (tupleDataCon boxity arity) pats tys

tidy1 _ (SumPat pat alt arity tys)
  = return (idDsWrapper, unLoc sum_ConPat)
  where
    sum_ConPat = mkPrefixConPat (sumDataCon alt arity) [pat] tys

-- LitPats: we *might* be able to replace these w/ a simpler form
tidy1 _ (LitPat lit)
  = return (idDsWrapper, tidyLitPat lit)

-- NPats: we *might* be able to replace these w/ a simpler form
tidy1 _ (NPat (L _ lit) mb_neg eq ty)
  = return (idDsWrapper, tidyNPat tidyLitPat lit mb_neg eq ty)

-- Everything else goes through unchanged...

tidy1 _ non_interesting_pat
  = return (idDsWrapper, non_interesting_pat)

--------------------
tidy_bang_pat :: Id -> SrcSpan -> Pat GhcTc -> DsM (DsWrapper, Pat GhcTc)

-- Discard par/sig under a bang
tidy_bang_pat v _ (ParPat (L l p))      = tidy_bang_pat v l p
tidy_bang_pat v _ (SigPatOut (L l p) _) = tidy_bang_pat v l p

-- Push the bang-pattern inwards, in the hope that
-- it may disappear next time
tidy_bang_pat v l (AsPat v' p)  = tidy1 v (AsPat v' (L l (BangPat p)))
tidy_bang_pat v l (CoPat w p t) = tidy1 v (CoPat w (BangPat (L l p)) t)

-- Discard bang around strict pattern
tidy_bang_pat v _ p@(LitPat {})    = tidy1 v p
tidy_bang_pat v _ p@(ListPat {})   = tidy1 v p
tidy_bang_pat v _ p@(TuplePat {})  = tidy1 v p
tidy_bang_pat v _ p@(SumPat {})    = tidy1 v p
tidy_bang_pat v _ p@(PArrPat {})   = tidy1 v p

-- Data/newtype constructors
tidy_bang_pat v l p@(ConPatOut { pat_con = L _ (RealDataCon dc)
                               , pat_args = args
                               , pat_arg_tys = arg_tys })
  -- Newtypes: push bang inwards (Trac #9844)
  =
    if isNewTyCon (dataConTyCon dc)
      then tidy1 v (p { pat_args = push_bang_into_newtype_arg l ty args })
      else tidy1 v p  -- Data types: discard the bang
    where
      (ty:_) = dataConInstArgTys dc arg_tys

-------------------
-- Default case, leave the bang there:
--    VarPat,
--    LazyPat,
--    WildPat,
--    ViewPat,
--    pattern synonyms (ConPatOut with PatSynCon)
--    NPat,
--    NPlusKPat
--
-- For LazyPat, remember that it's semantically like a VarPat
--  i.e.  !(~p) is not like ~p, or p!  (Trac #8952)
--
-- NB: SigPatIn, ConPatIn should not happen

tidy_bang_pat _ l p = return (idDsWrapper, BangPat (L l p))

-------------------
push_bang_into_newtype_arg :: SrcSpan
                           -> Type -- The type of the argument we are pushing
                                   -- onto
                           -> HsConPatDetails GhcTc -> HsConPatDetails GhcTc
-- See Note [Bang patterns and newtypes]
-- We are transforming   !(N p)   into   (N !p)
push_bang_into_newtype_arg l _ty (PrefixCon (arg:args))
  = ASSERT( null args)
    PrefixCon [L l (BangPat arg)]
push_bang_into_newtype_arg l _ty (RecCon rf)
  | HsRecFields { rec_flds = L lf fld : flds } <- rf
  , HsRecField { hsRecFieldArg = arg } <- fld
  = ASSERT( null flds)
    RecCon (rf { rec_flds = [L lf (fld { hsRecFieldArg = L l (BangPat arg) })] })
push_bang_into_newtype_arg l ty (RecCon rf) -- If a user writes !(T {})
  | HsRecFields { rec_flds = [] } <- rf
  = PrefixCon [L l (BangPat (noLoc (WildPat ty)))]
push_bang_into_newtype_arg _ _ cd
  = pprPanic "push_bang_into_newtype_arg" (pprConArgs cd)




































strictColumn :: PatternColumn MatchId -> Bool
strictColumn = all (isStrict . fst)

strictSet :: EqMatrix -> [Int]
--TODO: Include columns of 
strictSet m = 
    let firstRow = getRow m 0 :: PatternRow MatchId
        start = Seq.findIndexL (isStrict . fst) firstRow :: Maybe Int
        columns = [0.. fromJust (columnCount m) - 1] :: [Int]
        strictColumns = filter (strictColumn . getCol m) columns :: [Int]
    in
    case start of
        Nothing -> []
        (Just c) -> L.nub $ c:strictColumns

leftToRight :: EqMatrix -> Maybe Int
leftToRight m = 
    let ss = strictSet m
    in if null ss then Nothing else Just $ head ss


-- | Is evaluation of the pattern required
isStrict :: Pat MatchId -> Bool
isStrict WildPat {} = False
isStrict ConPatOut {} = True
isStrict LitPat {} = True
isStrict NPat {} = True -- 
isStrict NPlusKPat {} = True -- ?
isStrict _ = error "Should have been tidied already"




{---------------------------------------------
---------------------   ----------------------
-------------  Pattern Matrix  ---------------
---------------------   ----------------------
----------------------------------------------}

type Entry e = (Pat MatchId, e)

-- Pattern matrix row major. The plan is to store the pattern in a and additional info in e
type PM e rhs = (Seq.Seq (Seq.Seq (Entry e), rhs))

type PatternMatrix e rhs = PM e rhs
type PatternEquation e rhs = (Seq.Seq (Entry e), rhs)
type PatternRow e = Seq.Seq (Entry e)
type PatternColumn e = Seq.Seq (Entry e)


spanMatrixRowise :: forall e rhs. HasCallStack => (PatternEquation e rhs -> PatternEquation e rhs -> Bool) -> PatternMatrix e rhs -> (PatternMatrix e rhs, PatternMatrix e rhs)
spanMatrixRowise pred m =
    addEq m (Seq.empty, Seq.empty)
        where
            addEq :: PatternMatrix e rhs-> (PatternMatrix e rhs, PatternMatrix e rhs) -> (PatternMatrix e rhs, PatternMatrix e rhs)
            addEq (Seq.Empty) res = res
            addEq (eq :<| eqs) (Empty, Empty) = addEq eqs (Seq.singleton eq, Seq.empty)
            addEq marg@(eq :<| eqs) (mspan@(_reqs :|> leq), Empty) 
                | pred eq leq = 
                    addEq eqs (mspan |> eq, Seq.empty)
                | otherwise = (mspan, marg)
            addEq _ _ = error "Matrix invariants violated"



splitMatrixRowiseBy :: forall e rhs. (PatternEquation e rhs-> PatternEquation e rhs -> Bool) -> PatternMatrix e rhs-> [PatternMatrix e rhs]
splitMatrixRowiseBy pred m =
    F.foldl (\ml eq -> placeEquation ml eq) [] m
    where
        placeEquation :: [PatternMatrix e rhs] -> PatternEquation e rhs-> [PatternMatrix e rhs]
        placeEquation [] eq = [Seq.singleton eq]
        placeEquation (m:ms) eq = 
            if pred (Seq.index m 0) eq
                then (m Seq.|> eq) : ms
                else m : (placeEquation ms eq)

filterEqs :: HasCallStack => (PatternEquation e rhs -> Bool) ->  PatternMatrix e rhs -> PatternMatrix e rhs
filterEqs f m = Seq.filter f m

mapEqs :: HasCallStack => (PatternEquation e rhs -> PatternEquation d rhsb) -> PatternMatrix e rhs -> PatternMatrix d rhsb
mapEqs f m = fmap f m

foldEqsL :: (b -> PatternEquation e rhs -> b) -> b -> PatternMatrix e rhs -> b
foldEqsL = F.foldl'
    
rowCount :: HasCallStack => PatternMatrix e rhs -> Int
rowCount m = P.length m

columnCount :: HasCallStack => PatternMatrix e rhs -> Maybe Int
columnCount m 
    | P.null m = Nothing
    | otherwise = Just . P.length . fst $ Seq.index m 0


getRow :: HasCallStack => PatternMatrix e rhs -> Int -> PatternRow e
getRow (m) i = fst $ Seq.index m i

getEquation :: HasCallStack => PatternMatrix e rhs -> Int -> PatternEquation e rhs
getEquation (m) i = Seq.index m i

getRhs :: HasCallStack => PatternMatrix e rhs -> Int -> rhs
getRhs ( m) i = snd $ Seq.index m i

getCol :: PatternMatrix e rhs -> Int -> PatternColumn e
getCol (m) i = fmap (fromMaybe (error "Column out of bounds") . Seq.lookup i . fst) m

setCol :: forall e rhs. HasCallStack => PatternMatrix e rhs-> Int -> PatternColumn e -> PatternMatrix e rhs
setCol m col colEntries = 
    Seq.mapWithIndex (\i eq -> updateEq eq (Seq.index colEntries i)) m
        where
            updateRow :: Entry e -> PatternRow e -> PatternRow e
            updateRow entry row = Seq.update col entry row
            updateEq :: PatternEquation e rhs -> Entry e -> PatternEquation e rhs
            updateEq eq entry = first (updateRow entry :: PatternRow e -> PatternRow e) eq
        
insertCols :: forall e t rhs. HasCallStack => (Foldable t, Functor t) => PatternMatrix e rhs -> Int -> t (PatternColumn e) -> PatternMatrix e rhs
insertCols m pos cols =
    Seq.mapWithIndex (\i eq -> updateEq eq (getRowEntries i cols)) m
        where
        updateRow :: t (Entry e) -> PatternRow e -> PatternRow e
        updateRow entries row = F.foldr (\elem seq-> Seq.insertAt pos elem seq) row entries
        updateEq :: PatternEquation e rhs-> t (Entry e) -> PatternEquation e rhs
        updateEq eq entries = first (updateRow entries) eq
        getRowEntries :: Int -> t (PatternColumn e) -> t (Entry e)
        getRowEntries i cols = fmap (flip Seq.index i) cols

insertCol :: forall e t rhs. HasCallStack => PatternMatrix e rhs -> Int -> PatternColumn e -> PatternMatrix e rhs
insertCol m pos col =
    Seq.mapWithIndex (\i eq -> updateEq eq (getRowEntry i col)) m
        where
        updateRow :: Entry e -> PatternRow e -> PatternRow e
        updateRow entry row = Seq.insertAt pos entry row
        updateEq :: PatternEquation e rhs-> Entry e -> PatternEquation e rhs
        updateEq eq entries = first (updateRow entries) eq
        getRowEntry :: Int -> PatternColumn e -> Entry e
        getRowEntry i col_ = flip Seq.index i col_

insertEq :: HasCallStack => PatternMatrix e rhs-> PatternEquation e rhs-> PatternMatrix e rhs
insertEq m eq = Seq.insertAt 0 eq m


mapRow :: HasCallStack => (a -> b) -> (Seq.Seq a, Int) -> (Seq.Seq b, Int)
mapRow f (row, rhs) = (fmap f row, rhs)

-- | Row col addresing
getElement :: HasCallStack => PatternMatrix e rhs-> Int -> Int -> (Pat MatchId, e)
getElement ( m) row col = flip Seq.index col $ fst $ flip Seq.index row $ m

updateElem :: forall e rhs. PatternMatrix e rhs-> Int -> Int -> (Pat MatchId, e) -> PatternMatrix e rhs
updateElem m row col entry = 
    Seq.adjust updateRow row m
    where
        updateRow :: PatternEquation e rhs-> PatternEquation e rhs
        updateRow = first (\row -> Seq.update col entry row)

adjustElem :: forall e rhs. PatternMatrix e rhs-> Int -> Int -> (Entry e -> Entry e) -> PatternMatrix e rhs
adjustElem m row col f =
    updateElem m row col (f oldElem)
        where
            oldElem = getElement m row col :: Entry e

getColumns :: PatternMatrix e rhs-> [PatternColumn e]
getColumns m = 
    if isJust colCount 
        then fmap (\col -> fmap (flip Seq.index col . fst) m) [0..fromJust colCount - 1]
        else []
        where
            colCount = columnCount m

getRows :: PatternMatrix e rhs -> Seq (PatternRow e)
getRows m = fmap fst m



deleteCol :: HasCallStack => PatternMatrix e rhs -> Int -> PatternMatrix e rhs
deleteCol m i = fmap (first $ Seq.deleteAt i) m