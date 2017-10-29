{-# LANGUAGE CPP, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

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
import TyCon 

import  Data.Set (Set(..))
import qualified Data.Set as Set
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
import Data.Tuple (swap)
import Data.List as L

import HsDumpAst


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

data CondValue 
    = LitCond { cv_lit :: Literal }
    | ConCond 
        { cv_tag :: ConTag
        , cv_type :: TyCon }
    deriving (Eq)


--Represents knowledge about the given occurence.
--Left => Constructors which the Occurence does not match.
--Right Tag => Occurence matches the constructor.
type Evidence = (Occurrence, (Either [ConTag] ConTag))

--Represents a condition on the given occurence. Nothing represents evaluation.
--Just => Occurence matches the constructor.
--Nothing -> Just evaluation
type Condition = (Occurrence, Maybe CondValue)
type Conditions = [Condition]

type Constraint = Conditions
type Constraints = [Constraint]

type CPM = PM MatchId MatrixRHS
{--
 Set of all occurences and the constructor it was evaluated to.
 We generate no knowledge for default branches
-}
type DecompositionKnowledge = Map Occurrence (Either [CondValue] CondValue)

type Heuristic = CPM -> Maybe Int

-- Matrix Types
type EqMatrix = PM MatchId MatrixRHS

type MatrixRHS = (MatchResult, Constraints)


type Entry e = (Pat GhcTc, e)

-- Pattern matrix row major. The plan is to store the pattern in a and additional info in e
type PM e rhs = (Seq.Seq (Seq.Seq (Entry e), rhs))

type PatternMatrix e rhs = PM e rhs
type PatternEquation e rhs = (Seq.Seq (Entry e), rhs)
type PatternRow e = Seq.Seq (Entry e)
type PatternColumn e = Seq.Seq (Entry e)

type TreeEquation = PatternEquation Occurrence MatrixRHS







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


toPatternMatrix :: [MatchId] -> [EquationInfo] -> DsM EqMatrix
toPatternMatrix vars eqs = do
    rows <- mapM (toMatrixRow vars) eqs
    return $ Seq.fromList rows

toEqnInfo :: EqMatrix -> [EquationInfo]
toEqnInfo m = 
    let eqs = F.toList m
        withPat = fmap (first (map fst . F.toList)) eqs :: [([Pat GhcTc], MatrixRHS)]
        eqnInfos = fmap (\x -> EqnInfo (fst x) (fst . snd $ x)) withPat :: [EquationInfo]
    in
    eqnInfos

combineWrappers :: DsWrapper -> DsWrapper -> DsWrapper
combineWrappers wrap1 wrap2 = wrap2 . wrap1

toMatrixRow :: [MatchId] -> EquationInfo -> DsM (TreeEquation)
{-
    Gather wrappers for all patterns in a row.
    Combine them in a single wrapper
    Adjust the RHS to incude the wrappers.
-}
toMatrixRow vars (EqnInfo pats rhs) = do
    tidied <- mapM tidyEntry $ zip pats vars
    let (wrappers, pats) = unzip tidied
    let rhs = adjustMatchResult (foldr1 combineWrappers wrappers) rhs
    undefined



tidyEntry :: Entry Occurrence -> DsM (DsWrapper, Entry MatchId)
tidyEntry (pat, occ) = do
    (wrapper, pat) <- tidy1 occ pat
    return $ (wrapper, (pat, occ))
















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
isStrict :: Pat GhcTc -> Bool
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
getElement :: HasCallStack => PatternMatrix e rhs-> Int -> Int -> (Pat GhcTc, e)
getElement ( m) row col = flip Seq.index col $ fst $ flip Seq.index row $ m

updateElem :: forall e rhs. PatternMatrix e rhs-> Int -> Int -> (Pat GhcTc, e) -> PatternMatrix e rhs
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






















msInsert :: forall k v. (Ord k, Ord v) => Map k (Set v) -> k -> v -> Map k (Set v)
msInsert m k v =
    let set = fromMaybe (Set.empty) $ Map.lookup k m :: (Set v)
        newSet = Set.insert v set
        newMap = Map.insert k newSet m
    in
    newMap




setEqConstraint :: TreeEquation -> Constraints -> TreeEquation
setEqConstraint eq constraint = second (\rhs -> second (const constraint) rhs) eq



-- Calculate the constraints of the whole matrix
constrainMatrix :: CPM -> DsM (CPM)
constrainMatrix m = 
    let goRow :: Foldable t => Constraints -> t TreeEquation -> DsM [TreeEquation]
        goRow constraints m = do
            (row:eqs) <- return $ F.toList m
            newConstraint <- rowConstraint $ fst row :: DsM Constraint -- Conditions
            let constraintSum = newConstraint:constraints :: Constraints
            liftM ((setEqConstraint row constraintSum) : ) (goRow constraintSum eqs)
    in
    Seq.fromList <$> goRow [] m

{-
    mapAccumL 
        (\(constraints :: Constraints) eq -> 
            let row = fst eq
                newConstraint = rowConstraint row :: Constraint -- Conditions
                constraintSum = newConstraint:constraints :: Constraints
            in
            (   constraintSum
            ,   setEqConstraint eq (constraintSum) -- We dont need to add the new constraint. It is enforced by selecting the row already.
            )
        ) 
        [] 
        m -}

getPatternConstraint :: Pat GhcTc -> Occurrence -> DsM (Maybe Condition)
-- | The conditions imposed on the RHS by this pattern.
-- Result can have no condition, just evaluation or impose a condition on the
-- following constraints
getPatternConstraint WildPat {} occ = return Nothing
getPatternConstraint VarPat {} occ = return Nothing
getPatternConstraint _ _ = error "ConPat not done" {-}
    ( ConPatOut 
        {   pat_con = pCon
        ,   pat_arg_tys = _tys
        ,   pat_tvs = _tvs
        ,   pat_dicts = _p_dicts
        ,   pat_binds = _p_binds
        ,   pat_args = p_args
        ,   pat_wrap = ps_wrapper -- Wrapper to use for type synonyms.
        }   ) occ
    | RealDataCon dcon <- con = 
        return $ (occ, Just 
            (ConCond 
                (dataConTag dcon)
                (dataConTyCon dcon)
            )
        )
    | PatSynCon psyn <- con = error "PatSyn not implemented"
-}
getPatternConstraint NPat {} occ = 
    error "TODO"
getPatternConstraint (LitPat lit) occ = do
    df <- getDynFlags
    return $ Just $ 
        (occ, Just 
            (LitCond (hsLitKey df lit))
        )
getPatternConstraint NPlusKPat {} occ = 
    error "Not implemented NPK"
getPatternConstraint p occ = pprPanic "Pattern not implemented: " (showAstData BlankSrcSpan p)

--Build up constraints within a row from left to right.
rowConstraint :: Foldable t => t (Entry Occurrence) -> DsM Constraint
rowConstraint entries =
    foldM (buildConstraint) [] entries
        where
            buildConstraint :: Conditions -> Entry Occurrence -> DsM Conditions
            buildConstraint preConditions entry = do
                let (pattern, occurrence) = entry
                constraint <- uncurry getPatternConstraint entry
                case constraint of
                    Just c -> return $ preConditions ++ [c] --TODO: Don't append at end
                    Nothing -> return preConditions            
--                    return $ preConditions ++ [constraint]
            --CP {} -> preConditions ++ [(occurrence, Just (Right $ pTag pattern))] ++ 
            --rowConstraint (L.zipWith (\p i -> (p, occurrence ++ [i])) (pArgs pattern) [0..])


--matchWith heuristic (Seq.Empty) knowledge failExpr = return failExpr 
{-
Recursive match function. Parameters are:
    * The Pattern Matrix -> 
    * DecompositionKnowledge -> List of known value/occurence combinations
    * (CoreExpr,Constraint) -> The default expr for match failure and the associated
        Constraint.
-}
matchWith :: Heuristic -> CPM -> DecompositionKnowledge -> CoreExpr -> DsM MatchResult
matchWith heuristic m knowledge failExpr = do
    --deepseq (m,knowledge) (return ())
    --let heuristic = leftToRight
    let pickRhs = 
            let (expr, constraints) = getRhs m 0
            in  resolveConstraints m knowledge expr constraints
    when (null m) (error "Matching empty matrix")
    let matchCol = heuristic m :: Maybe Int 
    case matchCol of
        Nothing -> pickRhs
        Just colIndex -> mkCase heuristic m knowledge colIndex failExpr

{-
Split the matrix based on the given column, we use a helper data type to group patterns together.
-}

{--
In the tree based approach a group is anything that leads to the same case alternative.
So (Number 1) and (Number 2) would be put into different Groups.
-}
data PGrp
    = VarGrp
    | ConGrp (Int)
    | LitGrp (HsLit Var)
    deriving (Eq, Ord) -- , Show, Ord)

--deriving instance Eq (HsLit Var)
deriving instance Ord (HsLit Var)
--deriving instance Eq (Var)
--deriving instance Ord (Var)





getGrp :: Entry e -> PGrp
getGrp (p, _e ) = patGroup p

patGroup (WildPat {} ) = VarGrp
-- Since evaluation is taken care of in the constraint we can ignore them for grouping patterns.
patGroup (BangPat (L _loc p)) = patGroup p
patGroup (ConPatOut { pat_con = L _ con
                      , pat_arg_tys = tys })
    | PatSynCon psyn <- con                = error "Not implemented" -- gSyn psyn tys
    | RealDataCon dcon <- con              = error "Not implemented" -- gSyn psyn tys
        --Literals
patGroup _ = error "Not implemented"
patGroup (LitPat lit) = LitGrp lit


--Unpack the constructor at the given column in the matrix
unpackCol :: HasCallStack => CPM -> Int -> CPM
unpackCol pm splitColIndex =
    if arity == 0 
        then withoutCol pm
        else insertCols (withoutCol pm) splitColIndex $ newColumns pm
        where
            baseOccurrence m = snd $ getElement m 0 splitColIndex
            withoutCol m = deleteCol m splitColIndex :: CPM
            baseCol = (getCol pm splitColIndex)
            anyConEntry = do
                index_ <- findIndexL (\x -> case getGrp x of {ConGrp _tag -> True; _ -> False}) baseCol
                Seq.lookup index_ baseCol
            arity_ m = maybe (error "No constructor to unpack found") (P.length . pArgs . fst) anyConEntry  :: Int
            arity = arity_ pm
            args col = fmap 
                (\x -> case getGrp x of
                    ConGrp _t -> pArgs (fst x)
                    VarGrp    -> L.replicate arity LP 
                )
                col -- :: Seq [SimplePattern]
            --one column top down
            buildColum m colIndex = fmap 
                (\args -> 
                    let patEntry = args !! colIndex
                        occEntry = (baseOccurrence m) ++ [colIndex]
                    in
                    (patEntry, occEntry)
                )
                (args $ getCol m splitColIndex)
                :: Seq (Entry Occurrence)
            --list of columns left right (Seq top down)
            newColumns m = map (\col -> buildColum m col) [0..(arity :: Int)-1] :: [Seq (Entry Occurrence)]


mkCase :: Heuristic -> CPM -> DecompositionKnowledge -> Int -> CoreExpr -> DsM MatchResult
-- TODO: Extend from just literals
mkCase heuristic m knowledge colIndex failExpr =
    let column = getCol m colIndex
        occ = colOcc column :: Occurrence --What we match on

        --Scrutinee for the case expr
        scrutinee = varToCoreExpr occ :: CoreExpr

        groupRows :: Map PGrp (Set Int)
        groupRows = foldlWithIndex
            (\grps i a -> msInsert grps (getGrp a) i )
            Map.empty
            column -- :: Map PGrp (Set Int)
        
        defRows = fromMaybe Set.empty $ Map.lookup VarGrp groupRows :: Set Int
        grps = Map.keys groupRows :: [PGrp]
        cgrps = P.filter (\g -> case g of {VarGrp -> False; _ -> True}) grps :: [PGrp]
        hasDefaultGroup = Map.member VarGrp groupRows :: Bool
        defaultExcludes = mapMaybe (\g -> case g of { VarGrp -> Nothing; ConGrp i -> Just i} ) $ Map.keys groupRows :: [ConTag]

        newEvidence grp = 
            case grp of
                VarGrp -> Left defaultExcludes
                ConGrp i -> Right i
        getSubMatrix :: [Int] -> CPM
        getSubMatrix rows =
            fmap fromJust $ Seq.filter isJust $ Seq.mapWithIndex (\i r -> if (i `elem` rows) then Just r else Nothing) m :: CPM
        newMatrix :: PGrp -> CPM
        newMatrix grp = 
            let rows = Set.toAscList $ Set.union defRows $ groupRows Map.! grp :: [Int]
                matrix = getSubMatrix rows
            in
            case grp of
                VarGrp    -> deleteCol matrix colIndex
                ConGrp _i -> unpackCol matrix colIndex
        
        groupExpr :: PGrp -> DsM (CoreExpr)
        groupExpr grp =
            matchWith heuristic (newMatrix grp) (Map.insert occ (newEvidence grp) knowledge) failExpr

        defaultAlternative = if hasDefaultGroup
            then
                groupExpr VarGrp
            else
                return failExpr  
        
        --generate the alternative for a entry grp
        mkAlt :: PGrp -> DsM CoreExpr
        mkAlt (LitGrp l@(HsInt {})) = do
            let coreLit = dsLit l
            undefined


    in do 
    undefined -- TODO:
    -- Build the alternatives
    {-}
    (alternatives :: [(Int, CoreExpr)]) <- mapM 
        (\(ConGrp i) -> 
            do 
                alt <- groupExpr (ConGrp i)
                return (i,alt)
        )
        cgrps
    --deepseq (alternatives) (return ())
    def <- defaultAlternative :: DsM (CoreExpr)
    return $ Case
        { scrutinee = occ
        , alternatives = alternatives
        , def = Just def
        }
    -}


occColIndex :: forall rhs. PatternMatrix Occurrence rhs -> Occurrence -> Maybe Int
occColIndex m occ 
    | null m = Nothing
    | otherwise =
        let row = getRow m 0 :: PatternRow Occurrence
        in
        Seq.findIndexL (\p -> occ == snd p) row
    
-- :: (a -> Bool) -> Seq a -> Maybe Int
colOcc :: PatternColumn Occurrence -> Occurrence
colOcc c = snd $ Seq.index c 0

matrixOcc :: CPM -> [Occurrence]
matrixOcc m = F.toList $ fmap (snd) $ getRow m 0


resolveConstraints :: CPM -> DecompositionKnowledge -> CoreExpr -> Constraints -> DsM MatchResult
resolveConstraints m knowledge expr constraints = do
    -- TODO
    {-
    * Remove satisfied constraints
    * simplify constraints
    * Generate case
    * Apply resolveConstraints
    -}
    let simplifiedConstraints = L.filter (not . null) . map (flip simplifyConstraint knowledge) . map (truncateConstraint knowledge) $ constraints :: Constraints
    --traceM $ "simplified:" ++ show simplifiedConstraints
    --traceM $ "Knowledge:" ++ show (knowledge) ++ "\n"
    --traceShowM $ null simplifiedConstraints
    --unsafePerformIO $ threadDelay 300000 >> return (return ())
    if null simplifiedConstraints
        then --trace "BaseCase" $ 
            return expr
        else --trace "solveCase" 
            mkConstraintCase m knowledge expr simplifiedConstraints

mkConstraintCase :: CPM -> DecompositionKnowledge -> CoreExpr -> Constraints -> DsM MatchResult
{-
Resolve at least one constraint by introducing a additional case statement
-}
mkConstraintCase m knowledge expr constraints = do undefined {-
    --traceShowM ("mkConstraint", knowledge, expr, constraints)
    let cond@(occ,conVal) = head . head $ constraints :: Condition
    let occValues = concatMap (\constraint -> foldMap (\cond -> if fst cond == occ then [conVal] else []) constraint) constraints :: [Maybe (Either ConTag ConTag)]
    let occTags = nub $ map (either id id) $ catMaybes occValues :: [ConTag]
    let newEvidence tag = Right tag
    let tagExpr tag = resolveConstraints m (Map.insert occ (newEvidence tag) knowledge) expr constraints
    let defaultEvidence = Left occTags
    let defaultExpr = resolveConstraints m (Map.insert occ (defaultEvidence) knowledge) expr constraints
    let tagAlt tag = do
            e <- tagExpr tag;
            return (tag,e)
    
    alternatives <- mapM tagAlt occTags :: DsM [(Int, CoreExpr)]
    def <- defaultExpr
    return $ Case
        { scrutinee = occ
        , alternatives = alternatives
        , def = Just def
        }
    -}

truncateConstraint :: DecompositionKnowledge -> Constraint -> Constraint
--If we know one condition fails we can remove all following conditions.
truncateConstraint knowledge constraint =
    L.takeWhile 
        (\c -> 
            fromMaybe True $ knowledgeMatchesCond knowledge c
        )
        constraint    

simplifyConstraint :: Constraint -> DecompositionKnowledge -> Constraint
--Take a constraint and remove all entries which are satisfied
simplifyConstraint constraint knowledge =
    --traceShow (F.length knowledge) $
    --traceShow (sum $ map F.length constraint) $  
    L.filter 
        (\cond@(occ,_) -> 
            let evidence = fromJust $ Map.lookup occ knowledge
                m = case evidenceMatchesCond (occ, evidence) cond of
                        Nothing -> False
                        Just False -> False
                        Just True -> True
            in
            not $ if not (Map.member occ knowledge) then False else m
        ) 
        constraint

    where
        satisfies :: Evidence -> Constraint -> Bool
        {- Satisfies if we have evidence for the entry if:
            We have knowledge about the given occurence and it does not match.
        -}
        satisfies e@(occ, val) conditions =
            let constraintEntry = L.find (\x -> fst x == occ) conditions
            in
            case constraintEntry of
                Nothing -> False
                Just c -> 
                    case evidenceMatchesCond e c of
                        Nothing -> False
                        Just True -> False
                        Just False -> True

knowledgeMatchesCond :: DecompositionKnowledge -> Condition -> Maybe Bool
knowledgeMatchesCond knowledge condition@(occ, _occVal) = do
    evidence <- Map.lookup occ knowledge :: Maybe (Either [ConTag] ConTag)
    evidenceMatchesCond (occ, evidence) condition

{--
Answers the question if for the arguments
* If the pattern matching holds
* Fails
* We can't tell
-} 
evidenceMatchesCond :: Evidence -> Condition -> Maybe Bool
evidenceMatchesCond (eOcc, eVal) (cOcc, cVal)
    | eOcc /= cOcc = Nothing
    | cVal == Nothing = Just True
    | otherwise =
        let match :: ConTag -> Maybe Bool
            match cTag =
                case eVal of
                    Right eTag -> Just $ cTag == eTag
                    Left eTags -> maybe Nothing (const $ Just False) (L.find (==cTag) eTags)
        in either (\x -> not <$> match x ) (match) (fromJust cVal)
                



--Represents knowledge about the given occurence.
--Left => Constructors which the Occurence does not match.
--Right Tag => Occurence matches the constructor.
--type Evidence = (Occurrence, (Either [ConTag] ConTag))

--Represents a condition on the given occurence. Nothing represents evaluation.
--Left Tag => Occurence does not match the constructor
--Right Tag => Occurence matches the constructor.
--type Condition = (Occurrence, Maybe (Either ConTag ConTag))
