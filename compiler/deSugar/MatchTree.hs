{-# LANGUAGE CPP, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances, DeriveGeneric, DeriveDataTypeable #-}

module MatchTree 
    (match)
where

import {-#SOURCE#-} DsExpr (dsLExpr, dsSyntaxExpr)

#include "HsVersions.h"

import GhcPrelude
import PrelNames

--import DsExpr
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
import Var (varType)
import ConLike
import DataCon
import PatSyn
import MatchCon
import MatchLit
import Type
import Coercion ( eqCoercion )
import TcType ( toTcTypeBag, tcSplitTyConApp, isIntegerTy)
import TyCon( isNewTyCon )
import TysWiredIn
import ListSetOps
import SrcLoc
import Maybes
import Util
import Name
import Outputable
import BasicTypes ( isGenerated, fl_value, FractionalLit(..), il_value)
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
import qualified Outputable as O ((<>))
import Data.Ratio
import NameEnv
import MatchCon (selectConMatchVars)
import Var (EvVar)


--import Pattern.SimplePatterns
--import TL.Language
import Data.Foldable as F
import Prelude as P hiding (pred)
import Data.Bifunctor as BF
import Data.Foldable as F
import Data.Tuple (swap)
import Data.List as L
import Data.Data
import Debug.Trace
import Control.DeepSeq
import GHC.Generics

import HsDumpAst


type MatchId = Id   -- See Note [Match Ids]

type Occurrence = MatchId

--Also defined in MatchCon
type ConArgPats = HsConDetails (LPat GhcTc) (HsRecFields GhcTc (LPat GhcTc))

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
    = LitCond { cv_lit :: HsLit GhcTc }
    | ConCond { cv_con :: DataCon }
    deriving (Eq)

instance Outputable CondValue where
    ppr (ConCond con) = lparen O.<> text "ConVal " O.<> ppr con O.<> rparen
    ppr (LitCond lit) = lparen O.<> text "LitVal " O.<> ppr (lit) O.<> rparen

data PatInfo 
    = PatInfo 
    { patCol :: [Int]
    , patOcc :: !Occurrence }
    deriving (Eq, Ord, Data)

instance Outputable PatInfo where
    ppr info = lparen O.<> text "PatInfo " O.<> ppr (patCol info, patOcc info) O.<> rparen

--Represents knowledge about the given occurence.
--Left => Constructors which the Occurence does not match.
--Right Tag => Occurence matches the constructor.
type Evidence = (Occurrence, (Either [CondValue] CondValue))

{-
Taking apart nested constructors (W (A B)) requires us to insert new conditions into the list of conditions
In order to facilitate this we keep the PatInfo of the original pattern around which allows as to insert
new conditions in the middle of the list based on the patCol
-}
--Represents a condition on the given occurence. Nothing represents evaluation.
--Just => Occurence matches the constructor.
--Nothing -> Just evaluation
type Condition = (PatInfo, Maybe CondValue)
type Conditions = [Condition]

type Constraint = Conditions
type Constraints = [Constraint]

type CPM = PM PatInfo MatrixRHS
{--
 Set of all occurences and the constructor it was evaluated to.
 We generate no knowledge for default branches
-}
type DecompositionKnowledge = Map Occurrence (Either [CondValue] CondValue)

type Heuristic = CPM -> Maybe Int

-- Matrix Types
type EqMatrix = PM PatInfo MatrixRHS

type MatrixRHS = (MatchResult, Constraints)


type Entry e = (Pat GhcTc, e)

-- Pattern matrix row major. The plan is to store the pattern in a and additional info in e
type PM e rhs = (Seq.Seq (Seq.Seq (Entry e), rhs))

type PatternMatrix e rhs = PM e rhs
type PatternEquation e rhs = (Seq.Seq (Entry e), rhs)
type PatternRow e = Seq.Seq (Entry e)
type PatternColumn e = Seq.Seq (Entry e)

type TreeEquation = PatternEquation PatInfo MatrixRHS

-- "Debug" instances
instance Outputable a => Outputable (Seq a) where
    ppr sequence = lparen O.<> text "Seq" O.<> lparen O.<> ppr (F.toList sequence) O.<> rparen O.<> rparen

instance Outputable MatchResult where
    ppr (MatchResult _ mr) = text "MatchResult"

printmr :: MatchResult -> DsM ()
printmr (MatchResult _ mr) = do
    core <- (mr $ mkCharExpr 'F') 
    liftIO . putStrLn . showSDocUnsafe $ showAstData BlankSrcSpan core 



{-# INLINE addKnowledge #-}
addKnowledge :: DecompositionKnowledge -> Occurrence -> (Either [CondValue] CondValue) -> DecompositionKnowledge
addKnowledge knowledge occ information =
    Map.insert occ information knowledge 






match :: HasCallStack => [MatchId]        -- Variables rep\'ing the exprs we\'re matching with
                          -- See Note [Match Ids]
      -> Type             -- Type of the case expression
      -> [EquationInfo]   -- Info about patterns, etc. (type synonym below)
      -> DsM MatchResult  -- Desugared result!

match vars ty eqns = do
    df <- getDynFlags
    useTreeMatching <- goptM Opt_TreeMatching
    unless useTreeMatching failDs
    --traceM "match2"
    matrix <- (toPatternMatrix vars eqns)
    --traceM "created pattern Matrix"
    matchWith leftToRight ty matrix (Map.empty)


toPatternMatrix :: HasCallStack => [MatchId] -> [EquationInfo] -> DsM EqMatrix
toPatternMatrix vars eqs = do
    --traceM "DesugarMatrix"
    rows <- mapM (toMatrixRow vars) eqs
    --liftIO . putStrLn . showSDocUnsafe $ ppr $ fmap (fst . snd) rows
    --seq rows $ traceM "Desugared?"
    --traceM "made into matrix:"
    constrainMatrix $  Seq.fromList rows

toEqnInfo :: HasCallStack => EqMatrix -> [EquationInfo]
toEqnInfo m = 
    let eqs = F.toList m
        withPat = fmap (first (map fst . F.toList)) eqs :: [([Pat GhcTc], MatrixRHS)]
        eqnInfos = fmap (\x -> EqnInfo (fst x) (fst . snd $ x)) withPat :: [EquationInfo]
    in
    eqnInfos

addRowWrappers :: HasCallStack => CPM -> [DsWrapper] -> CPM
addRowWrappers m wrappers = 
    Seq.zipWith 
        (\wrapper row ->
            second (first (adjustMatchResult wrapper)) row
        )
        (Seq.fromList wrappers) 
        m


combineWrappers :: DsWrapper -> DsWrapper -> DsWrapper
combineWrappers wrap1 wrap2 = wrap1 . wrap2

toMatrixRow :: HasCallStack => [MatchId] -> EquationInfo -> DsM (TreeEquation)
{-
    Gather wrappers for all patterns in a row.
    Combine them in a single wrapper
    Adjust the RHS to incude the wrappers.
-}
toMatrixRow vars (EqnInfo pats rhs) = do
    --liftIO $ traceM "tidyRow"
    let patternInfos = zipWith (\occ col -> PatInfo {patOcc = occ, patCol = [col]}) vars [0..]
    --liftIO . putStrLn . showSDocUnsafe $ ppr patternInfos
    let entries = zip pats $ patternInfos
    tidied <- mapM tidyEntry entries :: DsM [(DsWrapper, Entry PatInfo)]
    --seq tidied $ traceM "rowDone:"
    --liftIO . putStrLn . showSDocUnsafe $ showAstData BlankSrcSpan $ map snd tidied
    --liftIO . putStrLn . showSDocUnsafe $ ppr vars
    --liftIO . putStrLn . showSDocUnsafe $ ppr "Pats + Vars"
    
    
    --liftIO . putStrLn . showSDocUnsafe $ ppr $ map snd tidied
    let (wrappers, desugaredPats) = unzip tidied
    --liftIO $ putStrLn "AdjustMatch"
    let rowMatchResult = adjustMatchResult (foldr1 combineWrappers wrappers) rhs
    return (Seq.fromList desugaredPats, (rowMatchResult, []))



tidyEntry :: HasCallStack => Entry PatInfo -> DsM (DsWrapper, Entry PatInfo)
tidyEntry (pat, info@PatInfo { patOcc = occ}) = do
    --liftIO $ putStrLn "tidyEntry"
    (wrapper, newPat) <- tidy1 occ pat
    --liftIO . putStrLn . showSDocUnsafe $ showAstData BlankSrcSpan newPat
    --liftIO . putStrLn $ "newPat"
    --liftIO $ putStrLn "tidied"
    return $ (wrapper, (newPat, info))
















tidy1 :: HasCallStack
      => Id                  -- The Id being scrutinised
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
tidy_bang_pat :: HasCallStack => Id -> SrcSpan -> Pat GhcTc -> DsM (DsWrapper, Pat GhcTc)

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




































strictColumn :: PatternColumn e -> Bool
strictColumn = all (isStrict . fst)

strictSet :: HasCallStack => EqMatrix -> [Int]
--TODO: Include columns of 
strictSet m = 
    let firstRow = getRow m 0 :: PatternRow PatInfo
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
isStrict p = error $ "Should have been tidied already:" ++ (showSDocUnsafe (ppr p)) ++ " " ++ showSDocUnsafe (showAstData BlankSrcSpan p)




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
{- 
Utility functions to track compatible groups
-}

addGrpEntry :: Eq k => (k,v) -> [(k,[v])] -> [(k,[v])]
addGrpEntry (k,v) [] 
    = [(k,[v])]
addGrpEntry e@(k,v)  ((lk, vs):xs)
    | k == lk = (lk, v:vs):xs
    | otherwise = (lk, vs) : addGrpEntry e xs

getGrpEntries :: Eq k => k -> [(k,[v])] -> Maybe [v]
getGrpEntries k [] = Nothing
getGrpEntries k ((lk,vs):xs)
    | k == lk = Just vs
    | otherwise = getGrpEntries k xs




setEqConstraint :: TreeEquation -> Constraints -> TreeEquation
setEqConstraint eq constraint = second (\rhs -> second (const constraint) rhs) eq



-- Calculate the constraints of the whole matrix
constrainMatrix :: HasCallStack => CPM -> DsM (CPM)
constrainMatrix m = 
    let goRow :: Constraints -> [TreeEquation] -> DsM [TreeEquation]
        goRow constraints m = do
            --traceM "goRow"
            case m of
                [] -> --liftIO (print "RowBaseCase") >> 
                    return []
                (row:eqs) -> --liftIO (print "rowRecurse") >> 
                    do
                    --traceM "rowCons:"
                    --liftIO $ putStrLn . showSDocUnsafe $ ppr constraints
                    newConstraint <- rowConstraint $ fst row :: DsM Constraint -- Conditions
                    --liftIO $ putStrLn . showSDocUnsafe $ ppr newConstraint
                    let constraintSum = newConstraint:constraints :: Constraints
                    let currentRow = setEqConstraint row constraintSum :: TreeEquation
                    --traceM "doneRow:"
                    --liftIO $ putStrLn . showSDocUnsafe $ ppr currentRow
                    nextRows <- goRow constraintSum eqs
                    return $ currentRow : nextRows
    in do
    --traceM "constrainMatrix"
    rows <- goRow [] $ F.toList m :: DsM [TreeEquation]
    return $ Seq.fromList rows

getConConstraint :: HasCallStack => ConLike -> DsM (CondValue)
getConConstraint (RealDataCon dcon) = return $ ConCond dcon
getConConstraint (PatSynCon  scon ) = --TODO
    warnDs NoReason (ppr "Pat Synonyms not implemented for tree matching") >> failDs -- pprPanic "PatSynCon constraint not implemented" $ ppr scon


getPatternConstraint :: HasCallStack => Entry PatInfo -> DsM (Maybe (Condition))
-- | The conditions imposed on the RHS by this pattern.
-- Result can have no condition, just evaluation or impose a condition on the
-- following constraints
getPatternConstraint ((LitPat lit),info) = do
    df <- getDynFlags :: DsM DynFlags
    return $ Just $ (info, Just (LitCond (lit)) )
getPatternConstraint ((ConPatOut { pat_con = con}), info) = do
    -- TODO: Extend for nested arguments
    df <- getDynFlags :: DsM DynFlags
    --traceM "conConstraint"
    conConstraint <- getConConstraint $ unLoc con
    return $ Just $  (info, Just $ conConstraint )
getPatternConstraint (WildPat {}, info) = 
    --traceM "wp" >> 
    return Nothing
getPatternConstraint (VarPat {}, info) = 
    --traceM "vp" >> 
    return Nothing
getPatternConstraint (p, info) = 
    warnDs NoReason (ppr ("Pat should have been tidied already or not implemented", p)) >> failDs
    --traceM "Error: getPatternConstraint" >> pprPanic "Pattern not implemented: " (showAstData BlankSrcSpan p)
{-
getPatternConstraint NPat {} occ = 
    error "TODO"
getPatternConstraint NPlusKPat {} occ = 
    error "Not implemented NPK"
getPatternConstraint ConPatOut {} _ = error "ConPat not done" -}



--Build up constraints within a row from left to right.
rowConstraint :: (HasCallStack, Foldable t) => t (Entry PatInfo) -> DsM Constraint
rowConstraint entries = do
    --traceM "rowConstraint"
    crow <- foldM (buildConstraint) [] entries
    --liftIO $ putStrLn . showSDocUnsafe $ ppr crow
    --traceM "row done"
    return crow
        where
            buildConstraint :: Conditions -> Entry PatInfo -> DsM Conditions
            buildConstraint preConditions entry = do
                --traceM "buildConstraint"
                let (pattern, occurrence) = entry
                --traceM "getPatConstraint"
                --liftIO $ putStrLn . showSDocUnsafe $ showAstData BlankSrcSpan pattern
                --traceM "patBuildCons"
                constraint <- getPatternConstraint entry
                --liftIO $ putStrLn . showSDocUnsafe $ ppr constraint
                case constraint of
                    Just c -> return $ preConditions ++ [c] --TODO: Don't append at end
                    Nothing -> return preConditions            

addConstraints :: (Traversable t, HasCallStack) => CPM -> t (t (Entry PatInfo)) -> DsM CPM
{- Takes a matrix and a list of unpacked entries.
This is used when unpacking constructors during desugaring.
* Calculate the constraints from the entries
* Update the matrix with the new Constraints

Important: Constraints have to be added at the right place in the constraint list (sorted according to patOcc in PatInfo)
-}
addConstraints m rows = do
    newRowConstraints <- F.toList <$> mapM rowConstraint rows :: DsM [Constraint]
    let addedConstraints = tail . inits $ newRowConstraints :: [Constraints]
    let oldRowConstraints = F.toList $ fmap (snd . snd) m :: [Constraints]
    let combinedConstraints = zipWith (++) oldRowConstraints addedConstraints :: [Constraints]
    let sortedConstraints = Seq.fromList $ map (map (sortOn (patCol . fst))) combinedConstraints :: Seq.Seq Constraints
    return $ Seq.zipWith (setEqConstraint) m (sortedConstraints)

--matchWith heuristic (Seq.Empty) knowledge failExpr = return failExpr 
{-
Recursive match function. Parameters are:
    * The Heuristic
    * The Type of the result
    * The Pattern Matrix -> 
    * DecompositionKnowledge -> List of known value/occurence combinations
    * (CoreExpr,Constraint) -> The default expr for match failure and the associated
        Constraint.
-}
matchWith :: HasCallStack => Heuristic -> Type -> CPM -> DecompositionKnowledge -> DsM MatchResult
matchWith heuristic ty m knowledge = do 
    --traceM "matchWith:"
    --liftIO $ putStrLn . showSDocUnsafe $ showAstData BlankSrcSpan $ fmap fst m
    --liftIO $ putStrLn . showSDocUnsafe $ text "Type:" O.<> ppr ty
    --traceM "Match matrix"
    when (null m) (error "Matching empty matrix")
    let matchCol = heuristic m :: Maybe Int 
    --liftIO $ print $ "Matchcol:" ++ show matchCol
    case matchCol of
        Nothing -> do
            --traceM "getRHS"
            let (expr, constraints) = getRhs m 0 :: (MatchResult, Constraints)
            --liftIO $ traceM "resCons"
            rhsWrapper <- (resolveConstraints m ty knowledge constraints)
            --traceM "wrapper"
            --liftIO . putStrLn $ showSDocUnsafe $ ppr (rhsWrapper $ mkCharExpr 'F')
            --traceM "adjust and return match"
            return $ adjustMatchResult rhsWrapper expr
            --return $ MatchResult CantFail $ const (return $ mkCharExpr 'F') -- debug expr
        Just colIndex -> 
            --return $ MatchResult CantFail $ const (return $ mkCharExpr 'F') -- debug expr
            return $ MatchResult CanFail (\failExpr -> mkCase heuristic ty m knowledge colIndex failExpr)

{-
Split the matrix based on the given column, we use a helper data type to group patterns together.

In the tree based approach a group is anything that leads to the same case alternative.
So (Number 1) and (Number 2) would be put into different Groups.
-}
data PGrp
    = VarGrp
    | ConGrp (DataCon)
    | LitGrp (HsLit GhcTc)
    deriving (Eq) -- , Show, Ord)

--deriving instance Eq  a => Eq  (HsLit a)
--deriving instance Ord a => Ord (HsLit a)

--deriving instance Ord (GhcTc)

--deriving instance Eq (Var)
--deriving instance Ord (Var)

{-}
instance Ord x => Ord (HsLit x) where
  (HsChar _ x1)       `compare` (HsChar _ x2)       = x1 `compare ` x2
  (HsCharPrim _ x1)   `compare` (HsCharPrim _ x2)   = x1 `compare ` x2
  (HsString _ x1)     `compare` (HsString _ x2)     = x1 `compare ` x2
  (HsStringPrim _ x1) `compare` (HsStringPrim _ x2) = x1 `compare ` x2
  (HsInt _ x1)        `compare` (HsInt _ x2)        = x1 `compare ` x2
  (HsIntPrim _ x1)    `compare` (HsIntPrim _ x2)    = x1 `compare ` x2
  (HsWordPrim _ x1)   `compare` (HsWordPrim _ x2)   = x1 `compare ` x2
  (HsInt64Prim _ x1)  `compare` (HsInt64Prim _ x2)  = x1 `compare ` x2
  (HsWord64Prim _ x1) `compare` (HsWord64Prim _ x2) = x1 `compare ` x2
  (HsInteger _ x1 _)  `compare` (HsInteger _ x2 _)  = x1 `compare ` x2
  (HsRat _ x1 _)      `compare` (HsRat _ x2 _)      = x1 `compare ` x2
  (HsFloatPrim _ x1)  `compare` (HsFloatPrim _ x2)  = x1 `compare ` x2
  (HsDoublePrim _ x1) `compare` (HsDoublePrim _ x2) = x1 `compare ` x2
  _                   `compare` _                   = pprPanic "Ordering between different Literals not defined" (text "")
  -}


getGrp :: HasCallStack => Entry e -> PGrp
getGrp (p, _e ) = patGroup p

patGroup :: HasCallStack => Pat GhcTc -> PGrp
patGroup (WildPat {} ) = VarGrp
-- Since evaluation is taken care of in the constraint we can ignore them for grouping patterns.
patGroup (BangPat (L _loc p)) = patGroup p
patGroup (ConPatOut { pat_con = L _ con
                      , pat_arg_tys = tys })
    | PatSynCon psyn <- con                = error "Not implemented" -- gSyn psyn tys
    | RealDataCon dcon <- con              = 
        ConGrp dcon
        --Literals
patGroup (LitPat lit) = LitGrp lit
patGroup _ = error "Not implemented"


--Unpack the constructor at the given column in the matrix
unpackCol :: HasCallStack => CPM -> Int -> DsM CPM
unpackCol pm splitColIndex = do 
    WARN (False, text "Unpack stub") (return ())
    let originalColumn = getCol pm splitColIndex
    let withoutCol = deleteCol pm splitColIndex
    
    
    error "TODO"
     -- see patternBench


mkCase :: HasCallStack => Heuristic -> Type -> CPM -> DecompositionKnowledge -> Int -> CoreExpr -> DsM CoreExpr
{-

-}
-- TODO: Extend from just literals
mkCase heuristic ty m knowledge colIndex failExpr =
    let column = getCol m colIndex
        occ = colOcc column :: Occurrence --What we match on

        --Scrutinee for the case expr
        scrutinee = varToCoreExpr occ :: CoreExpr

        groupRows :: [(PGrp,[Int])]
        groupRows = Seq.foldlWithIndex
            (\grps i a -> addGrpEntry ((getGrp a),i) grps )
            []
            column -- :: Map PGrp (Set Int)


        defRows = fromMaybe [] $ getGrpEntries VarGrp groupRows :: [Int]
        grps = map fst groupRows :: [PGrp]
        cgrps = P.filter (\g -> case g of {VarGrp -> False; _ -> True}) grps :: [PGrp]
        hasDefaultGroup = elem VarGrp $ map fst groupRows :: Bool

        defaultExcludes :: [CondValue]
        defaultExcludes = mapMaybe grpCond cgrps

        grpCond :: PGrp -> Maybe CondValue
        grpCond (LitGrp lit) =
            Just (LitCond lit)
        grpCond (VarGrp) =  
            Nothing
        grpCond (ConGrp dcon) =
            Just (ConCond dcon)
        grpCond _ = error "Not implemented grpCond"

        condVars :: PGrp -> Maybe [Var]
        condVars (ConGrp dcon) = Just $
            error "TODO"
        condVars _ =
            Nothing

        newEvidence :: PGrp -> Either [CondValue] CondValue
        -- Returns evidence gained by selecting this branch/grp
        newEvidence (VarGrp) =  
            Left defaultExcludes
        newEvidence grp =
            Right . fromJust . grpCond $ grp

        getGrpRows :: PGrp -> [Int]
        getGrpRows grp = concatMap snd $ filter (\x -> fst x == grp) groupRows
     
        getSubMatrix :: [Int] -> CPM
        getSubMatrix rows =
            fmap fromJust $ Seq.filter isJust $ Seq.mapWithIndex (\i r -> if (i `elem` rows) then Just r else Nothing) m :: CPM
        getNewMatrix :: PGrp -> DsM CPM
        -- Since we have to "splice in" the constructor arguments which requires more setup we deal
        -- with Constructor groups in another function
        getNewMatrix grp = 
            let rows = getGrpRows grp :: [Int]
                matrix = getSubMatrix rows
            in
            case grp of
                VarGrp    -> return $ deleteCol matrix colIndex
                LitGrp {} -> return $ deleteCol matrix colIndex
                ConGrp con  | dataConSourceArity con == 0 -> return $ deleteCol matrix colIndex
                            | otherwise                   -> error "Constructor group"
        

        groupExpr :: PGrp -> DsM CoreExpr
        groupExpr grp = do
            let newKnowledge = (Map.insert occ (newEvidence grp) knowledge)
            newMatrix <- getNewMatrix grp 
            (MatchResult _ f) <- matchWith heuristic ty (newMatrix) newKnowledge
            f failExpr

        defaultFailure :: DsM (Maybe CoreExpr)
        defaultFailure = if hasDefaultGroup
            then
                return Nothing -- Default can also be generated by the var group
            else
                -- | Add a check for exhaustivness
                return $ Just failExpr
        

        {- Generate the alternatives for nested constructors,
         this is somewhat more complex as we need to get vars,
         treat type arguments and so on.
        
        --TODO: Move into own function, PatSynonyms
        -}



            


        mkConAlt :: PGrp -> DsM CoreAlt
        mkConAlt grp@(ConGrp con) = 
            -- Look at the pattern info from the first pattern.
            let ConPatOut { pat_con = L _ con1, pat_arg_tys = arg_tys, pat_wrap = wrapper1,
                    pat_tvs = tvs1, pat_dicts = dicts1, pat_args = args1, pat_binds = bind }
                    = firstPat

                fields1 = map flSelector (conLikeFieldLabels con1)

                entries = getGrpPats grp :: [Entry PatInfo]
                firstPat = fst . head $ entries :: Pat GhcTc
                firstPatInfo = snd . head $ entries :: PatInfo
                        
                -- Choose the right arg_vars in the right order for this group
                -- Note [Record patterns]
                -- Taken from MatchCon, slightly modified
                select_arg_vars :: [Id] -> [ConArgPats] -> [Id]
                select_arg_vars arg_vars ((arg_pats) : _)
                    | RecCon flds <- arg_pats
                    , let rpats = rec_flds flds
                    , not (null rpats)     -- Treated specially; cf conArgPats
                    = ASSERT2( fields1 `equalLength` arg_vars,
                                ppr con1 $$ ppr fields1 $$ ppr arg_vars )
                        map lookup_fld rpats
                    | otherwise
                    = arg_vars
                    where
                        fld_var_env = mkNameEnv $ zipEqual "get_arg_vars" fields1 arg_vars
                        lookup_fld (L _ rpat) = lookupNameEnv_NF fld_var_env
                                                            (idName (unLoc (hsRecFieldId rpat)))
                select_arg_vars _ [] = panic "matchOneCon/select_arg_vars []"

                inst_tys = arg_tys ++ mkTyVarTys tvs1
                val_arg_tys = conLikeInstOrigArgTys con1 inst_tys
                
                --All patterns in column
                pats = map fst $ entries :: [Pat GhcTc]

                -- Desugar the given patterns and produce a suitable wrapper.
                desugarPats :: [Pat GhcTc] -> [Id]  -> DsM (DsWrapper, [Pat GhcTc])
                desugarPats pats vars = do
                    --liftIO . putStrLn . showSDocUnsafe $ ppr pats
                    (wrappers, pats) <- unzip <$> zipWithM tidy1 vars pats
                    --traceM "kjhsadf"
                    return (foldr combineWrappers idDsWrapper wrappers, pats)

                -- Assign the variables introduced by a binding to the appropriate values
                -- producing a wrapper for the rhs
                wrapPatBinds :: [TyVar] -> [EvVar] -> Pat GhcTc -> DsM DsWrapper
                wrapPatBinds tvs1 dicts1 ConPatOut{ pat_tvs = tvs, pat_dicts = ds,
                                        pat_binds = bind, pat_args = args }
                    = do
                        ds_bind <- dsTcEvBinds bind
                        return ( wrapBinds (tvs `zip` tvs1)
                                . wrapBinds (ds  `zip` dicts1)
                                . mkCoreLets ds_bind
                                )

                unpackCon :: Entry PatInfo -> [Id] -> DsM (DsWrapper, [Entry PatInfo])
                -- | Pick apart a constructor returning result suitable to be spliced into
                -- the match matrix
                unpackCon (conPat, PatInfo {patOcc = patOcc, patCol = patCol}) vars =
                    let args = pat_args conPat 
                        arg_pats = map unLoc $ hsConPatArgs args :: [Pat GhcTc]
                    in do
                    (wrappers, desugaredPats) <- unzip <$> zipWithM tidy1 vars arg_pats
                    let mkEntry p occ colOffset = (p, PatInfo {patOcc = occ, patCol = patCol ++ [colOffset]}) 
                    let entries = zipWith3 mkEntry desugaredPats vars [0..]
                    return (foldr (.) idDsWrapper wrappers, entries)

                getNewConMatrix :: PGrp -> [Id] -> DsM CPM
                getNewConMatrix grp@ConGrp {} vars = 
                    let rows = getGrpRows grp :: [Int]
                        filteredRows = getSubMatrix rows :: CPM
                        colEntries = getCol filteredRows colIndex :: PatternColumn PatInfo
                        withoutCol = deleteCol filteredRows colIndex :: CPM
                        
                    in do
                    (wrappers, entries) <- unzip <$> (mapM (\e -> unpackCon e vars) $ F.toList colEntries) :: DsM ([DsWrapper], [[Entry PatInfo]])
                    let wrappedMatrix = addRowWrappers withoutCol wrappers
                    let unpackedMatrix = insertCols wrappedMatrix colIndex (Seq.fromList . map Seq.fromList . transpose $ entries)
                    constrainedMatrix <- addConstraints unpackedMatrix entries
                    return constrainedMatrix

                    --TODO: Build constraint for added entries
                getNewConMatrix ConGrp {} _ = error "Constructor group2"

                conGroupExpr :: PGrp -> [Id] -> DsM CoreExpr
                conGroupExpr grp vars = do
                    let newKnowledge = (Map.insert occ (newEvidence grp) knowledge)
                    newMatrix <- getNewConMatrix grp vars  
                    (MatchResult _ f) <- matchWith heuristic ty (newMatrix) newKnowledge
                    f failExpr

            in do
            arg_vars <- selectConMatchVars val_arg_tys args1
            
            --TODO: make sure group is compatible (record patterns) and pattern variables in correct order
            --For now we just fail on records
            when 
                (any 
                    (\x -> case x of {RecCon {} -> True; _ -> False })
                    (map pat_args pats)
                )
                (failDs)

            --Variable etc wrapper
            (rhsDesugarWrapper, pats) <- desugarPats pats arg_vars
            --Type variables etc wrapper
            (rhsTyWrapper) <- foldr (.) idDsWrapper <$> mapM (wrapPatBinds tvs1 dicts1) pats :: DsM DsWrapper

            wrapper <- return $ rhsDesugarWrapper . rhsTyWrapper

            ds_bind <- dsTcEvBinds bind

            unpackedMatrix <- getNewConMatrix grp arg_vars :: DsM CPM

            expr <- conGroupExpr grp arg_vars

            return $ (DataAlt con, arg_vars, wrapper . mkCoreLets ds_bind $ expr)
        mkConAlt _ = error "mkConAlt - No Constructor Grp"

        getGrpPats :: PGrp -> [Entry PatInfo]
        getGrpPats grp = 
            let submatrix = getSubMatrix . getGrpRows $ grp
                column = getCol submatrix colIndex :: PatternColumn PatInfo
            in
            F.toList column




        {-
        ******************* End of Con Grp alt code *******************
        -}

        --generate the alternative for a entry grp
        mkAlt :: PGrp -> DsM CoreAlt
        mkAlt grp@(LitGrp lit@(HsIntPrim _ val)) = do
            let coreLit = MachInt val --dsLit lit
            expr <- groupExpr grp
            return $ (LitAlt coreLit, [], expr)
        mkAlt grp@(ConGrp _con) = do
            mkConAlt grp
        mkAlt (VarGrp) = do
            expr <- groupExpr VarGrp
            return $ (DEFAULT, [], expr)

        altExprs :: DsM [CoreExpr]
        altExprs = mapM groupExpr grps

        alts :: DsM [CoreAlt]
        alts = do
            grpAlts <- sortBy (\(a,x,y) (a2,_,_)-> compare a2 a) <$> mapM mkAlt grps
            liftM (addDefault grpAlts) defaultFailure
            -- defFailBranch


    in do
        --traceM "mkCase"
        alts <- alts
        --traceM "alts"
        --liftIO $ putStrLn $ showSDocUnsafe $ ppr alts
        return $ Case (Var occ) (mkWildValBinder (idType occ)) ty (alts)


occColIndex :: HasCallStack => forall rhs. HasCallStack => PatternMatrix Occurrence rhs -> Occurrence -> Maybe Int
occColIndex m occ 
    | null m = Nothing
    | otherwise =
        let row = getRow m 0 :: PatternRow Occurrence
        in
        Seq.findIndexL (\p -> occ == snd p) row
    
-- :: (a -> Bool) -> Seq a -> Maybe Int
colOcc :: PatternColumn PatInfo -> Occurrence
colOcc c = patOcc . snd $ Seq.index c 0

matrixOcc :: CPM -> [Occurrence]
matrixOcc m = F.toList $ fmap (patOcc . snd) $ getRow m 0


resolveConstraints :: HasCallStack => CPM -> Type -> DecompositionKnowledge -> Constraints -> DsM DsWrapper
{- Produces a wrapper which guarantees evaluation of arguments according to Augustsons algorithm.
 a match result to include required evaluation of occurences according to the constraints. -}

resolveConstraints m ty knowledge constraints = do
    -- TODO
    {-
    * Remove satisfied constraints
    * simplify constraints
    * Generate case
    * Apply resolveConstraints
    -}
    let simplifiedConstraints = L.filter (not . null) . 
                map (flip simplifyConstraint knowledge) . 
                map (truncateConstraint knowledge) $ constraints :: Constraints

    if null simplifiedConstraints
        then --trace "BaseCase" $ 
            return (\expr -> expr)
        else --trace "solveCase" 
            (mkConstraintCase m ty knowledge simplifiedConstraints)

mkConstraintCase :: HasCallStack => CPM -> Type -> DecompositionKnowledge -> Constraints -> DsM DsWrapper
{-
Resolve at least one constraint by introducing a additional case statement
-}
mkConstraintCase m ty knowledge constraints =
    --traceShowM ("mkConstraint", knowledge, expr, constraints)
    let cond@(info,conVal) = head . head $ constraints :: Condition
        occ = patOcc info :: Occurrence
        --ty = varType occ :: Kind
        occValues = concatMap 
            (\constraint -> foldMap (\(info, condVal) -> if (patOcc info) == occ then [conVal] else []) constraint) constraints :: [Maybe CondValue]
        occVals = nub $ catMaybes occValues :: [CondValue]
        newEvidence condVal = Right condVal

        getAltExpr :: CondValue -> DsM (CoreExpr -> CoreExpr)
        getAltExpr condVal = resolveConstraints m ty (Map.insert occ (newEvidence condVal) knowledge) constraints :: DsM DsWrapper

        defaultEvidence = Left occVals
        defaultExpr = resolveConstraints m ty (Map.insert occ (defaultEvidence) knowledge) constraints :: DsM DsWrapper

        scrutinee = varToCoreExpr occ :: CoreExpr

        --TODO: Finish
        condAlt :: CondValue -> DsM (CoreExpr -> CoreAlt)
        condAlt (LitCond lit) = do
            (Lit coreLit) <- dsLit (convertLit lit)
            return (\expr -> ((LitAlt coreLit), [], expr))
        --TODO: Fix breakage if constructor has arguments if arguments are passed
        condAlt (ConCond dcon) = do
            return (\expr -> ((DataAlt dcon), [], expr)) 

    
    in do
    def <- defaultExpr :: DsM DsWrapper
    let defAlt = (\rhs -> (DEFAULT, [], def rhs)) :: CoreExpr -> CoreAlt
    altWrappers <- mapM (condAlt) occVals :: DsM [CoreExpr -> CoreAlt]
    altExpressions <- mapM (getAltExpr) occVals :: DsM [CoreExpr -> CoreExpr]
    let alts = (\rhs ->
            (defAlt rhs) :
                (zipWithEqual
                    "MatchConstraints: expressions /= branches"
                    (\altWrap exprWrap -> altWrap (exprWrap rhs)) altWrappers altExpressions
                )
            ) :: CoreExpr -> [CoreAlt]
    

    return (\rhs ->
        Case (Var occ) (mkWildValBinder (idType occ)) ty (alts rhs)
        )
    
    

truncateConstraint :: HasCallStack => DecompositionKnowledge -> Constraint -> Constraint
--If we know one condition fails we can remove all following conditions.
truncateConstraint knowledge constraint =
    L.takeWhile 
        (\c -> 
            fromMaybe True $ knowledgeMatchesCond knowledge c
        )
        constraint    

simplifyConstraint :: HasCallStack => Constraint -> DecompositionKnowledge -> Constraint
--Take a constraint and remove all entries which are satisfied
simplifyConstraint constraint knowledge =
    L.filter 
        (\cond@(info,_) ->
            let occ = patOcc info :: Occurrence 
                evidence = fromJust $ Map.lookup occ knowledge :: Either [CondValue] CondValue
                m = case evidenceMatchesCond (occ, evidence) cond of
                        Nothing -> False
                        Just False -> False
                        Just True -> True
            in
            not $ if not (Map.member occ knowledge) then False else m
        ) 
        constraint

knowledgeMatchesCond :: HasCallStack => DecompositionKnowledge -> Condition -> Maybe Bool
knowledgeMatchesCond knowledge condition@(info, _occVal) = do
    let occ = patOcc info
    evidence <- Map.lookup occ knowledge :: Maybe (Either [CondValue] CondValue)
    evidenceMatchesCond (occ, evidence) condition

{--
    Answers the question if the given evidence satifies the given condition.
    Applying this to all knowledge tells us if we need to emit additional code
    to satisfy the conditions.

* If the eviden matching holds
* Fails
* We can't tell
-} 
evidenceMatchesCond :: HasCallStack => Evidence -> Condition -> Maybe Bool
evidenceMatchesCond (eOcc, eVal) (cInfo, cVal)
    | eOcc /= cOcc = Nothing
    | eOcc == cOcc && cVal == Nothing = Just True
    | otherwise =
        -- We can still not know if we took a default branch that din't list the
        -- value of the condition in the alternatives
        let match :: CondValue -> Maybe Bool 
            match condVal = 
                case eVal of
                    (Right evidence) -> Just $ evidence == condVal
                    (Left evs) -> if (any (==condVal) evs) then Just False else Nothing
        in match (fromJust cVal)
    where
        cOcc = patOcc cInfo :: Occurrence
{- 

data CondValue 
    = LitCond { cv_lit :: HsLit GhcTc }
    | ConCond DataCon
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


-}