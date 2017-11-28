{-# LANGUAGE CPP, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances, DeriveGeneric, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fprof-auto #-}

{-
TODO: 
* Include wildcard rows in literal/con rows.
 Ax
 _y =(B)> y
 Bz       z
* Gadt support
* Mixed Records per group
* String literals
* More Heuristics
* Post bac: PatSynonmys and other extensions   


-}
module MatchTree 
    (match, printmr, tidy1)
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
import Var (varType, varUnique)
import ConLike
import DataCon
import PatSyn
import MatchCon
import MatchLit
import Type
import Coercion ( eqCoercion )
import TcType ( toTcTypeBag, tcSplitTyConApp, isIntegerTy, isStringTy)
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
import MkId (DataConBoxer(..))
import UniqSupply (initUs_)
import HsTypes --(selectorFieldOcc)


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
import System.IO.Unsafe
import HsDumpAst
import RdrName

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
    = LitCond { cv_lit :: Literal }
    | ConCond { cv_con :: DataCon} --, cv_pat :: Pat GhcTc }

{-TODO:
We currently just check the Constructor for patterns equality.
This might be enough but requires doublechecking if for
f C = 1
f C = 2
C might differ (Dictionaries and the like)
-}
instance Eq CondValue where 
    (LitCond {}) == (ConCond {}) = False
    (LitCond lit1) == (LitCond lit2) = lit1 == lit2
    (ConCond {cv_con = c1}) == (ConCond {cv_con = c2}) = 
        c1 == c2
        
        
    

instance Outputable CondValue where
    ppr (ConCond {cv_con = con}) = lparen O.<> text "ConVal " O.<> ppr con O.<> rparen
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

printmr :: HasCallStack => MatchResult -> DsM ()
printmr (MatchResult CantFail mr) = do
    liftIO $ putStr "pmr: Matchresult: "
    filler <- mkStringExpr "Should not be able to fail"
    core <- (mr filler) 
    liftIO . putStrLn . showSDocUnsafe $ ppr core 
printmr (MatchResult CanFail mr) = do
    liftIO $ putStr "pmr: Matchresult: "
    core <- (mr $ mkCharExpr 'F') 
    liftIO . putStrLn . showSDocUnsafe $ ppr core 



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
    --dsPrint $ text "matchType:" O.<> ppr ty
    df <- getDynFlags
    useTreeMatching <- goptM Opt_TreeMatching
    unless useTreeMatching failDs
    matrix <- (toPatternMatrix vars eqns)
    --traceM "match:"
    --liftIO . putStrLn . showSDocUnsafe $ ppr $ eqns
    result <- matchWith leftToRight ty matrix (Map.empty)
    return result


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
    let rowMatchResult = adjustMatchResult (foldl1 (.) wrappers) rhs
    return (Seq.fromList desugaredPats, (rowMatchResult, []))



tidyEntry :: HasCallStack => Entry PatInfo -> DsM (DsWrapper, Entry PatInfo)
tidyEntry (pat, info@PatInfo { patOcc = occ}) = do
    --liftIO $ putStrLn "tidyEntry"
    (wrapper, newPat) <- tidy1 occ pat
    --liftIO . putStrLn . showSDocUnsafe $ showAstData BlankSrcSpan newPat
    --liftIO . putStrLn $ "newPat"
    --liftIO $ putStrLn "tidied"
    return $ (wrapper, (newPat, info))

tidy1 :: HasCallStack => Id                  -- The Id being scrutinised
      -> Pat GhcTc           -- The pattern against which it is to be matched
      -> DsM (DsWrapper,     -- Extra bindings to do before the match
              Pat GhcTc)     -- Equivalent pattern

-------------------------------------------------------
--      (pat', mr') = tidy1 v pat mr
-- tidies the *outer level only* of pat, giving pat'
-- It eliminates many pattern forms (as-patterns, variable patterns,
-- list patterns, etc) and returns any created bindings in the wrapper.

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










strictColumn :: PatternColumn e -> Bool
strictColumn = all (isStrict . fst)

strictSet :: HasCallStack => EqMatrix -> [Int]
--TODO: Include strict columns with not all patterns
--      Include patterns which are strict but are currently handled by tidy
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
{-
We select strict columns left to right for one exception:
If there is just a single row we can process patterns from
left to right no matter their strictness.
-}
leftToRight m 
    | null m = Nothing
    | rowCount m == 0 = Nothing
    | Just cols <- columnCount m, cols == 0 = Nothing
    | rowCount m == 1 && (fromJust $ columnCount m) > 0 = Just 0
    | (not . all isStrict) (fmap (fst . flip Seq.index 0. fst) m) = Just 0
    | null ss         = Nothing
    | otherwise       = Just $ head ss
    where
        ss = strictSet m


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


{- 
Utility functions to track compatible groups
-}
msInsert :: forall k v. (Ord k, Ord v) => Map k (Set v) -> k -> v -> Map k (Set v)
msInsert m k v =
    let set = msLookup k m :: (Set v)
        newSet = Set.insert v set
        newMap = Map.insert k newSet m
    in
    newMap

msLookup :: forall k v. (Ord k, Ord v) => k -> Map k (Set v) -> (Set v)
msLookup k m = fromMaybe Set.empty (Map.lookup k m)



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


getConConstraint :: HasCallStack => Pat GhcTc -> DsM (CondValue)
getConConstraint pat 
    | (L _ (RealDataCon dcon)) <- (pat_con pat) = return $ ConCond dcon
    | (L _ (PatSynCon   scon)) <- (pat_con pat) = --warnDs NoReason (ppr "Pat Synonyms not implemented for tree matching") >>
        failDs



getPatternConstraint :: HasCallStack => Entry PatInfo -> DsM (Maybe (Condition))
-- | The conditions imposed on the RHS by this pattern.
-- Result can have no condition, just evaluation or impose a condition on the
-- following constraints
getPatternConstraint ((LitPat lit),info) = do
    df <- getDynFlags :: DsM DynFlags
    return $ Just $ (info, Just (LitCond (hsLitKey df lit)) )
getPatternConstraint (pat@(ConPatOut { pat_con = con}), info) = do
    -- TODO: Extend for nested arguments
    df <- getDynFlags :: DsM DynFlags
    --traceM "conConstraint"
    conConstraint <- getConConstraint pat
    return $ Just $  (info, Just $ conConstraint )
getPatternConstraint (WildPat {}, info) = 
    --traceM "wp" >> 
    return Nothing
getPatternConstraint (VarPat {}, info) = 
    --traceM "vp" >> 
    return Nothing
getPatternConstraint (p, info) = 
    --warnDs NoReason (text "Pat should have been tidied already or not implemented" <+> ppr p)) >>
    failDs
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
matchWith heuristic ty m knowledge 
    | null m = do
        --traceM "nullMatrix"
        return $ alwaysFailMatchResult
    | otherwise = do 
        --traceM "matchWith:"
        --liftIO $ putStrLn . showSDocUnsafe $ text "Matrix" <+> (ppr $ fmap fst m)
        --liftIO $ putStrLn . showSDocUnsafe $ showAstData BlankSrcSpan $ fmap fst m
        --liftIO $ putStrLn . showSDocUnsafe $ text "Type:" O.<> ppr ty
        --traceM "Match matrix"

        --If we match on something like f x = <canFailRhs> we can end up with a match on an empty matrix
        let matchCol = heuristic m :: Maybe Int 
        df <- getDynFlags
        --liftIO $ putStrLn $ "Matchcol:" ++ show matchCol
        case matchCol of
        {-

        Consider a definition of the form:
        f _ | <evaluates to False> = e1
        f _ | otherwise            = e2

        Here we need to ensure we dont fail after trying the first rhs but instead continue with the second row.

        The heuristic can return no column in two cases:
        a) We already matched on all patterns
        b) There are no strict columns left.

        In the case of a) we can simply combine the MatchResult of all remaining rows.
        In the case of b) we have to continue matching on the rest of the matrix if the
        current row fails.

        -}
            Nothing 
                | fromJust (columnCount m) > 0 -> do
                    let (expr, constraints) = getRhs m 0 :: (MatchResult, Constraints)

                    continuation <- matchWith heuristic ty (Seq.drop 1 m) knowledge :: DsM MatchResult
                    constraintWrapper <- (resolveConstraints m ty knowledge constraints) :: DsM DsWrapper
                    let constrainedMatch = (adjustMatchResult constraintWrapper expr) :: MatchResult
                    --let constrainedMatch = (adjustMatchResult id expr) :: MatchResult

                    return $ combineMatchResults constrainedMatch continuation
                | fromJust (columnCount m) == 0 -> do
                    let rhss = F.toList $ fmap snd m :: [(MatchResult, Constraints)]
                    let (results, constraints) = unzip rhss
                    
                    constraintWrappers <- mapM (resolveConstraints m ty knowledge) constraints :: DsM [DsWrapper]
                    let constrainedMatches = zipWith adjustMatchResult constraintWrappers results :: [MatchResult]
                    --let constrainedMatches = zipWith adjustMatchResult (repeat id) results :: [MatchResult]

                    return $ foldr combineMatchResults alwaysFailMatchResult constrainedMatches

            Just colIndex -> do
                
                mr@(MatchResult cf _) <- mkCase heuristic df ty m knowledge colIndex
                --liftIO $ putStrLn $ case cf of { CanFail ->"CanFail"; CantFail -> "CantFail" }
                return mr

{-
Split the matrix based on the given column, we use a helper data type to group patterns together.

In the tree based approach a group is anything that leads to the same case alternative.
So (Number 1) and (Number 2) would be put into different Groups.
-}
data PGrp
    = VarGrp
    | ConGrp { pgrpCon :: DataCon}
    | LitGrp (Literal)
    deriving (Data) -- , Show, Ord)

{-
For constructors only compare based on constructor currently.
TODO: Also take care of field comparisons when dealing with Record patterns
-}
instance Eq PGrp where
    VarGrp == VarGrp = True
    LitGrp lit1 == LitGrp lit2 = lit1 == lit2
    ConGrp con1 == ConGrp con2 = con1 == con2
    _ == _ = False

{-
Comparisons are only valid if all grps are of the same type. 
-}
instance Ord PGrp where
    VarGrp    `compare` VarGrp    = EQ
    VarGrp    `compare` _         = LT
    _         `compare` VarGrp    = GT
    LitGrp l1 `compare` LitGrp l2 = compare l1 l2
    LitGrp {} `compare` _         = LT
    _         `compare` LitGrp {} = GT
    ConGrp d1 `compare` ConGrp d2 =
        ASSERT (dataConTyCon d1 == dataConTyCon d2)
        compare (dataConTag d1) (dataConTag d2)
    _            `compare` _            = panic "Invalid use of sort instance (PGrp)" 
    
    
    

getGrp :: HasCallStack => DynFlags -> Entry e -> PGrp
getGrp df (p, _e ) = patGroup df p

patGroup :: HasCallStack => DynFlags -> Pat GhcTc -> PGrp
patGroup _df (WildPat {} ) = VarGrp
-- Since evaluation is taken care of in the constraint we can ignore them for grouping patterns.
patGroup df  (BangPat (L _loc p)) = patGroup df p
patGroup _df (ConPatOut { pat_con = L _ con})
    | PatSynCon psyn <- con                = error "Not implemented" -- gSyn psyn tys
    | RealDataCon dcon <- con              = 
        ConGrp dcon
        --Literals
patGroup df (LitPat lit) = LitGrp $ hsLitKey df lit
patGroup _ _ = error "Not implemented"

-- Assign the variables introduced by a binding to the appropriate values
-- producing a wrapper for the rhs
wrapPatBinds :: [TyVar] -> [EvVar] -> Pat GhcTc -> DsM DsWrapper
wrapPatBinds tvs1 dicts1 ConPatOut{ pat_tvs = tvs, pat_dicts = ds,
                        pat_binds = bind, pat_args = args }
    = do
        ds_bind <- dsTcEvBinds bind
        --A pattern produces a list of types referenced in their RHS
        --if we combine these branches
        return ( wrapBinds (tvs `zip` tvs1)
                . wrapBinds (ds  `zip` dicts1)
                . mkCoreLets ds_bind
                )

mkCase :: HasCallStack => Heuristic -> DynFlags -> Type -> CPM -> DecompositionKnowledge -> Int -> DsM MatchResult
{-
The failure story:

We use the given fail expression to create:
* The default alternative
* A default expression

The default expression is:
* Built by using the fail expression and the RHS of the wildcard grp
  if one exists
* Otherwise we just use the given fail expression

We then use this default expression to generate the other alternatives.
    

-}
-- TODO: Extend for patSyn and all constructors
mkCase heuristic df ty m knowledge colIndex =
    let column = getCol m colIndex
        occ = colOcc column :: Occurrence --What we match on

        --Scrutinee for the case expr
        scrutinee = varToCoreExpr occ :: CoreExpr
        occType = (varType occ) :: Type

        groupRows :: DynFlags -> Map PGrp (Set Int)
        groupRows df = Seq.foldlWithIndex
            (\grps i a -> msInsert grps (getGrp df a) i)
            Map.empty
            column -- :: Map PGrp (Set Int)

        defRows = Set.toList $ msLookup VarGrp $ groupRows df :: [Int]

        grps :: DynFlags -> [PGrp] --All Grps
        grps df = Map.keys $ groupRows df

        grpSet :: DynFlags -> Set.Set PGrp
        grpSet df = Set.fromList $ grps df

        cgrps :: DynFlags -> [PGrp] -- Non default groups
        cgrps df = P.filter (\g -> case g of {VarGrp -> False; _ -> True}) $ grps df
        hasDefaultGroup df = Set.member VarGrp (grpSet df) :: Bool

        -- | If we take the default branch we record the branches NOT taken instead.
        defaultExcludes :: DynFlags -> [CondValue]
        defaultExcludes df = mapMaybe grpCond $ cgrps df

        grpCond :: PGrp -> Maybe CondValue
        grpCond (LitGrp lit) =
            Just (LitCond lit)
        grpCond (VarGrp) =  
            Nothing
        grpCond (ConGrp dcon) =
            Just (ConCond dcon)
        grpCond _ = error "Not implemented grpCond"

        newEvidence :: PGrp -> DsM (Either [CondValue] CondValue)
        -- Returns evidence gained by selecting this branch/grp
        newEvidence (VarGrp) = do
            df <- getDynFlags
            return (Left $ defaultExcludes df)
        newEvidence grp =
            return . Right . fromJust . grpCond $ grp

        getGrpRows :: DynFlags -> PGrp -> [Int]
        getGrpRows df grp = 
            Set.toList $ msLookup grp $ groupRows df
            
        getSubMatrix :: [Int] -> CPM
        getSubMatrix rows =
            fmap fromJust $ Seq.filter isJust $ Seq.mapWithIndex (\i r -> if (i `elem` rows) then Just r else Nothing) m :: CPM
        getNewMatrix :: DynFlags -> PGrp -> DsM CPM
        -- Since we have to "splice in" the constructor arguments which requires more setup we deal
        -- with Constructor groups in another function
        getNewMatrix df grp =
            let rows = getGrpRows df grp :: [Int]
                matrix = getSubMatrix rows
            in
            case grp of
                VarGrp    -> return $ deleteCol matrix colIndex
                LitGrp {} -> return $ deleteCol matrix colIndex
                ConGrp con | dataConSourceArity con == 0 -> return $ deleteCol matrix colIndex
                           | otherwise                   -> error "Constructor group"
        

        groupExpr :: PGrp -> DsM MatchResult
        groupExpr grp = do
            df <- getDynFlags
            evidence <- newEvidence grp
            let newKnowledge = (Map.insert occ evidence knowledge)
            newMatrix <- getNewMatrix df grp 
            matchWith heuristic ty (newMatrix) newKnowledge :: DsM MatchResult


        defBranchMatchResult :: DsM (Maybe MatchResult)
        {- 
        We use this as a filler for the non-variable cases
        since if they fail we want to use the default expr if available.
        -}
        defBranchMatchResult = do
            df <- getDynFlags
            if hasDefaultGroup df 
                then Just <$> (groupExpr VarGrp)
                else return $ Nothing

        isLitCase :: DsM Bool
        isLitCase = do
            df <- getDynFlags
            return $ any (\g -> case g of {LitGrp {} -> True; _ -> False}) $ cgrps df
                                 


        {- 
        Generate the alternatives for nested constructors,
          this is somewhat more complex as we need to get vars,
          treat type arguments and so on.
        
        --TODO: Move into own function, PatSynonyms


        Record Handling:

        We keep the ids in the order of the constructor for the match.
        -}

        

        mkConAlt :: HasCallStack => DynFlags -> PGrp -> DsM (CaseAlt AltCon) --(CoreExpr -> DsM CoreAlt, CanItFail)
        mkConAlt df grp@(ConGrp con) = 
            -- Look at the pattern info from the first pattern.
            let ConPatOut { pat_con = L _ con1, pat_arg_tys = arg_tys, pat_wrap = wrapper1,
                    pat_tvs = tvs1, pat_dicts = dicts1, pat_args = args1, pat_binds = bind }
                    = firstPat

                fields1 = map flSelector (conLikeFieldLabels con1) :: [Name]

                entries = getGrpPats df grp :: [Entry PatInfo]
                firstPat = fst . head $ entries :: Pat GhcTc
                firstPatInfo = snd . head $ entries :: PatInfo
                        
                inst_tys = arg_tys ++ mkTyVarTys tvs1
                val_arg_tys = conLikeInstOrigArgTys con1 inst_tys
                
                --All patterns in column
                pats = map fst $ entries :: [Pat GhcTc]

                isRecord :: Bool
                isRecord = any (\p -> case (pat_args p) of {RecCon {} -> True; _ -> False}) pats

                -- Desugar the given patterns and produce a suitable wrapper.
                desugarPats :: [Pat GhcTc] -> [Id]  -> DsM (DsWrapper, [Pat GhcTc])
                desugarPats pats vars = do
                    --liftIO . putStrLn . showSDocUnsafe $ ppr pats
                    (wrappers, pats) <- unzip <$> zipWithM tidy1 vars pats
                    return (foldr (.) idDsWrapper wrappers, pats)


                getNewConMatrix :: PGrp -> [Id] -> DsM CPM
                getNewConMatrix grp@ConGrp {} vars = do
                    let conRows = getGrpRows df grp :: [Int]
                    let varRows = getGrpRows df VarGrp
                    let rows = sort $ conRows ++ varRows :: [Int]
                    let filteredRows = getSubMatrix rows :: CPM
                    let colEntries = getCol filteredRows colIndex :: PatternColumn PatInfo
                    let withoutCol = deleteCol filteredRows colIndex :: CPM

                    --At this point we reorder the argument id's to match the order of occurence in the PATTERN

                    let adjusted_vars = if isRecord then matchFields vars grpConFields paddedLabels else vars 

                    --Unpack the constructors
                    (wrappers, entries) <- unzip <$> 
                                            (mapM 
                                                (\e -> unpackCon e adjusted_vars)
                                                (F.toList colEntries)) :: DsM ([DsWrapper], [[Entry PatInfo]])
                    let wrappedMatrix = addRowWrappers withoutCol wrappers
                    --Insert the unpacked entries.
                    let unpackedMatrix = insertCols wrappedMatrix colIndex (Seq.fromList . map Seq.fromList . transpose $ entries)
                    constrainedMatrix <- addConstraints unpackedMatrix entries
                    return constrainedMatrix

                    --TODO: Build constraint for added entries
                getNewConMatrix ConGrp {} _ = error "Constructor group2"

                conGroupExpr :: PGrp -> [Id] -> DsM MatchResult
                conGroupExpr grp vars = do
                    evidence <- newEvidence grp
                    let newKnowledge = (Map.insert occ evidence knowledge)
                    newMatrix <- getNewConMatrix grp vars  
                    matchWith heuristic ty (newMatrix) newKnowledge

                vanillaFields :: Pat GhcTc -> Bool
                vanillaFields ConPatOut {pat_args = args, pat_con = L _ con@(RealDataCon dataCon)}
                    | null (conLikeFieldLabels con) = True --Constructor has no records
                    | null (hsConPatArgs args) = True -- Con {} can be expanded by wildcards
                    | patLabels `isPrefixOf` conLabels = True
                    | otherwise = False 
                    where
                        conLabels = map flSelector $ conLikeFieldLabels con :: [Name]
                        patLabels = map (getName . selectorFieldOcc . unLoc . hsRecFieldLbl . unLoc) $ hsPatFields args :: [Name]
                vanillaFields _ = False

                grpConFields :: [Name]
                grpConFields = map (getName . selectorFieldOcc) $ getFields firstPat

                getFields :: Pat GhcTc -> [FieldOcc GhcTc]
                getFields = map (unLoc . hsRecFieldLbl . unLoc) . hsPatFields . pat_args

                patLabels :: [[Name]]
                patLabels = map (map (getName . selectorFieldOcc) . getFields) pats

                paddedLabels :: [Name]
                paddedLabels = extendFields con (head patLabels)


            in do

                --Arguments to the Constructor
                arg_vars <- selectConMatchVars val_arg_tys args1


                {- 
                TODO: GADTs require special attention to get bindings right.
                Particularly data2 showcases where we miss creating a binder
                so for now we just use regular matching on these constructors.
                -}
                unless (isVanillaDataCon con) $ --traceM "fail:NonVanilla" >> 
                    failDs


                {-
                If there are incompatible record orders in a pattern we fail.

                TODO: However if we have {x2} {x2,x1} {x2,x1,x3} these are
                compatible and can be combined. This can be done by:
                * Make sure every record is a prefix of the longest sequence
                * Padding them to the longest sequence
                * Then treat them the same way as vanilla records. (Padding, rearanging ids, ...)
                -}

                let sameFields = and (map (== head patLabels) patLabels) :: Bool
                unless (
                    all vanillaFields pats || sameFields ) $ do
                        --traceM "incompatible Patterns"
                        failDs

                --TODO: Check if type/dict variables are required for tidying
                --Variable etc wrapper
                (rhsDesugarWrapper, pats) <- desugarPats pats arg_vars
                --Type variables etc wrapper
                (rhsTyWrapper) <- foldr (.) idDsWrapper <$> mapM (wrapPatBinds tvs1 dicts1) pats :: DsM DsWrapper

                wrapper <- return $ rhsDesugarWrapper . rhsTyWrapper

                ds_bind <- dsTcEvBinds bind
                mr <- conGroupExpr grp arg_vars :: DsM MatchResult

                --given the rhs add the bindings created above.
                let bodyBuilder = wrapper . mkCoreLets ds_bind :: CoreExpr -> CoreExpr

                let altBindings = tvs1 ++ dicts1 ++ arg_vars

                return $ MkCaseAlt 
                    { alt_pat = DataAlt con
                    , alt_bndrs = altBindings
                    , alt_wrapper = WpHole
                    , alt_result = adjustMatchResult bodyBuilder mr
                    }
        
        mkConAlt _ _ = error "mkConAlt - No Constructor Grp"

        getGrpPats :: DynFlags -> PGrp -> [Entry PatInfo]
        getGrpPats df grp = 
            let submatrix = getSubMatrix . getGrpRows df $ grp
                column = getCol submatrix colIndex :: PatternColumn PatInfo
            in
            F.toList column

        {-
        ******************* End of Con Grp alt code *******************
        -}

        --generate the alternative for a entry grp
        mkAlt :: PGrp -> DsM (CaseAlt AltCon)
        mkAlt grp@(LitGrp lit) = do
            --TODO: For now fall back to regular matching when strings are involved
            if isStringTy occType then failDs else return ()
            mr <- groupExpr grp
            
            return $ MkCaseAlt 
                { alt_pat = LitAlt lit
                , alt_bndrs = []
                , alt_wrapper = WpHole
                , alt_result = mr } 

        mkAlt grp@(ConGrp {}) = do
            df <- getDynFlags
            mkConAlt df grp 
        mkAlt (VarGrp) = error "mk*CaseMatchResult takes the default result"
            

        alts :: DsM [CaseAlt AltCon]
        {-
        Does not include the default branch
        -}
        alts = do
            df <- getDynFlags
            mapM (mkAlt) (cgrps df)


        toLitPair :: CaseAlt AltCon -> (Literal, MatchResult)
        toLitPair MkCaseAlt {alt_pat = LitAlt lit, alt_result = mr} 
            = (lit, mr)
        toLitPair alt  
            = pprPanic "Alt not of literal type" $ ppr $ alt_pat alt

        toConAlt :: CaseAlt AltCon -> CaseAlt DataCon
        toConAlt alt@MkCaseAlt {alt_pat = DataAlt con}
            = alt {alt_pat = con}
        toConAlt alt  
            = pprPanic "Alt not of constructor type" $ showAstData NoBlankSrcSpan $ alt_pat alt
            
    in do
        --traceM "mkCase"
        caseAlts <- alts :: DsM [CaseAlt AltCon]
        df <- getDynFlags

        isLit <- isLitCase
        defBranch <- defBranchMatchResult :: DsM (Maybe MatchResult)
        --if (isJust defBranch) then do
        --        let (MatchResult f body) = fromJust defBranch
        --        dsPrint $ text "isLit" <+> ppr isLit <+> text "canDefaultFail:" <+> ppr (f == CanFail) 
        --    else dsPrint $ text "isLit" <+> ppr isLit <+> text "nothingDefault"
        
        case True of
            _   | null (cgrps df) -> 
                    return $ 
                        fromMaybe 
                            (error "No branch case not handled yet as") 
                            defBranch
                | isLit           -> do 
                    let litAlts = map toLitPair caseAlts
                    return $ mkCoPrimCaseMatchResult occ ty litAlts defBranch
                | otherwise       -> do
                    let conAlts = map toConAlt caseAlts
                    return $ mkCoAlgCaseMatchResult df occ ty conAlts defBranch

extendFields :: DataCon -> [Name] -> [Name]
-- Extend a list of fields by the unmentioned ones in order.
extendFields dataCon pat_fields =
    let con_fields = map flSelector $ dataConFieldLabels dataCon
        mentioned_fields = Set.fromList pat_fields
        unmentioned_fields = filter (\f -> not (Set.member f mentioned_fields)) con_fields
    in
    pat_fields ++ unmentioned_fields

-- Reorders to given id's such that they mirror the order
-- of the fieldlabels given
matchFields :: forall a. Outputable a => [a] -> [Name] -> [Name] -> [a]
matchFields args con_fields pat_fields
    | not (null pat_fields)     -- Treated specially; cf conArgPats
    = ASSERT2( con_fields `equalLength` args,
               ppr con_fields $$ ppr args )
    map lookup_fld pat_fields
    | otherwise
    = args
    where
    fld_var_env = mkNameEnv $ zipEqual "get_arg_vars" con_fields args
    lookup_fld :: Name -> a
    lookup_fld rpat = lookupNameEnv_NF fld_var_env
                                        (rpat)
matchFields _ _ [] = panic "matchTree/matchFields []"

unpackCon :: Entry PatInfo -> [Id] -> DsM (DsWrapper, [Entry PatInfo])
-- | Pick apart a constructor returning result suitable to be spliced into
-- the match matrix
{-
If we deal with a record constructor we might need to pad the patterns by inserting wildcards

We take the vars in the oder defined by the constructor (data T = T a b -> [a,b])
This is true even if it's a record pattern.

For this reason we have to reorder the given id's
to match the order of the fields in the pattern.

Then we pad the result with wildcard patterns
for unmentioned records.
-}
unpackCon (WildPat ty, PatInfo {patOcc = patOcc, patCol = patCol}) vars =
    let wildcards --Generate wildcard patterns for all ids
            = zipWith (\t p -> p t) (map idType vars) (repeat WildPat)
    in do
    let mkEntry p occ colOffset = (p, PatInfo {patOcc = occ, patCol = patCol ++ [colOffset]}) 
    let entries = zipWith3 mkEntry wildcards vars [0..]
    return (idDsWrapper, entries)

unpackCon (conPat,     PatInfo {patOcc = patOcc, patCol = patCol}) vars =
    let arg_pats 
            = map unLoc $ hsConPatArgs args1 :: [Pat GhcTc]
        normalized_pats --Regular patterns + Wildcards for missing ones
            = zipWith (\t p -> p t) (map idType vars) (map const arg_pats ++ repeat WildPat) :: [Pat GhcTc]
    in do
    (wrappers, desugaredPats) <- unzip <$> zipWithM tidy1 vars normalized_pats
    let mkEntry p occ colOffset = (p, PatInfo {patOcc = occ, patCol = patCol ++ [colOffset]}) 
    let entries = zipWith3 mkEntry desugaredPats vars [0..]
    return (foldr (.) idDsWrapper wrappers, entries)
    where
        ConPatOut { pat_con = L _ con1, pat_arg_tys = arg_tys, pat_wrap = wrapper1,
                pat_tvs = tvs1, pat_dicts = dicts1, pat_args = args1 } = conPat

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
        else do--trace "solveCase" 
            (mkConstraintCase m ty knowledge simplifiedConstraints)

dsPrint :: SDoc -> DsM ()
dsPrint = liftIO . putStrLn . showSDocUnsafe

mkConstraintCase :: HasCallStack => CPM -> Type -> DecompositionKnowledge -> Constraints -> DsM DsWrapper
{-
Resolve at least one constraint by introducing a additional case statement
There is some bookkeeping not done here which needs to be fixed.
-}
mkConstraintCase m ty knowledge constraints =
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

        condAlt :: CondValue -> DsM (CoreExpr -> CoreAlt)
        condAlt (LitCond lit) = do
            return (\expr -> ((LitAlt lit), [], expr))
        {- TODO: 
        Currently if we have constraints ((,) a b) we have no good way to
        determine the types of a, b or the number of arguments at all.

        The question if it's enought to use wildcard binders or if we have to
        be able to reuse these is also still not clear to me.
        -}
        condAlt (ConCond dcon) = do
        {-
            let ConPatOut { pat_con = L _ con1, pat_arg_tys = arg_tys, pat_wrap = wrapper1,
                    pat_tvs = tvs1, pat_dicts = dicts1, pat_args = args1, pat_binds = bind }
                    = pat

            --Extract constructor argument types
            let inst_tys   = arg_tys ++ mkTyVarTys tvs1
            let val_arg_tys = conLikeInstOrigArgTys dcon inst_tys
            arg_vars <- selectConMatchVars val_arg_tys args1

            wrapper <- wrapPatBinds tvs1 dicts1 pat
            
            --dsPrint $ text "altCon: " <+> ppr dcon
            -}
            
            --TODO: We should only have to care about the type of constructor hence no bindings given
            -- return (\expr -> ((DataAlt dcon), .. bindings .., wrapper expr)) 
            return (\expr -> ((DataAlt dcon), [], expr)) 

    
    in do
    --traceM ("mkConstraint")
    --dsPrint $ text "knowledge" <+> ppr knowledge
    --dsPrint $ text "constraints" <+> ppr constraints
    --dsPrint $ ppr ty
    def <- defaultExpr :: DsM DsWrapper
    let defAlt = (\rhs -> (DEFAULT, [], def rhs)) :: CoreExpr -> CoreAlt
    altBuilders <- mapM (condAlt) occVals :: DsM [CoreExpr -> CoreAlt]
    altExpressions <- mapM (getAltExpr) occVals :: DsM [CoreExpr -> CoreExpr]
    let alts = (\rhs ->
            (defAlt rhs) :
                (zipWithEqual
                    "MatchConstraints: expressions /= branches"
                    (\altWrap exprWrap -> altWrap (exprWrap rhs)) altBuilders altExpressions
                )
            ) :: CoreExpr -> [CoreAlt]
    
    let caseBuilder = (\rhs ->
            let appliedAlts = alts rhs
                sortedAlts = sortOn (\(x,_y,_z) -> x) appliedAlts
            in
            Case (Var occ) (mkWildValBinder (idType occ)) ty (sortedAlts)
            )
    return caseBuilder
    
    

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
