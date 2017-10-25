{-# LANGUAGE CPP, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances, DeriveGeneric, DeriveDataTypeable, LambdaCase#-}
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

* For a matrix like

A D = 1
_ E = 2
C F = 3

* Post bac: PatSynonmys and other extensions



-}
module MatchTree
    (match, printmr, tidy1, cacheExpr)
where

#include "HsVersions.h"

#ifndef HACKY
import {-#SOURCE#-} DsExpr (dsLExpr, dsSyntaxExpr)
-- import GhcPrelude
#endif

import PrelNames

--import DsExpr
import DynFlags
import GHC.LanguageExtensions as LangExt
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
import TcType ( tcSplitTyConApp, isIntegerTy, isStringTy)
import TyCon( isNewTyCon )
import TysWiredIn
import ListSetOps
import SrcLoc
import Maybes
import Util
import Name
import Outputable
import BasicTypes ( isGenerated, fl_value, FractionalLit(..))
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
import MkId (DataConBoxer(..), voidPrimId)
import UniqSupply (initUs_, MonadUnique(..))
import HsTypes --(selectorFieldOcc)


--import Pattern.SimplePatterns
--import TL.Language
import Data.Foldable as F
import Prelude as P hiding (pred)
import Data.Bifunctor as BF
import Data.Either
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
import qualified CoreMap as TM

type MatchId = Id   -- See Note [Match Ids]

type Occurrence = MatchId

--type GhcTc = Id

--Also defined in MatchCon
type ConArgPats = HsConDetails (LPat GhcTc) (HsRecFields GhcTc (LPat GhcTc))

{-
Our system is such that:
A condition represents that a occurence must be one of
    * evaluated (Nothing)
    * matches a constructor (Right tag)
    * doesn't match it (Left tag)

Conditions are ordered and represent the conditions that must
be met before we can select a rhs. If any of the conditions fail
we either have to move to the next row in the matrix or fail.

A constraint is a list of conditions as described above.

Constraints are the sum of all constraints applicable to a rhs.

-}

data CondValue
    = LitCond { cv_lit :: Literal }
    | ConCond { cv_con :: DataCon, cv_pat :: Pat GhcTc }

{-TODO:
We currently just check the Constructor for patterns equality.
This might be enough but requires doublechecking if for
f C = 1
f C = 2
C might differ (Dictionaries and the like)
-}
instance Eq CondValue where
    (LitCond lit1) == (LitCond lit2) = lit1 == lit2
    (ConCond {cv_con = c1}) == (ConCond {cv_con = c2}) =
        c1 == c2
    _              == _              = False


instance Outputable CondValue where
    ppr (ConCond {cv_con = con}) = lparen O.<> text "ConVal " O.<> ppr con O.<> rparen
    ppr (LitCond lit) = lparen O.<> text "LitVal " O.<> ppr (lit) O.<> rparen


data PatInfo
    = PatInfo
    { patCol :: [Int]
    , patOcc :: !Occurrence
    --, patStrictness :: Bool --TODO: Track strictness during the algorithm and generate evaluations after pattern matching code if neccesary
    }
    deriving (Eq, Ord, Data)

instance Outputable PatInfo where
    ppr info = lparen O.<> text "PatInfo " O.<> ppr (patCol info, patOcc info) O.<> rparen

--Represents knowledge about the given occurence.
--Left => Constructors which the Occurence does not match.
--Right Tag => Occurence matches the constructor.
data Evidence = Evidence Occurrence (Either [CondValue] CondValue)

{-
Taking apart nested constructors like (Just (Either a b)) requires us to
generate new constraints which only apply to paths which actually inspect the
outer constructor.
When doing so however we have to resolve constraints in the same order they
semantically apply. To facilitate this we keep the PatInfo of the original pattern around.
This allows as to insert new conditions in the middle of the list at the position given by patCol
-}
--Represents a condition on the given occurence.
data Condition = CondEvaluate PatInfo | CondMatch PatInfo CondValue

-- | Get the origin of a condition
getCondPos :: Condition -> [Int]
getCondPos = patCol . getCondPat

getCondPat :: Condition -> PatInfo
getCondPat (CondEvaluate i) = i
getCondPat (CondMatch i _)  = i

getCondMatchVal :: Condition -> Maybe CondValue
getCondMatchVal (CondEvaluate _) = Nothing
getCondMatchVal (CondMatch _ v)  = Just v

instance Outputable Condition where
    ppr (CondEvaluate i) =
        text "eval@" O.<> ppr i
    ppr (CondMatch i val) =
        text "match@" O.<> ppr i O.<>
        text ":" O.<> ppr val

type Conditions = [Condition]

type Constraint = Conditions
type Constraints = [Constraint]

type CPM = PM PatInfo MatrixRHS
{--
 Set of all occurences and the constructor it was evaluated to.
 We generate no knowledge for default branches
-}
type DecompositionKnowledge = Map Occurrence (Either [CondValue] CondValue)

type Heuristic = DynFlags -> CPM -> Maybe Int

-- Matrix Types
type EqMatrix = PM PatInfo MatrixRHS

{-
(c@Constraint, deadcs@Constraints):
c tracks the constraint that is generated by the row it's attached to.
We track this one seperatly since it might change when we unpack constructors.

cs tracks constraints of filtered rows. If we have:
    False -> NotMatched -> ...
then we might filter the row based on later arguments, we still have to resulve the constraint on the first
two arguments though.

Note: Theoretically we could construct all constraints based on the occurence index at the beginning
      and fill in the actual id's later. However this means we have to desugar all patterns as well
      which might lead to desugaring of redundant patterns.

TODO:
    It's better to store all closed/inherited constraints in the matrix and not once per row.
    This grow historically and can (and should!) be changed.

-}
type MatrixRHS = (MatchResult, (Constraint, Constraints))


type Entry e = (Pat GhcTc, e)

-- Pattern matrix row major. The plan is to store additional info in e
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
    let useTreeMatching = gopt Opt_TreeMatching df
    unless useTreeMatching failDs
    --dsPrint $ text "Tree:match" <+> ppr eqns
    matrix <- (toPatternMatrix vars eqns)
    --traceM "match:"
    --liftIO . putStrLn . showSDocUnsafe $ ppr $ eqns
    result <- matchWith complexHeuristic ty matrix (Map.empty)
    --result <- matchWith leftToRight ty matrix (Map.empty)

    case result of

        MatchResult CantFail match_fn -> do
            -- traceM "NonFailResult"
            filler <- Var <$> mkSysLocalOrCoVarM (fsLit "ds_share_") ty
            resExpr <- match_fn filler :: DsM CoreExpr
            -- traceM $ showSDocUnsafe $ showAstData NoBlankSrcSpan resExpr
            --let f = cacheExpr :: CoreExpr -> CoreExpr
            --fmap cantFailMatchResult $ cacheExpr $ resExpr
            return result
        _ -> return result


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
    return (Seq.fromList desugaredPats, (rowMatchResult, ([],[])))










strictColumn :: PatternColumn e -> Bool
strictColumn = all (isStrict . fst)

-- | Take a matrix and calculate occurences which are always evaluated.
strictSet :: HasCallStack => EqMatrix -> [Int]
--TODO: Include strict columns which contain wildcards in some rows
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

leftToRight :: DynFlags -> EqMatrix -> Maybe Int
{-
We select strict columns left to right for one exception:
If there is just a single row we can process patterns from
left to right no matter their strictness.
-}
leftToRight _df m
    | null m = Nothing
    | rowCount' == 0 = Nothing
    | colCount' == 0 = Nothing
    | rowCount' == 1 && colCount' > 0 = Just 0
    | all (not . isStrict) (fmap (fst . flip Seq.index 0. fst) m) = Just 0
    | null ss         = Nothing
    | otherwise       = Just $ head ss
    where
        ss = strictSet m
        rowCount' = (rowCount m)
        colCount' = fromMaybe 0 (columnCount m)

complexHeuristic :: HasCallStack => DynFlags -> EqMatrix -> Maybe Int
{-
Combine multiple heuristics on columns to pick the best ones.

TODO: Needs a rework before pattern extensions can work.
-}
complexHeuristic df m
    | null m                                        = --trace "c1" $
        Nothing
    | rowCount' == 0                                = --trace "c2" $
        Nothing
    | colCount' == 0                                = --trace "c3" $
        Nothing
    | rowCount' == 1 && colCount' > 0               = --trace "c4" $
        Just 0
    | all (not . isStrict)    --No column has a strict constructor
          (fmap (fst . flip Seq.index 0 . fst) m)    = --trace "c5" $
            Just 0
    | null ss                                       = --trace "c6" $
        Nothing
    | otherwise                                     = --trace "c7" $
        Just choice
    where
        ss = if xopt LangExt.Strict df then [0..colCount'] else strictSet m
        rowCount' = (rowCount m)
        colCount' = fromMaybe 0 (columnCount m)
        patColumns :: [ [Pat GhcTc] ]
        patColumns = map (toList . fmap fst) columns

        --We sort on the result of heuristics hence (-max = best, +max = worst)

        --The number of consecutive constructor patterns
        --is a good primary heuristic.
        conPrefixLength :: [Pat GhcTc] -> Int
        conPrefixLength pats =
            negate $ plength isCon pats

        --The number of different constructors appearing in a column
        --is useful to reduce the size of the resulting tree.
        --Generally prefer columns with many different constructors.
        conVariety :: [Pat GhcTc] -> Int
        conVariety pats =
            length $ Set.filter (/= VarGrp) $ Set.fromList $ map (patGroup df) pats

        --The constructor count can help to pick columns with many (non-consecutive)
        --patterns first.
        conCount :: [Pat GhcTc] -> Int
        conCount pats =
            negate . length $ filter isCon pats

        --TODO: The number of strict entries might also be a interesting heuristic
        -- although I expect it to cover mostly the same cases as conCount

        isCon :: Pat GhcTc -> Bool
        isCon ConPatOut {} = True
        isCon LitPat {} = True
        isCon _ = False

        -- | If a column has the same pattern in all rows pick it first.
        --   Implied by conVariety anyway
        {-
        singleGrp :: [Pat GhcTc] -> Int
        singleGrp pats =
            if all (== patGroup df (head pats)) $ map (patGroup df) pats
                then -1
                else 0
        -}


        columns = getColumns m :: [PatternColumn PatInfo]

        -- | pairs of (score,colum) with lower scores being better.
        rankedColumns :: [([Int], Int)]
        rankedColumns = sortOn fst (
            zipWith
            (\colPats i->
                ([ conPrefixLength colPats --length of constructor prefix (more is better)
                 --, singleGrp colPats
                 , conVariety colPats --Number of different constructors (less is better)
                 , conCount colPats --Number of constructors in column (more is better)
                 ]
                , i))
            patColumns [0..])
        choice :: Int
        choice = --trace "ss" $ traceShow ss $ traceShow rankedColumns $ trace "done" $
                snd . head $ filter (\(_p,idx) -> elem idx ss) rankedColumns


plength :: (a -> Bool) -> [a] -> Int
plength f  [] = 0
plength f (x:xs)
    | f x = 1 + plength f xs
    | otherwise   = 0



-- | Is evaluation of the pattern required
isStrict :: Pat GhcTc -> Bool
isStrict WildPat {} = False
isStrict ConPatOut {} = True
isStrict LitPat {} = True
isStrict NPat {} = True --
isStrict NPlusKPat {} = True -- ?
isStrict BangPat {} = True
isStrict p
    = error $ "Should have been tidied already: " ++
              (showSDocUnsafe (ppr p <+> showAstData BlankSrcSpan p))





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



setEqConstraint :: TreeEquation -> (Constraint, Constraints) -> TreeEquation
setEqConstraint eq constraintTuple = second (\rhs -> second (const constraintTuple) rhs) eq

getEqConstraint :: TreeEquation -> (Constraint, Constraints)
getEqConstraint eq = snd . snd $ eq

-- Calculate the constraints of the whole matrix
constrainMatrix :: HasCallStack => CPM -> DsM (CPM)
constrainMatrix m =
    let goRow :: [TreeEquation] -> DsM [TreeEquation]
        goRow m = do
            --traceM "goRow"
            case m of
                [] -> --liftIO (print "RowBaseCase") >>
                    return []
                (row:eqs) -> --liftIO (print "rowRecurse") >>
                    do
                    --traceM "rowCons:"
                    --liftIO $ putStrLn . showSDocUnsafe $ ppr constraints
                    newConstraint <- rowConstraint $ fst row :: DsM Constraint -- Conditions
                    let currentRow = setEqConstraint row (newConstraint, []) :: TreeEquation
                    --traceM "doneRow:"
                    --liftIO $ putStrLn . showSDocUnsafe $ ppr currentRow
                    nextRows <- goRow eqs
                    return $ currentRow : nextRows
    in do
    --traceM "constrainMatrix"
    rows <- goRow $ F.toList m :: DsM [TreeEquation]
    return $ Seq.fromList rows


getConConstraint :: HasCallStack => Pat GhcTc -> DsM (CondValue)
getConConstraint pat
    | (L _ (RealDataCon dcon)) <- (pat_con pat) = return $ ConCond dcon pat
    | (L _ (PatSynCon   scon)) <- (pat_con pat) = --warnDs NoReason (ppr "Pat Synonyms not implemented for tree matching") >>
        fallBack "PatSyn not supported"



getPatternConstraint :: HasCallStack => Entry PatInfo -> DsM (Maybe (Condition))
{- | The conditions imposed on the RHS by this pattern.
-- Result can be:
* No condition
* Evaluation -> The occurence requires evaluation (wildcards!)
* Constructor -> Evaluation + any following constraints
                 only have to be considered if the result matches the constructor.
-}
getPatternConstraint ((LitPat _ lit),info) = do
    df <- getDynFlags :: DsM DynFlags
    return $ Just $ CondMatch info $ (LitCond (hsLitKey df lit))
getPatternConstraint (pat@(ConPatOut { pat_con = con}), info) = do
    -- TODO: Extend for nested arguments
    df <- getDynFlags :: DsM DynFlags
    --traceM "conConstraint"
    conConstraint <- getConConstraint pat
    return $ Just $ CondMatch info conConstraint
getPatternConstraint (WildPat {}, info) =
    --traceM "wp" >>
    return Nothing
getPatternConstraint (VarPat {}, info) =
    --traceM "vp" >>
    return Nothing
getPatternConstraint (BangPat _ (L _ p), info)
    | WildPat {} <- p = return $ Just (CondEvaluate info)
    | VarPat {} <- p = return $ Just (CondEvaluate info)
getPatternConstraint (p@BangPat {}, info) =
    fallBack $ "Bang patterns should have been stripped of all supported patterns " ++ showSDocUnsafe (ppr p)
getPatternConstraint (p, info) =
    fallBack $ "Pat should have been tidied already or not implemented " ++ showSDocUnsafe (ppr p)

{-
getPatternConstraint NPat {} occ =
    error "TODO"
getPatternConstraint NPlusKPat {} occ =
    error "Not implemented NPK"
-}



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

addConstraints :: (Traversable t, Outputable (t (t (Entry PatInfo))), HasCallStack) => CPM -> t (t (Entry PatInfo)) -> DsM CPM
{- Takes a matrix and a list of unpacked entries.
This is used when unpacking constructors during desugaring.
* Calculate the constraints from the entries
* Update the matrix with the new Constraints

Important: Constraints have to be added at the right place in the constraint list (sorted according to patOcc in PatInfo)
-}
addConstraints m newRowEntries = do
    let setConstraint row newStuff = do
            let (oldConstraint, inherited) = snd . snd $ row :: (Constraint, Constraints)
            newConstraint <- rowConstraint newStuff
            let combined = sortOn (getCondPos) $ mappend oldConstraint newConstraint :: Constraint
            return $ setEqConstraint row (combined, inherited)

{-
    --Constraints for each row.
    newRowConstraints <- F.toList <$> mapM rowConstraint rows :: DsM [Constraint]

    --constraints of each row + the rows above it.
    let addedConstraints = tail . inits $ newRowConstraints :: [Constraints]
    --existing constraints
    let oldRowConstraints = F.toList $ fmap (snd . snd) m :: [(Constraint, Constraints)]
    {- Add new constraints! This is not complicated but easy to get wrong
    We have to add the newly found constraints INTO all existing constraints.
    This means if we had before (Just/0 -> ...) and discover (True/0.0) we combine
    them into (Just/0 -> True/0.0 -> ...)

    TODO: Verify that we can insert it in ALL constraints:
    * If the constraint is based on what we unpack we can add it ... maybe.
      * However if we have a constructor with two arguments (T2 _ _) where
        each row evaluates a different argument. we make the
    * If the constraint is based on a different constructor (eg Nothing for the example)
      the row has been filtered out by the time we unpack the constructor.
    * If the row was based on a wildcard we can't insert it either!
    -}
    let combinedConstraints = zipWith (++) oldRowConstraints addedConstraints :: [Constraints]
    let sortedConstraints = Seq.fromList $ map (map (sortOn (patCol . fst))) combinedConstraints :: Seq.Seq Constraints

    dsPrint $ text "Collect constraints from" <+> ppr rows
    dsPrint $ text "newRowConstraints" <+> ppr newRowConstraints
    dsPrint $ text "addedConstraints" <+> ppr addedConstraints
    dsPrint $ text "oldRowConstraints" <+> ppr oldRowConstraints
    dsPrint $ text "combinedConstraints" <+> ppr combinedConstraints
    dsPrint $ text "sortedConstraints" <+> ppr sortedConstraints
    -}
    sequence $ Seq.zipWith (setConstraint) m (Seq.fromList $ toList newRowEntries)

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
        --dsPrint $ text "matchWith:"
        --dsPrint $ text "Matrix" <+> (ppr $ fmap fst m)
        --dsPrint $ text "Constraints" <+> (ppr $ fmap (snd . snd) m)
        --dsPrint $ showAstData BlankSrcSpan $ fmap fst m
        --liftIO $ putStrLn . showSDocUnsafe $ text "Type:" O.<> ppr ty
        --traceM "Match matrix"

        --If we match on something like f x = <canFailRhs> we can end up with a match on an empty matrix
        df <- getDynFlags
        let matchCol = heuristic df m :: Maybe Int
        --dsPrint $ text "Matchcol:" <+> ppr matchCol
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
                    let (expr, (rowConstraint, inheritedConstraints)) = getRhs m 0 :: (MatchResult, (Constraint,Constraints))
                    let constraints = rowConstraint : inheritedConstraints

                    continuation <- matchWith heuristic ty (Seq.drop 1 m) knowledge :: DsM MatchResult
                    constraintWrapper <- (resolveConstraints m ty knowledge) constraints -- :: DsM DsWrapper
                    let constrainedMatch = adjustMatchResultDs constraintWrapper expr :: MatchResult

                    return $ combineMatchResults constrainedMatch continuation

                | fromJust (columnCount m) == 0 -> do
                    let rhss = F.toList $ fmap snd m :: [MatrixRHS]
                    let (results, constraintTuples) = unzip rhss

                    constraintWrappers <- mapM (resolveConstraints m ty knowledge . uncurry (:)) constraintTuples  :: DsM [CoreExpr -> DsM CoreExpr]
                    let constrainedMatches = zipWith adjustMatchResultDs constraintWrappers results :: [MatchResult]

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

-- Since evaluation is taken care of in the constraint we can ignore them for grouping patterns.
patGroup :: HasCallStack => DynFlags -> Pat GhcTc -> PGrp
patGroup _df (WildPat {} ) = VarGrp
patGroup _df (VarPat  {} ) = VarGrp
patGroup df  (BangPat _ (L _loc p)) = patGroup df p
patGroup _df (ConPatOut { pat_con = L _ con})
    | PatSynCon psyn <- con
    = pprPanic "Not implemented" (ppr con <+> showAstData NoBlankSrcSpan con)
    | RealDataCon dcon <- con              =
        ConGrp dcon
        --Literals
patGroup df (LitPat _ lit) = LitGrp $ hsLitKey df lit
patGroup _ p = pprPanic "Not implemented" (ppr p <+> showAstData NoBlankSrcSpan p)

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

altToLitPair :: CaseAlt AltCon -> (Literal, MatchResult)
altToLitPair MkCaseAlt {alt_pat = LitAlt lit, alt_result = mr}
    = (lit, mr)
altToLitPair alt
    = pprPanic "Alt not of literal type" $ ppr $ alt_pat alt

altToConAlt :: CaseAlt AltCon -> CaseAlt DataCon
altToConAlt alt@MkCaseAlt {alt_pat = DataAlt con}
    = alt {alt_pat = con}
altToConAlt alt
    = pprPanic "Alt not of constructor type" $
      showAstData NoBlankSrcSpan $ alt_pat alt

fallBack :: String -> DsM a
fallBack m = --traceM m >>
    failDs

info :: String -> DsM ()
info = traceM

{-
This is at the hear of algorithms recursion. We
    * Select a column
    * Generate a case expression
    * Fill the branches by recursive calls to this function,
      passing along constraints/info resulting from the case expression
-}
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
        occType = (varType occ) :: Type



        groupRows :: Map PGrp (Set Int)
        groupRows = Seq.foldlWithIndex
            (\grps i a -> msInsert grps (getGrp df a) i)
            Map.empty
            column -- :: Map PGrp (Set Int)

        defRows = Set.toList $ msLookup VarGrp $ groupRows :: [Int]

        grps :: [PGrp] --All Grps
        grps = Map.keys $ groupRows

        cgrps :: [PGrp] -- Non default groups
        cgrps = P.filter (\g -> case g of {VarGrp -> False; _ -> True}) grps

        hasDefaultGroup = Map.member VarGrp groupRows :: Bool

        -- | If we take the default branch we record the branches NOT taken instead.
        defaultExcludes :: [CondValue]
        defaultExcludes = mapMaybe grpCond cgrps

        grpCond :: PGrp -> Maybe CondValue
        grpCond (LitGrp lit) =
            Just (LitCond lit)
        grpCond (VarGrp) =
            Nothing
        grpCond (ConGrp dcon) =
            Just (ConCond dcon (error "Evidence patterns should not be checked"))
        grpCond _ = error "Not implemented grpCond"

        newEvidence :: PGrp -> DsM (Maybe (Either [CondValue] CondValue))
        -- Returns evidence gained by selecting this branch/grp
        newEvidence (VarGrp) =
            --If we have no constructor groups the result won't be a case
            --but just a deletion of the row. Hence we don't evaluate hence
            --no new knowledge
            if null cgrps
                then return Nothing
                else return (Just . Left $ defaultExcludes)
        newEvidence grp =
            return $ Just . Right . fromJust . grpCond $ grp

        getGrpRows :: PGrp -> [Int]
        getGrpRows grp =
            Set.toList $ msLookup grp $ groupRows

        getSubMatrix :: [Int] -> CPM
        getSubMatrix rows =
            let rowInfo = toList $ Seq.mapWithIndex (\i r -> if (i `elem` rows) then Right r else Left (snd.snd $ r)) m :: [(Either (Constraint, Constraints) TreeEquation)]
                addClosed :: Constraints -> TreeEquation -> TreeEquation
                addClosed closedConstraints row  =
                    let (c,cs) = getEqConstraint row :: (Constraint, Constraints)
                    in setEqConstraint row (c,cs++closedConstraints)

                --closedConstraints = map fst . lefts $ rowInfo :: Constraints

                updatedRows =
                    mapAccumL (\closed row ->
                        either
                            (\(c,cons) -> (c:closed, Nothing))
                            (\r    -> (closed     , Just (addClosed closed r)))
                            row
                        )
                        []
                        rowInfo

                --Add the now eliminated constraints as inherited to the remaining ones

            in
            Seq.fromList . catMaybes $ snd updatedRows
            --fmap fromJust $ Seq.filter isJust $ Seq.mapWithIndex (\i r -> if (i `elem` rows) then Just r else Nothing) m :: CPM
        getNewMatrix :: PGrp -> DsM CPM
        -- Since we have to "splice in" the constructor arguments which requires more setup we deal
        -- with Constructor groups in another function
        getNewMatrix grp =
            let rows = getGrpRows grp :: [Int]
                matrix = getSubMatrix rows
            in  (dsPrint $ text "submatrixConstraints\n" <+> ppr (fmap getEqConstraint matrix)) >>
            case grp of
                VarGrp    -> return $ deleteCol matrix colIndex
                LitGrp {} -> return $ deleteCol matrix colIndex
                ConGrp con | dataConSourceArity con == 0 -> return $ deleteCol matrix colIndex
                           | otherwise                   -> error "Constructor group"


        groupExpr :: PGrp -> DsM MatchResult
        groupExpr grp = do
            evidence <- newEvidence grp
            let newKnowledge = maybe knowledge (\evid -> Map.insert occ evid knowledge) evidence
            newMatrix <- getNewMatrix grp
            matchWith heuristic ty (newMatrix) newKnowledge :: DsM MatchResult


        defBranchMatchResult :: DsM (Maybe MatchResult)
        {-
        We use this as a filler for the non-variable cases
        since if they fail we want to use the default expr if available.
        -}
        defBranchMatchResult = do
            if hasDefaultGroup
                then Just <$> (groupExpr VarGrp)
                else return $ Nothing

        isLitCase :: DsM Bool
        isLitCase = do
            return $ any (\g -> case g of {LitGrp {} -> True; _ -> False}) $ cgrps

        {-
        Generate the alternatives for nested constructors,
          this is somewhat more complex as we need to get vars,
          treat type arguments and so on.

        --TODO: Move into own function, PatSynonyms


        Record Handling:

        We keep the ids in the order of the constructor for the match.
        -}



        mkConAlt :: HasCallStack => PGrp -> DsM (CaseAlt AltCon) --(CoreExpr -> DsM CoreAlt, CanItFail)
        mkConAlt grp@(ConGrp con) =
            -- Look at the pattern info from the first pattern.
            let ConPatOut { pat_con = L _ con1, pat_arg_tys = arg_tys, pat_wrap = wrapper1,
                    pat_tvs = tvs1, pat_dicts = dicts1, pat_args = args1, pat_binds = bind }
                    = firstPat

                conFields = map flSelector (conLikeFieldLabels con1) :: [Name]

                entries = getGrpPats grp :: [Entry PatInfo]
                firstPat = fst . head $ entries :: Pat GhcTc
                firstPatInfo = snd . head $ entries :: PatInfo

                inst_tys = arg_tys ++ mkTyVarTys tvs1
                val_arg_tys = conLikeInstOrigArgTys con1 inst_tys

                --All patterns in column
                pats = map fst $ entries :: [Pat GhcTc]

                isRecord :: Bool
                isRecord = any (\p -> case args1 of {RecCon {} -> True; _ -> False}) pats

                -- Desugar the given patterns and produce a suitable wrapper.
                desugarPats :: [Pat GhcTc] -> [Id]  -> DsM (DsWrapper, [Pat GhcTc])
                desugarPats pats vars = do
                    --liftIO . putStrLn . showSDocUnsafe $ ppr pats
                    (wrappers, pats) <- unzip <$> zipWithM tidy1 vars pats
                    return (foldr (.) idDsWrapper wrappers, pats)


                getNewConMatrix :: PGrp -> [Id] -> DsM CPM
                -- Take a pattern group and the list of id's resulting from
                -- Constructor alternative
                getNewConMatrix grp@ConGrp {} vars = do
                    let conRows = getGrpRows grp :: [Int]
                    let varRows = getGrpRows VarGrp
                    let rows = sort $ conRows ++ varRows :: [Int]
                    let filteredRows = getSubMatrix rows :: CPM
                    let colEntries = getCol filteredRows colIndex :: PatternColumn PatInfo
                    let withoutCol = deleteCol filteredRows colIndex :: CPM

                    --Determine strictness of the Constructor arguments
                    let bangs = dataConImplBangs con :: [HsImplBang]

                    let arg_info = zip vars bangs

                    --At this point we reorder the given ids to match the order of the written record.
                    adjusted_arg_info <-
                            if isRecord
                                then failDs --for now skip records
                                    -- unzip $ matchFields arg_info conFields paddedLabels
                                else return $ unzip arg_info



                    --Unpack the constructors
                    (wrappers, entries) <- unzip <$>
                                            (mapM
                                                (\e -> unpackCon e adjusted_arg_info)
                                                (F.toList colEntries)) :: DsM ([DsWrapper], [[Entry PatInfo]])
                    let wrappedMatrix = addRowWrappers withoutCol wrappers
                    --Insert the unpacked entries.
                    let unpackedMatrix = insertCols wrappedMatrix colIndex (Seq.fromList . map Seq.fromList . transpose $ entries)
                    --TODO: Fix this!
                    constrainedMatrix <- addConstraints unpackedMatrix entries
                    return constrainedMatrix

                    --TODO: Build constraint for added entries
                getNewConMatrix ConGrp {} _ = error "Constructor group2"

                conGroupExpr :: PGrp -> [Id] -> DsM MatchResult
                conGroupExpr grp vars = do
                    evidence <- newEvidence grp
                    let newKnowledge = maybe knowledge (\evid -> Map.insert occ evid knowledge) evidence
                    newMatrix <- getNewConMatrix grp vars
                    matchWith heuristic ty (newMatrix) newKnowledge

                vanillaFields :: Pat GhcTc -> Bool
                vanillaFields inpat@ConPatOut {pat_args = args, pat_con = L _ con@(RealDataCon dataCon)}
                    | null (conLikeFieldLabels con) = True --Constructor has no records
                    | null (hsConPatArgs args) = True -- Con {} can be expanded by wildcards
                    | patLabels `isPrefixOf` conLabels = True
                    | otherwise = False
                    where
                        conLabels = map flSelector $ conLikeFieldLabels con :: [Name]
                        patLabels :: [Name]
                        patLabels = getPatLabels inpat
                vanillaFields _ = False

                getPatLabels :: Pat GhcTc -> [Name]
                getPatLabels = map (getName . unLoc . hsRecFieldSel . unLoc) . hsPatFields . pat_args

                getPatFields :: Pat GhcTc -> [FieldOcc GhcTc]
                getPatFields = map (unLoc . hsRecFieldLbl . unLoc) . hsPatFields . pat_args

                patLabels :: [[Name]]
                patLabels = map getPatLabels pats

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
                    fallBack "Non-vanilla data con"


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
                        fallBack "incompatible Patterns"


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
        mkAlt :: PGrp -> DsM (CaseAlt AltCon)
        mkAlt grp@(LitGrp lit) = do
            mr <- groupExpr grp

            return $ MkCaseAlt
                { alt_pat = LitAlt lit
                , alt_bndrs = []
                , alt_wrapper = WpHole
                , alt_result = mr }

        mkAlt grp@(ConGrp {}) = do
            mkConAlt grp
        mkAlt (VarGrp) = error "mk*CaseMatchResult takes the default result"


        alts :: DsM [CaseAlt AltCon]
        {-
        Does not include the default branch
        -}
        alts = mapM (mkAlt) (cgrps)

    in do
        when (isStringTy occType) $ fallBack "fallBack:OccType=String "

        --traceM "mkCase"
        caseAlts <- alts :: DsM [CaseAlt AltCon]

        when (
            any (\x -> case x of {ConGrp {} -> True; _ -> False}) cgrps &&
            any (\x -> case x of {LitGrp {} -> True; _ -> False}) cgrps)
                --TODO: A string might be desugard as a list OR as a string literal.
                --If we counter both in the same column we fail for now.
                (fallBack "Mix of Lit and Con grps")

        isLit <- isLitCase
        defBranch <- defBranchMatchResult :: DsM (Maybe MatchResult)
        --if (isJust defBranch) then do
        --        let (MatchResult f body) = fromJust defBranch
        --        dsPrint $ text "isLit" <+> ppr isLit <+> text "canDefaultFail:" <+> ppr (f == CanFail)
        --    else dsPrint $ text "isLit" <+> ppr isLit <+> text "nothingDefault"

        case True of
            _   | null (cgrps) ->
                    return $
                        fromMaybe
                            (error "No branch case not handled yet as")
                            defBranch
                | isLit           -> do
                    let litAlts = map altToLitPair caseAlts
                    if isStringTy (occType)
                        then error "TODO:Fix but not used atm:" $ do
                            do  { eq_str <- dsLookupGlobalId eqStringName
                                ; mrs <- mapM (wrap_str_guard occ eq_str) litAlts
                                ; return (foldr1 combineMatchResults mrs) }
                        else
                            return $ mkCoPrimCaseMatchResult occ ty litAlts defBranch
                | otherwise       -> do
                    let conAlts = map altToConAlt caseAlts
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




-- | Pick apart a constructor returning result suitable to be spliced into
-- the match matrix
unpackCon :: Entry PatInfo -> ([Id],[HsImplBang]) -> DsM (DsWrapper, [Entry PatInfo])
{-
If we deal with a record constructor we might need to pad the patterns by inserting wildcards

We take the vars in the oder defined by the Pattern.

In the case of records we might have fewer patterns than the constructor has arguments.
In that case we fill these slots with wildcard patterns.

--- CONSTRAINTS ---

If we have a pattern like (Just X) we generate the constraint Just -> evaluate next occurence.
If X is:
 a) A constructor/literal this is fine.
    The next occurence will be
 1) A wildcard (_,var,!_,!var)
-}
unpackCon (WildPat ty, PatInfo {patOcc = patOcc, patCol = patCol}) (vars, bangs) =
    let wildcards --Generate wildcard patterns for all ids
            = zipWith3 (\t bang pat ->
                            if isBanged bang
                                then unLoc . addBang $ (L (error "Not looked at") (pat t))
                                else (pat t))
                (map idType vars)
                bangs
                (repeat WildPat)
    in do
    let mkEntry p occ colOffset = (p, PatInfo {patOcc = occ, patCol = patCol ++ [colOffset]})
    let entries = zipWith3 mkEntry wildcards vars [0..]
    return (idDsWrapper, entries)

unpackCon (conPat@ConPatOut {},     PatInfo {patOcc = patOcc, patCol = patCol}) (vars, bangs) =
    let arg_pats
            = map unLoc $ hsConPatArgs args1 :: [Pat GhcTc]
        normalized_pats --Regular patterns + Wildcards for missing ones
            = zipWith3 (\t bang pat ->
                            if isBanged bang
                                then unLoc . addBang $ (L (error "Not looked at") (pat t))
                                else (pat t))
                        (map idType vars)
                        bangs
                        (map const arg_pats ++ repeat WildPat) :: [Pat GhcTc]
    in do
    (wrappers, desugaredPats) <- unzip <$> zipWithM tidy1 vars normalized_pats
    let mkEntry p occ colOffset = (p, PatInfo {patOcc = occ, patCol = patCol ++ [colOffset]})
    let entries = zipWith3 mkEntry desugaredPats vars [0..]
    return (foldr (.) idDsWrapper wrappers, entries)
    where
        ConPatOut { pat_con = L _ con1, pat_arg_tys = arg_tys, pat_wrap = wrapper1,
                pat_tvs = tvs1, pat_dicts = dicts1, pat_args = args1 } = conPat
unpackCon (BangPat _ (L _ p), info) (vars, bangs) =
    unpackCon (p, info) (vars, bangs)
unpackCon (pat, info) _ =
    error $ "unpackCon failed on:" ++ showSDocUnsafe (ppr pat)

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


resolveConstraints :: HasCallStack => CPM -> Type -> DecompositionKnowledge -> Constraints -> DsM (CoreExpr -> DsM CoreExpr)
{- Produces a wrapper which guarantees evaluation of arguments according to Augustsons algorithm.
 a match result to include required evaluation of occurences according to the constraints. -}

resolveConstraints m ty knowledge constraints = do
    {-
    * Remove satisfied constraints
    * simplify constraints
    * Generate case
    * Apply resolveConstraints
    -}
    let simplifiedConstraints = L.filter (not . null) .
                map (flip simplifyConstraint knowledge) .
                map (truncateConstraint knowledge) $ constraints :: Constraints

    dsPrint $ text "resolve:"
    dsPrint $ text "knowledge" <+> ppr knowledge
    dsPrint $ text "constraints" <+> ppr constraints
    dsPrint $ text "simplified" <+> ppr simplifiedConstraints


    if null simplifiedConstraints
        then --trace "BaseCase" $
            return $ \e -> return e
        else do
            --traceM "solveCase"
            (mkConstraintCase m ty knowledge simplifiedConstraints)

dsPrint :: SDoc -> DsM ()
dsPrint doc =
    --liftIO . putStrLn . showSDocUnsafe >>
    return ()

mkConstraintCase :: HasCallStack => CPM -> Type -> DecompositionKnowledge -> Constraints -> DsM (CoreExpr -> DsM CoreExpr)
{-
Resolve at least one constraint by introducing a additional case statement
There is some bookkeeping not done here which needs to be fixed.???
-}
mkConstraintCase m ty knowledge constraints = --trace "mkConstraintCase" $
    let cond = head . head $ constraints :: Condition
        info = getCondPat cond
        occ = patOcc info :: Occurrence
        occType = varType occ
        --ty = varType occ :: Kind
        occValues :: [Maybe CondValue]
        occValues = concatMap
            (\constraint ->
                foldMap
                    (\cond' ->
                        if (patOcc . getCondPat $ cond') == occ then [getCondMatchVal cond'] else [])
                    constraint)
            constraints
        occVals = nub $ catMaybes occValues :: [CondValue]
        newEvidence condVal = Right condVal

        litConstraint = case head occVals of { LitCond {} -> True; _ -> False}

        getAltResult :: CondValue -> DsM MatchResult
        getAltResult condVal = do
            wrapper <- (resolveConstraints m ty (Map.insert occ (newEvidence condVal) knowledge) constraints)
            return $ adjustMatchResultDs wrapper $ MatchResult CanFail $ \expr -> return expr

        defaultEvidence :: (Either [CondValue] CondValue)
        defaultEvidence = Left occVals

        defaultResult :: DsM MatchResult
        defaultResult = do
            wrapper <- (resolveConstraints m ty (Map.insert occ (defaultEvidence) knowledge) constraints)
            return $ adjustMatchResultDs wrapper $ MatchResult CanFail $ \expr -> return expr

        mkConstraintAlt :: CondValue -> DsM (CaseAlt AltCon)
        mkConstraintAlt cond@(LitCond lit) = do
            --TODO: For now fall back to regular matching when strings are involved
            mr <- getAltResult cond

            return $ MkCaseAlt
                { alt_pat = LitAlt lit
                , alt_bndrs = []
                , alt_wrapper = WpHole
                , alt_result = mr }

        mkConstraintAlt cond@(ConCond {cv_con = dcon, cv_pat = pat}) = do
            let ConPatOut { pat_con = L _ con1, pat_arg_tys = arg_tys, pat_wrap = wrapper1,
                    pat_tvs = tvs1, pat_dicts = dicts1, pat_args = args1, pat_binds = bind }
                    = pat
            --Extract constructor argument types
            let inst_tys   = arg_tys ++ mkTyVarTys tvs1
            let val_arg_tys = conLikeInstOrigArgTys con1 inst_tys
            arg_vars <- selectConMatchVars val_arg_tys args1
            wrapper <- wrapPatBinds tvs1 dicts1 pat
            mr <- getAltResult cond

            --dsPrint $ text "altCon: " <+> ppr dcon

            --return (\expr -> ((DataAlt dcon), , wrapper expr))
            return $ MkCaseAlt
                { alt_pat = DataAlt dcon
                , alt_bndrs = tvs1 ++ dicts1 ++ arg_vars
                , alt_wrapper = WpHole
                , alt_result = adjustMatchResult wrapper mr }

        mkEvalCase expr =
            Case (varToCoreExpr occ) (mkWildValBinder occType) ty [(DEFAULT, [], expr)]

    in do
        --traceM ("mkConstraint")
        --dsPrint $ text "knowledge" <+> ppr knowledge
        --dsPrint $ text "constraints" <+> ppr constraints
        df <- getDynFlags
        defBranch <- defaultResult -- :: DsM (Maybe MatchResult)
        alts <- mapM mkConstraintAlt occVals

        let result
                | null alts, MatchResult _ f <- adjustMatchResult mkEvalCase defBranch = return f
                | litConstraint =
                    let MatchResult _ f = mkCoPrimCaseMatchResult occ ty (map altToLitPair alts) $ Just defBranch
                    in return f
                | otherwise =
                    let MatchResult _ f = mkCoAlgCaseMatchResult df occ ty (map altToConAlt alts) $ Just defBranch
                    in return f
        result




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
        (\cond ->
            let info = getCondPat cond
                occ = patOcc info :: Occurrence
                evidence = fromJust $ Map.lookup occ knowledge :: Either [CondValue] CondValue
                m = case evidenceMatchesCond (Evidence occ evidence) cond of
                        Nothing -> False
                        Just False -> False
                        Just True -> True
            in
            not $ if not (Map.member occ knowledge) then False else m
        )
        constraint

knowledgeMatchesCond :: HasCallStack => DecompositionKnowledge -> Condition -> Maybe Bool
knowledgeMatchesCond knowledge condition = do
    let occ = patOcc . getCondPat $ condition
    evidence <- Map.lookup occ knowledge :: Maybe (Either [CondValue] CondValue)
    evidenceMatchesCond (Evidence occ evidence) condition

{--
    Answers the question if the given evidence satifies the given condition.
    Applying this to all knowledge tells us if we need to emit additional code
    to satisfy the conditions.

* If the eviden matching holds
* Fails
* We can't tell
-}
evidenceMatchesCond :: HasCallStack => Evidence -> Condition -> Maybe Bool
evidenceMatchesCond (Evidence eOcc eVal) cond
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
        cInfo = getCondPat cond
        cVal = getCondMatchVal cond
        cOcc = patOcc cInfo :: Occurrence

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

-- tidy1 v pat
--     | pprTrace "tidy" (showAstData NoBlankSrcSpan pat) False
--     = undefined
tidy1 v (ParPat _ pat)      = tidy1 v (unLoc pat)
tidy1 v (SigPat _ pat)    = tidy1 v (unLoc pat)
tidy1 _ (WildPat ty)      = return (idDsWrapper, WildPat ty)
tidy1 v (BangPat _ (L l p))
    | pprTrace "tidy" (showAstData NoBlankSrcSpan p) False
    = undefined
    | otherwise = tidy_bang_pat v l p

        -- case v of { x -> mr[] }
        -- = case v of { _ -> let x=v in mr[] }
tidy1 v (VarPat _ (L _ var))
  = return (wrapBind var v, WildPat (idType var))

        -- case v of { x@p -> mr[] }
        -- = case v of { p -> let x=v in mr[] }
tidy1 v (AsPat _ (L _ var) pat)
  = do  { (wrap, pat') <- tidy1 v (unLoc pat)
        ; return (wrapBind var v . wrap, pat') }

{- now, here we handle lazy patterns:
    tidy1 v ~p bs = (v, v1 = case v of p -> v1 :
                        v2 = case v of p -> v2 : ... : bs )
    where the v_i's are the binders in the pattern.
    ToDo: in "v_i = ... -> v_i", are the v_i's really the same thing?
    The case expr for v_i is just: match [v] [(p, [], \ x -> Var v_i)] any_expr
-}

tidy1 v (LazyPat _ pat)
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

tidy1 _ (ListPat (ListPatTc ty Nothing) pats )
  = return (idDsWrapper, unLoc list_ConPat)
  where
    list_ConPat = foldr (\ x y -> mkPrefixConPat consDataCon [x, y] [ty])
                        (mkNilPat ty)
                        pats

tidy1 _ (TuplePat tys pats boxity)
  = return (idDsWrapper, unLoc tuple_ConPat)
  where
    arity = length pats
    tuple_ConPat = mkPrefixConPat (tupleDataCon boxity arity) pats tys

tidy1 _ (SumPat tys pat alt arity)
  = return (idDsWrapper, unLoc sum_ConPat)
  where
    sum_ConPat = mkPrefixConPat (sumDataCon alt arity) [pat] tys

-- LitPats: we *might* be able to replace these w/ a simpler form
tidy1 _ (LitPat _ lit)
  = return (idDsWrapper, tidyLitPat lit)

-- NPats: we *might* be able to replace these w/ a simpler form
tidy1 _ (NPat ty (L _ lit) mb_neg eq)
  = return (idDsWrapper, tidyNPat lit mb_neg eq ty)

-- Everything else goes through unchanged...

tidy1 _ non_interesting_pat
  = return (idDsWrapper, non_interesting_pat)

--------------------
tidy_bang_pat :: Id -> SrcSpan -> Pat GhcTc -> DsM (DsWrapper, Pat GhcTc)

-- Discard par/sig under a bang
tidy_bang_pat v _ (ParPat _ (L l p))  = tidy_bang_pat v l p
tidy_bang_pat v _ (SigPat _ (L l p) ) = tidy_bang_pat v l p

-- Push the bang-pattern inwards, in the hope that
-- it may disappear next time
tidy_bang_pat v l (AsPat _ v' p)  = tidy1 v (AsPat NoExt v' (L l (BangPat NoExt p)))
tidy_bang_pat v l (CoPat _ w p t) = tidy1 v (CoPat NoExt w (BangPat NoExt (L l p)) t)

-- Discard bang around strict pattern
tidy_bang_pat v _ p@(LitPat {})    = tidy1 v p
tidy_bang_pat v _ p@(ListPat {})   = tidy1 v p
tidy_bang_pat v _ p@(TuplePat {})  = tidy1 v p
tidy_bang_pat v _ p@(SumPat {})    = tidy1 v p

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

tidy_bang_pat _ l p = return (idDsWrapper, BangPat NoExt (L l p))

-------------------
push_bang_into_newtype_arg :: SrcSpan
                           -> Type -- The type of the argument we are pushing
                                   -- onto
                           -> HsConPatDetails GhcTc -> HsConPatDetails GhcTc
-- See Note [Bang patterns and newtypes]
-- We are transforming   !(N p)   into   (N !p)
push_bang_into_newtype_arg l _ty (PrefixCon (arg:args))
  = ASSERT( null args)
    PrefixCon [L l (BangPat NoExt arg)]
push_bang_into_newtype_arg l _ty (RecCon rf)
  | HsRecFields { rec_flds = L lf fld : flds } <- rf
  , HsRecField { hsRecFieldArg = arg } <- fld
  = ASSERT( null flds)
    RecCon (rf { rec_flds = [L lf (fld { hsRecFieldArg = L l (BangPat NoExt arg) })] })
push_bang_into_newtype_arg l ty (RecCon rf) -- If a user writes !(T {})
  | HsRecFields { rec_flds = [] } <- rf
  = PrefixCon [L l (BangPat NoExt (noLoc (WildPat ty)))]
push_bang_into_newtype_arg _ _ cd
  = pprPanic "push_bang_into_newtype_arg" (pprConArgs cd)



--Commoning up subtrees
type VarExpr = CoreExpr
type AltCache = (TM.CoreMap VarExpr,CoreExpr -> CoreExpr)

cacheExpr :: MonadUnique m => CoreExpr -> m CoreExpr
cacheExpr expr = do
    (e,c) <- cacheAlt expr (TM.emptyTM, id)
    return (snd c $ e)

cacheAlt :: forall m. MonadUnique m => CoreExpr -> AltCache -> m (CoreExpr, AltCache)
cacheAlt e@(Case scrut b ty alts) cache@(idMap,binders)
    | null alts = return (e,cache)
    | otherwise = do
    --Cache and update child alts
    (alts,cache) <- first reverse <$> foldM goAlt ([],cache) alts


    --replaceAlts = lookupTM

    --let exprs = map goAlt alts' :: [CoreExpr]
    --ids <- replicateM (length alts') (newSysLocalDs ty)
    --let newBinders = zipWith (\id val -> bindNonRec id val) ids exprs
    --let mapping = zip exprs ids
    --let cache'' = (
    --        foldl (\tm (e,id) -> TM.insertTM e id tm) idMap mapping,
    --        foldr (.) binders newBinders)
    return (e,cache)
        where   altKey = (\a -> Case scrut b ty [a])
                goAlt :: ( [CoreAlt], AltCache) -> CoreAlt -> m ( [CoreAlt], AltCache)
                goAlt (xs,cache) (c,b,e) = do
                    --update child branches
                    (e', cache') <- cacheAlt e cache
                    --check if there is already a equivalent alt, if so use that
                    let key = (altKey (c,b,e'))
                    case TM.lookupTM key (fst cache') of
                        Nothing -> do
                            v <- mkSysLocalOrCoVarM (fsLit "ds_share_") ty :: m Id
                            let lfn = bindNonRec v e' :: CoreExpr -> CoreExpr
                            let cache'' = bimap (TM.insertTM key (Var v)) ( . lfn) cache'
                            return ((c,b,Var v):xs, cache'')
                        Just v -> do
                            return ( ((c,b,v):xs), cache')

cacheAlt e@(Var {}) cache = return (e,cache)
cacheAlt e@(Lit {}) cache = return (e,cache)
cacheAlt e@(App f arg) cache = do
    (f',cache') <- cacheAlt f cache
    (arg',cache'') <- cacheAlt arg cache'
    return (App f' arg', cache'')
cacheAlt e@(Lam {}) cache = return (e,cache) --Useful?
cacheAlt e@(Let bnd body) cache
    | Rec {} <- bnd = return (e,cache) -- TODO
    | NonRec b e <- bnd = do
        (e',cache') <- cacheAlt e cache
        (body',cache'') <- cacheAlt body cache
        return (Let (NonRec b e') body',cache'')
cacheAlt (Cast e co) cache = do
    (e', cache') <- cacheAlt e cache
    return (Cast e' co,cache')
cacheAlt (Tick t e) cache = do
    (e', cache') <- cacheAlt e cache
    return (Tick t e', cache')
cacheAlt e@(Type {}) cache = return (e,cache)
cacheAlt e@(Coercion {}) cache = return (e,cache)


shareAlts :: CoreExpr -> DsM CoreExpr
shareAlts (Case scrut b ty alts) =
    undefined
shareAlts other = return other
