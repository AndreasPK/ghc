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
import qualified Data.Sequence as Seq
import Data.Sequence  as Seq ( Seq(..), (|>) )


--import Pattern.SimplePatterns
--import TL.Language
import Data.Foldable as F
import Prelude as P hiding (pred)
import Data.Bifunctor as BF
import Data.Foldable as F


type MatchId = Id   -- See Note [Match Ids]

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

type EqMatrix = PM () (CoreExpr)    













strictColumn :: PM.PatternColumn MatchId -> Bool
strictColumn = all (isStrict . fst)

strictSet :: CPM -> [Int]
--TODO: Include columns of 
strictSet m = 
    let firstRow = PM.getRow m 0 :: PM.PatternRow Occurrence
        start = Seq.findIndexL (isStrict . fst) firstRow :: Maybe Int
        columns = [0.. fromJust (PM.columnCount m) - 1] :: [Int]
        strictColumns = filter (strictColumn . PM.getCol m) columns :: [Int]
    in
    case start of
        Nothing -> []
        (Just c) -> L.nub $ c:strictColumns

rightToLeft :: Heuristic
rightToLeft m = 
    let ss = strictSet m
    in if null ss then Nothing else Just $ last ss

leftToRight :: Heuristic
leftToRight m = 
    let ss = strictSet m
    in if null ss then Nothing else Just $ head ss


-- | Is evaluation of the pattern required
isStrict :: Pat MatchId -> Bool
isStrict WildPat {} = False
isStrict ConPatOut {} = True
isStrict LitPat {} = True
isStrict NPat {} = True -- ?
isStrict NPlusKPat {} = True -- ?
isStrict _ = error "Should have been tidied already"






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