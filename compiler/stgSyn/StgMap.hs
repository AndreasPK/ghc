{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998
-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module StgMap(
   -- * Maps over 'Stg Expressions' values, however NOT over extension points.
    StgArgMap



 ) where

import GhcPrelude

import Literal
import UniqDFM
import Unique( Unique )

import qualified Data.Map    as Map
import qualified Data.IntMap as IntMap
import Outputable
import Control.Monad( (>=>) )

import StgSyn
import TrieMap
import UniqFM
import UniqDFM
import Unique

-- We don't need determinism, switch to UniqFM later!
type IdMap = UniqDFM

data StgArgMap a = StgArgMap
    { am_var :: (IdMap a)
    , am_lit :: (LiteralMap a)
    }

instance TrieMap StgArgMap where
    type Key StgArgMap = StgArg
    emptyTM = StgArgMap emptyTM emptyTM
    lookupTM k (StgArgMap vars lits) = case k of
        StgVarArg v ->   lookupTM (getUnique v) vars
        StgLitArg lit -> lookupTM lit lits
    alterTM k f m = case k of
        StgVarArg var -> m { am_var = alterTM (getUnique var) f (am_var m) }
        StgLitArg lit -> m { am_lit = alterTM lit f (am_lit m) }
    foldTM f (StgArgMap vars lits) = foldTM f vars . foldTM f lits
    mapTM f (StgArgMap vars lits) = StgArgMap (mapTM f vars) (mapTM f lits)



data StgBindMap = StgBindMap

data StgExprMap a
    = StgExprMap
    { sm_app :: IdMap (ListMap StgArgMap a)
    , sm_lit :: LiteralMap a
    , sm_conApp :: LiteralMap a
    , sm_opApp :: LiteralMap a
    , sm_lam :: LiteralMap a
    , sm_case :: LiteralMap a
    }

emptyExprMap = StgExprMap
    { sm_app = emptyTM
    , sm_lit = emptyTM
    , sm_conApp = emptyTM
    , sm_opApp = emptyTM
    , sm_lam = emptyTM
    , sm_case = emptyTM
    }

instance TrieMap StgExprMap where
    type Key StgExprMap = StgExpr
    emptyTM = emptyExprMap
    lookupTM = lkExpr
    alterTM = undefined
    foldTM = undefined
    mapTM = undefined

lkExpr :: StgExpr -> StgExprMap a -> Maybe a
lkExpr (StgApp _ func args) m =
    (lookupTM (getUnique func) $ sm_app m) >>=
    (lookupTM args)

-- xtExpr :: StgExpr -> _ -> StgExprMap a -> StgExprMap a
-- xtExpr (StgApp _ func args) f m =
--     m { sm_app = sm_app m |> undefined }


