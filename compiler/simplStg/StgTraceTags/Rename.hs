--
-- Copyright (c) 2019 Andreas Klebinger
--

{-# LANGUAGE CPP, TypeFamilies, RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs, TupleSections #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}

module StgTraceTags.Rename (rename) where

#include "HsVersions.h"

import GhcPrelude

import DataCon
import Data.Bifunctor
import Id
import StgSyn
import StgUtil
import Outputable
-- import VarEnv
import CoreSyn (AltCon(..))
-- import Data.List (mapAccumL)
import Data.Maybe (fromMaybe)

import VarSet
-- import UniqMap

import TyCon (tyConDataCons_maybe, PrimRep(..), tyConDataCons)
import Type -- (tyConAppTyCon, isUnliftedType, Type)
import Hoopl.Collections
-- import PrimOp
import UniqSupply
import StgCmmClosure (idPrimRep)
import RepType
import StgUtil

import Name
import PrelNames
-- import OccName
import SrcLoc
import FastString

import Control.Monad
-- import Data.Maybe
import qualified Data.List as L

import Unique
import UniqFM
import Util

import State
import Maybes
import Data.Foldable

import StgSubst
import VarEnv

data RenameState
    = RN
    { rm_us :: UniqSupply
    , rm_used :: InScopeSet
    , rm_subst :: Subst
    }

type RM = State RenameState

instance MonadUnique RM where
    getUniqueSupplyM = do
        s <- get
        let (us1,us2) = splitUniqSupply $ rm_us s
        put $ s {rm_us = us1}
        return us2

addUsed :: Id -> RM ()
addUsed id = do
    s <- get
    put $ s { rm_used = extendInScopeSet (rm_used s) id}

-- | Create new id and add substition
cloneId :: Id -> RM Id
cloneId id = do
    s <-  get
    let (id', subst') = substBndr id (rm_subst s)
    put $ s { rm_subst = subst'}
    return id

rename :: UniqSupply -> [StgTopBinding] -> [StgTopBinding]
rename us binds =
    let state = RN us emptyInScopeSet emptySubst
    in (flip evalState) state $ mapM renameTop binds

renameTop :: StgTopBinding -> RM StgTopBinding
renameTop str@(StgTopStringLit _v _) = return $ str
renameTop (StgTopLifted bind) = StgTopLifted <$> renameBind bind

renameBind :: StgBinding -> RM StgBinding
renameBind bind = return bind
