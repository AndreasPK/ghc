{-# LANGUAGE CPP, TypeFamilies, RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs, TupleSections #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

-- {-# LANGUAGE Strict #-}

{-# OPTIONS_GHC -O -fprof-auto #-}

module StgTraceTags.TraceUtils where

#include "HsVersions.h"

import GhcPrelude

import BasicTypes
import DataCon
import Data.Bifunctor
import Id
import StgSyn hiding (AlwaysEnter)
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

import Module
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
import qualified EnumSet as ES
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Util
import MonadUtils (whenM)
import Data.Ord (comparing)

import State
import Maybes
import Data.Foldable
import Control.Applicative hiding (empty)

import GHC.Generics
import Control.DeepSeq

import StgSubst


