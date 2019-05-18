{-# LANGUAGE CPP, ScopedTypeVariables, TypeFamilies #-}

module StgUtil
    ( mkStgAltType
    , getStrictConArgs
    , getStrictConFields
    ) where

#include "HsVersions.h"

import GhcPrelude

import Id
import Type
import TyCon
import DataCon
import CoreSyn
import CoreUtils

import RepType
import StgSyn


import Util
import Outputable

-- Checks if id is a top level error application.
-- isErrorAp_maybe :: Id ->

mkStgAltType :: Id -> [(AltCon, [a], b)] -> AltType
mkStgAltType bndr alts
  | isUnboxedTupleType bndr_ty || isUnboxedSumType bndr_ty
  = MultiValAlt (length prim_reps)  -- always use MultiValAlt for unboxed tuples

  | otherwise
  = case prim_reps of
      [LiftedRep] -> case tyConAppTyCon_maybe (unwrapType bndr_ty) of
        Just tc
          | isAbstractTyCon tc -> look_for_better_tycon
          | isAlgTyCon tc      -> AlgAlt tc
          | otherwise          -> ASSERT2( _is_poly_alt_tycon tc, ppr tc )
                                  PolyAlt
        Nothing                -> PolyAlt
      [unlifted] -> PrimAlt unlifted
      not_unary  -> MultiValAlt (length not_unary)
  where
   bndr_ty   = idType bndr
   prim_reps = typePrimRep bndr_ty

   _is_poly_alt_tycon tc
        =  isFunTyCon tc
        || isPrimTyCon tc   -- "Any" is lifted but primitive
        || isFamilyTyCon tc -- Type family; e.g. Any, or arising from strict
                            -- function application where argument has a
                            -- type-family type

   -- Sometimes, the TyCon is a AbstractTyCon which may not have any
   -- constructors inside it.  Then we may get a better TyCon by
   -- grabbing the one from a constructor alternative
   -- if one exists.
   look_for_better_tycon
        | ((DataAlt con, _, _) : _) <- data_alts =
                AlgAlt (dataConTyCon con)
        | otherwise =
                ASSERT(null data_alts)
                PolyAlt
        where
                (data_alts, _deflt) = findDefault alts


-- | Given a DataCon and list of args passed to it, return the ids we expect to be strict.
-- We use this to determine which of these require evaluation
getStrictConArgs :: DataCon -> [a] -> [a]
getStrictConArgs con args =
    strictArgs
  where
    conReps = dataConRepStrictness con
    strictArgs = map snd $ filter (\(s,_v) -> isMarkedStrict s) $ zip conReps args

-- | When given a list of ids this con binds, returns the list of ids coming
-- from strict fields.
getStrictConFields :: DataCon -> [Id] -> [Id]
getStrictConFields = getStrictConArgs
-- getStrictConFields con binds =
--     strictBinds
--   where
--     conReps = dataConRepStrictness con
--     strictBinds = map snd $ filter (\(s,_v) -> isMarkedStrict s) $ zip conReps binds

