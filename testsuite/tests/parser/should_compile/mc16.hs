{-# OPTIONS_GHC -XMonadComprehensions -XTransformListComp #-}

module Foo where

import Data.List
import GHC.Exts

foo = [ ()
      | x <- [1..10]
      , then take 5
      , then sortOn by x
      , then group by x using groupWith
      , then group using inits
      , then group by x using groupWith
      ]

