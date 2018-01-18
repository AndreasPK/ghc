{-# LANGUAGE GADTs #-}

module M where

data T where
  A :: T
  {-# LIKELY 1 #-} B :: T