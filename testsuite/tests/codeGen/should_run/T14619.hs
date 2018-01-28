{-# OPTIONS_GHC -O1 #-}

module Main (main) where

--The original code used regular sqrt which on 8.2 generated a c call
--behind the scenes. The immitate this behaviour on 8.4+ we force a
--call to a C function instead.

import Prelude hiding((*>), (<*))
import Foreign.C
import Unsafe.Coerce

foreign import ccall unsafe "sqrt" call_sqrt :: CDouble -> CDouble

type V3 = (Double, Double, Double)

absf :: V3 -> V3 -> Double
absf (x, y, z) (x', y', z') = x*x' +y*y'+z*z'


{-# NOINLINE sphereIntersection #-}
sphereIntersection :: V3 -> V3 -> (V3)
sphereIntersection orig dir@(_, _, dirz)
  | b < 0  = undefined
  | t1   > 0  = dir
  | t1   < 0  = orig
  | otherwise = undefined
    where b  = orig `absf` dir
          sqrtDisc = unsafeCoerce call_sqrt $ CDouble b
          t1 = b - sqrtDisc

main = print $ sphereIntersection (11, 22, 33) (44, 55, 66)
