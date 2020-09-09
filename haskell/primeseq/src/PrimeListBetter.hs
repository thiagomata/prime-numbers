module PrimeListBetter
    ( infiniteFusePrimeListBetter ) where

import MultiplesBetter
import Data.List



-------------------------------------------------------------------------------------
-- # infinite prime list using fuse
-------------------------------------------------------------------------------------

-- calculate the current value based in the current list
-- call the same function with the new combined value
recursivePrimeList xs = [nextValue] ++ (recursivePrimeList (nextList)) where
      nextValue = nextNonMultipleBetter(xs)
      nextList = xs ++ [nextValue]

initialPrimes = [2]
infiniteFusePrimeListBetter =  initialPrimes ++ recursivePrimeList initialPrimes


