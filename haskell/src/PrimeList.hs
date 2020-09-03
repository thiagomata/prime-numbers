module PrimeList
    ( infiniteFusePrimeList, infinitePrimeListUnfoldr ) where

import Multiples
import Data.List


---
--- @link https://stackoverflow.com/questions/63670787/how-to-create-a-infinite-list-in-haskell-where-the-new-value-consumes-all-the-pr?noredirect=1#comment112592628_63670787
---

-------------------------------------------------------------------------------------
-- # infinite prime list using unfoldr
-------------------------------------------------------------------------------------

nextPrimeVal xs = Just (s,xs ++ [s]) 
  where s = nextNonMultiple xs

firstPrimes = [2]
infinitePrimeListUnfoldr = firstPrimes ++ ( unfoldr nextPrimeVal firstPrimes)


-------------------------------------------------------------------------------------
-- # infinite prime list using fuse
-------------------------------------------------------------------------------------

-- calculate the current value based in the current list
-- call the same function with the new combined value
recursivePrimeList xs = [nextValue] ++ (recursivePrimeList (nextList)) where
      nextValue = nextNonMultiple(xs)
      nextList = xs ++ [nextValue]

initialPrimes = [2]
infiniteFusePrimeList =  initialPrimes ++ recursivePrimeList initialPrimes
