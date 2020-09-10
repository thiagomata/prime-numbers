module PrimeList
    ( infiniteFusePrimeList, infinitePrimeListUnfoldr, infiniteSumFuse, infiniteSumUnfoldr, infiniteFusePrimeListInverted ) where

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

-------------------------------------------------------------------------------------
-- # infinite prime list using fuse inverted
-------------------------------------------------------------------------------------

-- calculate the current value based in the current list
-- call the same function with the new combined value
recursivePrimeListInverted xs = [nextValue] ++ (recursivePrimeListInverted (nextList)) where
      nextValue = nextNonMultiple(xs)
      nextList = [nextValue] ++ xs

infiniteFusePrimeListInverted =  initialPrimes ++ recursivePrimeListInverted initialPrimes


-------------------------------------------------------------------------------------
-- # infinite sum list using unfoldr
-------------------------------------------------------------------------------------

nextSumVal xs = Just (s,xs ++ [s]) 
  where s = sum(xs)

firstSumValue = [1]
infiniteSumUnfoldr = firstSumValue ++ ( unfoldr nextPrimeVal firstSumValue)

-------------------------------------------------------------------------------------
-- # infinite sum of the previous using fuse
-------------------------------------------------------------------------------------

recursiveSum xs = [nextValue] ++ (recursiveSum (nextList)) where
      nextValue = sum(xs)
      nextList = xs ++ [nextValue]

initialSumValues = [1]
infiniteSumFuse =  initialPrimes ++ recursiveSum initialPrimes
