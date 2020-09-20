module Lib
    ( firstPrimes ) where

import qualified Data.List
import qualified Classic
import qualified PrimeList
import qualified PrimeListBetter
import qualified Sequence

getPrimeList :: [Char] -> [Integer]
getPrimeList primeSearch = case primeSearch of
        "classic"       ->   Classic.classicPrimeList
        "unfoldr"       ->   PrimeList.infinitePrimeListUnfoldr
        "fuse"          ->   PrimeList.infiniteFusePrimeListInverted
        "fuse-inverted" ->   PrimeList.infiniteFusePrimeListInverted
        "fuse-better"   ->   PrimeListBetter.infiniteFusePrimeListBetter
        "sequence"      ->   Sequence.primesFromSeq
        _               ->   [-1]

firstPrimes :: [Char] -> Int -> [Integer]
firstPrimes primeSearch (-1) = (getPrimeList primeSearch)
firstPrimes primeSearch    n = (take n (getPrimeList primeSearch))
