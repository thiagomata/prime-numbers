module Lib
    ( firstPrimes ) where

import Data.List
import Classic
import PrimeList


firstPrimes :: Int -> [Integer]
firstPrimes (-1) = infiniteFusePrimeList
firstPrimes n = (take n infiniteFusePrimeList)
