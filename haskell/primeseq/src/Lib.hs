module Lib
    ( firstPrimes ) where

import Data.List
import Classic
import PrimeListBetter


firstPrimes :: Int -> [Integer]
firstPrimes (-1) = infiniteFusePrimeListBetter
firstPrimes n = (take n infiniteFusePrimeListBetter)
