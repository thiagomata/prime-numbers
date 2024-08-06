module PrimeListBetter
    ( 
        infiniteFusePrimeListBetter,
        infiniteSequenceLen,
        infiniteSequenceSum,
        infiniteSequenceProportion,
        sequenceProportionBetter,
    ) where

import MultiplesBetter
import Data.List
import Data.Number.CReal 



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


sequenceLen :: [Integer] -> Integer -> [Integer]
sequenceLen (p:primes) previous = [currentValue] ++ (sequenceLen primes currentValue) where
        currentValue = previous * ( p - 1 )


infiniteSequenceLen = sequenceLen infiniteFusePrimeListBetter 1

sequenceSum :: [Integer] -> Integer -> [Integer]
sequenceSum (p:primes) previous = [currentValue] ++ (sequenceSum primes currentValue) where
        currentValue = previous * ( p )

infiniteSequenceSum = sequenceSum infiniteFusePrimeListBetter 1


sequenceProportion :: [Integer] -> [Integer] -> [CReal]
sequenceProportion (s:seqSum) (l:seqL) = [ fromInteger(l) / fromInteger(s) ] ++ (sequenceProportion seqSum seqL) 

infiniteSequenceProportion = sequenceProportion infiniteSequenceSum infiniteSequenceLen

sequenceProportionBetter :: [Integer] -> CReal -> [CReal]
sequenceProportionBetter (p:primes) previous = [currentValue] ++ (sequenceProportionBetter primes currentValue) where
        currentValue =  previous * fromInteger(p-1) /fromInteger(p)

-- infiniteSequenceProportionBetter = sequenceProportionBetter infiniteFusePrimeListBetter 1
