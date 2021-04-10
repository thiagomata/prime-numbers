{-# LANGUAGE ExistentialQuantification #-}
module Lib
    ( firstPrimes ) where

import qualified Data.List
import qualified Classic
import qualified PrimeList
import qualified PrimeListBetter
import qualified Sequence
import qualified Print


getPrimeList :: [Char] -> [String]
getPrimeList command = case command of
        "classic"       ->   [ show(v) | v <- Classic.classicPrimeList ]
        "unfoldr"       ->   [ show(v) | v <- PrimeList.infinitePrimeListUnfoldr ]
        "fuse"          ->   [ show(v) | v <- PrimeList.infiniteFusePrimeList ]
        "fuse-inverted" ->   [ show(v) | v <- PrimeList.infiniteFusePrimeListInverted ]
        "fuse-better"   ->   [ show(v) | v <- PrimeListBetter.infiniteFusePrimeListBetter ]
        "sequence"      ->   [ show(v) | v <- Sequence.primesFromSeq ]
        "seq-length"    ->   [ show(Sequence.ilength (Sequence.steps s)) | s <- (Sequence.infiniteSequences )]
        "seq-length2"   ->   [ show(v) | v <- PrimeListBetter.infiniteSequenceSum ]
        "seq-sum"       ->   [ show(Sequence.seqLength s) | s <- (Sequence.infiniteSequences )]
        "seq-sum2"      ->   [ show(v) | v <- PrimeListBetter.infiniteSequenceSum ]
        "seq-steps"     ->   [ show(Sequence.steps s) | s <- (Sequence.infiniteSequences )]
        "seq-steps-bounds"   ->   [ show([minimum(Sequence.steps s), maximum(Sequence.steps s)]) | s <- (Sequence.infiniteSequences )]
        "matrix"        ->   [ show(take 10000 (cycle(Sequence.steps s))) | s <- (Sequence.infiniteSequences )]
        "matrix-shift"  ->   [ show(take 10000 (replicate (length(Sequence.values s)) 0 ++ cycle(Sequence.steps s))) | s <- (Sequence.infiniteSequences )]
--------------------------        
        "prop-classic"        -> [ show(v) | v <- PrimeListBetter.infiniteSequenceProportion ]
        "prop-unfoldr"        -> [ show(v) | v <- PrimeListBetter.sequenceProportionBetter PrimeList.infinitePrimeListUnfoldr 1 ]
        "prop-fuse"           -> [ show(v) | v <- PrimeListBetter.sequenceProportionBetter PrimeList.infiniteFusePrimeList 1 ]
        "prop-fuse-inverted"  -> [ show(v) | v <- PrimeListBetter.sequenceProportionBetter PrimeList.infiniteFusePrimeListInverted 1 ]
        "prop-better"         -> [ show(v) | v <- PrimeListBetter.sequenceProportionBetter PrimeListBetter.infiniteFusePrimeListBetter 1 ]
        "prop-sequence"       -> [ show(v) | v <- PrimeListBetter.sequenceProportionBetter Sequence.primesFromSeq 1 ]
--------------------------
getPrimeList  _  =   [ show(-1) ]

firstPrimes :: [Char] -> Int -> [String]
firstPrimes primeSearch (-1) = (getPrimeList primeSearch)
firstPrimes primeSearch    n = (take n (getPrimeList primeSearch))
