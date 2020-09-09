module Lib
    ( someFunc ) where

import Data.List
import Classic
import PrimeList


someFunc :: IO ()
-- someFunc = putStrLn ("someFunc" ++ show(take 500 infiniteFusePrimeList))
someFunc = putStrLn ("someFunc" ++ show(take 10000 infiniteSumUnfoldr))

-- test = do
--     putStrLn ("a")
--     return (1)