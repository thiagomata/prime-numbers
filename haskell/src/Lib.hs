module Lib
    ( someFunc ) where

import Data.List
import Classic
import PrimeList


someFunc :: IO ()
someFunc = putStrLn ("someFunc" ++ show(infiniteFusePrimeList))

-- test = do
--     putStrLn ("a")
--     return (1)