module Main where
import System.Environment

import Lib

firstPrimesProg []         =  (firstPrimes "classic" 10     )
firstPrimesProg (v:[])     =  (firstPrimes v 10             )
firstPrimesProg (v:x:xs)   =  (firstPrimes v (read x :: Int))

-- printElements :: [Integer] => IO ()
printElements [] = putStrLn("")
printElements (x:xs) = putStrLn(show(x)) >> printElements xs

-- main :: IO ()
main = do
     args <- getArgs
     printElements((firstPrimesProg args))