module Main where
import System.Environment

import Lib

firstPrimesProg [] = (firstPrimes 10)
firstPrimesProg (x:_) =  (firstPrimes (read x :: Int))

-- printElements :: [Integer] => IO ()
printElements [] = putStrLn("")
printElements (x:xs) = putStrLn(show(x)) >> printElements xs

-- main :: IO ()
main = do
     args <- getArgs
     printElements((firstPrimesProg args))