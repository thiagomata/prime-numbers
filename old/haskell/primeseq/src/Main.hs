{-# LANGUAGE ExistentialQuantification #-}
module Main where
import System.Environment
import System.IO
import Lib

firstPrimesProg []         =  (firstPrimes "classic" 10     )
firstPrimesProg (v:[])     =  (firstPrimes v 10             )
firstPrimesProg (v:x:xs)   =  (firstPrimes v (read x :: Int))

-- printElements :: [String] => IO ()
printElements [] = do
     putStrLn("")
     hFlush stdout 
printElements (x:xs) = putStrLn(show(x)) >> printElements xs

main :: IO ()
main = do
     args <- getArgs
     printElements((firstPrimesProg args))