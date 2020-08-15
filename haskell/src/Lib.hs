module Lib
    ( someFunc, classicIsPrime
    ) where

-- # Classic is prime is the most trivial
-- # and not optmized function to calculate
-- # if a giving number is prime
classicIsPrimeLoop :: Int -> Int -> Bool
classicIsPrimeLoop _ 1 = True
classicIsPrimeLoop 1 _ = False
classicIsPrimeLoop _ 0 = False
classicIsPrimeLoop n m = if n < 0 then False else mod n m /= 0 && classicIsPrimeLoop n (m-1)
classicIsPrime n = classicIsPrimeLoop n (n-1)

firstMultipleLoop :: Int -> Int -> Int
firstMultipleLoop _ 1 = 1
firstMultipleLoop 1 _ = 1
firstMultipleLoop n m = if n < 0
                    then -1 
                    else
                        if mod n m == 0
                        then m
                        else firstMultipleLoop n (m-1)
firstMultiple n = firstMultipleLoop n (n-1)

someFunc :: IO ()
someFunc = putStrLn ("someFunc" ++ show(firstMultiple(3132)))
--someFunc = putStrLn ("someFunc" ++ show(firstMultiple(313213123123)))
