module Lib
    ( someFunc, classicIsPrime, firstMultiple
    ) where

-------------------------------------------------------------------------------------
-- # classic prime 
-------------------------------------------------------------------------------------

-- # Classic is prime is the most trivial
-- # and not optmized function to calculate
-- # if a giving number is prime
classicIsPrimeLoop :: Int -> Int -> Bool
-- # if is multiple only by 1 is prime
classicIsPrimeLoop _ 1 = True
-- # if the value is 1 is not prime
classicIsPrimeLoop 1 _ = False
-- # no number should be checked against zero
classicIsPrimeLoop _ 0 = False
-- # we define a prime number a positive number that is
-- # is not multiple by any previous number bigger than 1
-- # using n to define the number that we are evaluating
-- # using m to define the number smaller than n
classicIsPrimeLoop n m = if n < 0 then False else mod n m /= 0 && classicIsPrimeLoop n (m-1)

-- # define the classic prime
-- # calling the loop check to all the previous number
-- # until 1
classicIsPrime :: Int -> Bool
classicIsPrime n = classicIsPrimeLoop n (n-1)

-------------------------------------------------------------------------------------
-- # first multiple
-------------------------------------------------------------------------------------

firstMultipleLoop :: Int -> Int -> Int
-- # any number is multiple of 1
firstMultipleLoop _ 1 = 1
-- # 1 is multiple of any number
firstMultipleLoop 1 _ = 1
-- # check negative values or zero values and return -1 as error
-- # check if the number n is multiple by the current previous value
-- # and also to the value before that
firstMultipleLoop n m = if n < 1
                    then -1 
                    else
                        if mod n m == 0
                        then m
                        else firstMultipleLoop n (m-1)

-- # get the first biggest multiple from a number n
-- # call the loop check from n-1 until 1
firstMultiple :: Int -> Int
firstMultiple n = firstMultipleLoop n (n-1)


-------------------------------------------------------------------------------------
-- # all primes until
-------------------------------------------------------------------------------------

isMultipleByList :: Integer -> [Integer] -> Bool
isMultipleByList _ [] = False
isMultipleByList v (x:xs) = if (mod v x == 0)
                        then True
                        else (isMultipleByList v xs)

nextNotMultipleLoop :: Integer -> Integer -> [Integer] -> Integer
nextNotMultipleLoop step v xs = if not (isMultipleByList v xs)
                        then v
                        else nextNotMultipleLoop step (v + step) xs

nextNotMultiple :: [Integer] -> Integer
-- nextNotMultiple [2] = nextNotMultipleLoop 1 (maximum xs) xs
nextNotMultiple xs  = if xs == [2]
                        then nextNotMultipleLoop 1 (maximum xs) xs
                        else nextNotMultipleLoop 2 (maximum xs) xs


addNextNotMultiple xs = xs ++ [nextNotMultiple xs] 

infinitePrimeList = [2,3] : map (addNextNotMultiple) infinitePrimeList

-- classicNextPrime :: [Integer] -> Integer
-- classicNextPrime [] = 2
-- classicNextPrime xs = xs:nextNotMultipleLoop (maximum xs) xs



someFunc :: IO ()
someFunc = putStrLn ("someFunc" ++ show(firstMultiple(3132)))

-- test = do
--     putStrLn ("a")
--     return (1)