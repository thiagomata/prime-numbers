module Classic
    ( classicIsPrime, classicPrimeList) where

-------------------------------------------------------------------------------------
-- # classic prime 
-------------------------------------------------------------------------------------

-- # Classic is prime is the most trivial
-- # and not optmized function to calculate
-- # if a giving number is prime
classicIsPrimeLoop :: Integer -> Integer -> Bool
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
classicIsPrime :: Integer -> Bool
classicIsPrime n = classicIsPrimeLoop n (n-1)

-- Simple and not optimized search for the next prime
classicPrimeSearch :: Integer -> Integer
classicPrimeSearch n = if classicIsPrime n
                        then n
                        else classicPrimeSearch (n+1)

-- create a infinite list always searching for the next prime
classicIsPrimeListLoop :: Integer -> [Integer]
classicIsPrimeListLoop v = [p] ++ classicIsPrimeListLoop (p+1)
                        where p = classicPrimeSearch v

-- init the infinite list with the initial value [2]
classicPrimeList :: [Integer]
classicPrimeList = [2] ++ classicIsPrimeListLoop 3