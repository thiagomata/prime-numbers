module Multiples
    ( firstMultiple, nextNonMultiple ) where

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
-- # next non multiple
-------------------------------------------------------------------------------------
-- Receiving a list of values
-- returns the next bigger number that is not multiple of any ofthe values 
-- in the list

isMultipleByList :: Integer -> [Integer] -> Bool
isMultipleByList _ [] = False
isMultipleByList v (x:xs) = if (mod v x == 0)
                        then True
                        else (isMultipleByList v xs)

nextNonMultipleLoop :: Integer -> Integer -> [Integer] -> Integer
nextNonMultipleLoop step v xs = if not (isMultipleByList v xs)
                        then v
                        else nextNonMultipleLoop step (v + step) xs

nextNonMultiple :: [Integer] -> Integer
nextNonMultiple xs  = if xs == [2]
                        -- simple optimization in the search
                        -- before 2 search one by one
                        -- after 2 search two by two
                        then nextNonMultipleLoop 1 (maximum xs) xs
                        else nextNonMultipleLoop 2 (maximum xs) xs
