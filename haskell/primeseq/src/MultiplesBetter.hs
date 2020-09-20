module MultiplesBetter
    ( firstMultipleBetter, nextNonMultipleBetter ) where

-------------------------------------------------------------------------------------
-- # first multiple
-------------------------------------------------------------------------------------

isqrt :: Integer-> Integer
isqrt n = toInteger( floor (sqrt (fromIntegral n) :: Double) )

firstMultipleLoopBetter :: Integer -> Integer -> Integer
-- # any number is multiple of 1
firstMultipleLoopBetter _ 1 = 1
-- # 1 is multiple of any number
firstMultipleLoopBetter 1 _ = 1
-- # check negative values or zero values and return -1 as error
-- # check if the number n is multiple by the current previous value
-- # and also to the value before that
firstMultipleLoopBetter n m
    | n < 1           = -1
    | mod n m == 0    = m
    | otherwise       = firstMultipleLoopBetter n (m-1)

-- # get the first biggest multiple from a number n
-- # call the loop check from n-1 until 1
firstMultipleBetter :: Integer -> Integer
firstMultipleBetter n = firstMultipleLoopBetter n (isqrt(n))

-------------------------------------------------------------------------------------
-- # next non multiple
-------------------------------------------------------------------------------------
-- Receiving a list of values
-- receive the sqrt of the value ( any value bigger than the sqrt is not multiple )
-- returns the next bigger number that is not multiple of any ofthe values 
-- in the list

isMultipleByListBetter :: Integer -> Integer -> [Integer] -> Bool
isMultipleByListBetter _ _ [] = False
isMultipleByListBetter v s (x:xs) = if v == x then True
    else if x > s then False
    else if mod v x == 0 then True
    else (isMultipleByListBetter v s xs)
 
nextNonMultipleLoopBetter :: Integer -> Integer -> [Integer] -> Integer
nextNonMultipleLoopBetter step v xs = if not (isMultipleByListBetter v (isqrt v) xs)
                        then v
                        else nextNonMultipleLoopBetter step (v + step) xs

nextNonMultipleBetter :: [Integer] -> Integer
nextNonMultipleBetter xs  = if xs == [2]
                        -- simple optimization in the search
                        -- before 2 search one by one
                        -- after 2 search two by two
                        then nextNonMultipleLoopBetter 1 (1 + maximum xs) xs
                        else nextNonMultipleLoopBetter 2 (2 + maximum xs) xs


