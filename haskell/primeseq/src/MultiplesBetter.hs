module MultiplesBetter
    ( firstMultipleBetter, nextNonMultipleBetter ) where


caseWhenLists search []          _          notFound = notFound
caseWhenLists search (v:values) (r:returns) notFound = if ( search == v )
                        then r
                        else caseWhenLists search values returns notFound


caseWhenTuples search []                  notFound = notFound
caseWhenTuples search ((value,result):xs) notFound = if ( search == value )
                        then result
                        else caseWhenTuples search xs notFound

-------------------------------------------------------------------------------------
-- # first multiple
-------------------------------------------------------------------------------------

isqrt :: Int -> Int
isqrt n = floor (sqrt (fromIntegral n) :: Double)
firstMultipleLoopBetter :: Int -> Int -> Int
-- # any number is multiple of 1
firstMultipleLoopBetter _ 1 = 1
-- # 1 is multiple of any number
firstMultipleLoopBetter 1 _ = 1
-- # check negative values or zero values and return -1 as error
-- # check if the number n is multiple by the current previous value
-- # and also to the value before that
firstMultipleLoopBetter n m = if n < 1
                    then -1 
                    else
                        if mod n m == 0
                        then m
                        else firstMultipleLoopBetter n (m-1)

-- # get the first biggest multiple from a number n
-- # call the loop check from n-1 until 1
firstMultipleBetter :: Int -> Int
firstMultipleBetter n = firstMultipleLoopBetter n (isqrt(n))

-------------------------------------------------------------------------------------
-- # next non multiple
-------------------------------------------------------------------------------------
-- Receiving a list of values
-- returns the next bigger number that is not multiple of any ofthe values 
-- in the list

isMultipleByList :: Integer -> [Integer] -> Bool
isMultipleByList _ [] = False
isMultipleByList v (x:xs) = caseWhenTuples True [
        ((v == x),          True), -- if v equals x then is Multiple
        ((v < x * x),       False),-- if v is smaller than x squared then is Not Multiple 
        ((mod v x == 0),    True)  -- if mod of v and x is zero then is Multiple 
    ] (isMultipleByList v xs)
 
nextNonMultipleLoopBetter :: Integer -> Integer -> [Integer] -> Integer
nextNonMultipleLoopBetter step v xs = if not (isMultipleByList v xs)
                        then v
                        else nextNonMultipleLoopBetter step (v + step) xs

nextNonMultipleBetter :: [Integer] -> Integer
nextNonMultipleBetter xs  = if xs == [2]
                        -- simple optimization in the search
                        -- before 2 search one by one
                        -- after 2 search two by two
                        then nextNonMultipleLoopBetter 1 (1 + maximum xs) xs
                        else nextNonMultipleLoopBetter 2 (2 + maximum xs) xs


