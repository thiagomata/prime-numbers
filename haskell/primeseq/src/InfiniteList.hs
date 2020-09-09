module InfiniteList
    ( infiniteFuseAccList ) where

-- calculate the current value based in the current list
-- call the same function with the new combined value
recursiveList :: [a] -> ([a] -> a) -> [a]
recursiveList xs nextFromList = [nextValue] ++ (recursiveList nextList nextFromList) where
      nextValue = nextFromList(xs)
--      nextList = xs ++ [nextValue]
      nextList =  [nextValue] ++ xs

-- define the infinite list based in the initial values and in the function that
-- receiving all the previous values should define the new value
infiniteFuseAccList :: [a] -> ([a] -> a) -> [a]
infiniteFuseAccList initialValues nextFromList =  initialValues ++ recursiveList initialValues nextFromList