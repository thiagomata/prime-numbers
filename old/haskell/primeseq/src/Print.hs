module Print
    ( printElements, printFloat ) where
import System.Environment
import System.IO
import Data.Number.CReal 

printElements [] = do
     putStrLn("")
     hFlush stdout 
printElements (x:xs) = putStrLn(show(x)) >> printElements xs


printFloat [] = do
     putStrLn("")
     hFlush stdout 

printFloat (x:xs) = do
    putStrLn (showCReal 100 (x :: CReal) ) 
    hFlush stdout 
    >> printFloat xs


-- printRational :: [Rational] -> IO()
-- printRational (f:fs) = do
--     putStrLn (showCReal 100 f) 
--     hFlush stdout 
--     >> printRational fs


-- # *Lib Data.Number.CReal> [ showCReal 100 (fromInteger(toInteger(length(Sequence.steps s))) / fromInteger(sum(Sequence.steps s))) | s <- (Sequence.infiniteSequences )]
