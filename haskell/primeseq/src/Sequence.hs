module Sequence
    ( 
        Sequence.itake, 
        Sequence.sequenceLoop, 
        Seq(..), 
        Sequence.firstSequence, 
        Sequence.rotateList, 
        Sequence.next, 
        Sequence.preview,
        Sequence.infinitePreview,
        Sequence.getNextSequence,
        Sequence.infiniteSequences,
        Sequence.seqTo,
        Sequence.seqToLoop
    ) where

imod :: Integer -> Integer -> Integer
imod a b = a - b * ( a `div` b )

itake :: Integer -> [Integer] -> [Integer]
itake 0 xs = []
itake _ [] = []
itake n (x:xs) = [x] ++ itake (n - 1) xs

untilValue [] _ = []
untilValue (x:xs) v = if x >= v then [x] else [x] ++ untilValue xs v

sequenceLoop :: [Integer] -> Integer -> Integer -> Integer -> [Integer]
sequenceLoop []       n acc l = []
sequenceLoop xs       n acc 0 = []
sequenceLoop [x]      n acc l = [x]
--sequenceLoop (x:y:xs) n acc l = [acc,x,y]
sequenceLoop (x:y:xs) n acc l = 
    if (acc+x == l ) then [x] else
    if (acc+x+y == l ) then [x+y] else
    if m == 0
    then [x+y] ++ sequenceLoop xs     n (acc+x+y) l
    else [x]   ++ sequenceLoop (y:xs) n (acc+x)   l
    where 
        m = imod (acc+x) n
        c = (acc+x+y) == l

-- getNextSequence ::  [Integer] -> Integer ->  Integer -> [Integer]
getNextSequence finiteList n next l = newFiniteSeq where
    infiniteList = cycle finiteList
    newFiniteSeq = Sequence.sequenceLoop infiniteList n next (l+next)


rotateList :: [a] -> [a]
rotateList (x:xs) = xs ++ [x]


data Seq = Seq  { values     :: [Integer]
                , steps      :: [Integer]
                , seqLength  :: Integer
                } deriving (Show)

firstSequence :: Seq
firstSequence = Seq  { values = [3,2]
                     , steps = [2]
                     , seqLength = 2
                     }

next :: Seq -> Seq
next seq = Seq { values = nextValues
               , steps = nextSteps
               , seqLength = nextSeqLength
               } where
               h = head(currentSteps)
               nextValue     = currentValue + h
               nextValues    = (nextValue:currentValues)
               nextSteps     = ( Sequence.getNextSequence rotatedSteps currentValue nextValue nextSeqLength )
               nextSeqLength = currentSeqLength * currentValue
               currentValues     = Sequence.values         seq
               currentSteps      = Sequence.steps          seq
               currentSeqLength  = Sequence.seqLength      seq
               currentValue      = head(currentValues) 
               rotatedSteps      = Sequence.rotateList currentSteps



previewLoop :: Integer -> [Integer] ->  Integer -> [Integer]
previewLoop 0 _ _ = []  
previewLoop count (x:xs) acc = [acc + x] ++ previewLoop (count - 1) xs (acc + x)

infinitePreviewLoop :: [Integer] ->  Integer -> [Integer]
infinitePreviewLoop (x:xs) acc = [acc + x] ++ infinitePreviewLoop xs (acc + x)

preview :: Seq -> Integer -> [Integer]
preview seq count = reverse(currentValues) ++ previewLoop count (cycle currentSteps) acc where
        currentSteps      = Sequence.steps    seq
        currentValues     = Sequence.values   seq 
        currentValue      = head(currentValues)
        acc = currentValue


infinitePreview :: Seq -> [Integer]
infinitePreview seq  = reverse(currentValues) ++ infinitePreviewLoop (cycle currentSteps) acc where
        currentSteps      = Sequence.steps          seq
        currentValues     = Sequence.values         seq 
        currentValue      = head(currentValues)
        acc = currentValue


infiniteSequencesLoop seq = [n] ++ infiniteSequencesLoop(n) where n = Sequence.next( seq )

infiniteSequences = [Sequence.firstSequence] ++ infiniteSequencesLoop( Sequence.firstSequence )
-- # s3 = Sequence.sequence (rotateList s2) 5

seqToLoop :: Seq -> Integer -> Seq
seqToLoop seq n = if currentSquared >= n
                  then seq
                  else seqToLoop nextSequence n where
                  current = head(Sequence.values seq)
                  currentSquared = current * current
                  nextSequence = Sequence.next seq

seqTo n = untilValue ( Sequence.infinitePreview ( seqToLoop seq n )) n where seq = Sequence.firstSequence