import           Lib
import           Test.Tasty
import           Test.Tasty.HUnit
import           ClassicIsPrime

main :: IO ()
main = defaultMain test

test :: TestTree
test = testGroup "Tests" [maintests]

maintests :: TestTree
maintests = testGroup "unit tests" [testClassicPrime, testFirstMultiple]

testClassicPrime :: TestTree
testClassicPrime = testGroup
  "testClassicPrime"
  [ testCase "2 is prime" $ ClassicIsPrime 2 @?= True
  , testCase "3 is prime" $ ClassicIsPrime 3 @?= True
  , testCase "7 is prime" $ ClassicIsPrime 7 @?= True
  , testCase "8 is not prime" $ ClassicIsPrime 8 @?= False
  , testCase "1 is not prime" $ ClassicIsPrime 1 @?= False
  , testCase "0 is not prime" $ ClassicIsPrime 0 @?= False
  , testCase "-1 is not prime" $ ClassicIsPrime (-1) @?= False
  , testCase "-10 is not prime" $ ClassicIsPrime (-10) @?= False
  , testCase "117 is not prime" $ ClassicIsPrime 117 @?= False
  ]

testFirstMultiple :: TestTree
testFirstMultiple = testGroup
  "testFirstMultiple"
  [ testCase "first multiple of 2 is 1" $ (firstMultiple 2) @?= 1
  ]
