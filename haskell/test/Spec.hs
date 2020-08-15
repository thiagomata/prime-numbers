import           Lib
import           Test.Tasty
import           Test.Tasty.HUnit

main :: IO ()
main = defaultMain test

test :: TestTree
test = testGroup "Tests" [maintests]

maintests :: TestTree
maintests = testGroup "unit tests" [testClassicPrime]

testClassicPrime :: TestTree
testClassicPrime = testGroup
  "testClassicPrime"
  [ testCase "2 is prime" $ classicIsPrime 2 @?= True
  , testCase "3 is prime" $ classicIsPrime 3 @?= True
  , testCase "7 is prime" $ classicIsPrime 7 @?= True
  , testCase "8 is not prime" $ classicIsPrime 8 @?= False
  , testCase "1 is not prime" $ classicIsPrime 1 @?= False
  , testCase "0 is not prime" $ classicIsPrime 0 @?= False
  , testCase "-1 is not prime" $ classicIsPrime (-1) @?= False
  , testCase "-10 is not prime" $ classicIsPrime (-10) @?= False
  , testCase "117 is not prime" $ classicIsPrime 117 @?= False
  ]
