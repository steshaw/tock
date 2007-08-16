module TestMain () where

import qualified RainParseTest (tests)
import qualified RainPassTest (tests)
import qualified UsageCheckTest (tests)
import Test.HUnit

main :: IO ()
main = do runTestTT $ TestList [RainParseTest.tests,RainPassTest.tests,UsageCheckTest.tests]
          return ()
