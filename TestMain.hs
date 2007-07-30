module TestMain () where

import qualified RainParseTest as RP
import qualified UsageCheckTest as UC
import Test.HUnit

main :: IO ()
main = do runTestTT $ TestList [RP.tests,UC.tests]
          return ()
