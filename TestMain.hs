{-
Tock: a compiler for parallel languages
Copyright (C) 2007  University of Kent

This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation, either version 2 of the License, or (at your
option) any later version.

This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License along
with this program.  If not, see <http://www.gnu.org/licenses/>.
-}

-- | A module containing the 'main' function for the Tock test suite.  It currently runs tests from the following modules:
--
-- * "BackendPassesTest"
--
-- * "CommonTest"
--
-- * "FlowGraphTest"
--
-- * "GenerateCTest"
--
-- * "ParseRainTest"
--
-- * "PassTest"
--
-- * "RainPassesTest"
--
-- * "RainTypesTest"
--
-- * "RainUsageCheckTest"
module TestMain () where

import System.Console.GetOpt
import System.Environment
import Test.HUnit

import qualified BackendPassesTest (tests)
import qualified CommonTest (tests)
import qualified FlowGraphTest (qcTests)
import qualified GenerateCTest (tests)
import qualified ParseRainTest (tests)
import qualified PassTest (tests)
import qualified RainPassesTest (tests)
import qualified RainTypesTest (tests)
import qualified RainUsageCheckTest (qcTests)
import TestUtils
import Utils

-- We run all the HUnit tests before all the QuickCheck tests.
-- We run them apart so that the output from QuickCheck doesn't get
-- confusing by being amongst the HUnit output,
-- and we run HUnit first because these are typically the more
-- interesting (and most worked on tests) so we see failures earlier.
main :: IO ()
main = do opts <- getArgs >>* getOpt RequireOrder options
          qcLevel <- case opts of
                       ([Right level], [], []) -> return level
                       ([Left unknownLevel], [], []) -> err ("Unknown level: " ++ unknownLevel)
                       (_,_,errs) -> err (concat errs)

          runTestTT hunitTests
          case qcLevel of
            Just level -> sequence_ $ applyAll level qcTests
            Nothing -> return ()
  where
    err msg = ioError (userError (msg ++ usageInfo header options))
    header = "Usage: tocktest [OPTION..]"
    options = [Option [] ["qc","quickcheck"]
                 (ReqArg matchLevel "LEVEL (off, low, medium, high, extensive)") "QuickCheck level"]

    matchLevel :: String -> Either String (Maybe QuickCheckLevel)
    matchLevel s = case s of
                     "off" -> Right Nothing
                     "low" -> Right $ Just QC_Low
                     "medium" -> Right $ Just QC_Medium
                     "high" -> Right $ Just QC_High
                     "extensive" -> Right $ Just QC_Extensive
                     unknown -> Left unknown

    hunitTests = TestList $ map fst tests
    qcTests = concatMap snd tests

    tests = [
              noqc BackendPassesTest.tests
              ,noqc CommonTest.tests
              ,FlowGraphTest.qcTests
              ,noqc GenerateCTest.tests
              ,noqc ParseRainTest.tests
              ,noqc PassTest.tests
              ,noqc RainPassesTest.tests
              ,noqc RainTypesTest.tests
              ,RainUsageCheckTest.qcTests
            ]

    noqc :: Test -> (Test, [QuickCheckTest])
    noqc t = (t,[])
