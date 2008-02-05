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
-- * "ArrayUsageCheckTest"
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

import Control.Monad
import System.Console.GetOpt
import System.Environment
import System.IO
import Test.HUnit

import qualified ArrayUsageCheckTest (ioqcTests)
import qualified BackendPassesTest (tests)
import qualified CommonTest (tests)
import qualified FlowGraphTest (qcTests)
import qualified GenerateCTest (tests)
import qualified ParseRainTest (tests)
import qualified PassTest (tests)
import qualified RainPassesTest (tests)
import qualified RainTypesTest (tests)
import qualified RainUsageCheckTest (tests)
import TestUtils
import Utils

data TestOption =
  QC (Either String (Maybe QuickCheckLevel))
  | OutputType Bool -- True is plain, False is erasing

-- We run all the HUnit tests before all the QuickCheck tests.
-- We run them apart so that the output from QuickCheck doesn't get
-- confusing by being amongst the HUnit output,
-- and we run HUnit first because these are typically the more
-- interesting (and most worked on tests) so we see failures earlier.
main :: IO ()
main = do (opts, nonOpts, errs) <- getArgs >>* getOpt RequireOrder options
          when (not $ null errs) $ err (concat errs)
          when (not $ null nonOpts) $ err ("Options not recognised: " ++ concat nonOpts)
          qcLevel <- case findLevel opts of
                       Right level -> return level
                       Left unknownLevel -> err ("Unknown level: " ++ unknownLevel)
          let testType = case findType opts of
                           Just True -> True
                           _ -> False

          hunitTests >>= if testType
                           then liftM fst . runTestText (putTextToHandle stdout False)
                           else runTestTT
          case qcLevel of
            -- Monadic mess!
            Just level -> mapM_ (runQCTest level) =<< qcTests
            Nothing -> return ()
  where
    err msg = ioError (userError (msg ++ usageInfo header options))
    header = "Usage: tocktest [OPTION..]"
    options = [Option [] ["qc","quickcheck"]
                 (ReqArg matchLevel "LEVEL (off, low, medium, high, extensive)") "QuickCheck level"
              ,Option [] ["plain"] (NoArg (OutputType True)) "Show the test output as plain text"]
    
    findLevel :: [TestOption] -> Either String (Maybe QuickCheckLevel)
    findLevel (QC qc:_) = qc
    findLevel (_:os) = findLevel os
    findLevel [] = Right $ Just QC_Medium
    
    findType :: [TestOption] -> Maybe Bool
    findType (OutputType t:_) = Just t
    findType (_:os) = findType os
    findType [] = Nothing

    matchLevel :: String -> TestOption
    matchLevel s = QC $ case s of
                     "off" -> Right Nothing
                     "low" -> Right $ Just QC_Low
                     "medium" -> Right $ Just QC_Medium
                     "high" -> Right $ Just QC_High
                     "extensive" -> Right $ Just QC_Extensive
                     unknown -> Left unknown

    runQCTest :: QuickCheckLevel -> LabelledQuickCheckTest -> IO ()
    runQCTest level (label, test) = putStr (label ++ ": ") >> test level

    hunitTests :: IO Test
    hunitTests = sequence tests >>* (TestList . fst . unzip)
    qcTests :: IO [LabelledQuickCheckTest]
    qcTests = concatMapM (liftM snd) tests

    tests = [
              ArrayUsageCheckTest.ioqcTests
              ,noqc BackendPassesTest.tests
              ,noqc CommonTest.tests
              ,return FlowGraphTest.qcTests
              ,noqc GenerateCTest.tests
              ,noqc ParseRainTest.tests
              ,noqc PassTest.tests
              ,noqc RainPassesTest.tests
              ,noqc RainTypesTest.tests
              ,noqc RainUsageCheckTest.tests
            ]

    noqc :: Test -> IO (Test, [LabelledQuickCheckTest])
    noqc t = return (t,[])

