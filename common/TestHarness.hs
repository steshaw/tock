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

{-|

This TestHarness module contains helper functions that deal with a file of the following format.

There is an initial prologue, assumed to be source code.  Any lines beginning with "%%" are deemed
to be destinations for substitution.  The prologue is terminated by the first test.

Each test has a starting line that begins with a single % followed by either PASS or FAIL,
optionally followed by an * (indicating this test is a good benchmark for timing)
followed by a test name.  The lines that run to the start of the next test are the source substitution.

The file is terminated by a single percent on its own line.

-}

module TestHarness (automaticTest, automaticTimeTest) where

import Control.Monad.Error
import Control.Monad.State
import Data.List
import Data.Maybe
import System.IO
import Test.HUnit hiding (performTest)
import Text.Regex

import CompState
import ParseOccam
import Pass
import PassList
import PreprocessOccam
import TestUtils
import Utils

automaticTest :: FilePath -> IO Test
automaticTest fileName = readFile fileName >>* performTest fileName

automaticTimeTest :: (Int, Int, Int) -> FilePath -> IO [TimedTask]
automaticTimeTest scale fileName = readFile fileName >>* performTimeTest scale fileName

-- Bit of a hard-hack, until usage-checking is on by default:
defaultState :: CompState
defaultState = emptyState {csUsageChecking = True}

-- | Tests if compiling the given source gives any errors.
-- If there are errors, they are returned.  Upon success, Nothing is returned
testOccam :: String -> IO (Maybe String)
testOccam source = do result <- evalStateT (runErrorT compilation) defaultState
                      return $ case result of
                                 Left (_,err) -> Just err
                                 Right _  -> Nothing
  where
    compilation = preprocessOccamSource source >>= parseOccamProgram >>= runPasses (getPassList defaultState)

-- | Substitutes each substitution into the prologue
substitute :: String -> [(Bool, Bool, String, String)] -> [(Bool, Bool, String, String)]
substitute prologue = map (\(a,b,c,subst) -> (a,b,c,subRegex (mkRegex "%%") prologue subst))


-- | Given a file's contents, tests it
performTest :: String -> String -> Test
performTest fileName fileContents
  = case parseTestFile fileContents of
      Left err -> TestCase $ assertFailure $ "Error processing file \"" ++ fileName ++ "\": " ++ err
      Right (prologue,tests) -> TestLabel fileName $ TestList $ map performTest' (substitute prologue tests)
      
  where
    performTest' :: (Bool, Bool, String, String) -> Test
    performTest' (expPass, _, testName, testText)
      = TestCase $ 
        do result <- testOccam testText
           case result of
             Just err -> if expPass then assertFailure (testName ++ " failed with error: " ++ err) else return ()
             Nothing  -> if expPass then return () else assertFailure (testName ++ " expected to fail but passed")

performTimeTest :: (Int, Int, Int) -> String -> String -> [TimedTask]
performTimeTest scale fileName fileContents
  = case parseTestFile fileContents of
      Left err -> error $ "Error processing file \"" ++ fileName ++ "\": " ++ err
      Right (prologue,tests) -> mapMaybe performTimeTest' (substitute prologue tests)
  
  where
    performTimeTest' :: (Bool, Bool, String, String) -> Maybe TimedTask
    performTimeTest' (_, False, _, _) = Nothing
    performTimeTest' (_, True, testName, testText) = Just $ timeTask testName scale (testOccam testText >> return ())

-- | Splits a file's contents into the prologue, and subsequent testcases
parseTestFile :: String -> Either String (String, [(Bool, Bool, String, String)])
parseTestFile wholeText = seqPair (return $ unlines prologue, splitCases testcases)
  where
    allLines = lines wholeText
    (prologue, testcases) = span (\l -> ("%%" `isPrefixOf` l) || (not $ "%" `isPrefixOf` l)) allLines
    
    splitCases :: [String] -> Either String [(Bool, Bool, String, String)]
    splitCases [] = throwError "Unexpected EOF"
    splitCases (headLine:otherLines)
      | "%PASS" `isPrefixOf` headLine = joinM (True, hasStar, testTitle, unlines testCaseLines) (splitCases furtherLines) 
      | "%FAIL" `isPrefixOf` headLine = joinM (False, hasStar, testTitle, unlines testCaseLines) (splitCases furtherLines)
      | "%" == headLine               = return []
      | otherwise = throwError $ "Unexpected format in testcase-header line: \"" ++ headLine ++ "\""
        where
          (hasStar, testTitle) = if headLine !! 5 == '*' then (True, drop 6 headLine) else (False, drop 5 headLine)
        
          (testCaseLines, furtherLines) = span (not . isPrefixOf "%") otherLines
    
    joinM :: Monad m => a -> m [a] -> m [a]
    joinM x mxs = mxs >>* (x :)
