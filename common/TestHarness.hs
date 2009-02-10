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
to be destinations for substitution.  You can label different substitutions by
following the double-percent with other characters (but not PASS or FAIL), e.g. %%2.
The prologue is terminated by the first test.

Each test has a starting line that begins with a single % followed by either PASS or FAIL,
followed by a test name.  The lines that run to the start of the next test, or
to the next line beginning with a percent are the source substitution.  If you have
two or more substitution destinations (e.g. %% and %%2), you substitute them with

%PASS
First substitution
%2
Second substitution

i.e. using the label after your percent.

The file is terminated by a single percent on its own line.

-}

module TestHarness (automaticTest) where

import Control.Monad.Error
import Control.Monad.Writer
import Data.List
import Data.Maybe
import System.IO
import Test.HUnit hiding (performTest)

import CompState
import Metadata
import ParseOccam
import ParseRain
import Pass
import PassList
import PreprocessOccam
import Utils

data TestLine = Line String | Sub String {- without percents -}
data TestBody = TestBody Bool String [(String {- substName -}, [String] {- content -})]

data AutoTest = AutoTest
  { prologueLines :: [TestLine]
  , bodies :: [TestBody]
  }

automaticTest :: CompFrontend -> Int -> FilePath -> IO Test
automaticTest fr verb fileName = readFile fileName >>* performTest fr verb fileName

defaultState :: CompFrontend -> Int -> CompState
defaultState fr v = emptyState {csVerboseLevel = v, csFrontend = fr}

-- | Tests if compiling the given source gives any errors.
-- If there are errors, they are returned.  Upon success, Nothing is returned
testOccam :: Int -> String -> IO (Maybe (Maybe Meta, String))
testOccam v source = do (result,_) <- runPassM (defaultState FrontendOccam v) compilation
                        return $ case result of
                                 Left err -> Just err
                                 Right _  -> Nothing
  where
    compilation = preprocessOccamSource source
                  >>= parseOccamProgram
                  >>= runPasses (getPassList $ defaultState FrontendOccam v)

testRain :: Int -> String -> IO (Maybe (Maybe Meta, String))
testRain v source = do (result,_) <- runPassM (defaultState FrontendRain v) compilation
                       return $ case result of
                                 Left err -> Just err
                                 Right _  -> Nothing
  where
    compilation = parseRainProgram "<test>" source
                  >>= runPasses (getPassList $ defaultState FrontendRain v)

-- | Substitutes each substitution into the prologue
substitute :: AutoTest -> Either String [(Bool, String, String)]
substitute t = sequence [ do ls <- execWriterT $ subst n (prologueLines t, ss)
                             return (p, n, unlines ls)
                        | TestBody p n ss <- bodies t]
  where
    subst :: String -> ([TestLine], [(String, [String])]) -> WriterT [String] (Either String) ()
    subst _ ([], []) = return ()
    subst n ([], subs) = throwError $ "Left over substitutions: " ++ show subs
      ++ " in " ++ n
    subst n (Line l : ls, subs) = tell [l] >> subst n (ls, subs)
    subst n (Sub s : ls, subs)
      = case lookup s subs of
          Just subLines -> tell subLines >> subst n (ls, filter ((/= s) . fst) subs)
          Nothing -> throwError $ "Could not find substitution \"" ++ s
            ++ "\" in test: " ++ n


-- | Given a file's contents, tests it
performTest :: CompFrontend -> Int -> String -> String -> Test
performTest fr v fileName fileContents
  = case parseTestFile fileContents of
      Left err -> TestCase $ assertFailure $ "Error processing file \"" ++ fileName ++ "\": " ++ err
      Right test -> TestLabel fileName $ TestList $
        either
          (singleton . TestCase . assertFailure . (fileName ++))
          (map performTest')
       (substitute test)
  where
    performTest' :: (Bool, String, String) -> Test
    performTest' (expPass, testName, testText)
      = TestCase $ 
        do result <- (if fr == FrontendOccam then testOccam else testRain) v testText
           case result of
             Just err -> if expPass then assertFailure (testName ++ " failed with error: " ++ show err) else return ()
             Nothing  -> if expPass then return () else assertFailure (testName ++ " expected to fail but passed")

-- | Splits a file's contents into the prologue, and subsequent testcases
parseTestFile :: String -> Either String AutoTest
parseTestFile wholeText = liftM2 AutoTest parsePrologue (splitCases testcases)
  where
    allLines = lines wholeText
    (prologue, testcases) = span (\l -> ("%%" `isPrefixOf` l) || (not $ "%" `isPrefixOf` l)) allLines

    parsePrologue :: Either String [TestLine]
    parsePrologue = if nub subs == subs then return parsed else
      throwError "Multiple substitutions with the same name"
      where
        subs = [s | Sub s <- parsed]
        
        parsed = [ if "%%" `isPrefixOf` l
                     then Sub $ drop 2 l
                     else Line l
                 | l <- prologue ]
    
    splitCases :: [String] -> Either String [TestBody]
    splitCases [] = throwError "Unexpected EOF"
    splitCases (headLine:otherLines)
      | "%PASS" `isPrefixOf` headLine
        = (TestBody True testTitle $ foldl testCaseSubs [("",[])] testCaseLines)
            `joinM` (splitCases furtherLines) 
      | "%FAIL" `isPrefixOf` headLine
        = (TestBody False testTitle $ foldl testCaseSubs [("",[])] testCaseLines)
            `joinM` (splitCases furtherLines)
      | "%" == headLine = return []
      | otherwise = throwError $ "Unexpected format in testcase-header line: \"" ++ headLine ++ "\""
        where
          testTitle = drop 5 headLine
        
          (testCaseLines, furtherLines) = span (\x -> not $ "%PASS" `isPrefixOf`
            x || "%FAIL" `isPrefixOf` x || "%" == x) otherLines

          testCaseSubs :: [(String, [String])] -> String -> [(String, [String])]
          testCaseSubs acc ('%':id) = (id, []) : acc -- start new subst
          testCaseSubs ((aName, aSubst):as) l = (aName,aSubst++[l]) : as -- join to current
          
    
    joinM :: Monad m => a -> m [a] -> m [a]
    joinM x mxs = mxs >>* (x :)
