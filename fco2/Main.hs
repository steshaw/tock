-- | Driver for the compiler.
module Main where

import List
import System
import System.Console.GetOpt
import System.IO

import Pass
import PrettyShow
import Parse
import ParseState
import SimplifyExprs
import SimplifyProcs
import Unnest
import GenerateC

passes :: [(String, Pass)]
passes =
  [ ("Simplify expressions", simplifyExprs)
  , ("Simplify processes", simplifyProcs)
  , ("Flatten nested declarations", unnest)
  ]

options :: [OptDescr Flag]
options =
  [ Option [] ["parse-only"] (NoArg ParseOnly) "only parse input file"
  , Option ['v'] ["verbose"] (NoArg Verbose) "show progress information"
  , Option [] ["debug"] (NoArg Debug) "show detailed information for debugging"
  ]

getOpts :: [String] -> IO ([Flag], [String])
getOpts argv =
  case getOpt RequireOrder options argv of
    (o,n,[]  ) -> return (o,n)
    (_,_,errs) -> error (concat errs ++ usageInfo header options)
  where header = "Usage: fco [OPTION...] SOURCEFILE"

numberedListing :: String -> String
numberedListing s = concat $ intersperse "\n" $ [(show n) ++ ": " ++ s | (n, s) <- zip [1..] (lines s)]

main :: IO ()
main = do
  argv <- getArgs
  (opts, args) <- getOpts argv

  let fn = case args of
              [fn] -> fn
              _ -> error "Must specify a single input file"

  let state0 = emptyState { psFlags = opts }

  progressIO state0 $ "Options: " ++ show opts
  progressIO state0 $ "Compiling " ++ fn
  progressIO state0 ""

  debugIO state0 "{{{ Preprocess"
  progressIO state0 $ "Preprocess " ++ fn
  preprocessed <- readSource fn
  debugIO state0 $ numberedListing preprocessed
  debugIO state0 "}}}"

  debugIO state0 "{{{ Parse"
  progressIO state0 $ "Parse " ++ fn
  (ast1, state1) <- parseSource preprocessed fn state0
  debugASTIO state1 ast1
  debugIO state1 "}}}"

  if ParseOnly `elem` opts then
      putStrLn $ show ast1
    else do
      progressIO state1 "Passes:"
      (ast2, state2) <- runPass (runPasses passes) ast1 state1

      debugIO state2 "{{{ Generate C"
      progressIO state2 "Generate C"
      c <- generateC state2 ast2
      putStr c
      debugIO state2 "}}}"
      progressIO state2 "Done"

