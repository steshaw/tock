-- | Driver for the compiler.
module Main where

import List
import System
import System.Console.GetOpt
import System.IO

import GenerateC
import Parse
import ParseState
import Pass
import PrettyShow
import SimplifyExprs
import SimplifyProcs
import Unnest

passes :: [(String, Pass)]
passes =
  [ ("Simplify expressions", simplifyExprs)
  , ("Simplify processes", simplifyProcs)
  , ("Flatten nested declarations", unnest)
  ]

type OptFunc = ParseState -> IO ParseState

options :: [OptDescr OptFunc]
options =
  [ Option [] ["parse-only"] (NoArg optParseOnly) "only parse input file"
  , Option ['v'] ["verbose"] (NoArg $ optVerboseLevel 1) "show progress information"
  , Option [] ["debug"] (NoArg $ optVerboseLevel 2) "show detailed information for debugging"
  , Option ['o'] ["output"] (ReqArg optOutput "FILE") "output file (default \"-\")"
  ]

optParseOnly :: OptFunc
optParseOnly ps = return $ ps { psParseOnly = True }

optVerboseLevel :: Int -> OptFunc
optVerboseLevel n ps = return $ ps { psVerboseLevel = max (psVerboseLevel ps) n }

optOutput :: String -> OptFunc
optOutput s ps = return $ ps { psOutputFile = s }

getOpts :: [String] -> IO ([OptFunc], [String])
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

  state0 <- foldl (>>=) (return emptyState) opts

  debugIO state0 "{{{ Preprocess"
  state0a <- loadSource fn state0
  debugIO state0a "}}}"

  debugIO state0a "{{{ Parse"
  progressIO state0a $ "Parse"
  (ast1, state1) <- parseProgram fn state0a
  debugASTIO state1 ast1
  debugIO state1 "}}}"

  if psParseOnly state1 then
      putStrLn $ show ast1
    else do
      progressIO state1 "Passes:"
      (ast2, state2) <- runPass (runPasses passes) ast1 state1

      debugIO state2 "{{{ Generate C"
      progressIO state2 "Generate C"
      c <- generateC state2 ast2
      case psOutputFile state2 of
        "-" -> putStr c
        file ->
          do progressIO state2 $ "Writing output file " ++ file
             f <- openFile file WriteMode
             hPutStr f c
             hClose f
      debugIO state2 "}}}"
      progressIO state2 "Done"

