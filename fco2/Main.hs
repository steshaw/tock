-- | Driver for the compiler.
module Main where

import List
import System
import System.Console.GetOpt
import System.IO

import Pass
import PrettyShow
import Parse
import SimplifyExprs
import Unnest
import GenerateC

passes :: [(String, Pass)]
passes =
  [ ("Simplify expressions", simplifyExprs)
  , ("Flatten nested declarations", unnest)
  ]

data Flag = ParseOnly | Verbose
  deriving (Eq, Show)

options :: [OptDescr Flag]
options =
  [ Option [] ["parse-only"] (NoArg ParseOnly) "only parse input file"
  , Option ['v'] ["verbose"] (NoArg Verbose) "show more detail about what's going on"
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

  let progress = if Verbose `elem` opts then hPutStrLn stderr else (\s -> return ())

  progress $ "Options: " ++ (show opts)
  progress $ "Compiling " ++ fn
  progress ""

  progress "{{{ Preprocessor"
  preprocessed <- readSource fn
  progress $ numberedListing preprocessed
  progress "}}}"

  progress "{{{ Parser"
  (ast, state) <- parseSource preprocessed fn
  progress $ pshow ast
  progress $ pshow state
  progress "}}}"

  if ParseOnly `elem` opts then
      putStrLn $ show ast
    else do
      (ast', state') <- runPass (runPasses passes) ast state

      progress "{{{ Generate C"
      c <- generateC state' ast'
      putStr c
      progress "}}}"
      progress "Done"

