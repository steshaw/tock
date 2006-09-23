-- Driver for FCO

module Main where

import System
import System.Console.GetOpt

import Parse
import Tree
import SExpression
import Pass
import PhaseSource
import PhaseIntermediate
import PhaseOutput

phaseList = [phaseSource, phaseIntermediate, phaseOutput]

doPhases :: [Phase] -> Node -> IO Node
doPhases [] n = do return n
doPhases (p:ps) n = do
  n' <- runPhase p n
  n'' <- doPhases ps n'
  return n''

data Flag = ParseOnly
  deriving Eq

options :: [OptDescr Flag]
options =
  [ Option ['p'] ["parse-only"] (NoArg ParseOnly) "parse input files and output S-expression" ]

getOpts :: [String] -> IO ([Flag], [String])
getOpts argv =
  case getOpt RequireOrder options argv of
    (o,n,[]  ) -> return (o,n)
    (_,_,errs) -> error (concat errs ++ usageInfo header options)
  where header = "Usage: fco [OPTION...] SOURCEFILE"

main :: IO ()
main = do
  argv <- getArgs
  (opts, args) <- getOpts argv

  let fn = case args of
              [fn] -> fn
              _ -> error "Must specify a single input file"

  putStrLn $ "Compiling " ++ fn
  putStrLn ""

  parsed <- parseSourceFile fn
  putStrLn ""

  if ParseOnly `elem` opts
    then do
      putStrLn $ show (nodeToSExp parsed)
    else do
      putStrLn $ "Parsed: " ++ show parsed
      putStrLn ""

      out <- doPhases phaseList parsed
      putStrLn ""
      putStrLn $ "After phases: " ++ show out

