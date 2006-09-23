-- Driver for FCO

module Main where

import List
import System
import System.Console.GetOpt
import System.IO

import Parse
import Tree
import SExpression
import Pass
import PhaseSource
import PhaseIntermediate
import PhaseOutput

phaseList = [phaseSource, phaseIntermediate, phaseOutput]

doPhases :: [Phase] -> Node -> Progress -> IO Node
doPhases [] n progress = do return n
doPhases (p:ps) n progress = do
  n' <- runPhase p n progress
  n'' <- doPhases ps n' progress
  return n''

data Flag = ParseOnly | SOccamOnly | Verbose
  deriving (Eq, Show)

options :: [OptDescr Flag]
options =
  [ Option [] ["parse-tree"] (NoArg ParseOnly) "parse input files and output S-expression parse tree"
  , Option [] ["soccam"] (NoArg SOccamOnly) "parse input files and output soccam"
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

  preprocessed <- readSource fn
  progress $ "Preprocessed: "
  progress $ numberedListing preprocessed
  progress $ ""

  let parsed = parseSource preprocessed

  if ParseOnly `elem` opts then do
      putStrLn $ show (nodeToSExp parsed)
    else if SOccamOnly `elem` opts then do
      putStrLn $ show (nodeToSOccam parsed)
    else do
      progress $ "Parsed: " ++ show parsed
      progress ""

      out <- doPhases phaseList parsed progress
      progress ""
      progress $ "After phases: " ++ show out

