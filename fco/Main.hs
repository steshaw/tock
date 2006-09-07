-- Driver for FCO

module Main where

import System

import Parse
import Tree
import Pass
import PhaseSource
import PhaseIntermediate
import PhaseOutput

phaseList = [phaseSource, phaseIntermediate, phaseOutput]

doPhases :: [Phase] -> Node -> IO Node
doPhases [] n = do return n
doPhases (p:ps) n = do  n' <- runPhase p n
                        n'' <- doPhases ps n'
                        return n''

main :: IO ()
main = do args <- getArgs
          let fn = case args of
                      [fn] -> fn
                      _ -> error "Usage: fco [SOURCEFILE]"
          putStrLn $ "Compiling " ++ fn
          putStrLn ""

          parsed <- parseSourceFile fn
          putStrLn ""

          putStrLn $ "Parsed: " ++ show parsed
          putStrLn ""

          out <- doPhases phaseList parsed
          putStrLn ""
          putStrLn $ "After phases: " ++ show out

