-- Driver for FCO

module Main where

import System

import Parse
import Tree
import Pass
import PhaseSource

doPhases :: [Phase] -> Node -> IO Node
doPhases [] n = do return n
doPhases (p:ps) n = do  n' <- runPhase p n
                        return n'

main :: IO ()
main = do args <- getArgs
          let fn = case args of
                      [fn] -> fn
                      _ -> error "Usage: fco [SOURCEFILE]"
          putStrLn $ "Compiling " ++ fn

          parsed <- parseSourceFile fn
          putStrLn $ "Parsed: " ++ show parsed

          out <- doPhases [phaseSource] parsed
          putStrLn $ "After phases: " ++ show out

