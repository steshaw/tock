-- Driver for FCO

module Main where

import System

import Parse

main :: IO ()
main = do args <- getArgs
          let fn = case args of
                      [fn] -> fn
                      _ -> error "Usage: fco [SOURCEFILE]"
          putStr ("Compiling " ++ fn ++ "...\n")
          tree <- parseSourceFile fn
          putStr (show tree ++ "\n")


