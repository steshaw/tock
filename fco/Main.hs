-- Driver for FCO

module Main where

import Text.ParserCombinators.Parsec

import Parse

main = do d <- getContents
          parseTest process (prepare d)


