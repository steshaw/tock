-- State that is kept while parsing (and compiling) occam.

module ParseState where

import Data.Generics

import qualified AST as A

data ParseState = ParseState {
    localNames :: [(String, A.Name)],
    names :: [(String, A.Name)],
    nameCounter :: Int
  }
  deriving (Show, Eq, Typeable, Data)

emptyState :: ParseState
emptyState = ParseState {
    localNames = [],
    names = [],
    nameCounter = 0
  }

