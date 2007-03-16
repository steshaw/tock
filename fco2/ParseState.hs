-- State that is kept while parsing (and compiling) occam.

module ParseState where

import Data.Generics

import qualified AST as A

data NameInfo = NameInfo {
    originalDef :: A.Name,
    mappedName :: String
  }
  deriving (Show, Eq, Typeable, Data)

data ParseState = ParseState {
    localNames :: [(String, NameInfo)],
    names :: [(String, NameInfo)],
    nameCounter :: Int
  }
  deriving (Show, Eq, Typeable, Data)

emptyState :: ParseState
emptyState = ParseState {
    localNames = [],
    names = [],
    nameCounter = 0
  }

