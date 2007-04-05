-- State that is kept while parsing (and compiling) occam.

module ParseState where

import Data.Generics

import qualified AST as A

data ParseState = ParseState {
    psLocalNames :: [(String, A.Name)],
    psNames :: [(String, A.NameDef)],
    psNameCounter :: Int
  }
  deriving (Show, Eq, Typeable, Data)

emptyState :: ParseState
emptyState = ParseState {
    psLocalNames = [],
    psNames = [],
    psNameCounter = 0
  }

psLookupName :: ParseState -> A.Name -> Maybe A.NameDef
psLookupName ps n = lookup (A.nameName n) (psNames ps)

