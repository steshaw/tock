-- | Compiler state.
module ParseState where

import Data.Generics
import Control.Monad.State

import qualified AST as A
import Metadata

-- FIXME This is a rather inappropriate name now...
-- | State necessary for compilation.
data ParseState = ParseState {
    psLocalNames :: [(String, A.Name)],
    psNames :: [(String, A.NameDef)],
    psNameCounter :: Int,
    psNonceCounter :: Int,
    psPulledItems :: [A.Process -> A.Process]
  }
  deriving (Show, Data, Typeable)

instance Show (A.Process -> A.Process) where
  show p = "(function on A.Process)"

emptyState :: ParseState
emptyState = ParseState {
    psLocalNames = [],
    psNames = [],
    psNameCounter = 0,
    psNonceCounter = 0,
    psPulledItems = []
  }

-- | Add the definition of a name.
psDefineName :: A.Name -> A.NameDef -> ParseState -> ParseState
psDefineName n nd ps = ps { psNames = (A.nameName n, nd) : psNames ps }

-- | Find the definition of a name.
psLookupName :: ParseState -> A.Name -> Maybe A.NameDef
psLookupName ps n = lookup (A.nameName n) (psNames ps)

-- | Generate a throwaway unique name.
makeNonce :: MonadState ParseState m => String -> m String
makeNonce s
    =  do ps <- get
          let i = psNonceCounter ps
          put ps { psNonceCounter = i + 1 }
          return $ s ++ "_n" ++ show i

-- | Add a pulled item to the collection.
addPulled :: MonadState ParseState m => (A.Process -> A.Process) -> m ()
addPulled item
    =  do ps <- get
          put $ ps { psPulledItems = item : psPulledItems ps }

-- | Apply pulled items to a Process.
applyPulled :: MonadState ParseState m => A.Process -> m A.Process
applyPulled ast
    =  do ps <- get
          let ast' = foldl (\p f -> f p) ast (psPulledItems ps)
          put $ ps { psPulledItems = [] }
          return ast'
