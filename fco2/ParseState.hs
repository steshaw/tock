-- | Compiler state.
module ParseState where

import Data.Generics
import Control.Monad.State

import qualified AST as A

-- FIXME This is a rather inappropriate name now...
-- | State necessary for compilation.
data ParseState = ParseState {
    psLocalNames :: [(String, A.Name)],
    psNames :: [(String, A.NameDef)],
    psNameCounter :: Int,
    psNonceCounter :: Int
  }
  deriving (Show, Eq, Typeable, Data)

emptyState :: ParseState
emptyState = ParseState {
    psLocalNames = [],
    psNames = [],
    psNameCounter = 0,
    psNonceCounter = 0
  }

-- | Add the definition of a name.
psDefineName :: A.Name -> A.NameDef -> ParseState -> ParseState
psDefineName n nd ps = ps { psNames = (A.nameName n, nd) : psNames ps }

-- | Find the definition of a name.
psLookupName :: ParseState -> A.Name -> Maybe A.NameDef
psLookupName ps n = lookup (A.nameName n) (psNames ps)

-- | Generate a throwaway unique name.
makeNonce :: MonadState ParseState m => m String
makeNonce
    =  do ps <- get
          let i = psNonceCounter ps
          put ps { psNonceCounter = i + 1 }
          return $ "nonce" ++ show i

