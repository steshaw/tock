{-
Tock: a compiler for parallel languages
Copyright (C) 2007  University of Kent

This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation, either version 2 of the License, or (at your
option) any later version.

This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License along
with this program.  If not, see <http://www.gnu.org/licenses/>.
-}

-- | Compiler state.
module CompState where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Generics
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import qualified AST as A
import Errors (Die, dieP, ErrorReport)
import Metadata

-- | Modes that Tock can run in.
data CompMode = ModeFlowGraph | ModeParse | ModeCompile | ModePostC | ModeFull
  deriving (Show, Data, Typeable, Eq)

-- | Backends that Tock can use.
data CompBackend = BackendC | BackendCPPCSP | BackendDumpAST
  deriving (Show, Data, Typeable, Eq)

-- | Frontends that Tock can use.
data CompFrontend = FrontendOccam | FrontendRain
  deriving (Show, Data, Typeable, Eq)

-- | State necessary for compilation.
data CompState = CompState {
    -- This structure needs to be printable with pshow.
    -- There are explicit rules for the Maps and Sets used here
    -- in PrettyShow.hs; if you add any new ones here then remember
    -- to add matching rules there.

    -- Set by Main (from command-line options)
    csMode :: CompMode,
    csBackend :: CompBackend,
    csFrontend :: CompFrontend,
    csSanityCheck :: Bool,
    csUsageChecking :: Bool,
    csVerboseLevel :: Int,
    csOutputFile :: String,

    -- Set by preprocessor
    csCurrentFile :: String,
    csUsedFiles :: Set String,

    -- Set by Parse
    csLocalNames :: [(String, A.Name)],
    csMainLocals :: [(String, A.Name)],
    csNames :: Map String A.NameDef,
    csUnscopedNames :: Map String String,
    csNameCounter :: Int,
    csTypeContext :: [Maybe A.Type],

    -- Set by passes
    csNonceCounter :: Int,
    csFunctionReturns :: Map String [A.Type],
    csPulledItems :: [[PulledItem]],
    csAdditionalArgs :: Map String [A.Actual],
    csParProcs :: Set A.Name
  }
  deriving (Data, Typeable)

type PulledItem = (Meta, Either A.Specification A.Process) -- Either Spec or ProcThen

emptyState :: CompState
emptyState = CompState {
    csMode = ModeFull,
    csBackend = BackendC,
    csFrontend = FrontendOccam,
    csSanityCheck = False,
    csUsageChecking = False, -- For now!  TODO turn this on by default
    csVerboseLevel = 0,
    csOutputFile = "-",

    csCurrentFile = "none",
    csUsedFiles = Set.empty,

    csLocalNames = [],
    csMainLocals = [],
    csNames = Map.empty,
    csUnscopedNames = Map.empty,
    csNameCounter = 0,
    csTypeContext = [],

    csNonceCounter = 0,
    csFunctionReturns = Map.empty,
    csPulledItems = [],
    csAdditionalArgs = Map.empty,
    csParProcs = Set.empty
  }

-- | Class of monads which keep a CompState.
-- (This is just shorthand for the equivalent MonadState constraint.)
class (CSMR m, MonadState CompState m) => CSM m
instance (CSMR m, MonadState CompState m) => CSM m

-- | This class is like a specific instance of MonadReader.  I tried playing
-- with introducing all sorts of MonadReader classes, trying to infer it from
-- MonadState.  But due to various problems (you can't directly infer MonadReader
-- from MonadState, you can't easily stack different MonadReader instances, etc)
-- this was the easiest method to get a read-only CompState monad.
--
-- If you introduce new monads or monad transformers elsewhere in the code you
-- may have to define your own instance (see for example, ParseOccam or GenerateCBased)
class Monad m => CSMR m where
  getCompState :: m CompState

instance Monad m => CSMR (ReaderT CompState m) where
  getCompState = ask

instance Monad m => CSMR (StateT CompState m) where
  getCompState = get

instance CSMR (Reader CompState) where
  getCompState = ask

instance CSMR (State CompState) where
  getCompState = get

instance (CSMR m, Error e) => CSMR (ErrorT e m) where
  getCompState = lift getCompState

instance (CSMR m, Monoid w) => CSMR (WriterT w m) where
  getCompState = lift getCompState


--instance (MonadWriter [WarningReport] m) => Warn m where
--  warnReport r = tell [r]

--{{{  name definitions
-- | Add the definition of a name.
defineName :: CSM m => A.Name -> A.NameDef -> m ()
defineName n nd
    = modify $ (\ps -> ps { csNames = Map.insert (A.nameName n) nd (csNames ps) })

-- | Find the definition of a name.
lookupName :: (CSMR m, Die m) => A.Name -> m A.NameDef
lookupName n = lookupNameOrError n (dieP (findMeta n) $ "cannot find name " ++ A.nameName n)

lookupNameOrError :: CSMR m => A.Name -> m A.NameDef -> m A.NameDef
lookupNameOrError n err
    =  do ps <- getCompState
          case Map.lookup (A.nameName n) (csNames ps) of
            Just nd -> return nd
            Nothing -> err

--}}}

--{{{  pulled items
-- | Enter a pulled-items context.
pushPullContext :: CSM m => m ()
pushPullContext = modify (\ps -> ps { csPulledItems = [] : csPulledItems ps })

-- | Leave a pulled-items context.
popPullContext :: CSM m => m ()
popPullContext = modify (\ps -> ps { csPulledItems = tail $ csPulledItems ps })

-- | Add a pulled item to the collection.
addPulled :: CSM m => PulledItem -> m ()
addPulled item
    = modify (\ps -> case csPulledItems ps of
                       (l:ls) -> ps { csPulledItems = (item:l):ls })

-- | Do we currently have any pulled items?
havePulled :: CSMR m => m Bool
havePulled
    =  do ps <- getCompState
          case csPulledItems ps of
            ([]:_) -> return False
            _ -> return True

-- | Apply pulled items to a Structured.
applyPulled :: (CSM m, Data a) => A.Structured a -> m (A.Structured a)
applyPulled ast
    =  do ps <- get
          case csPulledItems ps of
            (l:ls) -> do put $ ps { csPulledItems = [] : ls }
                         return $ foldl (\p f -> apply f p) ast l
  where
    apply :: Data a => PulledItem -> A.Structured a -> A.Structured a
    apply (m, Left spec) = A.Spec m spec
    apply (m, Right proc) = A.ProcThen m proc

--}}}

--{{{  type contexts
-- | Enter a type context.
pushTypeContext :: CSM m => Maybe A.Type -> m ()
pushTypeContext t
    = modify (\ps -> ps { csTypeContext = t : csTypeContext ps })

-- | Leave a type context.
popTypeContext :: CSM m => m ()
popTypeContext
    = modify (\ps -> ps { csTypeContext = tail $ csTypeContext ps })

-- | Get the current type context, if there is one.
getTypeContext :: CSMR m => m (Maybe A.Type)
getTypeContext
    =  do ps <- getCompState
          case csTypeContext ps of
            (Just c):_ -> return $ Just c
            _ -> return Nothing
--}}}

--{{{ nonces
-- | Generate a throwaway unique name.
makeNonce :: CSM m => String -> m String
makeNonce s
    =  do ps <- get
          let i = csNonceCounter ps
          put ps { csNonceCounter = i + 1 }
          return $ s ++ "_n" ++ show i

-- | Generate and define a nonce specification.
defineNonce :: CSM m => Meta -> String -> A.SpecType -> A.NameType -> A.AbbrevMode -> m A.Specification
defineNonce m s st nt am
    =  do ns <- makeNonce s
          let n = A.Name m nt ns
          let nd = A.NameDef {
                     A.ndMeta = m,
                     A.ndName = ns,
                     A.ndOrigName = ns,
                     A.ndNameType = nt,
                     A.ndType = st,
                     A.ndAbbrevMode = am,
                     A.ndPlacement = A.Unplaced
                   }
          defineName n nd
          return $ A.Specification m n st

-- | Generate and define a no-arg wrapper PROC around a process.
makeNonceProc :: CSM m => Meta -> A.Process -> m A.Specification
makeNonceProc m p
    = defineNonce m "wrapper_proc" (A.Proc m A.PlainSpec [] p) A.ProcName A.Abbrev

-- | Generate and define a counter for a replicator.
makeNonceCounter :: CSM m => String -> Meta -> m A.Name
makeNonceCounter s m
    =  do (A.Specification _ n _) <- defineNonce m s (A.Declaration m A.Int Nothing) A.VariableName A.ValAbbrev
          return n

-- | Generate and define a variable abbreviation.
makeNonceIs :: CSM m => String -> Meta -> A.Type -> A.AbbrevMode -> A.Variable -> m A.Specification
makeNonceIs s m t am v
    = defineNonce m s (A.Is m am t v) A.VariableName am

-- | Generate and define an expression abbreviation.
makeNonceIsExpr :: CSM m => String -> Meta -> A.Type -> A.Expression -> m A.Specification
makeNonceIsExpr s m t e
    = defineNonce m s (A.IsExpr m A.ValAbbrev t e) A.VariableName A.ValAbbrev

-- | Generate and define a variable.
makeNonceVariable :: CSM m => String -> Meta -> A.Type -> A.NameType -> A.AbbrevMode -> m A.Specification
makeNonceVariable s m t nt am
    = defineNonce m s (A.Declaration m t Nothing) nt am
--}}}

diePC :: (CSMR m, Die m) => Meta -> m String -> m a
diePC m str = str >>= (dieP m)

--dieC :: (CSM m, Die m) => m String -> m a
--dieC str = str >>= die

throwErrorC :: (CSMR m,MonadError ErrorReport m) => (Maybe Meta,m String) -> m a
throwErrorC (m,str) = str >>= ((curry throwError) m)

findAllProcesses :: CSMR m => m [(String,A.Process)]
findAllProcesses
  = do st <- getCompState
       return $ mapMaybe findAllProcesses' (Map.assocs $ csNames st)
  where
    findAllProcesses' :: (String, A.NameDef) -> Maybe (String, A.Process)
    findAllProcesses' (n, nd)
      = case A.ndType nd of
          A.Proc _ _ _ p -> Just (n, p)
          _ -> Nothing