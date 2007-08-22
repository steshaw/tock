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

import Data.Generics
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State

import qualified AST as A
import Errors
import Metadata

-- | Modes that Tock can run in.
data CompMode = ModeParse | ModeCompile | ModePostC
  deriving (Show, Data, Typeable, Eq)

-- | Backends that Tock can use.
data CompBackend = BackendC | BackendCPPCSP
  deriving (Show, Data, Typeable, Eq)

-- | Frontends that Tock can use.
data CompFrontend = FrontendOccam | FrontendRain
  deriving (Show, Data, Typeable, Eq)

-- | State necessary for compilation.
data CompState = CompState {
    -- Set by Main (from command-line options)
    csMode :: CompMode,
    csBackend :: CompBackend,
    csFrontend :: CompFrontend,
    csVerboseLevel :: Int,
    csOutputFile :: String,

    -- Set by preprocessor
    csCurrentFile :: String,
    csUsedFiles :: Set.Set String,

    -- Set by Parse
    csLocalNames :: [(String, A.Name)],
    csMainLocals :: [(String, A.Name)],
    csNames :: Map String A.NameDef,
    csUnscopedNames :: Map String String,
    csNameCounter :: Int,
    csTypeContext :: [Maybe A.Type],
    csLoadedFiles :: [String],
    csWarnings :: [String],

    -- Set by passes
    csNonceCounter :: Int,
    csFunctionReturns :: Map String [A.Type],
    csPulledItems :: [[A.Structured -> A.Structured]],
    csAdditionalArgs :: Map String [A.Actual],

    -- Set by code generators
    csGeneratedDefs :: [String]
  }
  deriving (Show, Data, Typeable)

instance Show (A.Structured -> A.Structured) where
  show p = "(function on Structured)"

emptyState :: CompState
emptyState = CompState {
    csMode = ModeCompile,
    csBackend = BackendC,
    csFrontend = FrontendOccam,
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
    csLoadedFiles = [],
    csWarnings = [],

    csNonceCounter = 0,
    csFunctionReturns = Map.empty,
    csPulledItems = [],
    csAdditionalArgs = Map.empty,

    csGeneratedDefs = []
  }

-- | Class of monads which keep a CompState.
-- (This is just shorthand for the equivalent MonadState constraint.)
class MonadState CompState m => CSM m
instance MonadState CompState m => CSM m

--{{{  name definitions
-- | Add the definition of a name.
defineName :: CSM m => A.Name -> A.NameDef -> m ()
defineName n nd
    = modify $ (\ps -> ps { csNames = Map.insert (A.nameName n) nd (csNames ps) })

-- | Find the definition of a name.
lookupName :: (CSM m, Die m) => A.Name -> m A.NameDef
lookupName n
    =  do ps <- get
          case Map.lookup (A.nameName n) (csNames ps) of
            Just nd -> return nd
            Nothing -> die $ "cannot find name " ++ A.nameName n
--}}}

--{{{  warnings
-- | Add a warning with no source position.
addPlainWarning :: CSM m => String -> m ()
addPlainWarning msg = modify (\ps -> ps { csWarnings = msg : csWarnings ps })

-- | Add a warning.
addWarning :: CSM m => Meta -> String -> m ()
addWarning m s = addPlainWarning $ "Warning: " ++ show m ++ ": " ++ s
--}}}

--{{{  pulled items
-- | Enter a pulled-items context.
pushPullContext :: CSM m => m ()
pushPullContext = modify (\ps -> ps { csPulledItems = [] : csPulledItems ps })

-- | Leave a pulled-items context.
popPullContext :: CSM m => m ()
popPullContext = modify (\ps -> ps { csPulledItems = tail $ csPulledItems ps })

-- | Add a pulled item to the collection.
addPulled :: CSM m => (A.Structured -> A.Structured) -> m ()
addPulled item
    = modify (\ps -> case csPulledItems ps of
                       (l:ls) -> ps { csPulledItems = (item:l):ls })

-- | Do we currently have any pulled items?
havePulled :: CSM m => m Bool
havePulled
    =  do ps <- get
          case csPulledItems ps of
            ([]:_) -> return False
            _ -> return True

-- | Apply pulled items to a Structured.
applyPulled :: CSM m => A.Structured -> m A.Structured
applyPulled ast
    =  do ps <- get
          case csPulledItems ps of
            (l:ls) -> do put $ ps { csPulledItems = [] : ls }
                         return $ foldl (\p f -> f p) ast l
--}}}

--{{{  generated definitions
-- | Add a generated definition to the collection.
addGeneratedDef :: CSM m => String -> m ()
addGeneratedDef s = modify (\ps -> ps { csGeneratedDefs = s : csGeneratedDefs ps })

-- | Get and clear the collection of generated definitions.
getGeneratedDefs :: CSM m => m [String]
getGeneratedDefs
    =  do ps <- get
          put $ ps { csGeneratedDefs = [] }
          return $ csGeneratedDefs ps
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
getTypeContext :: CSM m => m (Maybe A.Type)
getTypeContext
    =  do ps <- get
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
    =  do (A.Specification _ n _) <- defineNonce m s (A.Declaration m A.Int) A.VariableName A.ValAbbrev
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
    = defineNonce m s (A.Declaration m t) nt am
--}}}
