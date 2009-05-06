{-
Tock: a compiler for parallel languages
Copyright (C) 2007, 2008  University of Kent

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

-- | Common definitions for passes over the AST.
module Pass where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Generics (Constr, Data)
import Data.Generics.Polyplate
import Data.List
import Data.Ord
import qualified Data.Set as Set
import System.IO

import qualified AST as A
import CompState
import Errors
import Metadata
import PrettyShow
import TreeUtils
import Utils

-- | The monad in which AST-mangling passes operate.
type PassM = ErrorT ErrorReport (StateT CompState IO)

instance Die PassM where
  dieReport = throwError

instance Warn PassM where
  warnReport w@(_,t,_) = lift $ modify $
    \cs -> cs { csWarnings =
      if t `Set.member` csEnabledWarnings (csOpts cs)
        then csWarnings cs ++ [w]
        else csWarnings cs }

-- Instances for the lower half of PassM; an instance in CompState automatically
-- traverses the ErrorT to reach these:
instance CSMR (StateT CompState IO) where
  getCompState = get

instance CSM (StateT CompState IO) where
  putCompState = put
  modifyCompState = modify

-- Some instances to support StateT stuff on top of PassM, which some passes do
-- to add temporary state for that pass.  We can't just define CSM (StateT s m),
-- because that would conflict with our above instance for CSM (StateT CompState
-- IO), so instead we provide an instance for StateT that is directly on top of
-- PassM:
instance CSMR (StateT s PassM) where
  getCompState = lift getCompState

instance CSM (StateT s PassM) where
  putCompState = lift . putCompState
  modifyCompState = lift . modifyCompState

instance Die (StateT s PassM) where
  dieReport = lift . dieReport

instance Warn (StateT s PassM) where
  warnReport = lift . warnReport

instance CSMR (ReaderT r PassM) where
  getCompState = lift getCompState

instance CSM (ReaderT r PassM) where
  putCompState = lift . putCompState
  modifyCompState = lift . modifyCompState

instance Die (ReaderT r PassM) where
  dieReport = lift . dieReport

instance Warn (ReaderT r PassM) where
  warnReport = lift . warnReport

-- | The type of a pass function.
-- This is as generic as possible. Passes are used on 'A.AST' in normal use,
-- but for explicit descent and testing it's useful to be able to run them
-- against AST fragments of other types as well.
type PassType t = t -> PassM t

type PassOnOpsM ops
  = (PolyplateM t ops BaseOpM, PolyplateM t BaseOpM ops) => Pass t

type PassOnOps ops = PassOnOpsM ops

type PassASTOnOps ops
  = (PolyplateM A.AST ops BaseOpM, PolyplateM A.AST BaseOpM ops) => Pass A.AST

type PassTypeOnOps ops
  = (PolyplateM t ops BaseOpM, PolyplateM t BaseOpM ops) => PassType t

type PassOn t = PassOnOps (OneOpM t)
type PassOn2 s t = PassOnOps (TwoOpM s t)
type PassOnM2 s t = PassOnOpsM (TwoOpM s t)
type PassTypeOn t = PassTypeOnOps (OneOpM t)

-- | A description of an AST-mangling pass.
data Pass t = Pass {
    passCode :: PassType t
  , passName :: String
  , passPre :: Set.Set Property
  , passPost :: Set.Set Property
  , passEnabled :: CompOpts -> Bool
}

instance Eq (Pass t) where
  x == y = passName x == passName y

instance Ord (Pass t) where
  compare = comparing passName

-- | A property that can be asserted and tested against the AST.
data Property = Property {
    propName :: String
  , propCheck :: A.AST -> PassM ()
  }

instance Eq Property where
  x == y = propName x == propName y

instance Ord Property where
  compare = comparing propName

instance Show Property where
  show = propName

runPassM :: CompState -> PassM a -> IO (Either ErrorReport a, CompState)
runPassM cs pass
    =  flip runStateT cs $ runErrorT pass

enablePassesWhen :: (CompOpts -> Bool) -> [Pass A.AST] -> [Pass A.AST]
enablePassesWhen f
    = map (\p -> p { passEnabled = \c -> f c && (passEnabled p c) })

-- | A helper to run a pass at the top-level, or deliver an error otherwise
passOnlyOnAST :: String -> (A.AST -> PassM A.AST) -> (A.AST -> PassM A.AST)
passOnlyOnAST name = id

type PassMaker t = String -> [Property] -> [Property] -> PassType t -> Pass t

passMakerHelper :: (CompOpts -> Bool) -> PassMaker t
passMakerHelper f name pre post code
  = Pass { passCode = code
         , passName = name
         , passPre = Set.fromList pre
         , passPost = Set.fromList post
         , passEnabled = f
         }

rainOnlyPass :: PassMaker t
rainOnlyPass = passMakerHelper $ (== FrontendRain) . csFrontend

occamOnlyPass :: PassMaker t
occamOnlyPass = passMakerHelper $ (== FrontendOccam) . csFrontend

occamAndCOnlyPass :: PassMaker t
occamAndCOnlyPass = passMakerHelper $
  \st -> (csFrontend st == FrontendOccam) && (csBackend st == BackendC)

cOnlyPass :: PassMaker t
cOnlyPass = passMakerHelper $ (== BackendC) . csBackend

cppOnlyPass :: PassMaker t
cppOnlyPass = passMakerHelper $ (== BackendCPPCSP) . csBackend

cOrCppOnlyPass :: PassMaker t
cOrCppOnlyPass = passMakerHelper $ (`elem` [BackendC, BackendCPPCSP]) . csBackend

pass :: PassMaker t
pass = passMakerHelper (const True)

-- | Compose a list of passes into a single pass by running them in the order given.
runPasses :: [Pass A.AST] -> (A.AST -> PassM A.AST)
runPasses [] ast = return ast
runPasses (p:ps) ast
    =  do debug $ "{{{ " ++ passName p
          progress $ "- " ++ passName p
          ast' <- passCode p ast
          debugAST ast'
          debug $ "}}}"
          runPasses ps ast'

-- | Print a message if above the given verbosity level.
verboseMessage :: (CSMR m, MonadIO m) => Int -> String -> m ()
verboseMessage n s
    =  do ps <- getCompState
          when (csVerboseLevel (csOpts ps) >= n) $
            liftIO $ hPutStrLn stderr s

-- | Print a progress message.
progress :: (CSMR m, MonadIO m) => String -> m ()
progress = verboseMessage 1

-- | Print a debugging message.
debug :: (CSMR m, MonadIO m) => String -> m ()
debug = verboseMessage 2

-- | Print a really verbose debugging message.
veryDebug :: (CSMR m, MonadIO m) => String -> m ()
veryDebug = verboseMessage 3

-- | Dump the AST and parse state.
debugAST :: (CSMR m, MonadIO m, Data t) => t -> m ()
debugAST p
    =  do veryDebug $ "{{{ AST"
          veryDebug $ pshow p
          veryDebug $ "}}}"
          veryDebug $ "{{{ State"
          ps <- getCompState
          veryDebug $ show ps
          veryDebug $ "}}}"

-- | Transform the 'A.Only' items in a 'A.Structured'.
-- This can be used to convert one kind of 'A.Structured' into another.
transformOnly :: (Monad m, Data a, Data b) =>
               (Meta -> a -> m (A.Structured b))
               -> A.Structured a -> m (A.Structured b)
transformOnly f (A.Spec m sp s) = transformOnly f s >>* A.Spec m sp
transformOnly f (A.ProcThen m p s) = transformOnly f s >>* A.ProcThen m p
transformOnly f (A.Several m ss) = mapM (transformOnly f) ss >>* A.Several m
transformOnly f (A.Only m o) = f m o

excludeConstr :: (Data a, CSMR m) => [Constr] -> a -> m a
excludeConstr cons x 
  = if null items then return x else dieInternal (Nothing, "Excluded item still remains in source tree: " ++ (show $ head items) ++ " tree is: " ++ pshow x)
      where
        items = checkTreeForConstr cons x
