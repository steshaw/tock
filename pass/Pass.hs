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
import Control.Monad.State
import Control.Monad.Writer
import Data.Generics
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
  warnReport w = lift $ modify $
    \cs -> cs { csWarnings = csWarnings cs ++ [w] }

-- | The type of a pass function.
-- This is as generic as possible. Passes are used on 'A.AST' in normal use,
-- but for explicit descent and testing it's useful to be able to run them
-- against AST fragments of other types as well.
type PassType = (forall s. Data s => s -> PassM s)

-- | A description of an AST-mangling pass.
data Pass = Pass {
    passCode :: PassType
  , passName :: String
  , passPre :: Set.Set Property
  , passPost :: Set.Set Property
  , passEnabled :: CompState -> Bool
}

instance Eq Pass where
  x == y = passName x == passName y

instance Ord Pass where
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

enablePassesWhen :: (CompState -> Bool) -> [Pass] -> [Pass]
enablePassesWhen f
    = map (\p -> p { passEnabled = \c -> f c && (passEnabled p c) })

-- | A helper to run a pass at the top-level, or deliver an error otherwise
passOnlyOnAST :: forall t. Data t => String -> (A.AST -> PassM A.AST) -> t -> PassM t
passOnlyOnAST name func x
    = case cast x :: Maybe A.AST of
        Nothing -> dieP emptyMeta $ name ++ " only operates at top-level"
        Just x' ->
           do y <- func x'
              case cast y :: Maybe t of
                Nothing -> dieP emptyMeta $ name ++ " crazy cast error at top-level"
                Just y' -> return y'

-- For all functions of this type, do NOT use dollar before the pass.
-- That is, do not write: pass "" [] [] $ some code
-- On GHC 6.6 (without impredicative polymorphism from 6.8.1) this
-- will force the RHS (some code) to become monomorphic, where in fact
-- it needs to remain polymorphic.  So just bracket the code for the
-- pass instead, and everything will be fine
type PassMaker = String -> [Property] -> [Property] -> PassType -> Pass

passMakerHelper :: (CompState -> Bool) -> PassMaker
passMakerHelper f name pre post code
  = Pass { passCode = code
         , passName = name
         , passPre = Set.fromList pre
         , passPost = Set.fromList post
         , passEnabled = f
         }

rainOnlyPass :: PassMaker
rainOnlyPass = passMakerHelper $ (== FrontendRain) . csFrontend

occamOnlyPass :: PassMaker
occamOnlyPass = passMakerHelper $ (== FrontendOccam) . csFrontend

cOnlyPass :: PassMaker
cOnlyPass = passMakerHelper $ (== BackendC) . csBackend

cppOnlyPass :: PassMaker
cppOnlyPass = passMakerHelper $ (== BackendCPPCSP) . csBackend

pass :: PassMaker
pass = passMakerHelper (const True)

-- | Compose a list of passes into a single pass by running them in the order given.
runPasses :: [Pass] -> (A.AST -> PassM A.AST)
runPasses [] ast = return ast
runPasses (p:ps) ast
    =  do debug $ "{{{ " ++ passName p
          progress $ "- " ++ passName p
          ast' <- passCode p ast
          debugAST ast'
          debug $ "}}}"
          runPasses ps ast'

-- | Print a message if above the given verbosity level.
verboseMessage :: (CSM m, MonadIO m) => Int -> String -> m ()
verboseMessage n s
    =  do ps <- get
          when (csVerboseLevel ps >= n) $
            liftIO $ hPutStrLn stderr s

-- | Print a progress message.
progress :: (CSM m, MonadIO m) => String -> m ()
progress = verboseMessage 1

-- | Print a debugging message.
debug :: (CSM m, MonadIO m) => String -> m ()
debug = verboseMessage 2

-- | Print a really verbose debugging message.
veryDebug :: (CSM m, MonadIO m) => String -> m ()
veryDebug = verboseMessage 3

-- | Dump the AST and parse state.
debugAST :: (CSM m, MonadIO m, Data t) => t -> m ()
debugAST p
    =  do veryDebug $ "{{{ AST"
          veryDebug $ pshow p
          veryDebug $ "}}}"
          veryDebug $ "{{{ State"
          ps <- get
          veryDebug $ pshow ps
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
