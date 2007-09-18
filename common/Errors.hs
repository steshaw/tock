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

-- | Error handling and reporting.
module Errors where

import Control.Monad.Error
import Control.Monad.Trans

import qualified AST as A
import Metadata

type ErrorReport = (Maybe Meta, String)

instance Error ErrorReport where
  strMsg s = (Nothing, s)

-- | Class of monads that can fail.
class Monad m => Die m where
  dieReport :: ErrorReport -> m a

  -- | Fail, giving an error message.
  die :: String -> m a
  die s = dieReport (Nothing, s)

  -- | Fail, giving a position and an error message.
  dieP :: Die m => Meta -> String -> m a
  dieP m s = dieReport (Just m,s)

-- | Wrapper around error that gives nicer formatting.
dieIO :: (Monad m, MonadIO m) => ErrorReport -> m a
dieIO (_,s) = error $ "\n\nError: " ++ s ++ "\n"

-- | Fail after an internal error.
dieInternal :: Monad m => ErrorReport -> m a
dieInternal (m,s) = error $ "\n\n" ++ (maybe "" show m) ++ "Internal error: " ++ s

-- | Extract a value from a Maybe type, dying with the given error if it's Nothing.
checkJust :: Die m => String -> Maybe t -> m t
checkJust _ (Just v) = return v
checkJust err _ = die err
