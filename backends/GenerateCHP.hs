{-
Tock: a compiler for parallel languages
Copyright (C) 2008  University of Kent

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

-- | Generate CHP code from the AST
module GenerateCHP where

import Control.Monad.Trans
import System.IO

import qualified AST as A
import Pass

generateCHP :: Handle -> A.AST -> PassM ()
generateCHP h tr = do
  liftIO $ hPutStrLn h "main :: IO ()"
  liftIO $ hPutStrLn h "main = return ()"
  genAST tr

genAST _ = return ()
