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

-- | Top-level process support.
module TLP where

import Control.Monad.State
import Data.Generics
import Data.List
import Data.Maybe

import qualified AST as A
import CompState
import Errors
import Metadata
import Types

data TLPChannel = TLPIn | TLPOut | TLPError
  deriving (Show, Eq, Typeable, Data)

-- | Get the name of the TLP and the channels it uses.
-- Fail if the process isn't using a valid interface.
tlpInterface :: (CSMR m, Die m) => m ( A.Name, [(A.Direction, TLPChannel)] )
tlpInterface
    =  do ps <- getCompState
          when (null $ csMainLocals ps) (dieReport (Nothing,"No main process found"))
          let mainName = snd $ head $ csMainLocals ps
          st <- specTypeOfName mainName
          (m,formals) <- case st of
                       A.Proc m _ fs _ -> return (m,fs)
                       _ -> dieP (findMeta mainName) "Last definition is not a PROC"
          chans <- mapM (tlpChannel m) formals
          when ((nub (map snd chans)) /= (map snd chans)) $ dieP (findMeta mainName) "Channels used more than once in TLP"
          return (mainName, chans)
  where
    tlpChannel :: (CSMR m, Die m) => Meta -> A.Formal -> m (A.Direction, TLPChannel)
    tlpChannel m (A.Formal _ (A.Chan dir _ _) n)
        =  do def <- lookupName n
              let origN = A.ndOrigName def
              case lookup origN tlpChanNames of
                Just c ->
                  if (dir == A.DirUnknown || dir == (tlpDir c))
                    then return (dir,c)
                    else dieP m $ "TLP formal " ++ show n ++ " has wrong direction for its name"
                _ -> dieP m $ "TLP formal " ++ show n ++ " has unrecognised name"
    tlpChannel m (A.Formal _ _ n)
        = dieP m $ "TLP formal " ++ show n ++ " has unrecognised type"

    tlpDir :: TLPChannel -> A.Direction
    tlpDir TLPIn = A.DirInput
    tlpDir TLPOut = A.DirOutput
    tlpDir TLPError = A.DirOutput

    tlpChanNames :: [(String, TLPChannel)]
    tlpChanNames
        = [ ("in", TLPIn)
          , ("kb", TLPIn)
          , ("keyb", TLPIn)
          , ("keyboard", TLPIn)
          , ("out", TLPOut)
          , ("scr", TLPOut)
          , ("screen", TLPOut)
          , ("err", TLPError)
          , ("error", TLPError)
          ]

