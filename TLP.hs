-- | Top-level process support.
module TLP where

import Control.Monad.Error
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
tlpInterface :: (CSM m, Die m) => m (A.Name, [TLPChannel])
tlpInterface
    =  do ps <- get
          let mainName = snd $ head $ csMainLocals ps
          st <- specTypeOfName mainName
          formals <- case st of
                       A.Proc _ _ fs _ -> return fs
                       _ -> die "Last definition is not a PROC"
          chans <- mapM tlpChannel formals
          when ((nub chans) /= chans) $ die "Channels used more than once in TLP"
          return (mainName, chans)
  where
    tlpChannel :: (CSM m, Die m) => A.Formal -> m TLPChannel
    tlpChannel (A.Formal _ (A.Chan A.Byte) n)
        =  do def <- lookupName n
              let origN = A.ndOrigName def
              case lookup origN tlpChanNames of
                Just c -> return c
                _ -> die $ "TLP formal " ++ show n ++ " has unrecognised name"
    tlpChannel (A.Formal _ _ n)
        = die $ "TLP formal " ++ show n ++ " has unrecognised type"

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

