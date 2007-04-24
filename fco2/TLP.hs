-- | Top-level process support.
module TLP where

import Control.Monad.Error
import Control.Monad.State
import Data.Generics
import Data.List
import Data.Maybe

import qualified AST as A
import Metadata
import ParseState
import Types

data TLPChannel = TLPIn | TLPOut | TLPError
  deriving (Show, Eq, Typeable, Data)

-- | Get the name of the TLP and the channels it uses.
-- Fail if the process isn't using a valid interface.
tlpInterface :: (MonadState ParseState m, MonadError String m) => m (A.Name, [TLPChannel])
tlpInterface
    =  do ps <- get
          let mainName = snd $ head $ psMainLocals ps
          formals <- case fromJust $ specTypeOfName ps mainName of
                       A.Proc _ fs _ -> return fs
                       _ -> throwError "Last definition is not a PROC"
          chans <- mapM tlpChannel formals
          when ((nub chans) /= chans) $ throwError "Channels used more than once in TLP"
          return (mainName, chans)
  where
    tlpChannel :: (MonadState ParseState m, MonadError String m) => A.Formal -> m TLPChannel
    tlpChannel (A.Formal _ (A.Chan A.Byte) n)
        =  do ps <- get
              let origN = A.ndOrigName $ fromJust $ psLookupName ps n
              case lookup origN tlpChanNames of
                Just c -> return c
                _ -> throwError $ "TLP formal " ++ show n ++ " has unrecognised name"
    tlpChannel (A.Formal _ _ n)
        = throwError $ "TLP formal " ++ show n ++ " has unrecognised type"

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

