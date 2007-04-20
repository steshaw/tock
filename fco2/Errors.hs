-- | Error handling and reporting.
module Errors where

import Data.Generics
import Control.Monad.Error

import qualified AST as A
import Metadata

data OccError = OccError {
    errorText :: String,
    errorPos :: Maybe OccSourcePos
  }
  deriving (Show, Eq, Typeable, Data)

type OccErrorT m a = ErrorT OccError m a

die :: String -> a
die s = error $ "\n\nError:\n" ++ s

dieInternal :: Monad m => String -> m a
dieInternal s = die $ "Internal error: " ++ s

formatPos :: Meta -> String
formatPos m
    = case findSourcePos m of
        Just o -> show o
        Nothing -> "?"

dieP :: Monad m => Meta -> String -> m a
dieP m s = die $ formatPos m ++ ": " ++ s

