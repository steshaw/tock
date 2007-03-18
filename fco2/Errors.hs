module Errors where

import Data.Generics
import Control.Monad.Error

import Metadata

data OccError = OccError {
    errorText :: String,
    errorPos :: Maybe OccSourcePos
  }
  deriving (Show, Eq, Typeable, Data)

type OccErrorT m a = ErrorT OccError m a

die :: Monad m => String -> m a
die s = error $ "\n\nError:\n" ++ s

dieInternal :: Monad m => String -> m a
dieInternal s = die $ "Internal error: " ++ s

dieP :: Monad m => Meta -> String -> m a
dieP m s = case findSourcePos m of
             Just (OccSourcePos f l c) -> die $ f ++ ":" ++ (show l) ++ ":" ++ (show c) ++ ": " ++ s
             Nothing -> die s

