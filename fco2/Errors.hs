-- | Error handling and reporting.
module Errors where

import qualified AST as A
import Metadata

die :: String -> a
die s = error $ "\n\nError:\n" ++ s

dieInternal :: Monad m => String -> m a
dieInternal s = die $ "Internal error: " ++ s

dieP :: Monad m => Meta -> String -> m a
dieP m s = die $ show m ++ ": " ++ s

