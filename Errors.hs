-- | Error handling and reporting.
module Errors where

import qualified AST as A
import Metadata

-- | Class of monads that can fail.
class Monad m => Die m where
  -- | Fail, giving an error message.
  die :: String -> m a

  -- | Fail, giving a position and an error message.
  dieP :: Die m => Meta -> String -> m a
  dieP m s = die $ show m ++ ": " ++ s

-- | Wrapper around error that gives nicer formatting.
dieIO :: Monad m => String -> m a
dieIO s = error $ "\n\nError: " ++ s ++ "\n"

-- | Fail after an internal error.
dieInternal :: Monad m => String -> m a
dieInternal s = dieIO $ "Internal error: " ++ s

-- | Extract a value from a Maybe type, dying with the given error if it's Nothing.
checkJust :: Die m => String -> Maybe t -> m t
checkJust _ (Just v) = return v
checkJust err _ = die err
