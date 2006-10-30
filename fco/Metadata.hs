-- Metadata types

module Metadata where

import Data.Generics
import Data.List

type Meta = [Metadatum]

data Metadatum =
  SourcePos String Int Int
  deriving (Show, Eq, Typeable, Data)

findSourcePos :: Meta -> Maybe Metadatum
findSourcePos ms = find (\x -> case x of SourcePos _ _ _ -> True
                                         otherwise -> False) ms

formatSourcePos :: Meta -> String
formatSourcePos m = case findSourcePos m of
                      Just (SourcePos f l c) -> "<@" ++ show l ++ ":" ++ show c ++ ">"
                      Nothing -> "<?>"

die :: Monad m => String -> m a
die s = error $ "error: " ++ s

dieP :: Monad m => Meta -> String -> m a
dieP m s = case findSourcePos m of
             Just (SourcePos f l c) -> die $ f ++ ":" ++ (show l) ++ ":" ++ (show c) ++ ": " ++ s
             Nothing -> die $ "unknown position: " ++ s

