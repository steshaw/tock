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

