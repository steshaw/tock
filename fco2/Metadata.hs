-- Metadata types

module Metadata where

import Data.Generics
import Data.List

type Meta = [Metadatum]

data OccSourcePos = OccSourcePos String Int Int
  deriving (Show, Eq, Typeable, Data)

data Metadatum =
  MdSourcePos OccSourcePos
  deriving (Show, Eq, Typeable, Data)

findSourcePos :: Meta -> Maybe OccSourcePos
findSourcePos ms
    =  do sps <- find (\x -> case x of MdSourcePos _ -> True
                                       otherwise -> False) ms
          return $ case sps of MdSourcePos sp -> sp

formatSourcePos :: Meta -> String
formatSourcePos m = case findSourcePos m of
                      Just (OccSourcePos f l c) -> "<@" ++ show l ++ ":" ++ show c ++ ">"
                      Nothing -> "<?>"

