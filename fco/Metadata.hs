-- Metadata types

module Metadata where

import Data.Generics

type Meta = [Metadatum]

data Metadatum =
  SourcePos String Int Int
  deriving (Show, Eq, Typeable, Data)

