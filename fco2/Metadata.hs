-- | Metadata -- i.e. source position.
module Metadata where

import Data.Generics

data Meta = Meta {
    metaFile :: Maybe String,
    metaLine :: Int,
    metaColumn :: Int
  }
  deriving (Eq, Typeable, Data)

emptyMeta :: Meta
emptyMeta = Meta {
              metaFile = Nothing,
              metaLine = 0,
              metaColumn = 0
            }

instance Show Meta where
  show m =
      case metaFile m of
        Just s -> s ++ ":" ++ show (metaLine m) ++ ":" ++ show (metaColumn m)
        Nothing -> "no source position"
