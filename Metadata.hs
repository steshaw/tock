-- | Metadata -- i.e. source position.
module Metadata where

import Data.Generics

import Utils

data Meta = Meta {
    metaFile :: Maybe String,
    metaLine :: Int,
    metaColumn :: Int
  }
  deriving (Typeable, Data)

emptyMeta :: Meta
emptyMeta = Meta {
              metaFile = Nothing,
              metaLine = 0,
              metaColumn = 0
            }

instance Show Meta where
  show m =
      case metaFile m of
        Just s -> basenamePath s ++ ":" ++ show (metaLine m) ++ ":" ++ show (metaColumn m)
        Nothing -> "no source position"

--emptyMeta is equal to any meta tag:
instance Eq Meta where
  (==) a b = 
    if ((metaFile a == Nothing) && (metaLine a == 0) && (metaColumn a == 0)) then True else
    if ((metaFile b == Nothing) && (metaLine b == 0) && (metaColumn b == 0)) then True else
    ((metaFile a == metaFile b) && (metaLine a == metaLine b) && (metaColumn a == metaColumn b))
