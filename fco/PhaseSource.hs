-- Source-rewriting passes

module PhaseSource (phaseSource) where

import Tree
import Pass
import BaseTransforms
import Control.Monad.State

bases = [baseTransformOc]

phaseSource
  = (Phase "Source rewriting"
      [
        ("C-ify identifiers", makePass () cifyIdentifiers bases),
        ("Number identifiers", makePass 0 numberIdentifiers bases)
      ])

cifyIdentifiers :: Transform ()
cifyIdentifiers next top node
  = case node of
      OcName n -> return $ OcName [if c == '.' then '_' else c | c <- n]
      _ -> next node

numberIdentifiers :: Transform Int
numberIdentifiers next top node
  = case node of
      OcName n -> do
        i <- get
        put $ i + 1
        return $ OcName (n ++ "." ++ (show i))
      _ -> next node

