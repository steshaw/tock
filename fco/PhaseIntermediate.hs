-- Intermediate passes

module PhaseIntermediate (phaseIntermediate) where

import qualified Tree as N
import Pass
import BaseTransforms
import Control.Monad.State
import Data.Map as Map

bases = [baseTransformOc, baseTransformInt]

phaseIntermediate
  = (Phase "Intermediate mangling"
      [
        ("Mark declarations", makePass () markDecls bases)
--       , ("Unique identifiers", makePass (0, Map.empty) uniqueIdentifiers bases)
      ])

nestDecls :: [(N.Node, N.Node)] -> N.Node -> N.Node
nestDecls l n = foldl (\a b -> b a) n [N.IntDecl n d | (N.Name n, d) <- l]

markDecls :: Transform ()
markDecls next top node
  = case node of
      -- FIXME same for functions
      N.Decl d body -> do
        body' <- top body
        return $ case d of
          N.Vars t ns -> nestDecls [(n, t) | n <- ns] body'
          N.Is (N.Name n) _ -> N.IntDecl n d body'
          N.IsType (N.Name n) _ _ -> N.IntDecl n d body'
          N.ValIs (N.Name n) _ -> N.IntDecl n d body'
          N.ValIsType (N.Name n) _ _ -> N.IntDecl n d body'
          N.DataType (N.Name n) _ -> N.IntDecl n d body'
          N.Protocol (N.Name n) _ -> N.IntDecl n d body'
          N.FuncIs (N.Name n) _ _ _ -> N.IntDecl n d body'
          N.Retypes (N.Name n) _ _ -> N.IntDecl n d body'
          N.ValRetypes (N.Name n) _ _ -> N.IntDecl n d body'
          N.Reshapes (N.Name n) _ _ -> N.IntDecl n d body'
          N.ValReshapes (N.Name n) _ _ -> N.IntDecl n d body'
          _ -> error ("Unhandled type of declaration: " ++ (show d))
      _ -> next node

uniqueIdentifiers :: Transform (Int, Map.Map String String)
uniqueIdentifiers next top node
  = case node of
      N.IntDecl name def body -> do
        (n, ids) <- get
        let newname = name ++ "_" ++ (show n)
        put (n + 1, Map.insert name newname ids)
        def' <- top def
        body' <- top body
        modify (\(n, _) -> (n, ids))
        return $ N.IntDecl newname def' body'
      N.Name s -> do
        (_, ids) <- get
        return $ if Map.member s ids then N.Name (Map.findWithDefault "" s ids) else error ("Unknown identifier: " ++ s)
      _ -> next node

