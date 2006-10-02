-- Intermediate passes

module PhaseIntermediate (phaseIntermediate) where

import Tree
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

nestDecls :: [(Node, Node)] -> Node -> Node
nestDecls l n = foldl (\a b -> b a) n [IntDecl n d | (OcName n, d) <- l]

markDecls :: Transform ()
markDecls next top node
  = case node of
      OcDecl (OcProc nn@(OcName n) args code) body -> do
        body' <- top body
        code' <- top code
        let pdecl = nestDecls [(n, d) | d@(OcFormal _ n) <- args] (OcProc nn args code')
        return $ IntDecl n pdecl body'
      OcDecl (OcFunc nn@(OcName n) args rets code) body -> do
        error "blah"
        body' <- top body
        code' <- top code
        let pdecl = nestDecls [(n, d) | d@(OcFormal _ n) <- args] (OcFunc nn args rets code')
        return $ IntDecl n pdecl body'
      -- FIXME same for functions
      OcDecl d body -> do
        body' <- top body
        return $ case d of
          OcVars t ns -> nestDecls [(n, t) | n <- ns] body'
          OcIs (OcName n) _ -> IntDecl n d body'
          OcIsType (OcName n) _ _ -> IntDecl n d body'
          OcValIs (OcName n) _ -> IntDecl n d body'
          OcValIsType (OcName n) _ _ -> IntDecl n d body'
          OcDataType (OcName n) _ -> IntDecl n d body'
          OcProtocol (OcName n) _ -> IntDecl n d body'
          OcFuncIs (OcName n) _ _ _ -> IntDecl n d body'
          OcRetypes (OcName n) _ _ -> IntDecl n d body'
          OcValRetypes (OcName n) _ _ -> IntDecl n d body'
          OcReshapes (OcName n) _ _ -> IntDecl n d body'
          OcValReshapes (OcName n) _ _ -> IntDecl n d body'
          _ -> error ("Unhandled type of declaration: " ++ (show d))
      _ -> next node

uniqueIdentifiers :: Transform (Int, Map.Map String String)
uniqueIdentifiers next top node
  = case node of
      IntDecl name def body -> do
        (n, ids) <- get
        let newname = name ++ "_" ++ (show n)
        put (n + 1, Map.insert name newname ids)
        def' <- top def
        body' <- top body
        modify (\(n, _) -> (n, ids))
        return $ IntDecl newname def' body'
      OcName s -> do
        (_, ids) <- get
        return $ if Map.member s ids then OcName (Map.findWithDefault "" s ids) else error ("Unknown identifier: " ++ s)
      _ -> next node

