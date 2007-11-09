{-
Tock: a compiler for parallel languages
Copyright (C) 2007  University of Kent

This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation, either version 2 of the License, or (at your
option) any later version.

This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License along
with this program.  If not, see <http://www.gnu.org/licenses/>.
-}

-- | Simplify communications.
module SimplifyComms where

import Control.Monad.State
import Data.Generics
import Data.List

import qualified AST as A
import CompState
import Metadata
import Pass
import Types
import Utils

simplifyComms :: Pass
simplifyComms = runPasses passes
  where
    passes =
      [ ("Define temporary variables for outputting expressions", outExprs)
       ,("Transform ? CASE statements/guards into plain CASE", transformInputCase)
      ]

outExprs :: Data t => t -> PassM t
outExprs = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric outExprs

    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Output m c ois)
        =  do (ois', specs) <- mapAndUnzipM changeItem ois
              let foldedSpec = foldFuncs specs
              return $ A.Seq m (foldedSpec $ A.OnlyP m $ A.Output m c ois')
    doProcess (A.OutputCase m c tag ois)
        =  do (ois', specs) <- mapAndUnzipM changeItem ois
              let foldedSpec = foldFuncs specs
              return $ A.Seq m (foldedSpec $ A.OnlyP m $ A.OutputCase m c tag ois')
    doProcess p = doGeneric p
  
    changeItem :: A.OutputItem -> PassM (A.OutputItem, A.Structured -> A.Structured)
    changeItem (A.OutExpression m e) = do (e', spec) <- transExpr m e
                                          return (A.OutExpression m e', spec)
    changeItem (A.OutCounted m ce ae) = do (ce', ceSpec) <- transExpr m ce
                                           (ae', aeSpec) <- transExpr m ae
                                           return (A.OutCounted m ce' ae', ceSpec . aeSpec)

    transExpr :: Meta -> A.Expression -> PassM (A.Expression, A.Structured -> A.Structured)
    -- If it's already an output direct from a variable, no need to change it:
    transExpr _ e@(A.ExprVariable {}) = return (e, id)
    transExpr m e = do (nm, spec) <- abbrevExpr m e
                       return (A.ExprVariable m $ A.Variable m nm, spec)
    
    abbrevExpr :: Meta -> A.Expression -> PassM (A.Name, A.Structured -> A.Structured)
    abbrevExpr m e = do t <- typeOfExpression e
                        specification@(A.Specification _ nm _) <- defineNonce m "output_var" (A.IsExpr m A.ValAbbrev t e) A.VariableName A.ValAbbrev
                        return (nm, A.Spec m specification)

{- The explanation for this pass is taken from my (Neil's) mailing list post "Case protocols" on tock-discuss, dated 10th October 2007:

Currently in Tock (from occam) we have CASE statements, and inputs for variant 
protocols.  They are parsed into separate AST entries, which is sensible.  But 
then in the backend there is some duplicate code because both things get turned 
into some form of switch statement.  It would be straightforward to unify the 
code in the C/C++ backends, but I was wondering about doing something which 
would be a bit cleaner; unifying them in an earlier pass (everything should be 
a pass in nanopass :).  The idea would be to turn (example is from the occam 2 
manual):

from.dfs ? CASE
 record; rnumber; rlen::buffer
   -- process A
 error ; enumber; elen::buffer
   -- process B

into:

INT temp.var:
SEQ
 from.dfs ? temp.var
 CASE temp.var
   3
     SEQ
       from.dfs ? rnumber ; rlen::buffer
       -- process A
   4
     SEQ
       from.dfs ? enumber ; elen::buffer
       -- process B

Note that the tags are turned into integer literals, which is what happens in 
Tock already anyway.  Note that in Tock each protocol item is already a 
separate communication, so splitting out the sequential inputs is fine.  ALTs 
would have to be split as follows, by turning:

ALT
 from.dfs ? CASE
   request ; query
     -- process C
   error ; enumber; elen::buffer
     -- process D

into:

ALT
 INT temp.var:
 from.dfs ? temp.var
   CASE temp.var
     0
       SEQ
         from.dfs ? query
         -- process C
     1
       SEQ
         from.dfs ? enumber ; elen::buffer
         -- process D
-}

transformInputCase :: Data t => t -> PassM t
transformInputCase = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric transformInputCase

    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Input m v (A.InputCase m' s))
      = do spec@(A.Specification _ n _) <- defineNonce m "input_tag" (A.Declaration m' A.Int Nothing) A.VariableName A.Original
           s' <- doStructured v s
           return $ A.Seq m $ A.Spec m' spec $ A.Several m'
             [A.OnlyP m $ A.Input m v (A.InputSimple m [A.InVariable m (A.Variable m n)])
             ,A.OnlyP m' $ A.Case m' (A.ExprVariable m $ A.Variable m n) s']
    doProcess (A.Alt m pri s)
      = do s' <- doStructured undefined s
           return (A.Alt m pri s')
    doProcess p = doGeneric p
    
    doStructured :: A.Variable -> A.Structured -> PassM A.Structured
    -- These entries all just burrow deeper into the structured:
    doStructured v (A.ProcThen m p s)
      = do s' <- doStructured v s
           p' <- doProcess p
           return (A.ProcThen m p' s')
    doStructured v (A.Spec m sp st)
      = do st' <- doStructured v st
           return (A.Spec m sp st')
    doStructured v (A.Several m ss)
      = do ss' <- mapM (doStructured v) ss
           return (A.Several m ss')
    doStructured v (A.Rep m rep s)
      = do s' <- doStructured v s
           return (A.Rep m rep s')
           
    -- Transform variant options:
    doStructured chanVar (A.OnlyV m (A.Variant m' n iis p))
      = do (Right items) <- protocolItems chanVar
           let (Just idx) = elemIndex n (fst $ unzip items)
           p' <- doProcess p
           return $ A.OnlyO m $ A.Option m' [makeConstant m' idx] $
             if (length iis == 0)
               then p'
               else A.Seq m' $ A.Several m'
                      [A.OnlyP m' $ A.Input m' chanVar (A.InputSimple m' iis)
                      ,A.OnlyP (findMeta p') p']
                      
    -- Transform alt guards:
    -- The processes that are the body of input-case guards are always skip, so we can discard them:
    doStructured _ (A.OnlyA m (A.Alternative m' v (A.InputCase m'' s) _))
      = do spec@(A.Specification _ n _) <- defineNonce m "input_tag" (A.Declaration m' A.Int Nothing) A.VariableName A.Original
           s' <- doStructured v s
           return $ A.Spec m' spec $ A.OnlyA m $ 
             A.Alternative m' v (A.InputSimple m [A.InVariable m (A.Variable m n)]) $
             A.Case m'' (A.ExprVariable m'' $ A.Variable m n) s'
    doStructured _ (A.OnlyA m (A.AlternativeCond m' e v (A.InputCase m'' s) _))
      = do spec@(A.Specification _ n _) <- defineNonce m "input_tag" (A.Declaration m' A.Int Nothing) A.VariableName A.Original
           s' <- doStructured v s
           return $ A.Spec m' spec $ A.OnlyA m $ 
             A.AlternativeCond m' e v (A.InputSimple m [A.InVariable m (A.Variable m n)]) $
             A.Case m'' (A.ExprVariable m'' $ A.Variable m n) s'
    -- Leave other guards untouched:
    doStructured _ a@(A.OnlyA {}) = return a
