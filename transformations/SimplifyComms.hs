{-
Tock: a compiler for parallel languages
Copyright (C) 2007, 2008  University of Kent

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
import Data.List
import Data.Maybe

import qualified AST as A
import CompState
import Metadata
import Pass
import qualified Properties as Prop
import Traversal
import Types
import Utils

simplifyComms :: [Pass A.AST]
simplifyComms =
    [ outExprs
    , transformInputCase
    , transformProtocolInput
    ]

outExprs :: PassOn A.Process
outExprs = pass "Define temporary variables for outputting expressions"
  (Prop.agg_namesDone ++ Prop.agg_typesDone)
  [Prop.outExpressionRemoved]
  (applyBottomUpM doProcess)
  where
    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Output m c ois)
        =  do (ois', specs) <- mapAndUnzipM changeItem ois
              let foldedSpec = foldFuncs specs
              return $ A.Seq m (foldedSpec $ A.Only m $ A.Output m c ois')
    doProcess (A.OutputCase m c tag ois)
        =  do (ois', specs) <- mapAndUnzipM changeItem ois
              let foldedSpec = foldFuncs specs
              return $ A.Seq m (foldedSpec $ A.Only m $ A.OutputCase m c tag ois')
    doProcess p = return p
  
    changeItem :: A.OutputItem -> PassM (A.OutputItem, A.Structured A.Process -> A.Structured A.Process)
    changeItem (A.OutExpression m e) = do (e', spec) <- transExpr m e
                                          return (A.OutExpression m e', spec)
    changeItem (A.OutCounted m ce ae) = do (ce', ceSpec) <- transExpr m ce
                                           (ae', aeSpec) <- transExpr m ae
                                           return (A.OutCounted m ce' ae', ceSpec . aeSpec)

    transExpr :: Meta -> A.Expression -> PassM (A.Expression, A.Structured A.Process -> A.Structured A.Process)
    -- If it's already an output direct from a variable, no need to change it:
    transExpr _ e@(A.ExprVariable {}) = return (e, id)
    transExpr m e = do (nm, spec) <- abbrevExpr m e
                       return (A.ExprVariable m $ A.Variable m nm, spec)
    
    abbrevExpr :: Meta -> A.Expression -> PassM (A.Name, A.Structured A.Process -> A.Structured A.Process)
    abbrevExpr m e = do t <- astTypeOf e
                        specification@(A.Specification _ nm _) <-
                          defineNonce m "output_var" (A.Is m A.ValAbbrev t $
                            A.ActualExpression e) A.ValAbbrev
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

transformInputCase :: PassOn A.Process
transformInputCase = pass "Transform ? CASE statements/guards into plain CASE"
  (Prop.agg_namesDone ++ Prop.agg_typesDone)
  [Prop.inputCaseRemoved]
  (applyBottomUpM doProcess)
  where
    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Input m v (A.InputCase m' ty s))
      = do spec@(A.Specification _ n _) <- defineNonce m "input_tag" (A.Declaration m' A.Int) A.Original
           case ty of
             A.InputCaseNormal -> do 
               s' <- doStructuredV Nothing v s
               return $ A.Seq m $ A.Spec m' spec $ A.Several m'
                 [A.Only m $ A.Input m v (A.InputSimple m [A.InVariable m (A.Variable m n)] Nothing)
                 ,A.Only m' $ A.Case m' (A.ExprVariable m $ A.Variable m n) s']
             A.InputCaseExtended -> do 
               sA <- doStructuredV (Just A.InputCaseExtended) v s
               sB <- doStructuredV (Just A.InputCaseNormal) v s
               return $ A.Seq m $ A.Spec m' spec $ A.Several m' $ map (A.Only m')
                 [A.Input m v (A.InputSimple m [A.InVariable m (A.Variable m n)]
                    $ Just (A.Case m' (A.ExprVariable m $ A.Variable m n) sA))
                 ,A.Case m' (A.ExprVariable m $ A.Variable m n) sB
                 ]
                 
    doProcess (A.Alt m pri s)
      = do s' <- doStructuredA s
           return (A.Alt m pri s')
    doProcess p = return p

    -- Convert Structured Variant into the equivalent Structured Option.
    --
    -- For extended inputs, if there are no extra inputs after the tag, we must
    -- perform the extended action during the extended input on the tag.  This
    -- is when (Just A.InputCaseExtended) is passed.  If there are extra inputs
    -- after the tag, we perform SKIP for the extended action, and then do our
    -- real extended action on the further inputs
    doStructuredV :: (Maybe A.InputCaseType) -> A.Variable -> A.Structured A.Variant -> PassM (A.Structured A.Option)
    doStructuredV mty chanVar = transformOnly transform
      where
        transform m (A.Variant m' n iis p mp)
            =  do (Right items) <- protocolItems m' chanVar
                  let (Just idx) = elemIndex n (fst $ unzip items)
                  return $ A.Only m $ A.Option m' [makeConstant m' idx] $
                    case (mty, null iis) of
                      -- Normal input, no extra inputs:
                      (Nothing, True) -> p
                      -- Extended phase, no extra inputs, so do extended process now:
                      (Just A.InputCaseExtended, True) -> p
                      -- After extended, no extra inputs, do after process:
                      (Just A.InputCaseNormal, True) -> fromMaybe (A.Skip m) mp
                      -- Normal input, extra inputs to do:
                      (Nothing, False) -> A.Seq m' $ A.Several m'
                             [A.Only m' $ A.Input m' chanVar (A.InputSimple m' iis Nothing),
                              A.Only (findMeta p) p]
                      -- Extended phase, extra inputs to do:
                      (Just A.InputCaseExtended, False) -> A.Skip m
                      -- After extended, extra inputs to do:
                      (Just A.InputCaseNormal, False) -> A.Seq m' $ A.Several m'
                        $ map (A.Only m') $
                          [A.Input m' chanVar (A.InputSimple m' iis $ Just p)
                          ] ++ maybeToList mp

    -- Transform alt guards.
    doStructuredA :: A.Structured A.Alternative -> PassM (A.Structured A.Alternative)
    doStructuredA = transformOnly doAlternative
      where
        -- The processes that are the body of input-case guards are always
        -- skip, so we can discard them.
        doAlternative m (A.Alternative m' e v (A.InputCase m'' ty s) _)
          = do spec@(A.Specification _ n _) <- defineNonce m "input_tag" (A.Declaration m' A.Int) A.Original
               case ty of
                 A.InputCaseNormal -> do
                   s' <- doStructuredV Nothing v s
                   return $ A.Spec m' spec $ A.Only m $ 
                     A.Alternative m' e v (A.InputSimple m [A.InVariable m (A.Variable m n)] Nothing) $
                     A.Case m'' (A.ExprVariable m'' $ A.Variable m n) s'
                 A.InputCaseExtended -> do
                   sA <- doStructuredV (Just A.InputCaseExtended) v s
                   sB <- doStructuredV (Just A.InputCaseNormal) v s
                   return $ A.Spec m' spec $ A.Only m $ 
                     A.Alternative m' e v (A.InputSimple m [A.InVariable m (A.Variable m n)] $
                       Just $ A.Case m'' (A.ExprVariable m'' $ A.Variable m n) sA)
                       (A.Case m'' (A.ExprVariable m'' $ A.Variable m n) sB)
        -- Leave other guards untouched.
        doAlternative m a = return $ A.Only m a

transformProtocolInput :: PassOn2 A.Process A.Alternative
transformProtocolInput = pass "Flatten sequential protocol inputs into multiple inputs"
  (Prop.agg_namesDone ++ Prop.agg_typesDone ++ [Prop.inputCaseRemoved])
  [Prop.seqInputsFlattened]
  (applyBottomUpM2 doProcess doAlternative)
  where
    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Input m v (A.InputSimple m' iis@(_:_:_) mp))
      = return $ A.Seq m $ A.Several m $ map (A.Only m . A.Input m v) $ flatten m' iis mp
    doProcess p = return p

    -- We put the extended input on the final input:
    flatten :: Meta -> [A.InputItem] -> Maybe A.Process -> [A.InputMode]
    flatten m [ii] mp = [A.InputSimple m [ii] mp]
    flatten m (ii:iis) mp = A.InputSimple m [ii] Nothing : flatten m iis mp

    doAlternative :: A.Alternative -> PassM A.Alternative
    doAlternative (A.Alternative m cond v (A.InputSimple m' (firstII:(otherIIS@(_:_))) mp) body)
      = return $ A.Alternative m cond v (A.InputSimple m' [firstII] Nothing) $ A.Seq m' $ A.Several m' $
             (map (A.Only m' . A.Input m' v) $ flatten m' otherIIS mp)
             ++ [A.Only m' body]
    doAlternative s = return s
