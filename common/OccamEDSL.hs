{-
Tock: a compiler for parallel languages
Copyright (C) 2008  University of Kent

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

module OccamEDSL (ExpInp, ExpInpT, oSEQ, oPAR, oPROC, oSKIP, oINT,
  Occ, oA, oB, oC, oX, oY, oZ, (*?), (*!), (*:=), decl, oempty, testOccamPass, ExpInpC(..)) where

import Control.Monad.State
import Data.Generics
import Test.HUnit hiding (State)

import qualified AST as A
import CompState
import Metadata
import Pass
import TestUtils
import Utils

-- The rough rules for converting occam to pseudo-occam are to stick a lower-case
-- o on the front of keywords, turn colons into dollars, put an asterisk before
-- every operator, empty items (e.g. following declarations) into oempty
-- and stick decl on the front of declarations (and indent the scope) and make
-- all the items in a SEQ or PAR into a list.
--  Other things to remember:
-- * The variables must each be used once, since their declaration is added to
-- the state
-- * Scope is more explicit in this, so you must indent for a variable's scope
--
-- The following:
--
-- PROC foo (INT a)
-- :
--
-- PROC bar ()
--   SEQ
--     INT y:
--     SEQ
--       BYTE x:
--       x := 3
--       BYTE z:
--       PAR
--         y := 0
--         z := 2
--       y := 1
-- :
--
-- becomes:
--
-- sPROC "foo" [(oINT, a)]
--   oempty
-- $
-- sPROC "bar" [] (
--   oSEQ [
--     decl oINT y $
--     oSEQ
--     [
--       [decl oBYTE x $
--         x *:= 3
--       ,decl oBYTE z $
--          sPAR
--           [y *:= 0
--           ,z *:= 2
--           ]
--     ,y *:= 1
--     ]
--   ]
-- $
-- oempty

-- This is an item that allows the expected and input values to be manipulated
-- together, or separately
data ExpInp a = ExpInp a a

data Monad m => ExpInpT m a = ExpInpT {
  fstExpInpT :: m a,
  sndExpInpT :: m a }

instance MonadTrans ExpInpT where
  lift m = ExpInpT m m

instance Monad m => Monad (ExpInpT m) where
  return x = ExpInpT (return x) (return x)
  (>>=) (ExpInpT x y) f
    = ExpInpT (x >>= (fstExpInpT . f)) (y >>= (sndExpInpT . f))

liftExpInp :: Monad m => ExpInp a -> ExpInpT m a
liftExpInp (ExpInp x y) = ExpInpT (return x) (return y)

instance Functor ExpInp where
  fmap f (ExpInp x y) = ExpInp (f x) (f y)

instance Monad ExpInp where
  return x = ExpInp x x
  (>>=) (ExpInp x y) f = ExpInp (let ExpInp x' _ = f x in x')
                                (let ExpInp _ y' = f y in y')


instance MonadState s (ExpInpT (State s)) where
  get = ExpInpT get get
  put x = ExpInpT (put x) (put x)

instance CSMR (ExpInpT (State CompState)) where
  getCompState = get

type O a = ExpInpT (State CompState) a
type Occ a = O a

class ProcessC a where
  structProcess :: a -> A.Structured A.Process
  fromProcess :: A.Process -> a

instance ProcessC A.Process where
  structProcess = A.Only emptyMeta
  fromProcess = id

instance ProcessC (A.Structured A.Process) where
  structProcess = id
  fromProcess = A.Only emptyMeta

oSEQ, oPAR :: ProcessC c => [O (A.Structured A.Process)] -> O c
oSEQ = liftM (fromProcess . A.Seq emptyMeta . A.Several emptyMeta) . sequence
oPAR = liftM (fromProcess . A.Par emptyMeta A.PlainPar . A.Several emptyMeta) . sequence

singlify :: Data a => A.Structured a -> A.Structured a
singlify (A.Several _ [s]) = s
singlify ss = ss


oPROC :: Data a => String -> [(A.Type, A.Variable)] -> O A.Process -> O (A.Structured
  a) -> O (A.Structured a)
oPROC str params body scope = do
  p <- body
  s <- scope
  defineProc str [(A.nameName name, A.Original, t) | (t, A.Variable _ name) <- params]
  return $ A.Spec emptyMeta (A.Specification emptyMeta (simpleName str) $
             A.Proc emptyMeta A.PlainSpec formals p
           ) (singlify s)
  where
    formals = [A.Formal A.Original t n | (t, A.Variable _ n) <- params]

oSKIP :: ProcessC a => O a
oSKIP = return $ fromProcess $ A.Skip emptyMeta

oINT :: ExpInp A.Type
oINT = return A.Int

oA,oB,oC,oX,oY,oZ :: ExpInp A.Variable
oA = return $ variable "A"
oB = return $ variable "B"
oC = return $ variable "C"
oX = return $ variable "X"
oY = return $ variable "Y"
oZ = return $ variable "Z"

(*?) :: ExpInp A.Variable -> ExpInp A.Variable -> O (A.Structured A.Process)
(*?) bch bdest = do
  ch <- liftExpInp bch
  dest <- liftExpInp bdest
  return $ A.Only emptyMeta $ A.Input emptyMeta ch (A.InputSimple emptyMeta [A.InVariable emptyMeta dest])

(*!), (*:=) :: CanBeExpression e => ExpInp A.Variable -> ExpInp e -> O (A.Structured A.Process)
(*!) bch bsrc = do
  ch <- liftExpInp bch
  src <- liftExpInp bsrc >>* expr
  return $ A.Only emptyMeta $ A.Output emptyMeta ch [A.OutExpression emptyMeta
    src]
(*:=) bdest bsrc = do
  dest <- liftExpInp bdest
  src <- liftExpInp bsrc >>* expr
  return $ A.Only emptyMeta $ A.Assign emptyMeta [dest] (A.ExpressionList emptyMeta
    [src])


decl :: Data a => ExpInp A.Type -> ExpInp A.Variable ->  O (A.Structured a) ->
  O (A.Structured a)
decl bty bvar scope = do
  ty <- liftExpInp bty
  (A.Variable _ name) <- liftExpInp bvar
  defineVariable (A.nameName name) ty
  s <- scope
  return $ A.Spec emptyMeta (A.Specification emptyMeta name $ A.Declaration emptyMeta ty)
    (singlify s)
  

class CanBeExpression a where
  expr :: a -> A.Expression

instance CanBeExpression A.Variable where
  expr = A.ExprVariable emptyMeta

instance CanBeExpression A.Expression where
  expr = id

instance CanBeExpression Int where
  expr = A.Literal emptyMeta A.Int . A.IntLiteral emptyMeta . show

oempty :: Data a => O (A.Structured a)
oempty = return $ A.Several emptyMeta []

testOccamPass :: String -> O A.AST -> Pass -> Test
testOccamPass str code pass
  = let ExpInpT expm inpm = liftM singlify code
        (exp, expS) = runState expm emptyState
        (inp, inpS) = runState inpm emptyState
    in TestCase $ testPassWithStateCheck str exp pass inp (put inpS) (assertEqual
      str (csNames expS) . csNames)

class ExpInpC a where
  shouldComeFrom :: a -> a -> a

instance ExpInpC (ExpInp a) where
  shouldComeFrom (ExpInp exp _) (ExpInp _ inp) = ExpInp exp inp

instance ExpInpC (ExpInpT (State CompState) a) where
  shouldComeFrom (ExpInpT exp _) (ExpInpT _ inp) = ExpInpT exp inp
