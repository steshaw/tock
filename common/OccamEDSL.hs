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
  a, b, c, x, y, z, (*?), (*!), (*:=), decl, oempty, OccamStructuredM, testOccamPass) where

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
-- every operator, empty items into oempty
-- and stick decl on the front of declarations (and indent the scope) and add a do after SEQ and PAR.
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
--   INT y:
--   SEQ
--     BYTE x:
--     x := 3
--     BYTE z:
--     PAR
--       y := 0
--       z := 2
--     y := 1
-- :
--
-- becomes:
--
-- sPROC "foo" [(oINT, a)]
--   oempty
-- $
-- sPROC "bar" [] (
--   decl oINT y $
--   oSEQ $ do
--     decl oBYTE x $
--       x *:= 3
--     decl oBYTE z $
--       sPAR $ do
--         y *:= 0
--         z *:= 2
--     y *:= 1
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

runExpInpT :: Monad m => ExpInpT m a -> m (ExpInp a)
runExpInpT (ExpInpT mx my) = do
  x <- mx
  y <- my
  return $ ExpInp x y

liftExpInp :: Monad m => ExpInp a -> ExpInpT m a
liftExpInp (ExpInp x y) = ExpInpT (return x) (return y)

instance Functor ExpInp where
  fmap f (ExpInp x y) = ExpInp (f x) (f y)

instance Monad ExpInp where
  return x = ExpInp x x
  (>>=) (ExpInp x y) f = ExpInp (let ExpInp x' _ = f x in x')
                                (let ExpInp _ y' = f y in y')


newtype OccamStructuredM a b = OccamStructuredM (State (ExpInp CompState, [ExpInp (A.Structured a)]) b)
  deriving (Monad)

instance MonadState s (ExpInpT (State s)) where
  get = ExpInpT get get
  put x = ExpInpT (put x) (put x)

instance CSMR (ExpInpT (State CompState)) where
  getCompState = get

type O a = ExpInpT (State CompState) a

termFunc :: Data a => Maybe (A.Structured a) -> A.Structured a
termFunc (Just s) = s
termFunc Nothing = A.Several emptyMeta []

oSEQ, oPAR :: OccamStructuredM A.Process () -> O A.Process
oSEQ = liftM (A.Seq emptyMeta . A.Several emptyMeta) . getStruct
oPAR = liftM (A.Par emptyMeta A.PlainPar . A.Several emptyMeta) . getStruct

getStruct :: OccamStructuredM a () -> O [A.Structured a]
getStruct (OccamStructuredM m) = ExpInpT
  (do s <- get
      let (ExpInp s' _, es) = execState m (ExpInp s undefined, [])
      put s'
      return [x | ExpInp x _ <- es])
  (do s <- get
      let (ExpInp _ s', es) = execState m (ExpInp undefined s, [])
      put s'
      return [x | ExpInp x _ <- es])

recordLine :: O (A.Structured a) -> OccamStructuredM a ()
recordLine (ExpInpT mx my) = OccamStructuredM $ modify $ \(ExpInp sx sy, ls) ->
  let (lx, sx') = runState mx sx
      (ly, sy') = runState my sy
  in (ExpInp sx' sy', ls ++ [ExpInp lx ly])

singlify :: Data a => [A.Structured a] -> A.Structured a
singlify [s] = s
singlify ss = A.Several emptyMeta ss


oPROC :: Data a => String -> [(A.Type, A.Variable)] -> O A.Process -> OccamStructuredM a ()
  -> OccamStructuredM a ()
oPROC str params body scope = recordLine $ do
  p <- body
  s <- getStruct scope
  defineProc str [(A.nameName name, A.Original, t) | (t, A.Variable _ name) <- params]
  return $ A.Spec emptyMeta (A.Specification emptyMeta (simpleName str) $
             A.Proc emptyMeta A.PlainSpec formals p
           ) (singlify s)
  where
    formals = [A.Formal A.Original t n | (t, A.Variable _ n) <- params]

oSKIP :: O A.Process
oSKIP = return $ A.Skip emptyMeta

oINT :: ExpInp A.Type
oINT = return A.Int

a,b,c,x,y,z :: ExpInp A.Variable
a = return $ variable "a"
b = return $ variable "b"
c = return $ variable "c"
x = return $ variable "x"
y = return $ variable "y"
z = return $ variable "z"

(*?) :: ExpInp A.Variable -> ExpInp A.Variable -> OccamStructuredM A.Process ()
(*?) bch bdest = recordLine $ do
  ch <- liftExpInp bch
  dest <- liftExpInp bdest
  return $ A.Only emptyMeta $ A.Input emptyMeta ch (A.InputSimple emptyMeta [A.InVariable emptyMeta dest])
(*!), (*:=) :: CanBeExpression e => ExpInp A.Variable -> ExpInp e -> OccamStructuredM
  A.Process ()
(*!) bch bsrc = recordLine $ do
  ch <- liftExpInp bch
  src <- liftExpInp bsrc >>* expr
  return $ A.Only emptyMeta $ A.Output emptyMeta ch [A.OutExpression emptyMeta
    src]
(*:=) bdest bsrc = recordLine $ do
  dest <- liftExpInp bdest
  src <- liftExpInp bsrc >>* expr
  return $ A.Only emptyMeta $ A.Assign emptyMeta [dest] (A.ExpressionList emptyMeta
    [src])


decl :: Data a => ExpInp A.Type -> ExpInp A.Variable ->  OccamStructuredM a () ->
  OccamStructuredM a ()
decl bty bvar scope = recordLine $ do
  ty <- liftExpInp bty
  (A.Variable _ name) <- liftExpInp bvar
  defineVariable (A.nameName name) ty
  s <- getStruct scope
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

oempty :: OccamStructuredM a ()
oempty = return ()

testOccamPass :: String -> OccamStructuredM () () -> Pass -> Test
testOccamPass str code pass
  = let ExpInpT expm inpm = liftM singlify $ getStruct code
        (exp, expS) = runState expm emptyState
        (inp, inpS) = runState inpm emptyState
    in TestCase $ testPassWithStateCheck str exp pass inp (put inpS) (assertEqual
      str (csNames expS) . csNames)
--TODO could get fancy with the Metas, and near-predict them
