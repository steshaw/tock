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

-- | The necessary components for using an occam EDSL (for building test-cases).
module OccamEDSL (ExpInp, ExpInpT,
  oSEQ, oPAR, oPROC, oSKIP, oINT, oWHILE,
  oCASE, oCASEinput, caseOption, inputCaseOption, 
  oALT, guard,
  oIF, ifChoice,
  Occ, oA, oB, oC, oX, oY, oZ, p0, p1, p2, (*?), (*!), (*:=), (*+), decl, declNonce, decl',
    sub,
    oempty, testOccamPass,
    oprocess,
    testOccamPassWarn, testOccamPassTransform, ExpInpC(shouldComeFrom),
    becomes) where

import Control.Monad.State hiding (guard)
import Data.Generics
import qualified Data.Map as Map
import qualified Data.Set as Set
import Test.HUnit hiding (State)

import qualified AST as A
import CompState
import Errors
import Metadata
import Pass
import Pattern
import TestUtils
import TreeUtils
import Types
import Utils

-- The rough rules for converting occam to pseudo-occam are:
--
-- * stick a lower-case o on the front of keywords
--
-- * For variables, use oA, oB, oC, oX, oY, oZ for A,B,C,X,Y,Z
--
-- * put an asterisk before every operator
--
-- * turn empty items (e.g. following declarations at the top-level) into oempty
--
-- * stick decl on the front of declarations, and treat the insides as a new block
-- (see next point)
--
-- * make all the items in a block (such as SEQ or PAR) into a list.
--
-- * Omit any SEQs inside SEQs (or similar) after declarations
-- 
-- * The variables must each be used once, since their declaration is added to
-- the state, hence their scope is effectively the whole fragment
--
-- The following:
--
-- PROC foo (INT a)
--   SKIP
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
-- oPROC "foo" [(oINT, a)]
--   oSKIP
-- $
-- oPROC "bar" [] (
--   oSEQ [
--     decl oINT y
--       [
--       decl oBYTE x
--         [x *:= 3]
--       ,decl oBYTE z
--         [sPAR
--           [y *:= 0
--           ,z *:= 2
--           ]
--         ]
--       ,y *:= 1
--       ]
--     ]
-- )$
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

-- | A type-class to finesse the difference between a raw thing and an A.Only
-- item containing that thing.
class Castable a structItem | a -> structItem where
  makeStruct :: a -> A.Structured structItem
  makePlain :: structItem -> a

instance Castable A.Process A.Process where
  makeStruct = A.Only emptyMeta
  makePlain = id

instance Castable (A.Structured A.Process) A.Process where
  makeStruct = id
  makePlain = A.Only emptyMeta

instance Castable A.Option A.Option where
  makeStruct = A.Only emptyMeta
  makePlain = id

instance Castable (A.Structured A.Option) A.Option where
  makeStruct = id
  makePlain = A.Only emptyMeta

instance Castable A.Variant A.Variant where
  makeStruct = A.Only emptyMeta
  makePlain = id

instance Castable (A.Structured A.Variant) A.Variant where
  makeStruct = id
  makePlain = A.Only emptyMeta

instance Castable A.Choice A.Choice where
  makeStruct = A.Only emptyMeta
  makePlain = id

instance Castable (A.Structured A.Choice) A.Choice where
  makeStruct = id
  makePlain = A.Only emptyMeta


p0, p1, p2 :: Castable c A.Process => O c
p0 = return $ makePlain $ A.Skip emptyMeta
p1 = return $ makePlain $ A.Seq emptyMeta (A.Several emptyMeta [])
p2 = return $ makePlain $ A.Par emptyMeta A.PlainPar (A.Several emptyMeta [])


oSEQ, oPAR :: Castable c A.Process => [O (A.Structured A.Process)] -> O c
oSEQ = liftM (makePlain . A.Seq emptyMeta . singlify . A.Several emptyMeta) . sequence
oPAR = liftM (makePlain . A.Par emptyMeta A.PlainPar . singlify . A.Several emptyMeta) . sequence

oCASE :: (CanBeExpression e, Castable c A.Process) => e -> [O (A.Structured A.Option)] -> O c
oCASE e os = do
  e' <- liftExpInp (expr e)
  os' <- sequence os
  return $ makePlain $ A.Case emptyMeta e' $ singlify $ A.Several emptyMeta os'

caseOption :: (CanBeExpression e, Castable c A.Option) => ([e], O A.Process) -> O c
caseOption (es, p)
  = do es' <- mapM (liftExpInp . expr) es
       p' <- p
       return $ makePlain $ A.Option emptyMeta es' p'

inputCaseOption :: (Castable c A.Variant) => (A.Name, [ExpInp A.Variable], O A.Process) -> O c
inputCaseOption (n, is, p)
  = do is' <- sequence $ map liftExpInp is
       p' <- p
       return $ makePlain $ A.Variant emptyMeta n (map (A.InVariable emptyMeta) is') p'


oCASEinput :: [O (A.Structured A.Variant)] -> O (A.Structured A.Variant)
oCASEinput = liftM (singlify . A.Several emptyMeta) . sequence

oALT :: Castable c A.Process => [O (A.Structured A.Alternative)] -> O c
oALT = liftM (makePlain . A.Alt emptyMeta False . singlify . A.Several emptyMeta) . sequence

guard :: (O A.Process, O A.Process) -> O (A.Structured A.Alternative)
guard (inp, body)
  = do (A.Input m v im) <- inp
       body' <- body
       return $ A.Only emptyMeta $ A.Alternative m (A.True emptyMeta) v im body'

oIF :: Castable c A.Process => [O (A.Structured A.Choice)] -> O c
oIF = liftM (makePlain . A.If emptyMeta . singlify . A.Several emptyMeta) . sequence

ifChoice :: (CanBeExpression e, Castable c A.Choice) => (e, O A.Process) -> O c
ifChoice (e, body)
  = do e' <- liftExpInp $ expr e
       body' <- body
       return $ makePlain $ A.Choice emptyMeta e' body'

oWHILE :: (CanBeExpression e, Castable r A.Process) => e -> O A.Process -> O r
oWHILE e body
  = do e' <- liftExpInp $ expr e
       body' <- body
       return $ makePlain $ A.While emptyMeta e' body'


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
             A.Proc emptyMeta (A.PlainSpec, A.PlainRec) formals (Just p)
           ) (singlify s)
  where
    formals = [A.Formal A.Original t n | (t, A.Variable _ n) <- params]

oSKIP :: Castable a A.Process => O a
oSKIP = return $ makePlain $ A.Skip emptyMeta

oINT :: ExpInp A.Type
oINT = return A.Int

oA,oB,oC,oX,oY,oZ :: ExpInp A.Variable
oA = return $ variable "A"
oB = return $ variable "B"
oC = return $ variable "C"
oX = return $ variable "X"
oY = return $ variable "Y"
oZ = return $ variable "Z"

(*?) :: (Castable r A.Process, ExpInpC c a, CanBeInput a) => ExpInp A.Variable -> c a -> O r
(*?) bch bdest = do
  ch <- liftExpInp bch
  dest <- liftExpInp bdest >>* inputItem
  return $ makePlain $ A.Input emptyMeta ch dest

(*!), (*:=) :: (Castable r A.Process, CanBeExpression e) => ExpInp A.Variable -> ExpInp e -> O r
(*!) bch bsrc = do
  ch <- liftExpInp bch
  src <- liftExpInp bsrc >>= (liftExpInp . expr)
  return $ makePlain $ A.Output emptyMeta ch [A.OutExpression emptyMeta src]
(*:=) bdest bsrc = do
  dest <- liftExpInp bdest
  src <- liftExpInp bsrc >>= (liftExpInp . expr)
  return $ makePlain $ A.Assign emptyMeta [dest] (A.ExpressionList emptyMeta [src])

infix 8 *:=

(*+) :: (CanBeExpression e, CanBeExpression e') => e -> e' -> ExpInp (A.Expression)
(*+) x y = do x' <- expr x
              y' <- expr y
              return $ addExprsInt x' y'


sub :: ExpInp A.Variable -> Int -> ExpInp A.Variable
sub v n = liftM (A.SubscriptedVariable emptyMeta (A.Subscript emptyMeta A.CheckBoth
  $ intLiteral $ toInteger n)) v

decl :: Data a => ExpInp A.Type -> ExpInp A.Variable ->
  [O (A.Structured a)] -> O (A.Structured a)
decl bty bvar scope = do
  ty <- liftExpInp bty
  (A.Variable _ name) <- liftExpInp bvar
  defineVariable (A.nameName name) ty
  s <- sequence scope
  return $ A.Spec emptyMeta (A.Specification emptyMeta name $ A.Declaration emptyMeta ty)
    (singlify $ A.Several emptyMeta s)

declNonce :: Data a => ExpInp A.Type -> ExpInp A.Variable ->
  [O (A.Structured a)] -> O (A.Structured a)
declNonce bty bvar scope = do
  ty <- liftExpInp bty
  (A.Variable _ name) <- liftExpInp bvar
  defineThing (A.nameName name) (A.Declaration emptyMeta ty) A.Original A.NameNonce
  s <- sequence scope
  return $ A.Spec emptyMeta (A.Specification emptyMeta name $ A.Declaration emptyMeta ty)
    (singlify $ A.Several emptyMeta s)

decl' :: Data a => A.Name -> A.SpecType -> A.AbbrevMode -> A.NameSource ->
  [O (A.Structured a)] -> O (A.Structured a)
decl' n sp am ns scope = do
  defineThing (A.nameName n) sp am ns
  s <- sequence scope
  return $ A.Spec emptyMeta (A.Specification emptyMeta n sp)
    (singlify $ A.Several emptyMeta s)


-- | A type-class to finesse the difference between components of expressions (such
-- as variables, literals) and actual expressions
class CanBeExpression a where
  expr :: a -> ExpInp A.Expression

instance CanBeExpression A.Variable where
  expr = return . A.ExprVariable emptyMeta

instance CanBeExpression A.Expression where
  expr = return

instance CanBeExpression Int where
  expr = return . A.Literal emptyMeta A.Int . A.IntLiteral emptyMeta . show

instance CanBeExpression Bool where
  expr True = return $ A.True emptyMeta
  expr False = return $ A.False emptyMeta

instance CanBeExpression e => CanBeExpression (ExpInp e) where
  expr = join . liftM expr

class CanBeInput a where
  inputItem :: a -> A.InputMode

instance CanBeInput A.Variable where
  inputItem v = A.InputSimple emptyMeta [A.InVariable emptyMeta v]

instance CanBeInput [A.Variable] where
  inputItem = A.InputSimple emptyMeta . map (A.InVariable emptyMeta)

instance CanBeInput (A.Structured A.Variant) where
  inputItem = A.InputCase emptyMeta

instance CanBeInput A.InputMode where
  inputItem = id

oempty :: Data a => O (A.Structured a)
oempty = return $ A.Several emptyMeta []

oprocess :: O (A.Structured A.Process) -> O (A.Structured A.Process)
oprocess = id

testOccamPass :: Data a => String -> O a -> Pass a -> Test
testOccamPass str code pass
  = let ExpInpT expm inpm = code
        (exp, expS) = runState expm emptyState
        (inp, inpS) = runState inpm emptyState
    in TestCase $ testPassWithStateCheck str exp pass inp (put inpS) (assertEqual
      str (csNames expS) . csNames)

-- | Give back True if the result is as expected for the warnings
testOccamPassWarn :: Data a => String -> ([WarningReport] -> Bool) -> O a -> Pass a -> Test
testOccamPassWarn str check code pass
  = let ExpInpT expm inpm = code
        (exp, expS) = runState expm emptyState
        (inp, inpS) = runState inpm emptyStateWithWarnings
        pass' = pass {passCode = \x -> do y <- passCode pass x
                                          ws <- getCompState >>* csWarnings
                                          when (not $ check ws) $
                                            dieP emptyMeta $ str ++ " warnings not as expected: "
                                              ++ (show ws)
                                          return y}
    in TestCase $ testPassWithStateCheck str exp pass' inp
      (put $ inpS {csWarnings = []}) -- Blank the warnings for the new pass
      (assertEqual str (csNames expS) . csNames)
  where
    emptyStateWithWarnings = emptyState { csEnabledWarnings = Set.fromList [minBound..maxBound] }

-- | Like testOccamPass, but applies a transformation to the patterns (such as
-- using stopCaringPattern) before pattern-matching
testOccamPassTransform :: Data a => String -> (Pattern -> Pattern) -> O a -> Pass a -> Test
testOccamPassTransform str trans code pass
  = let ExpInpT expm inpm = code
        (exp, expS) = runState expm emptyState
        (inp, inpS) = runState inpm emptyState
    in TestCase $ testPassWithStateCheck str (trans $ mkPattern exp) pass inp (put inpS) (testPatternMatchOneOf
      (str ++ " state check") [trans $ mkPattern pr | pr <- permutation $ Map.toList $ csNames expS] . Map.toList
        . csNames)
    -- It's important to convert the maps to lists first, as Map doesn't have a
    -- Data instance.
    --
    -- But there is a problem.  We need to compare two maps (as lists of pairs),
    -- but due to nonce names and such, the lists of pairs may be in different
    -- order, and to make things worse we must to compare using structural equality.
    --  Hence we must use a permutation comparison


class ExpInpC c a where
  shouldComeFrom :: c a -> c a -> c a
  liftExpInp :: c a -> ExpInpT (State CompState) a

instance ExpInpC ExpInp a where
  shouldComeFrom (ExpInp exp _) (ExpInp _ inp) = ExpInp exp inp
  liftExpInp (ExpInp x y) = ExpInpT (return x) (return y)

instance ExpInpC (ExpInpT (State CompState)) a where
  shouldComeFrom (ExpInpT exp _) (ExpInpT _ inp) = ExpInpT exp inp
  liftExpInp = id

becomes :: ExpInpC c a => c a -> c a -> c a
becomes = flip shouldComeFrom
