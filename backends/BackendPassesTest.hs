{-
Tock: a compiler for parallel languages
Copyright (C) 2007, 2008, 2009  University of Kent
Copyright (C) 2011  Adam Sampson <ats@offog.org>

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

-- #ignore-exports

-- | Currently contains tests just for the transformWaitFor pass that is run for the C backend.
module BackendPassesTest (qcTests) where

import Control.Monad.State
import Data.Generics (Data)
import qualified Data.Map as Map
import Test.HUnit hiding (State)
import Test.QuickCheck

import qualified AST as A
import BackendPasses
import CompState
import Metadata
import Pattern
import TagAST
import TestFramework
import TestUtils
import TreeUtils
import Types
import Utils

m :: Meta
m = emptyMeta

timerName :: A.Name
timerName = simpleName "rain_timer"

waitFor :: A.Expression -> A.Process -> A.Alternative
waitFor e body = A.Alternative emptyMeta (A.True emptyMeta) (A.Variable emptyMeta timerName) (A.InputTimerFor emptyMeta e)
    body

waitUntil :: A.Expression -> A.Process -> A.Alternative
waitUntil e body = A.Alternative emptyMeta (A.True emptyMeta) (A.Variable emptyMeta timerName) (A.InputTimerAfter emptyMeta e)
    body

mWaitUntil :: (Data a, Data b) => a -> b -> Pattern
mWaitUntil e body = mAlternative (A.True emptyMeta) (mVariable timerName) (mInputTimerAfter e) body

mGetTime :: Pattern -> Pattern
mGetTime v = mInput (mVariable timerName) (mInputTimerRead $ mInVariable v)

-- | Test WaitUntil guard (should be unchanged)
testTransformWaitFor0 :: Test
testTransformWaitFor0 = TestCase $ testPass "testTransformWaitFor0" orig transformWaitFor orig (return ())
  where
    orig = A.Alt m True $ A.Only m $ waitUntil (exprVariable "t") (A.Skip m)
    
-- | Test pulling out a single WaitFor:
testTransformWaitFor1 :: Test
testTransformWaitFor1 = TestCase $ testPass "testTransformWaitFor1" exp transformWaitFor orig (return ())
  where
    orig = A.Alt m True $ A.Only m $ waitFor (exprVariable "t") (A.Skip m)
    exp = tag2 A.Seq DontCare $ mSpecP (tag3 A.Specification DontCare varName $ A.Declaration m A.Time) $
            mSeveralP
              [
                mOnlyP $ mGetTime var
                ,mOnlyP $ mAssign [var] $ mExpressionList
                  [mFunctionCall (A.Name m $ occamDefaultOperator "PLUS" [A.Int, A.Int]) [evar, exprVariablePattern "t"]]
                ,mOnlyP $ tag3 A.Alt DontCare True $ mOnlyA $ mWaitUntil evar (A.Skip m)
              ]
    varName = (tag2 A.Name DontCare $ Named "nowt" DontCare)
    var = tag2 A.Variable DontCare varName
    evar = tag2 A.ExprVariable DontCare var

-- | Test pulling out two WaitFors:
testTransformWaitFor2 :: Test
testTransformWaitFor2 = TestCase $ testPass "testTransformWaitFor2" exp transformWaitFor orig (return ())
  where
    orig = A.Alt m True $ A.Several m [A.Only m $ waitFor (exprVariable "t0") (A.Skip m),
                                       A.Only m $ waitFor (exprVariable "t1") (A.Skip m)]
    exp = tag2 A.Seq DontCare $ mSpecP (tag3 A.Specification DontCare varName0 $ A.Declaration m A.Time) $
          mSpecP (tag3 A.Specification DontCare varName1 $ A.Declaration m A.Time) $
            mSeveralP
              [
                mOnlyP $ mGetTime var0
                ,mOnlyP $ mAssign [var0] $ mExpressionList [mFunctionCall (A.Name m $ occamDefaultOperator
                  "PLUS" [A.Int, A.Int]) [evar0, exprVariablePattern "t0"]]
                ,mOnlyP $ mGetTime var1
                ,mOnlyP $ mAssign [var1] $ mExpressionList [mFunctionCall (A.Name m $ occamDefaultOperator
                  "PLUS" [A.Int, A.Int]) [evar1, exprVariablePattern "t1"]]
                ,mOnlyP $ tag3 A.Alt DontCare True $ mSeveralA
                  [mOnlyA $ mWaitUntil evar0 (A.Skip m)
                  ,mOnlyA $ mWaitUntil evar1 (A.Skip m)]
              ]
    varName0 = (tag2 A.Name DontCare $ Named "nowt0" DontCare)
    var0 = tag2 A.Variable DontCare varName0
    evar0 = tag2 A.ExprVariable DontCare var0
    varName1 = (tag2 A.Name DontCare $ Named "nowt1" DontCare)
    var1 = tag2 A.Variable DontCare varName1
    evar1 = tag2 A.ExprVariable DontCare var1

-- | Test pulling out a single WaitFor with an expression:
testTransformWaitFor3 :: Test
testTransformWaitFor3 = TestCase $ testPass "testTransformWaitFor3" exp transformWaitFor orig (return ())
  where
    orig = A.Alt m True $ A.Only m $ waitFor (A.FunctionCall m (A.Name emptyMeta
      $ occamDefaultOperator "PLUS" [A.Int, A.Int]) [exprVariable "t0", exprVariable "t1"]) (A.Skip m)
    exp = tag2 A.Seq DontCare $ mSpecP (tag3 A.Specification DontCare varName $ A.Declaration m A.Time) $
            mSeveralP
              [
                mOnlyP $ mGetTime var
                ,mOnlyP $ tag3 A.Assign DontCare [var] $ tag2 A.ExpressionList DontCare
                   [mFunctionCall (A.Name m $ occamDefaultOperator "PLUS" [A.Int, A.Int])
                     [evar
                     ,mFunctionCall (A.Name m $ occamDefaultOperator "PLUS" [A.Int, A.Int])
                       [exprVariable "t0", exprVariable "t1"]]]
                ,mOnlyP $ tag3 A.Alt DontCare True $ mOnlyA $ mWaitUntil evar (A.Skip m)
              ]
    varName = (tag2 A.Name DontCare $ Named "nowt" DontCare)
    var = tag2 A.Variable DontCare varName
    evar = tag2 A.ExprVariable DontCare var

-- | Test pulling out a single WaitFor with some slight nesting in the ALT:
testTransformWaitFor4 :: Test
testTransformWaitFor4 = TestCase $ testPass "testTransformWaitFor4" exp transformWaitFor orig (return ())
  where
    orig = A.Alt m True $ A.Several m [A.Only m $ waitFor (exprVariable "t") (A.Skip m)]
    exp = tag2 A.Seq DontCare $ mSpecP (tag3 A.Specification DontCare varName $ A.Declaration m A.Time) $
            mSeveralP
              [
                mOnlyP $ mGetTime var
                ,mOnlyP $ tag3 A.Assign DontCare [var] $ tag2 A.ExpressionList DontCare
                  [mFunctionCall (A.Name m $ occamDefaultOperator "PLUS" [A.Int, A.Int]) [evar, exprVariablePattern "t"]]
                ,mOnlyP $ tag3 A.Alt DontCare True $ mSeveralA
                  [mOnlyA $ mWaitUntil evar (A.Skip m)]
              ]
    varName = (tag2 A.Name DontCare $ Named "nowt" DontCare)
    var = tag2 A.Variable DontCare varName
    evar = tag2 A.ExprVariable DontCare var

-- | Test pulling out two WaitFors that use the same variable:
testTransformWaitFor5 :: Test
testTransformWaitFor5 = TestCase $ testPass "testTransformWaitFor5" exp transformWaitFor orig (return ())
  where
    orig = A.Alt m True $ A.Several m [A.Only m $ waitFor (exprVariable "t") (A.Skip m),
                                       A.Only m $ waitFor (exprVariable "t") (A.Skip m)]
    exp = tag2 A.Seq DontCare $ mSpecP (tag3 A.Specification DontCare varName0 $ A.Declaration m A.Time) $
          mSpecP (tag3 A.Specification DontCare varName1 $ A.Declaration m A.Time) $
            mSeveralP
              [
                mOnlyP $ mGetTime var0
                ,mOnlyP $ tag3 A.Assign DontCare [var0] $ tag2 A.ExpressionList DontCare
                  [mFunctionCall (A.Name m $ occamDefaultOperator "PLUS" [A.Int, A.Int]) [evar0, exprVariablePattern "t"]]
                ,mOnlyP $ mGetTime var1
                ,mOnlyP $ tag3 A.Assign DontCare [var1] $ tag2 A.ExpressionList DontCare
                  [mFunctionCall (A.Name m $ occamDefaultOperator "PLUS" [A.Int, A.Int]) [evar1, exprVariablePattern "t"]]
                ,mOnlyP $ tag3 A.Alt DontCare True $ mSeveralA
                  [mOnlyA $ mWaitUntil evar0 (A.Skip m)
                  ,mOnlyA $ mWaitUntil evar1 (A.Skip m)]
              ]
    varName0 = (tag2 A.Name DontCare $ Named "nowt0" DontCare)
    var0 = tag2 A.Variable DontCare varName0
    evar0 = tag2 A.ExprVariable DontCare var0
    varName1 = (tag2 A.Name DontCare $ Named "nowt1" DontCare)
    var1 = tag2 A.Variable DontCare varName1
    evar1 = tag2 A.ExprVariable DontCare var1

newtype PosInts = PosInts [Int] deriving (Show)

instance Arbitrary PosInts where
  arbitrary = do len <- choose (1, 10)
                 replicateM len (choose (1,1000)) >>* PosInts

newtype PosInt = PosInt Int deriving (Show)

instance Arbitrary PosInt where
  arbitrary = choose (1,20) >>* PosInt

newtype StaticTypeList = StaticTypeList [A.Type] deriving (Show)

instance Arbitrary StaticTypeList where
  arbitrary = do len <- choose (1,10)
                 tl <- replicateM len $ frequency
                   [ (10, return A.Int)
                   , (10, return A.Byte)
                   , (20, do len <- choose (1,5)
                             ns <- replicateM len $ choose (1,1000)
                             t <- oneof [return A.Int, return A.Byte]
                             return $ A.Array (map dimension ns) t)
                   ]
                 return $ StaticTypeList tl

newtype DynTypeList = DynTypeList [A.Type] deriving (Show)

instance Arbitrary DynTypeList where
  arbitrary = do len <- choose (1,10)
                 tl <- replicateM len $ frequency
                   [ (10, return A.Int)
                   , (10, return A.Byte)
                   , (20, do len <- choose (1,5)
                             ds <- replicateM len $ oneof
                               [choose (1,1000) >>* dimension
                               ,return A.UnknownDimension]
                             t <- oneof [return A.Int, return A.Byte]
                             return $ A.Array ds t)
                   ]
                 return $ DynTypeList tl

-- types of thing being abbreviated, types of abbreviation, subscripts
newtype AbbrevTypesIs = AbbrevTypesIs ([A.Dimension], [A.Dimension], [A.Subscript]) deriving (Show)

instance Arbitrary AbbrevTypesIs where
  arbitrary = do lenSrc <- choose (1,10)
                 lenDest <- choose (1, lenSrc)
                 srcDims <- replicateM lenSrc $ oneof [return A.UnknownDimension, choose (1,1000) >>* dimension]
                 destDims <- flip mapM (take lenDest srcDims) $ \d ->
                   case d of
                     A.UnknownDimension -> return A.UnknownDimension
                     _ -> oneof [return d, return A.UnknownDimension]
                 subs <- replicateM (length srcDims - length destDims) $ return $ A.Subscript emptyMeta A.NoCheck (A.True emptyMeta)
                 return $ AbbrevTypesIs (srcDims, destDims, subs)

qcTestDeclareSizes :: [LabelledQuickCheckTest]
qcTestDeclareSizes =
  [
   ("Test Adding _sizes For Declarations", scaleQC (20, 100, 500, 1000) (runQCTest . testFoo 0 . declFoo . \(PosInts xs) -> xs))
  ,("Test Adding _sizes For IsChannelArray", scaleQC (20, 100, 500, 1000) (runQCTest . testFoo 1 . isChanArrFoo . \(PosInt x) -> x))
  ,("Test Adding _sizes For RecordType", scaleQC (20, 100, 500, 1000) (runQCTest . testRecordFoo 2 . \(StaticTypeList ts) -> ts))

  ,("Test Adding _sizes For Is", scaleQC (20, 100, 500, 1000)
    (\(AbbrevTypesIs dds@(_,dds',_)) -> A.UnknownDimension `elem` dds' ==> (runQCTest $ testFoo 3 $ isIsFoo dds)))

  ,("Test Adding _sizes For IsExpr (static)", scaleQC (20, 100, 500, 1000) (runQCTest . testFoo 4 . isExprStaticFoo . \(PosInts xs) -> xs))
   --TODO add tests for dynamic IsExpr
   --TODO test reshapes/retypes abbreviations (and add checks)
  ]
  where
    -- spectype of foo, spectype of foo_sizes
    testFoo :: TestMonad m r => Int -> (A.SpecType, A.SpecType, State CompState ()) -> m ()
    testFoo n (fooSpec, fooSizesSpec, st) = test n
      (strFooSizes $ strFoo term)
      (strFoo term) st (checkFooSizes fooSizesSpec)
      where
        strFoo :: Data a => A.Structured a -> A.Structured a
        strFoo = A.Spec emptyMeta (A.Specification emptyMeta (simpleName "foo") fooSpec)
        strFooSizes :: Data a => A.Structured a -> A.Structured a
        strFooSizes = A.Spec emptyMeta (A.Specification emptyMeta (simpleName "foo_sizes") fooSizesSpec)

    isChanArrFoo :: Int -> (A.SpecType, A.SpecType, State CompState ())
    isChanArrFoo n = (A.Is emptyMeta A.Abbrev (A.Array [dimension n] $ A.Chan (A.ChanAttributes A.Unshared A.Unshared) A.Byte)
      (A.ActualChannelArray $ replicate n $ variable "c")
                     ,valSize [makeConstant emptyMeta n], return ())

    isIsFoo :: ([A.Dimension], [A.Dimension], [A.Subscript]) -> (A.SpecType, A.SpecType, State CompState ())
    isIsFoo (srcDims, destDims, subs)
      = (A.Is emptyMeta A.Abbrev (A.Array destDims A.Byte) $ A.ActualVariable
          (foldr (A.SubscriptedVariable emptyMeta) (variable "src") subs)
        ,specSizes, defSrc)
      where
        specSizes = A.Is emptyMeta A.ValAbbrev (A.Array [dimension $ length destDims] A.Int) $
          A.ActualExpression $ A.ExprVariable m $
            A.SubscriptedVariable emptyMeta (A.SubscriptFromFor emptyMeta
              A.NoCheck
              (intLiteral $ toInteger $ length srcDims - length destDims)
              (intLiteral $ toInteger $ length destDims)
              ) (variable "src_sizes")
        defSrc = do defineTestName "src" (A.Declaration emptyMeta (A.Array srcDims A.Byte)) A.Original
                    defineTestName "src_sizes" (A.Is emptyMeta A.ValAbbrev (A.Array srcDims A.Byte)
                      $ A.ActualExpression dummyExpr) A.ValAbbrev
        dummyExpr = A.True emptyMeta

    testRecordFoo :: forall m r. TestMonad m r => Int -> [A.Type] -> m ()
    -- Give fields arbitrary names (for testing), then check that all ones that are array types
    -- do get _sizes array (concat of array name, field name and _sizes)
    testRecordFoo n ts = test n
      (declRecord fields $ flip (foldr declSizeItems) (reverse fields) term)
      (declRecord fields term) (return ()) (sequence_ . flip applyAll (map checkSizeItems fields))
      where
        fields =  (zip ["x_" ++ show n | n <- [(0::Integer)..]] ts)
        
        declRecord :: Data a => [(String, A.Type)] -> A.Structured a -> A.Structured a
        declRecord fields = A.Spec emptyMeta (A.Specification emptyMeta (simpleName "foo") fooSpec)
          where
            fooSpec = A.RecordType emptyMeta (A.RecordAttr False False) (map (\(n,t) -> (simpleName n, t)) fields)
        
        declSizeItems :: Data a => (String, A.Type) -> A.Structured a -> A.Structured a
        declSizeItems (n, A.Array ds _) = A.Spec emptyMeta (A.Specification emptyMeta (simpleName $ "foo" ++ n) $
          valSize $ map (\(A.Dimension n) -> n) ds)
        declSizeItems _ = id
        
        checkSizeItems :: (String, A.Type) -> CompState -> m ()
        checkSizeItems (n, A.Array ds _) = checkName ("foo" ++ n) (valSize $ map (\(A.Dimension n) -> n) ds) A.ValAbbrev
        checkSizeItems _ = const (return ())

    isExprStaticFoo :: [Int] -> (A.SpecType, A.SpecType, State CompState ())
    isExprStaticFoo ns = (A.Is emptyMeta A.ValAbbrev t $ A.ActualExpression (A.True emptyMeta), valSize (map (makeConstant emptyMeta) ns), return ())
      where
        t = A.Array (map dimension ns) A.Byte

    declFoo :: [Int] -> (A.SpecType, A.SpecType, State CompState ())
    declFoo ns = (A.Declaration emptyMeta t, valSize (map (makeConstant emptyMeta) ns), return ())
      where
        t = A.Array (map dimension ns) A.Byte

    valSize :: [A.Expression] -> A.SpecType
    valSize ds = A.Is emptyMeta A.ValAbbrev (A.Array [dimension $ length ds] A.Int)
      $ A.ActualExpression $ makeSizesLiteral ds

    makeSizesLiteral :: [A.Expression] -> A.Expression
    makeSizesLiteral xs = A.Literal emptyMeta (A.Array [dimension $ length xs] A.Int) $
      A.ArrayListLiteral emptyMeta $ A.Several emptyMeta $ map (A.Only emptyMeta) xs
    
    checkFooSizes :: TestMonad m r => A.SpecType -> CompState -> m ()
    checkFooSizes sp = checkName "foo_sizes" sp A.ValAbbrev

    term = A.Only emptyMeta ()
    
    test :: TestMonad m r => Int -> A.Structured () -> A.Structured () -> State CompState () -> (CompState -> m ()) -> m ()
    test n exp inp st chk = testPassWithStateCheck label exp declareSizesArray inp st chk
      where
        label = "testDeclareSizes " ++ show n


defineTestName :: String -> A.SpecType -> A.AbbrevMode -> State CompState ()
defineTestName n sp am
  = defineName (simpleName n) $ A.NameDef {
          A.ndMeta = emptyMeta
         ,A.ndName = n
         ,A.ndOrigName = n
         ,A.ndSpecType = sp
         ,A.ndAbbrevMode = am
         ,A.ndNameSource = A.NameUser
         ,A.ndPlacement = A.Unplaced
         }

checkName :: TestMonad m r => String -> A.SpecType -> A.AbbrevMode -> CompState -> m ()
checkName n spec am cs
      = do nd <- case Map.lookup n (csNames cs) of
             Just nd -> return nd
             Nothing -> testFailure ("Could not find " ++ n) >> return undefined
           testEqual "ndName" n (A.ndName nd)
           testEqual "ndOrigName" n (A.ndOrigName nd)
           testEqual "ndSpecType" spec (A.ndSpecType nd)
           testEqual "ndAbbrevMode" am (A.ndAbbrevMode nd)

{-
qcTestSizeParameters :: [LabelledQuickCheckTest]
qcTestSizeParameters =
  [
    ("Test Adding _sizes parameters to PROC formals (static)", scaleQC (20, 100, 500, 1000) (runQCTest . testFormal . \(StaticTypeList ts) -> ts))
   ,("Test Adding _sizes parameters to PROC actuals (static)", scaleQC (20, 100, 500, 1000) (runQCTest . testActual . \(StaticTypeList ts) -> ts))
   ,("Test Adding _sizes parameters to PROC formals (dynamic)", scaleQC (20, 100, 500, 1000) (runQCTest . testFormal . \(DynTypeList ts) -> ts))
   ,("Test Adding _sizes parameters to PROC actuals (dynamic)", scaleQC (20, 100, 500, 1000) (runQCTest . testActual . \(DynTypeList ts) -> ts))
  ]
  where
    -- TODO need to test both with dynamically sized arrays
  
    testActual :: TestMonad m r => [A.Type] -> m ()
    testActual ts = testPassWithStateCheck "qcTestSizeParameters Actual"
      (procCall "p" $ argsWithSizes ts)
      addSizesActualParameters (procCall "p" $ args ts)
      (do recordProcDef $ args ts
          recordProcFormals $ args ts)
      (const $ return ())

    args ts = [(Left $ "x" ++ show n, t, A.Abbrev) | (n, t) <- zip [(0::Integer)..] ts]
    argsWithSizes ts = concat [
          case t of
            (A.Array ds _) -> [(Left $ "x" ++ show n, t, A.Abbrev), (Right $ "x" ++ show n, A.Array [dimension $ length ds] A.Int, A.ValAbbrev)]
            _ -> [(Left $ "x" ++ show n, t, A.Abbrev)]
          | (n, t) <- zip [(0::Integer)..] ts]

    testFormal :: TestMonad m r => [A.Type] -> m ()
    testFormal ts = testPassWithStateCheck "qcTestSizeParameters Formal"
      (wrapSpec "p" $ makeProcDef $ argsWithSizes ts)
      addSizesFormalParameters (wrapSpec "p" $ makeProcDef $ args ts)
      (do recordProcDef $ args ts
          recordProcFormals $ args ts)
      (\x -> do checkProcDef (argsWithSizes ts) x
                checkProcFormals (argsWithSizes ts) x)
    
    makeProcDef :: [(Either String String, A.Type, A.AbbrevMode)] -> A.SpecType
    makeProcDef nts = A.Proc emptyMeta (A.PlainSpec, A.PlainRec)
      [A.Formal am t $ simpleName $ either id (++"_sizes") n | (n, t, am) <- nts] (A.Skip emptyMeta)
    
    recordProcDef :: [(Either String String, A.Type, A.AbbrevMode)] -> State CompState ()
    recordProcDef nts = defineTestName "p" (makeProcDef nts) A.Original
    
    recordProcFormals :: [(Either String String, A.Type, A.AbbrevMode)] -> State CompState ()
    recordProcFormals = mapM_ rec
      where
        rec :: (Either String String, A.Type, A.AbbrevMode) -> State CompState ()
        rec (n, t, am) = defineTestName (either id (++"_sizes") n) (A.Declaration emptyMeta t) am

    checkProcDef :: TestMonad m r => [(Either String String, A.Type, A.AbbrevMode)] -> CompState -> m ()
    checkProcDef nts cs = checkName "p" (makeProcDef nts) A.Original cs

    checkProcFormals :: TestMonad m r => [(Either String String, A.Type, A.AbbrevMode)] -> CompState -> m ()
    checkProcFormals nts cs = mapM_ (\(n,t,am) -> checkName (either id (++"_sizes") n) (A.Declaration emptyMeta t) am cs) nts

    wrapSpec :: String -> A.SpecType -> A.Structured ()
    wrapSpec n spec = A.Spec emptyMeta (A.Specification emptyMeta (simpleName n) spec) (A.Only emptyMeta ())
    
    procCall :: String -> [(Either String String, A.Type, A.AbbrevMode)] -> A.Process
    procCall p nts = A.ProcCall emptyMeta (simpleName p)
      [case en of
        Left n -> A.ActualVariable (variable n)
        Right n -> A.ActualExpression $ A.AllSizesVariable emptyMeta $ variable n
      | (en, _, _) <- nts]
-}
---Returns the list of tests:
qcTests :: (Test, [LabelledQuickCheckTest])
qcTests = (TestLabel "BackendPassesTest" $ TestList
 [
   testTransformWaitFor0
  ,testTransformWaitFor1
  ,testTransformWaitFor2
  ,testTransformWaitFor3
  ,testTransformWaitFor4
  ,testTransformWaitFor5
 ]
 ,qcTestDeclareSizes {- ++ qcTestSizeParameters -})


