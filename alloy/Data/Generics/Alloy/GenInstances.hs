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

-- | A module containing code to generate instances of the Polyplate classes for
-- you.
--
-- Generating Polyplate instances by hand would be laborious, complex and error-prone.
--  This module provides a way, based on the Scrap Your Boilerplate ("Data.Generics")
-- generics that have built-in support in GHC.  So you should just need to add
--
-- > deriving (Data, Typeable)
--
-- after all your data-types, then use the functions in this module to generate
-- some Haskell code with instances of the Polyplate classes.  The simplest functions
-- for doing this are 'writeInstances' and 'writeInstancesTo'.
--
-- You do not even have to modify the definitions of your data-types if you are
-- using GHC 6.8.2 or later, you can simply add these lines in your module for
-- generating the instances (assuming the data-type is not hidden during import):
--
-- > deriving instance Typeable Foo
-- > deriving instance Data Foo
module Data.Generics.Alloy.GenInstances
  (GenOverlappedOption(..), GenClassOption(..),
   GenInstance, genInstance, genMapInstance, genSetInstance, genInstances,
   writeInstances, writeInstancesTo) where

import Control.Monad.State
import Data.Char
import Data.Generics
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set

-- | The option controlling whether the generated instances can be overlapped.
--  If you choose 'GenWithOverlapped' many less instances (around half, in Tock)
-- will be generated, but you must enable the overlapping-instances flag in GHC
-- (-XOverlappingInstances in GHC 6.8 and 6.10) when compiling the instances.
data GenOverlappedOption = GenWithOverlapped | GenWithoutOverlapped
  deriving (Eq)

-- | The option controlling whether the generated instances have one class per
-- type, or just generate instances of the primary Alloy class.  Having one
-- class per type compiles faster on GHC, but can give less clear error messages
-- due to the name munging that goes on.
data GenClassOption
  = GenClassPerType
  | GenOneClass
  | GenSlowDelegate -- ^ This is only for benchmarking purposes.  Do not use.
  deriving (Eq)

-- | A default name munging scheme for use with GenClassPerType.  Munges special
-- characters into their ASCII (or is it UTF?) code determined by ord,
-- prefixed by two underscores.
--
-- Given a string with a type name, such as "Map Int (Maybe ([String],Bool))"
-- this function must munge it into a valid suffix for a Haskell identifier,
-- i.e. using only alphanumeric characters, apostrophe and underscore.
-- Also, there may be type-level operators such as "->".  I was going to let users
-- override this, but any user that creates type like Foo__32Bar gets what they
-- deserve.
mungeName :: String -> String
mungeName = concatMap munge
  where
    munge :: Char -> String
    munge x
      | isAlphaNum x = [x]
      | otherwise = "__" ++ show (ord x)

-- | A type that represents a generator for instances of a set of types.
newtype GenInstance = GenInstance (TypeMapM ())

-- | Generates instances for all types within the given type.  Therefore you should
-- only need one or two of these calls to cover all of a complex data structure,
-- by calling this on the largest types in your structure.  The function is non-strict
-- in its argument, so the easiest way to call it is:
--
-- > genInstance (undefined :: MyType)
genInstance :: Data t => t -> GenInstance
genInstance = GenInstance . findTypesIn

data Witness
  = Plain { witness :: DataBox }
    | Detailed { witness :: DataBox
               , _directlyContains :: [DataBox]
               -- First is funcSameType, second is funcNewType:
               , _processChildrenMod :: (Bool -> String, Bool -> String) -> [String]
               }

-- The Eq instance is based on the inner type.
instance Eq Witness where
  (==) wx wy = case (witness wx, witness wy) of
    (DataBox x, DataBox y) -> typeOf x == typeOf y

funcPlain :: Bool -> String
funcPlain True = "return"
funcPlain False = "pure"

funcAp :: Bool -> String
funcAp True = "`ap`"
funcAp False = "<*>"

funcTraverse :: Bool -> String
funcTraverse True = "T.mapM"
funcTraverse False = "T.traverse"

-- | Generates an instance for the 'Data.Map.Map' type.  Map is a difficult type
-- because its instance of Data hides its implementation, so we can't actually
-- use the Data instance to work out what the children are (as we can do for other
-- algebraic data types).  So for every different Map that you want to process
-- (or that you have inside other types you want to process), you must also call
-- this function to effectively notify the generation-functions of the existence
-- of your map.  We wish there was an easier, non-hacky way but we can't see one.
genMapInstance :: forall k v. (Ord k, Data k, Data v) => k -> v -> GenInstance
genMapInstance k v
  = GenInstance $ do
       -- Must find types for contained types, in case they are not generated elsewhere.
       --  This is true for Tock, where NameDefs only exist in AST or CompState
       -- in a Map.
       findTypesIn (k, v) -- This does types in k and v, and their pairing
       tk <- liftIO $ typeKey m
       modify (Map.insert tk (show $ typeOf m,
         Detailed (DataBox m) [DataBox (k, v), DataBox k, DataBox v]
         (\(funcSameType, funcNewType) -> concat [
           [funcSameType b ++ " _ ops (v, r) = let mns = zip (Map.toList v) (map ((r @->) . routeDataMap) [0..]) in"
           ,"  " ++ funcPlain b ++ " Map.fromList " ++ funcAp b
             ++ " (" ++ funcTraverse b ++ " (" ++ funcNewType b ++ " ops BaseOpARoute) mns)"
           ]
           | b <- [True, False]])
         ))
  where
    m :: Map k v
    m = undefined

-- | Generates an instance for the 'Data.Set.Set' type.  See 'genMapInstance' for
-- an explanation.
genSetInstance :: forall a. (Ord a, Data a) => a -> GenInstance
genSetInstance x
  = GenInstance $ do
       -- Must find types for contained types, in case they are not generated elsewhere.
       findTypesIn x
       tk <- liftIO $ typeKey s
       modify (Map.insert tk (show $ typeOf s,
         Detailed (DataBox s) [DataBox x]
         (\(funcSameType, funcNewType) -> concat [
           [funcSameType b ++ " _ ops (v, r) = let sns = zip (Set.toList v) (map ((r @->) . routeDataSet) [0..]) in"
           ,"  " ++ funcPlain b ++ " Set.fromList " ++ funcAp b
             ++ " (" ++ funcTraverse b ++ " (" ++ funcNewType b ++ " ops BaseOpARoute) sns)"
           ] | b <- [True, False]])

        ))
  where
    s :: Set a
    s = undefined

    
-- Explanation of Alloy's instances:
--
-- Alloy is a type-class system for automatically applying generic transformations
-- to the first instance of a specific type in a large data structure.
--
-- A set of operations is represented as a tuple list, e.g.
--
-- > (a -> m a, (b -> m b, (c -> m c, ())))
--
-- The unit type is the list terminator.
--
-- The Alloy class takes four parameters:
--
-- * The first is the type currently being processed.
--
-- * The second is the list of operations still to be checked against the current type.
--
-- * The third is the list of operations to be applied if we end up processing
-- the current type's children.
--
-- * The fourth is the monad in which it operates, which is just passed through.
--
-- There are broadly four types of instance generated by this module:
-- 
-- * The "exact match" instance.  These are of the form:
-- 
-- > instance Monad m => AlloyA a (a -> m a, r) ops m where
-- >   transformM (f,_) _ v = f v
-- 
-- This just applies the transformation directly, as you can see, ignoring the
-- other bits and bobs.
-- 
-- * The "process children" instance.  For a data type:
--
-- > data Foo = ConstrBar Bar | ConstrBazQuux Baz Quux
--
-- This is of the form:
-- 
-- > instance (Monad m,
-- >           AlloyA Bar (f,ops) () m,
-- >           AlloyA Baz (f,ops) () m,
-- >           AlloyA Quux (f,ops) () m) =>
-- >         AlloyA Foo () (f, ops) m where
-- >  transformM () ops (ConstrBar a0)
-- >    = do r0 <- transformM ops () a0
-- >         return (ConstrBar r0)
-- >  transformM () ops (ConstrBazQuux a0 a1)
-- >    = do r0 <- transformM ops () a0
-- >         r1 <- transformM ops () a1
-- >         return (ConstrBazQuux r0 r1)
--
-- The reason for using (f, ops) in the type-class header is to distinguish this
-- from the empty set of operations (see lower down).  The operations that are
-- to be applied on descent (the third parameter) are passed to the sub-instances
-- as the list of operations to be checked (the second parameter), with a new blank
-- list of operations to apply on descent.  The bodies of the methods just apply
-- transformM to each child of the constructor, and pull the data-type back together
-- again.
--
--
-- * The "can contain" instance.  This is of the form:
--
-- > instance (Monad m, AlloyA t r (a -> m a, ops) m) =>
-- >         AlloyA t (a -> m a, r) ops m where
-- >  transformM (f, rest) ops v = transformM rest (f, ops) v
--
-- Here, the type being considered, t, /can/ contain the type referred to by the
-- operation, a.  So we transfer the operation from the list we're processing onto
-- the list to apply in case of direct recursion.  Then we continue processing
-- the list of operations.
--
-- * The "cannot contain" instance.  This is of the form:
--
-- > instance (Monad m, AlloyA t r ops m) =>
-- >         AlloyA t (a -> m a, r) ops m where
-- >  transformM (_, rest) ops v = transformM rest ops v
--
-- This instance is based on the logic that if we have worked out that a big type
-- (like Foo) cannot contain a certain type (say, String) then by implication,
-- neither of its children can contain Strings either.  So we omit the transformation
-- of the type (in this example String) when we directly descend into Foo, by not
-- copying the transformation onto the third parameter.
--
-- The final thing we need, is a base case
-- for when both the second and third parameters are empty.  This means there are
-- no operations left to examine, but also none available for direct recursion.
-- At this point we just return the value unchanged.


-- | Instances for a particular data type (i.e. where that data type is the
-- first argument to 'Alloy').
instancesFrom :: forall t. Data t => GenOverlappedOption -> GenClassOption -> [Witness] -> t -> IO [String]
instancesFrom genOverlapped genClass boxes w
    = do (specialProcessChildren, containedTypes) <-
           case find (== Plain (DataBox w)) boxes of
             Just (Detailed _ containedTypes doChildren) ->
               -- It's a special case, use the detailed info:
               do eachContained <- sequence [findTypesIn' c | DataBox c <- containedTypes]
                  return (Just (containedTypes, doChildren), foldl Map.union Map.empty eachContained)
             -- It's a normal case, use findTypesIn' directly:
             _ -> do ts <- findTypesIn' w
                     return (Nothing, ts)
         containedKeys <- liftM Set.fromList
           (sequence [typeKey c | DataBox c <- map witness $ justBoxes containedTypes])
         wKey <- typeKey w
         otherInsts <- sequence [do ck <- typeKey c
                                    return (otherInst wKey containedKeys c ck)
                                | DataBox c <- map witness boxes]
         return $ baseInst specialProcessChildren ++ concat otherInsts
  where
    wName = show $ typeOf w
    wMunged = mungeName wName
    wDType = dataTypeOf w
    wCtrs = if isAlgType wDType then dataTypeConstrs wDType else []

    -- The module prefix of this type, so we can use it in constructor names.
    modPrefix
        = if '.' `elem` (takeWhile (\c -> isAlphaNum c || c == '.') wName)
            then takeWhile (/= '.') wName ++ "."
            else ""

    ctrArgs ctr
        = gmapQ DataBox (fromConstr ctr :: t)
    ctrArgTypes types
        = [show $ typeOf w | DataBox w <- types]

    -- Given the context (a list of instance requirements), the left-hand ops,
    -- the right-hand ops, and a list of lines for the body of the class, generates
    -- an instance.
    --
    -- For GenOneClass this will be an instance of AlloyA.
    --
    -- For GenClassPerType this will be an instance of AlloyAFoo (or whatever)
    --
    -- For GenSlowDelegate this will be an instance of AlloyA', with the first
    -- and last arguments swapped.
    genInst :: [String] -> String -> String -> [String] -> [String]
    genInst context ops0 ops1 body
      = ["instance (" ++ concat (intersperse ", " context) ++ ") =>"
        ,"         " ++ contextSameType ops0 ops1 ++ " where"
        ] ++ map ("  " ++) body

    -- Generates the name of an instance for the same type with the given two ops
    -- sets.  The class name will be the same as genInst.
    contextSameType :: String -> String -> String
    contextSameType ops0 ops1 = case genClass of
      GenOneClass -> "AlloyARoute (" ++ wName ++ ") " ++ ops0 ++ " " ++ ops1
      GenClassPerType -> "AlloyARoute" ++ wMunged ++" " ++ ops0 ++ " " ++ ops1
      GenSlowDelegate -> "AlloyARoute' " ++ ops0 ++ " " ++ ops1 ++ " (" ++ wName ++ ")"

    -- Generates the name of an instance for a different type (for processing children).
    --  This will be AlloyA or AlloyA'.
    contextNewType :: String -> String -> String -> String
    contextNewType cName ops0 ops1 = case genClass of
      GenOneClass -> "AlloyARoute (" ++ cName ++ ") " ++ ops0 ++ " " ++ ops1
      GenClassPerType -> "AlloyARoute (" ++ cName ++ ") " ++ ops0 ++ " " ++ ops1
      GenSlowDelegate -> "AlloyARoute' " ++ ops0 ++ " " ++ ops1 ++ " (" ++ cName ++ ")"
      

    -- The function to define in the body, and also to use for processing the same
    -- type.
    funcSameType :: Bool -> String
    funcSameType monad = case genClass of
      GenClassPerType -> base ++ wMunged
      GenOneClass -> base
      GenSlowDelegate -> base ++ "'"
      where
        base = if monad then "transformMRoute" else "transformARoute"

    -- The function to use for processing other types
    funcNewType :: Bool -> String
    funcNewType monad = case genClass of
      GenClassPerType -> base
      GenOneClass -> base
      GenSlowDelegate -> base ++ "'"
      where
        base = if monad then "transformMRoute" else "transformARoute"

    -- | An instance that describes what to do when we have no transformations
    -- left to apply.  You can pass it an override for the case of processing children
    -- (and the types that make up the children).
    baseInst :: Maybe ([DataBox], (Bool -> String, Bool -> String) -> [String]) -> [String]
    baseInst mdoChildren
        = concat
          [genInst context "BaseOpARoute" "(f :-@ ops)" $
              maybe
                (concat
                [if isAlgType wDType
                    -- An algebraic type: apply to each child if we're following.
                    then (concatMap (constrCase b) wCtrs)
                    -- A primitive (or non-represented) type: just return it.
                    else [funcSameType b ++ " _ _ (v, _) = " ++ funcPlain b ++ " v"]
                | b <- [True, False]])
                (\(_,f) -> f (funcSameType, funcNewType)) mdoChildren
          ,genInst [] "BaseOpARoute" "BaseOpARoute"
             [funcSameType b ++ " _ _ (v, _) = " ++ funcPlain b ++ " v" | b <- [True, False]]
          ,if genOverlapped == GenWithoutOverlapped then [] else
            genInst
              [ contextSameType "r" "ops" ]
              "(a :-@ r)" "ops" 
                [funcSameType b ++ " (_ :-@ rest) ops vr = " ++ funcSameType b ++ " rest ops vr"
                | b <- [True, False]]
          ,if genClass == GenClassPerType
             then ["class AlloyARoute" ++ wMunged ++ " o o' where"
                  ,"  " ++ funcSameType True ++ " :: Monad m => o m outer -> o' m outer -> (" ++ wName
                    ++ ", Route (" ++ wName ++ ") outer) -> m (" ++ wName ++ ")"
                  ,"  " ++ funcSameType False ++ " :: Applicative a => o a outer -> o' a outer -> (" ++ wName
                    ++ ", Route (" ++ wName ++ ") outer) -> a (" ++ wName ++ ")"
                  ,""
                  ,"instance (" ++ contextSameType "o0" "o1" ++ ") =>"
                  ,"         AlloyARoute (" ++ wName ++ ") o0 o1 where"
                  ,"  transformMRoute = " ++ funcSameType True
                  ,"  transformARoute = " ++ funcSameType False
                  ]
             else []
          ]
      where
        -- | Class context for 'baseInst'.
        -- We need an instance of Alloy for each of the types directly contained within
        -- this type, so we can recurse into them.
        context :: [String]
        context
          = [ contextNewType argType "(f :-@ ops)" "BaseOpARoute"
            | argType <- nub $ sort $ concatMap ctrArgTypes $
                maybe (map ctrArgs wCtrs) ((:[]) . fst) mdoChildren]

    -- | A 'transformM' case for a particular constructor of this (algebraic)
    -- data type: pull the value apart, apply 'transformM' to each part of it,
    -- then stick it back together.
    constrCase :: Bool -> Constr -> [String]
    constrCase b ctr
        = [ funcSameType b ++ " _ " ++ (if argNums == [] then "_" else "ops") ++
            " (" ++ ctrInput ++ " , " ++ (if argNums == [] then "_" else "rt") ++ ")"
          , "    = " ++ funcPlain b ++ " " ++ ctrName
          ] ++
          [ " " ++ funcAp b ++ " (" ++ funcNewType b ++ " ops BaseOpARoute (a" ++ show i
                        ++ ", rt @-> makeRoute [" ++ show i ++ "] "
                        ++ "(\\f (" ++ ctrMod ++ ") -> f b" ++ show i
                        ++ " >>= (\\b" ++ show i ++ " -> return (" ++ ctrMod ++ ")))))"
           | i <- argNums]
      where
        argNums = [0 .. ((length $ ctrArgs ctr) - 1)]
        ctrS = show ctr
        ctrName = modPrefix ++ ctrS
        makeCtr vs = ctrName ++ concatMap (" " ++) vs
        ctrInput = makeCtr ["a" ++ show i | i <- argNums]
        ctrMod = makeCtr ["b" ++ show i | i <- argNums]

    -- | An instance that describes how to apply -- or not apply -- a
    -- transformation.
    otherInst :: Data s => Int -> Set.Set Int -> s -> Int -> [String]
    otherInst wKey containedKeys c cKey
        = if not shouldGen then [] else
            genInst context
                    ("((" ++ cName ++ ") :-@ r)")
                    "ops"
                    impl
      where
        cName = show $ typeOf c
        (shouldGen, context, impl)
          -- This type matches the transformation: apply it.
          | wKey == cKey
            = (True
              ,[]
              ,[funcSameType b ++ " (f :-@ _) _ vr = f vr" | b <- [True, False]])
          -- This type might contain the type that the transformation acts
          -- upon
          | cKey `Set.member` containedKeys
            = (True
              ,[contextSameType "r" ("((" ++ cName ++ ") :-@ ops)")]
              ,[funcSameType b ++ " (f :-@ rest) ops vr = " ++ funcSameType b ++ " rest (f :-@ ops) vr"
               | b <- [True, False]])
          -- This type can't contain the transformed type; just move on to the
          -- next transformation.
          | genOverlapped == GenWithoutOverlapped
            = (True
              ,[contextSameType "r" "ops"]
              ,[funcSameType b ++ " (_ :-@ rest) ops vr = " ++ funcSameType b ++ " rest ops vr"
               | b <- [True, False]])
          -- This is covered by one big overlapping instance:
          | otherwise = (False,[],[])

-- | Generates all the given instances (eliminating any duplicates)
-- with the given options.  The return is a pair of a list of instances of AlloyARoute,
-- and a list of instances of AlloySpine
genInstances :: GenOverlappedOption -> GenClassOption -> [GenInstance] ->
  IO [String]
genInstances op1 op2 insts
  =  do typeMap <- flip execStateT Map.empty (sequence [g | GenInstance g <- insts])
        let inst = [instancesFrom op1 op2 (justBoxes typeMap) w
                   | DataBox w <- map witness $ justBoxes typeMap]
        inst' <- sequence inst
        return $ concat inst'
-- | Generates the instances according to the options and writes it to stdout with
-- the given header (the header is a list of lines without newline characters).
writeInstances :: GenOverlappedOption -> GenClassOption -> [GenInstance] -> [String] -> IO ()
writeInstances op1 op2 inst header
  = do instLines <- genInstances op1 op2 inst
       putStr (unlines (header ++ instLines))

-- | Generates the instances according to the options and writes it to a file with
-- the given header (the header is a list of lines without newline characters).
writeInstancesTo :: GenOverlappedOption -> GenClassOption -> [GenInstance] -> [String]
  -> FilePath -> IO ()
writeInstancesTo op1 op2 inst header fileName
  = do instLines <- genInstances op1 op2 inst
       writeFile fileName (unlines (header ++ instLines))


--{{{ Various SYB-based functions that we don't export, for discovering contained types:

-- | A type that can contain any 'Data' item.
data DataBox = forall t. Data t => DataBox t

type TypeMap = Map Int (String, Witness)
type TypeMapM = StateT TypeMap IO

typeKey :: Typeable t => t -> IO Int
typeKey x = typeRepKey $ typeOf x

findTypesIn' :: Data t => t -> IO TypeMap
findTypesIn' x = execStateT (findTypesIn x) Map.empty

-- | Given a starting value, find all the types that could possibly be inside
-- it.
findTypesIn :: Data t => t -> TypeMapM ()
findTypesIn start = doType start
  where
    doType :: Data t => t -> TypeMapM ()
    doType x
        =  do map <- get
              key <- liftIO $ typeRepKey rep
              when (not $ key `Map.member` map) $
                 do modify $ Map.insert key (reps, Plain (DataBox x))
                    when (isAlgType dtype) $
                      mapM_ doConstr $ dataTypeConstrs dtype
      where
        rep = typeOf x        
        reps = show rep
        dtype = dataTypeOf x

        doConstr :: Constr -> TypeMapM ()
        doConstr ctr
            = sequence_ [doType x' | DataBox x' <- args]
          where
            args = gmapQ DataBox (asTypeOf (fromConstr ctr) x)

-- | Reduce a 'TypeMap' to a list of 'Witness'es, sorted by name.
justBoxes :: TypeMap -> [Witness]
justBoxes = map snd . sortBy (comparing fst) . Map.elems

--}}}
