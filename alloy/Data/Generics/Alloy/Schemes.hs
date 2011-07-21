{-
Tock: a compiler for parallel languages
Copyright (C) 2008, 2009  University of Kent

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


module Data.Generics.Alloy.Schemes where

import Control.Monad.State

import Data.Generics.Alloy
import Data.Generics.Alloy.Route

-- * Adding traversal to modifiers

-- | Given a list of operations and a modifier function, augments that modifier
-- function to first descend into the value before then applying the modifier function.
--  This can be used to perform a bottom-up depth-first traversal of a structure
-- (see 'applyBottomUp').
makeBottomUp :: Alloy t BaseOp opT => opT -> (t -> t) -> t -> t
makeBottomUp ops f v = f (makeDescend ops v)

-- | Given a list of operations and a monadic modifier function, augments that modifier
-- function to first descend into the value before then applying the modifier function.
--  This can be used to perform a bottom-up depth-first traversal of a structure
-- (see 'applyBottomUpM').
makeBottomUpM :: (AlloyA t BaseOpA opT, Monad m) => opT m -> (t -> m t) -> t -> m t
makeBottomUpM ops f v = makeDescendM ops v >>= f

-- | As makeBottomUpM, but with routes as well.
makeBottomUpMRoute :: forall m opT t outer. (Monad m, AlloyARoute t BaseOpARoute opT) =>
  opT m outer -> ((t, Route t outer) -> m t) -> (t, Route t outer) -> m t
makeBottomUpMRoute ops f (v, r)
  = do v' <- transformMRoute base ops (v, r)
       f (v', r)
  where
    base :: BaseOpARoute m outer
    base = baseOpARoute

-- | Given a list of operations and a modifier function, augments that modifier
-- function to first apply the modifier function before then descending into the value.
--  This can be used to perform a top-down depth-first traversal of a structure
-- (see 'applyTopDown').
makeTopDown :: Alloy t BaseOp opT => opT -> (t -> t) -> t -> t
makeTopDown ops f v = makeDescend ops (f v)

-- | Given a list of operations and a monadic modifier function, augments that modifier
-- function to first apply the modifier function before then descending into the value.
--  This can be used to perform a top-down depth-first traversal of a structure
-- (see 'applyTopDownM').
makeTopDownM :: (AlloyA t BaseOpA opT, Monad m) => opT m -> (t -> m t) -> t -> m t
makeTopDownM ops f v = f v >>= makeDescendM ops

-- | As makeTopDownM, but with routes as well.
makeTopDownMRoute :: (AlloyARoute t BaseOpARoute opT, Monad m) =>
  opT m outer -> ((t, Route t outer) -> m t) -> (t, Route t outer) -> m t
makeTopDownMRoute ops f (v, r)
  = do v' <- f (v, r)
       transformMRoute baseOpARoute ops (v', r)



{- TODO
makeCheckM :: AlloyA t () opT m => opT -> (t -> m ()) -> t -> m t
makeCheckM ops f v
    =  do v' <- descend v
          f v'
          return v'
  where
    descend = makeDescend ops
-}

-- * Listify functions that return lists of items that satisfy given criteria

-- | Given a function that examines a type \"s\" and gives an answer (True to include
-- the item in the list, False to drop it), finds all items of type \"s\" in some
-- larger item (of type \"t\") that satisfy this function, listed in depth-first
-- order.
listifyDepth :: (AlloyA t (OneOpA s) BaseOpA
                ,AlloyA s BaseOpA (OneOpA s)) => (s -> Bool) -> t -> [s]
-- We use applyBottomUp because we are prepending to the list.  If we prepend from
-- the bottom up, that's the same as appending from the top down, which is what
-- this function is meant to be doing.
listifyDepth qf = flip execState [] . applyBottomUpM qf'
  where
    qf' x = if qf x then modify (x:) >> return x else return x

-- | Like listifyDepth, but with routes
listifyDepthRoute :: (AlloyARoute t (OneOpARoute s) (BaseOpARoute)
                     ,AlloyARoute s (BaseOpARoute) (OneOpARoute s))
                     => ((s, Route s t) -> Bool) -> t -> [(s, Route s t)]
listifyDepthRoute qf = flip execState [] . applyBottomUpMRoute qf'
  where
    qf' x = if qf x then modify (x:) >> return (fst x) else return (fst x)


-- * Check functions to apply monadic checks throughout a data structure

-- | Given a monadic function that operates on items of type \"s\" (without modifying
-- them), applies the function to all items of types \"s\" within an item of type
-- \"t\", in depth-first order.
--
-- This can be used, for example, to perform checks on items in an error monad,
-- or to accumulate information in a state monad.
checkDepthM :: (Monad m, AlloyA t (OneOpA s) BaseOpA
                       , AlloyA s BaseOpA (OneOpA s)) => (s -> m ()) -> t -> m ()
checkDepthM f x = applyBottomUpM (\x -> f x >> return x) x >> return ()

-- | As 'checkDepthM', but takes two functions (one operating on type \"r\", the
-- other on type \"s\").
checkDepthM2 :: (Monad m, AlloyA t (TwoOpA r s) (BaseOpA)
                        , AlloyA r (BaseOpA) (TwoOpA r s)
                        , AlloyA s (BaseOpA) (TwoOpA r s)
                        ) =>
  (r -> m ()) -> (s -> m ()) -> t -> m ()
checkDepthM2 f g x = applyBottomUpM2 (\x -> f x >> return x)
                                     (\y -> g y >> return y) x >> return ()

-- * Functions to easily apply transformations throughout a data structure

-- | Given a monadic function that applies to a particular type (\"s\"), automatically
-- applies that function to every instance of \"s\" in a larger structure of type \"t\",
-- performing the transformations in a bottom-up fashion.  It does a depth first
-- traversal in order of a constructor's children (assuming you are using one of
-- the generated instances, not your own), descending first and applying the function
-- afterwards on the way back up.
applyBottomUpM :: (AlloyA t (OneOpA s) BaseOpA,
                   AlloyA s BaseOpA (OneOpA s), Monad m) =>
                  (s -> m s) -> t -> m t
applyBottomUpM f = makeRecurseM ops
  where
    ops = makeBottomUpM ops f :-* baseOpA

applyBottomUpMRoute :: forall m s t.
                       (AlloyARoute t (OneOpARoute s) (BaseOpARoute),
                        AlloyARoute s (BaseOpARoute) (OneOpARoute s),
                        Monad m) =>
                       ((s, Route s t) -> m s) -> t -> m t
applyBottomUpMRoute f x = transformMRoute ops baseOpARoute (x, identityRoute)
  where
    ops = makeBottomUpMRoute ops f :-@ baseOpARoute


-- | As 'applyBottomUpM', but applies two functions.  These should not be modifying
-- the same type.
applyBottomUpM2 :: (AlloyA t (TwoOpA sA sB) (BaseOpA),
                    AlloyA sA (BaseOpA) (TwoOpA sA sB),
                    AlloyA sB (BaseOpA) (TwoOpA sA sB),
                    Monad m
                   ) =>
                   (sA -> m sA) -> (sB -> m sB) -> t -> m t
applyBottomUpM2 fA fB = makeRecurseM ops
  where
    ops = makeBottomUpM ops fA :-* makeBottomUpM ops fB :-* baseOpA

-- | As 'applyBottomUpM', but non-monadic.
applyBottomUp :: (Alloy t (OneOp s) BaseOp,
                  Alloy s BaseOp (OneOp s)) =>
                 (s -> s) -> t -> t
applyBottomUp f = makeRecurse ops
  where
    ops = makeBottomUp ops f :- baseOp

-- | As 'applyBottomUpM2', but non-monadic.
applyBottomUp2 :: (Alloy t (TwoOp sA sB) BaseOp,
                  Alloy sA BaseOp (TwoOp sA sB),
                  Alloy sB BaseOp (TwoOp sA sB)) =>
                 (sA -> sA) -> (sB -> sB) -> t -> t
applyBottomUp2 fA fB = makeRecurse ops
  where
    ops = makeBottomUp ops fA :- makeBottomUp ops fB :- baseOp

-- | Given a monadic function that applies to a particular type (\"s\"), automatically
-- applies that function to every instance of \"s\" in a larger structure of type \"t\",
-- performing the transformations in a top-down fashion.  It does a depth first
-- traversal in order of a constructor's children (assuming you are using one of
-- the generated instances, not your own), applying the function first and then
-- descending.
applyTopDownM :: (AlloyA t (s :-* BaseOpA) BaseOpA,
                  AlloyA s BaseOpA (s :-* BaseOpA),
                  Monad m) =>
                 (s -> m s) -> t -> m t
applyTopDownM f = makeRecurseM ops
  where
    ops = makeTopDownM ops f :-* baseOpA

-- | As applyTopDownM, but applies two functions.  These should not be modifying
-- the same type.
applyTopDownM2 :: (AlloyA t (sA :-* sB :-* BaseOpA) BaseOpA,
                   AlloyA sA BaseOpA (sA :-* sB :-* BaseOpA),
                   AlloyA sB BaseOpA (sA :-* sB :-* BaseOpA),
                   Monad m
                  ) =>
                  (sA -> m sA) -> (sB -> m sB) -> t -> m t
applyTopDownM2 fA fB = makeRecurseM ops
  where
    ops = makeTopDownM ops fA :-* makeTopDownM ops fB :-* baseOpA


{- TODO
checkDepthM :: (Alloy m (s -> m s, ()) () t,
                 Alloy m ()             (s -> m s, ()) s) =>
                (s -> m ()) -> t -> m t
checkDepthM f = makeRecurse ops
  where
    ops = baseOp `extOp` makeCheck ops f
-}
