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


module Data.Generics.Polyplate.Schemes where

import Control.Monad.State

import Data.Generics.Polyplate
import Data.Generics.Polyplate.Route

-- * Adding traversal to modifiers

-- | Given a list of operations and a modifier function, augments that modifier
-- function to first descend into the value before then applying the modifier function.
--  This can be used to perform a bottom-up depth-first traversal of a structure
-- (see 'applyBottomUp').
makeBottomUp :: Polyplate t BaseOp opT => opT -> (t -> t) -> t -> t
makeBottomUp ops f v = f (makeDescend ops v)

-- | Given a list of operations and a monadic modifier function, augments that modifier
-- function to first descend into the value before then applying the modifier function.
--  This can be used to perform a bottom-up depth-first traversal of a structure
-- (see 'applyBottomUpM').
makeBottomUpM :: (PolyplateM t BaseOpM opT, Monad m) => opT m -> (t -> m t) -> t -> m t
makeBottomUpM ops f v = makeDescendM ops v >>= f

-- | As makeBottomUpM, but with routes as well.
makeBottomUpMRoute :: forall m opT t outer. (Monad m, PolyplateMRoute t BaseOpMRoute opT) =>
  opT m outer -> ((t, Route t outer) -> m t) -> (t, Route t outer) -> m t
makeBottomUpMRoute ops f (v, r)
  = do v' <- transformMRoute base ops (v, r)
       f (v', r)
  where
    base :: BaseOpMRoute m outer
    base = baseOpMRoute

-- | Given a list of operations and a modifier function, augments that modifier
-- function to first apply the modifier function before then descending into the value.
--  This can be used to perform a top-down depth-first traversal of a structure
-- (see 'applyTopDown').
makeTopDown :: Polyplate t () opT => opT -> (t -> t) -> t -> t
makeTopDown ops f v = makeDescend ops (f v)

-- | Given a list of operations and a monadic modifier function, augments that modifier
-- function to first apply the modifier function before then descending into the value.
--  This can be used to perform a top-down depth-first traversal of a structure
-- (see 'applyTopDownM').
makeTopDownM :: (PolyplateM t BaseOpM opT, Monad m) => opT m -> (t -> m t) -> t -> m t
makeTopDownM ops f v = f v >>= makeDescendM ops

-- | As makeTopDownM, but with routes as well.
makeTopDownMRoute :: (PolyplateMRoute t BaseOpMRoute opT, Monad m) =>
  opT m outer -> ((t, Route t outer) -> m t) -> (t, Route t outer) -> m t
makeTopDownMRoute ops f (v, r)
  = do v' <- f (v, r)
       transformMRoute baseOpMRoute ops (v', r)



{- TODO
makeCheckM :: PolyplateM t () opT m => opT -> (t -> m ()) -> t -> m t
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
listifyDepth :: (PolyplateM t (OneOpM s) BaseOpM
                ,PolyplateM s BaseOpM (OneOpM s)) => (s -> Bool) -> t -> [s]
-- We use applyBottomUp because we are prepending to the list.  If we prepend from
-- the bottom up, that's the same as appending from the top down, which is what
-- this function is meant to be doing.
listifyDepth qf = flip execState [] . applyBottomUpM qf'
  where
    qf' x = if qf x then modify (x:) >> return x else return x

-- | Like listifyDepth, but with routes
listifyDepthRoute :: (PolyplateMRoute t (OneOpMRoute s) (BaseOpMRoute)
                     ,PolyplateMRoute s (BaseOpMRoute) (OneOpMRoute s))
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
checkDepthM :: (Monad m, PolyplateM t (OneOpM s) BaseOpM
                       , PolyplateM s BaseOpM (OneOpM s)) => (s -> m ()) -> t -> m ()
checkDepthM f x = applyBottomUpM (\x -> f x >> return x) x >> return ()

-- | As 'checkDepthM', but takes two functions (one operating on type \"r\", the
-- other on type \"s\").
checkDepthM2 :: (Monad m, PolyplateM t (TwoOpM r s) (BaseOpM)
                        , PolyplateM r (BaseOpM) (TwoOpM r s)
                        , PolyplateM s (BaseOpM) (TwoOpM r s)
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
applyBottomUpM :: (PolyplateM t (OneOpM s) BaseOpM,
                   PolyplateM s BaseOpM (OneOpM s), Monad m) =>
                  (s -> m s) -> t -> m t
applyBottomUpM f = makeRecurseM ops
  where
    ops = baseOpM `extOpM` makeBottomUpM ops f

applyBottomUpMRoute :: forall m s t.
                       (PolyplateMRoute t (OneOpMRoute s) (BaseOpMRoute),
                        PolyplateMRoute s (BaseOpMRoute) (OneOpMRoute s),
                        Monad m) =>
                       ((s, Route s t) -> m s) -> t -> m t
applyBottomUpMRoute f x = transformMRoute ops base (x, identityRoute)
  where
    base :: BaseOpMRoute m t
    base = baseOpMRoute
    
    ops = base `extOpMRoute` makeBottomUpMRoute ops f


-- | As 'applyBottomUpM', but applies two functions.  These should not be modifying
-- the same type.
applyBottomUpM2 :: (PolyplateM t (TwoOpM sA sB) (BaseOpM),
                    PolyplateM sA (BaseOpM) (TwoOpM sA sB),
                    PolyplateM sB (BaseOpM) (TwoOpM sA sB),
                    Monad m
                   ) =>
                   (sA -> m sA) -> (sB -> m sB) -> t -> m t
applyBottomUpM2 fA fB = makeRecurseM ops
  where
    ops = makeBottomUpM ops fA :-* makeBottomUpM ops fB :-* baseOpM

-- | As 'applyBottomUpM', but non-monadic.
applyBottomUp :: (Polyplate t (OneOp s) (),
                  Polyplate s () (OneOp s)) =>
                 (s -> s) -> t -> t
applyBottomUp f = makeRecurse ops
  where
    ops = baseOp `extOp` makeBottomUp ops f

-- | As 'applyBottomUpM2', but non-monadic.
applyBottomUp2 :: (Polyplate t (TwoOp sA sB) (),
                  Polyplate sA () (TwoOp sA sB),
                  Polyplate sB () (TwoOp sA sB)) =>
                 (sA -> sA) -> (sB -> sB) -> t -> t
applyBottomUp2 fA fB = makeRecurse ops
  where
    ops = baseOp `extOp` makeBottomUp ops fA `extOp` makeBottomUp ops fB

-- | Given a monadic function that applies to a particular type (\"s\"), automatically
-- applies that function to every instance of \"s\" in a larger structure of type \"t\",
-- performing the transformations in a top-down fashion.  It does a depth first
-- traversal in order of a constructor's children (assuming you are using one of
-- the generated instances, not your own), applying the function first and then
-- descending.
applyTopDownM :: (PolyplateM t (s :-* BaseOpM) BaseOpM,
                  PolyplateM s BaseOpM (s :-* BaseOpM),
                  Monad m) =>
                 (s -> m s) -> t -> m t
applyTopDownM f = makeRecurseM ops
  where
    ops = makeTopDownM ops f :-* baseOpM

-- | As applyTopDownM, but applies two functions.  These should not be modifying
-- the same type.
applyTopDownM2 :: (PolyplateM t (sA :-* sB :-* BaseOpM) BaseOpM,
                   PolyplateM sA BaseOpM (sA :-* sB :-* BaseOpM),
                   PolyplateM sB BaseOpM (sA :-* sB :-* BaseOpM),
                   Monad m
                  ) =>
                  (sA -> m sA) -> (sB -> m sB) -> t -> m t
applyTopDownM2 fA fB = makeRecurseM ops
  where
    ops = makeTopDownM ops fA :-* makeTopDownM ops fB :-* baseOpM


{- TODO
checkDepthM :: (Polyplate m (s -> m s, ()) () t,
                 Polyplate m ()             (s -> m s, ()) s) =>
                (s -> m ()) -> t -> m t
checkDepthM f = makeRecurse ops
  where
    ops = baseOp `extOp` makeCheck ops f
-}
