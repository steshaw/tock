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
makeBottomUp :: Polyplate t () opT => opT -> (t -> t) -> t -> t
makeBottomUp ops f v = f (makeDescend ops v)

-- | Given a list of operations and a monadic modifier function, augments that modifier
-- function to first descend into the value before then applying the modifier function.
--  This can be used to perform a bottom-up depth-first traversal of a structure
-- (see 'applyBottomUpM').
makeBottomUpM :: PolyplateM t () opT m => opT -> (t -> m t) -> t -> m t
makeBottomUpM ops f v = makeDescendM ops v >>= f

-- | As makeBottomUpM, but with routes as well.
makeBottomUpMRoute :: PolyplateMRoute t () opT m outer =>
  opT -> ((t, Route t outer) -> m t) -> (t, Route t outer) -> m t
makeBottomUpMRoute ops f (v, r)
  = do v' <- transformMRoute () ops (v, r)
       f (v', r)

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
makeTopDownM :: PolyplateM t () opT m => opT -> (t -> m t) -> t -> m t
makeTopDownM ops f v = f v >>= makeDescendM ops

-- | As makeTopDownM, but with routes as well.
makeTopDownMRoute :: PolyplateMRoute t () opT m outer =>
  opT -> ((t, Route t outer) -> m t) -> (t, Route t outer) -> m t
makeTopDownMRoute ops f (v, r)
  = do v' <- f (v, r)
       transformMRoute () ops (v', r)



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
listifyDepth :: (PolyplateM t (OneOpM (State [s]) s) () (State [s])
                ,PolyplateM s () (OneOpM (State [s]) s) (State [s])) => (s -> Bool) -> t -> [s]
-- We use applyBottomUp because we are prepending to the list.  If we prepend from
-- the bottom up, that's the same as appending from the top down, which is what
-- this function is meant to be doing.
listifyDepth qf = flip execState [] . applyBottomUpM qf'
  where
    qf' x = if qf x then modify (x:) >> return x else return x

-- * Check functions to apply monadic checks throughout a data structure

-- | Given a monadic function that operates on items of type \"s\" (without modifying
-- them), applies the function to all items of types \"s\" within an item of type
-- \"t\", in depth-first order.
--
-- This can be used, for example, to perform checks on items in an error monad,
-- or to accumulate information in a state monad.
checkDepthM :: (Monad m, PolyplateM t (OneOpM m s) () m
                       , PolyplateM s () (OneOpM m s) m) => (s -> m ()) -> t -> m ()
checkDepthM f x = applyBottomUpM (\x -> f x >> return x) x >> return ()

-- | As 'checkDepthM', but takes two functions (one operating on type \"r\", the
-- other on type \"s\").
checkDepthM2 :: (Monad m, PolyplateM t (TwoOpM m r s) () m
                        , PolyplateM r () (TwoOpM m r s) m
                        , PolyplateM s () (TwoOpM m r s) m
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
applyBottomUpM :: (PolyplateM t (OneOpM m s) () m,
                   PolyplateM s () (OneOpM m s) m) =>
                  (s -> m s) -> t -> m t
applyBottomUpM f = makeRecurseM ops
  where
    ops = baseOp `extOpM` makeBottomUpM ops f

-- | As 'applyBottomUpM', but applies two functions.  These should not be modifying
-- the same type.
applyBottomUpM2 :: (PolyplateM t (TwoOpM m sA sB) () m,
                    PolyplateM sA () (TwoOpM m sA sB) m,
                    PolyplateM sB () (TwoOpM m sA sB) m
                   ) =>
                   (sA -> m sA) -> (sB -> m sB) -> t -> m t
applyBottomUpM2 fA fB = makeRecurseM ops
  where
    ops = baseOp `extOpM` makeBottomUpM ops fA `extOpM` makeBottomUpM ops fB

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
applyTopDownM :: (PolyplateM t (OneOpM m s) () m,
                  PolyplateM s () (OneOpM m s) m) =>
                 (s -> m s) -> t -> m t
applyTopDownM f = makeRecurseM ops
  where
    ops = baseOp `extOpM` makeTopDownM ops f

-- | As applyTopDownM, but applies two functions.  These should not be modifying
-- the same type.
applyTopDownM2 :: (PolyplateM t (TwoOpM m sA sB) () m,
                   PolyplateM sA () (TwoOpM m sA sB) m,
                   PolyplateM sB () (TwoOpM m sA sB) m
                  ) =>
                  (sA -> m sA) -> (sB -> m sB) -> t -> m t
applyTopDownM2 fA fB = makeRecurseM ops
  where
    ops = baseOp `extOpM` makeTopDownM ops fA `extOpM` makeTopDownM ops fB


{- TODO
checkDepthM :: (Polyplate m (s -> m s, ()) () t,
                 Polyplate m ()             (s -> m s, ()) s) =>
                (s -> m ()) -> t -> m t
checkDepthM f = makeRecurse ops
  where
    ops = baseOp `extOp` makeCheck ops f
-}
