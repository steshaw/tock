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

import Data.Maybe
import Data.Tree

import Data.Generics.Polyplate

-- | Given a list of operations and a modifier function, augments that modifier
-- function to first descend into the value before then applying the modifier function.
--  This can be used to perform a bottom-up depth-first traversal of a structure
-- (see 'applyBottomUpM').
makeBottomUpM :: PolyplateM t () opT m => opT -> (t -> m t) -> t -> m t
makeBottomUpM ops f v = makeDescendM ops v >>= f

-- | Given a list of operations and a modifier function, augments that modifier
-- function to first apply the modifier function before then descending into the value.
--  This can be used to perform a top-down depth-first traversal of a structure
-- (see 'applyTopDownM').
makeTopDownM :: PolyplateM t () opT m => opT -> (t -> m t) -> t -> m t
makeTopDownM ops f v = f v >>= makeDescendM ops

-- | Given a list of operations and a modifier function, augments that modifier
-- function to first descend into the value before then applying the modifier function.
--  This can be used to perform a bottom-up depth-first traversal of a structure
-- (see 'applyBottomUp').
makeBottomUp :: Polyplate t () opT => opT -> (t -> t) -> t -> t
makeBottomUp ops f v = f (makeDescend ops v)

-- | Given a list of operations and a modifier function, augments that modifier
-- function to first apply the modifier function before then descending into the value.
--  This can be used to perform a top-down depth-first traversal of a structure
-- (see 'applyTopDown').
makeTopDown :: Polyplate t () opT => opT -> (t -> t) -> t -> t
makeTopDown ops f v = makeDescend ops (f v)


{- TODO
makeCheckM :: PolyplateM t () opT m => opT -> (t -> m ()) -> t -> m t
makeCheckM ops f v
    =  do v' <- descend v
          f v'
          return v'
  where
    descend = makeDescend ops
-}
checkDepthM :: (Monad m, PolyplateSpine t (OneOpQ (m ()) s) () (m ())) => (s -> m ()) -> t -> m ()
checkDepthM f = sequence_ . catMaybes . flatten . applyQuery f

checkDepthM2 :: (Monad m, PolyplateSpine t (TwoOpQ (m ()) r s) () (m ())) =>
  (r -> m ()) -> (s -> m ()) -> t -> m ()
checkDepthM2 f g = sequence_ . catMaybes . flatten . applyQuery2 f g


checkBreadthM :: (Monad m, PolyplateSpine t (OneOpQ (m ()) s) () (m ())) => (s -> m ()) -> t -> m ()
checkBreadthM f = sequence_ . catMaybes . concat . levels . applyQuery f

applyQuery :: PolyplateSpine t (OneOpQ a s) () a => (s -> a) -> t -> Tree (Maybe a)
applyQuery qf = transformSpineSparse ops ()
  where
    ops = baseOp `extOpQ` qf

applyQuery2 :: PolyplateSpine t (TwoOpQ a sA sB) () a => (sA -> a) -> (sB -> a) -> t -> Tree (Maybe a)
applyQuery2 qfA qfB = transformSpineSparse ops ()
  where
    ops = baseOp `extOpQ` qfA `extOpQ` qfB 

applyListifyDepth :: PolyplateSpine t (OneOpQ (Maybe s) s) () (Maybe s) => (s -> Bool) -> t -> [s]
applyListifyDepth qf = catMaybes . flatten . fmap (fromMaybe Nothing) . transformSpineSparse ops ()
  where
    qf' x = if qf x then Just x else Nothing
    ops = baseOp `extOpQ` qf'

applyListifyBreadth :: PolyplateSpine t (OneOpQ (Maybe s) s) () (Maybe s) => (s -> Bool) -> t -> [s]
applyListifyBreadth qf = catMaybes . (concat . levels) . fmap (fromMaybe Nothing) . transformSpineSparse ops ()
  where
    qf' x = if qf x then Just x else Nothing
    ops = baseOp `extOpQ` qf'


-- | Given a monadic function that applies to a particular type (s), automatically
-- applies that function to every instance of s in a larger structure of type t,
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

applyBottomUp :: (Polyplate t (OneOp s) (),
                  Polyplate s () (OneOp s)) =>
                 (s -> s) -> t -> t
applyBottomUp f = makeRecurse ops
  where
    ops = baseOp `extOp` makeBottomUp ops f

-- | Given a monadic function that applies to a particular type (s), automatically
-- applies that function to every instance of s in a larger structure of type t,
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

-- | As applyBottomUpM, but applies two functions.  These should not be modifying
-- the same type.
applyBottomUpM2 :: (PolyplateM t (TwoOpM m sA sB) () m,
                    PolyplateM sA () (TwoOpM m sA sB) m,
                    PolyplateM sB () (TwoOpM m sA sB) m
                   ) =>
                   (sA -> m sA) -> (sB -> m sB) -> t -> m t
applyBottomUpM2 fA fB = makeRecurseM ops
  where
    ops = baseOp `extOpM` makeBottomUpM ops fA `extOpM` makeBottomUpM ops fB

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
