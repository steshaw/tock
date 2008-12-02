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


-- | Given a list of operations and a modifier function, augments that modifier
-- function to first descend into the value before then applying the modifier function.
--  This can be used to perform a bottom-up depth-first traversal of a structure
-- (see 'applyBottomUpM').
makeBottomUpM :: PolyplateM t () opT m => opT -> (t -> m t) -> t -> m t
makeBottomUpM ops f v = descend v >>= f
  where
    descend = makeDescend ops

-- | Given a list of operations and a modifier function, augments that modifier
-- function to first apply the modifier function before then descending into the value.
--  This can be used to perform a top-down depth-first traversal of a structure
-- (see 'applyTopDownM').
makeTopDownM :: PolyplateM t () opT m => opT -> (t -> m t) -> t -> m t
makeTopDownM ops f v = f v >>= descend
  where
    descend = makeDescend ops

-- | Given a list of operations and a modifier function, augments that modifier
-- function to first descend into the value before then applying the modifier function.
--  This can be used to perform a bottom-up depth-first traversal of a structure
-- (see 'applyBottomUp').
makeBottomUp :: Polyplate t () opT => opT -> (t -> t) -> t -> t
makeBottomUp ops f v = f (descend v)
  where
    descend = makeDescend ops

-- | Given a list of operations and a modifier function, augments that modifier
-- function to first apply the modifier function before then descending into the value.
--  This can be used to perform a top-down depth-first traversal of a structure
-- (see 'applyTopDown').
makeTopDown :: Polyplate t () opT => opT -> (t -> t) -> t -> t
makeTopDown ops f v = descend (f v)
  where
    descend = makeDescend ops


{- TODO
makeCheckM :: PolyplateM t () opT m => opT -> (t -> m ()) -> t -> m t
makeCheckM ops f v
    =  do v' <- descend v
          f v'
          return v'
  where
    descend = makeDescend ops
-}

-- TODO also add a listify-like thing (maybe return a rose tree):
-- applyQuery :: (s -> a) -> t -> Tree a

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
