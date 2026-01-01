{-# OPTIONS --cubical --guardedness #-}

module EffectfulPath where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import Data.Bool
open import Agda.Builtin.String renaming (primStringAppend to _++_)


------------------------------------------------------------------------
-- This file is a minimal experiment probing the interaction between
-- cubical paths and effect-like behavior.
--
-- Design principle:
--   * Cubical structure (intervals, paths, Kan filling) remains pure.
--   * Effects are introduced only *around* paths, not inside them.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Effectful wrapper around paths
------------------------------------------------------------------------

-- EffectfulPath represents a computation that may either:
--   * successfully produce a cubical path, or
--   * fail (modeling an effect such as exception or partiality).
--
-- Crucially, the Path itself remains pure.
data EffectfulPath (A : Type) (x y : A) : Type where
  success : Path A x y → EffectfulPath A x y
  failure : EffectfulPath A x y

-- Example: a successful effectful path
examplePath : EffectfulPath S¹ base base
examplePath = success loop

-- Example: a failed computation producing no path
failedPath : EffectfulPath S¹ base base
failedPath = failure

------------------------------------------------------------------------
-- Using effectful paths
------------------------------------------------------------------------

-- A consumer of effectful paths.
-- Note that we only *inspect* the effectful wrapper;
-- the cubical path itself is never modified or recomputed.
usePath :
  {A : Type} {x y : A} →
  EffectfulPath A x y →
  Bool
usePath (success _) = true
usePath failure     = false

------------------------------------------------------------------------
-- A more forceful example: why exceptions CANNOT occur mid-path
------------------------------------------------------------------------

-- A computation type with exceptions
data Comp (A : Type) : Type where
  return : A → Comp A
  throw  : Comp A

-- We can lift any pure path into Comp:
liftPath : {A : Type} {x y : A} → Path A x y → Path (Comp A) (return x) (return y)
liftPath p i = return (p i)

-- Example: lifting the loop into Comp
loopInComp : Path (Comp S¹) (return base) (return base)
loopInComp = liftPath loop

-- CRUCIAL OBSERVATION:
-- A path (Comp A) (return x) (return y) CANNOT pass through throw
-- at any intermediate point i.
--
-- Why? Because paths in sum types are "constructor-preserving".
-- If p : Path (Comp A) (return x) (return y), then for ALL i : I,
-- p i must be of the form (return _).
--
-- There is no path connecting (return x) to throw, because they
-- live in different constructors. The interval I is connected,
-- so any function I → Comp A starting at (return x) must stay in return.

-- This is why "throwing mid-path" is impossible:
-- The following type is UNINHABITED for any x:
--
--   Path (Comp A) (return x) throw
--
-- You cannot construct a path that "starts succeeding and then crashes".

-- CONTRAST with EffectfulPath:
-- EffectfulPath allows failure, but the failure is a DECISION made
-- BEFORE the path, not an event DURING the path.

------------------------------------------------------------------------
-- Demonstration: what would break if we could throw mid-path
------------------------------------------------------------------------

-- If we could somehow have a path that throws in the middle,
-- transport would be unsound:
--
-- Given p : Path (Comp A) (return x) (return y)  where p 0.5 = throw
-- transport p (return x) should give (return y)
-- But evaluating at the midpoint would crash!
--
-- This is exactly why cubical type theory requires paths to be
-- continuous functions I → A, with no room for effects.

------------------------------------------------------------------------
-- Conceptual note:
--
-- If effects were internalized into the Path type itself
-- (e.g. Path A x y performing effectful computation),
-- definitional equalities such as refl-transport would fail,
-- breaking strictness and potentially Kan filling.
--
-- This file demonstrates that when effects are kept external,
-- basic cubical structure remains intact.

------------------------------------------------------------------------

test : (Comp String)
test  = (return "dude")

f : String → (Comp String)
f s = (return (s ++ s))


g : Comp String
g  = throw




