/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Fintype/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Fintype.EquivFin

/-!
# Coordinate-by-coordinate induction for updating functions on finite types

Replacing one coordinate at a time transforms `x : ∀ i, α i` into `y : ∀ i, α i` when the index
type `ι` is finite (`Function.update_induction`). Game-theoretic and social-choice proofs use this
hybrid argument to move between profiles agent by agent while invoking unilateral strategy-proofness
at each step.

## Main results

* `Function.update_induction`: a property holding at `x` and preserved whenever a coordinate `i`
  with `z i = x i ≠ y i` is updated to `y i` (from any mixed function `z`) holds at `y`.
-/

public section

namespace Function

/-- Coordinate-by-coordinate replacement of a function on a finite index type. A property `P` that
holds at `x`, and that survives updating one coordinate `i` with `z i = x i ≠ y i` to `y i` from
any function `z` taking each coordinate from `{x j, y j}`, holds at `y`. -/
theorem update_induction {ι : Type*} {α : ι → Type*} [Finite ι] [DecidableEq ι]
    {P : (∀ i, α i) → Prop} {x y : ∀ i, α i} (hx : P x)
    (step : ∀ z : ∀ i, α i, (∀ j, z j = x j ∨ z j = y j) → P z →
      ∀ i, z i = x i → z i ≠ y i → P (Function.update z i (y i))) :
    P y := by
  classical
  let _ := Fintype.ofFinite ι
  let m : Finset ι → ∀ j, α j := fun S j => if j ∈ S then y j else x j
  suffices h : ∀ S, P (m S) by simpa only [m, Finset.mem_univ, ↓reduceIte] using h Finset.univ
  intro S
  induction S using Finset.induction with
  | empty => simpa only [m, Finset.notMem_empty, ↓reduceIte] using hx
  | insert i S hi ih =>
    have hupd : m (insert i S) = Function.update (m S) i (y i) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp only [m, Finset.mem_insert_self, ↓reduceIte, Function.update_self]
      · simp only [m, Finset.mem_insert, hj, false_or, Function.update_of_ne hj]
    have hmi : m S i = x i := by simp only [m, hi, ↓reduceIte]
    by_cases hxy : x i = y i
    · rwa [hupd, ← hxy, ← hmi, Function.update_eq_self]
    rw [hupd]
    refine step _ (fun j => ?_) ih i hmi (hmi ▸ hxy)
    by_cases hj : j ∈ S <;> simp only [m, hj, ↓reduceIte, or_true, true_or]

end Function
