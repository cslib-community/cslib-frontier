/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Arrays as finite maps with defaults

Compiled checkers keep finite maps from numbers to values in arrays indexed by the number,
reading past the end as a default. `Array.setGrow` writes an entry, first padding the array with
the default up to its index.

## Main definitions

* `Array.setGrow`: write an entry, growing the array as needed.

## Main results

* `Array.getD_setGrow`, `Array.getD_setIfInBounds_self`: reading after a write, and after
  resetting an entry to the default.
* `Array.lt_size_setGrow`, `Array.size_le_size_setGrow`: the written index is in range, and the
  array only grows.
-/

public section

namespace Array

/-- Write `x` at index `i`, first padding the array with `d` up to `i` if it is too short. A write
just past the end is a plain `push`, which allocates no padding. Exposed, so that the kernel
evaluates its callers. -/
@[expose] def setGrow {α : Type*} (a : Array α) (i : ℕ) (d x : α) : Array α :=
  if i < a.size then a.setIfInBounds i x
  else if i = a.size then a.push x
  else (a ++ Array.replicate (i - a.size) d).push x

theorem getD_setGrow {α : Type*} (a : Array α) (i j : ℕ) (d x : α) :
    (a.setGrow i d x).getD j d = if j = i then x else a.getD j d := by
  unfold setGrow
  simp only [Array.getD_eq_getD_getElem?]
  split
  · rename_i hi
    by_cases hj : j = i
    · subst hj
      simp [hi]
    · simp [Ne.symm hj, hj]
  split
  · rename_i hi he
    subst he
    rw [Array.getElem?_push]
    by_cases hj : j = a.size <;> simp [hj]
  · rename_i hi he
    have hs : a.size + (i - a.size) = i := by omega
    rw [Array.getElem?_push, Array.size_append, Array.size_replicate, hs]
    by_cases hj : j = i
    · simp [hj]
    · simp only [hj, ↓reduceIte, Array.getElem?_append]
      split
      · rfl
      · rw [Array.getElem?_replicate, Array.getElem?_eq_none (by omega)]
        split <;> rfl

theorem getD_setIfInBounds_self {α : Type*} (a : Array α) (i j : ℕ) (d : α) :
    (a.setIfInBounds i d).getD j d = if j = i then d else a.getD j d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split <;> split <;> simp_all

theorem size_le_size_setGrow {α : Type*} (a : Array α) (i : ℕ) (d x : α) :
    a.size ≤ (a.setGrow i d x).size := by
  unfold setGrow
  split
  · simp
  · split <;> simp

theorem lt_size_setGrow {α : Type*} (a : Array α) (i : ℕ) (d x : α) :
    i < (a.setGrow i d x).size := by
  unfold setGrow
  split
  · simpa
  split
  · simp_all
  · simp only [size_push, size_append, size_replicate]; omega

end Array
