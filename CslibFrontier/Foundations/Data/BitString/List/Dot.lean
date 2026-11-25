/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Operations
import Mathlib.Algebra.BigOperators.Fin

/-!
# The Boolean inner product of bit lists

`Cslib.BitString.listDot x r` is the parity of the positions where both lists have a `true` bit,
the inner product `⟨x, r⟩` over `𝔽₂` computed by Goldreich–Levin, Boolean Gaussian elimination
and small-bias checks. Bits beyond the shorter list are ignored. On `n`-bit strings it agrees with
the dot product `x ⬝ᵥ r`.

## Main definitions

* `Cslib.BitString.listDot`: the inner product of two bit lists.

## Main results

* `Cslib.BitString.listDot_ofFn`: on finite bit strings, `listDot` is the dot product `⬝ᵥ`.
-/

@[expose] public section

namespace Cslib.BitString

/-- The inner product over `𝔽₂` of two bit lists: the parity of the positions where both are
`true`. Bits beyond the shorter list are ignored. -/
def listDot (left right : List Bool) : Bool :=
  (left.zipWith Bool.and right).foldl Bool.xor false

/-- The inner product with an empty list is `false`. -/
@[simp]
theorem listDot_nil_left (right : List Bool) : listDot [] right = false :=
  rfl

/-- The inner product with an empty list is `false`. -/
@[simp]
theorem listDot_nil_right (left : List Bool) : listDot left [] = false := by
  cases left <;> rfl

/-- On `n`-bit strings, the list inner product is the dot product. -/
@[simp]
theorem listDot_ofFn {n : ℕ} (left right : BitString n) :
    listDot (List.ofFn left) (List.ofFn right) = left ⬝ᵥ right :=
  (dotProduct_eq_foldl left right).symm

/-- The bit-list inner product as a sum over the first list, reading absent bits as zero. -/
theorem listDot_eq_sum_getD (left right : List Bool) :
    listDot left right = ∑ i : Fin left.length, left.getD i false * right.getD i false := by
  have hsum (l : List Bool) : l.foldl Bool.xor false = l.sum := by
    simp [List.sum_eq_foldl, Bool.add_eq_xor, Bool.zero_eq_false]
  simp only [listDot, hsum]
  induction left generalizing right with
  | nil => simp
  | cons b l ih =>
    cases right with
    | nil => simp [← Bool.zero_eq_false]
    | cons c r =>
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp [ih r, Bool.mul_eq_and]

end Cslib.BitString
