/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.SymmDiff

/-!
# Finset sums of bit strings

Elementary cancellation properties of `Finset.sum` in `Cslib.BitString b` (where every element has
additive order dividing `2`).

## Main results

* `Cslib.BitString.sum_bitString_eq_iff_sum_symmDiff_eq_zero`: two finset sums in `BitString b` are
  equal if and only if the sum over the symmetric difference `symmDiff S₁ S₂` is `0`.
-/

public section

namespace Cslib.BitString

open scoped BigOperators

/-- In `BitString b` (where every element has additive order dividing `2`), two finset sums are
equal if and only if the sum over their symmetric difference is `0`. -/
theorem sum_bitString_eq_iff_sum_symmDiff_eq_zero {ι : Type*} [DecidableEq ι] {b : ℕ}
    (S₁ S₂ : Finset ι) (g : ι → BitString b) :
    ∑ α ∈ S₁, g α = ∑ α ∈ S₂, g α ↔ ∑ α ∈ symmDiff S₁ S₂, g α = 0 := by
  have hsplit (A B : Finset ι) : ∑ α ∈ A, g α = ∑ α ∈ A \ B, g α + ∑ α ∈ A ∩ B, g α := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter A B), Finset.sdiff_union_inter]
  change _ ↔ ∑ α ∈ S₁ \ S₂ ∪ S₂ \ S₁, g α = 0
  rw [hsplit S₁ S₂, hsplit S₂ S₁, Finset.inter_comm S₂ S₁, add_right_cancel_iff,
    Finset.sum_union disjoint_sdiff_sdiff]
  refine ⟨fun h => by rw [h, BitString.add_self], fun h => ?_⟩
  calc ∑ α ∈ S₁ \ S₂, g α
      = ∑ α ∈ S₁ \ S₂, g α + (∑ α ∈ S₁ \ S₂, g α + ∑ α ∈ S₂ \ S₁, g α) := by
        rw [h, add_zero]
    _ = ∑ α ∈ S₂ \ S₁, g α := BitString.add_cancel_left _ _

end Cslib.BitString
