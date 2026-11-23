/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier

/-!
# Pulling Boolean characters back along coordinate maps

For a map `π : β → γ`, the *mod-2 projection* `BitString.projectSet π T` of `T : Finset β`
contains the points of `γ` with an odd number of preimages in `T`. Pulling a character back
along `π` projects its frequency set: `chi T (f ∘ π) = chi (projectSet π T) f`
(`BitString.chi_comp_eq_chi_projectSet`) [Håstad][Hastad2001]. In particular, repeated
coordinates cancel in pairs; the coordinate map need not be injective.

## Main results

* `Cslib.BitString.chi_comp_eq_chi_projectSet`: character pullback along any coordinate map.
* `Cslib.BitString.card_projectSet_le`: mod-2 projection never increases cardinality.

## References

* [J. Håstad, *Some optimal inapproximability results*][Hastad2001]
-/

public section

open Finset
open scoped BigOperators symmDiff

namespace Cslib.BitString

variable {β γ : Type*}

/-! ### Mod-2 projection of subsets and character pullback -/

section Projection

variable [Fintype γ] [DecidableEq γ]

/-- The **mod-2 projection** `π₂(T)` of `T : Finset β` along `π : β → γ`: the set of `y : γ`
whose fiber in `T` under `π` has odd cardinality [Håstad][Hastad2001]. -/
@[expose] def projectSet (π : β → γ) (T : Finset β) : Finset γ :=
  univ.filter fun y => Odd #{x ∈ T | π x = y}

/-- `y` lies in the mod-2 projection of `T` exactly when its fiber in `T` has odd cardinality. -/
@[simp]
theorem mem_projectSet {π : β → γ} {T : Finset β} {y : γ} :
    y ∈ projectSet π T ↔ Odd #{x ∈ T | π x = y} := by
  simp [projectSet]

/-- The mod-2 projection of the empty set is empty. -/
@[simp]
theorem projectSet_empty (π : β → γ) : projectSet π ∅ = ∅ := by
  ext y
  simp [projectSet]

/-- Every element of `projectSet π T` lies in the image of `T` under `π`. -/
theorem exists_mem_of_mem_projectSet {π : β → γ} {T : Finset β} {y : γ}
    (hy : y ∈ projectSet π T) : ∃ x ∈ T, π x = y := by
  rw [mem_projectSet] at hy
  have hpos : 0 < #{x ∈ T | π x = y} := Nat.pos_of_ne_zero (by rintro h0; simp [h0] at hy)
  obtain ⟨x, hx⟩ := card_pos.1 hpos
  exact ⟨x, (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩

/-- The mod-2 projection of `T` along `π` is contained in the image `T.image π`. -/
theorem projectSet_subset_image (π : β → γ) (T : Finset β) :
    projectSet π T ⊆ T.image π := fun y hy => by
  obtain ⟨x, hx, rfl⟩ := exists_mem_of_mem_projectSet hy
  exact mem_image_of_mem π hx

/-- The mod-2 projection never increases cardinality: `#(projectSet π T) ≤ #T`. -/
theorem card_projectSet_le (π : β → γ) (T : Finset β) : #(projectSet π T) ≤ #T :=
  (card_le_card (projectSet_subset_image π T)).trans card_image_le

variable [DecidableEq β]

/-- Inserting `x ∉ T` toggles `π x` in `projectSet π T`. -/
theorem projectSet_insert (π : β → γ) {x : β} {T : Finset β} (hx : x ∉ T) :
    projectSet π (insert x T) = symmDiff (projectSet π T) {π x} := by
  ext y
  rw [mem_projectSet, mem_symmDiff, mem_projectSet, mem_singleton, filter_insert]
  by_cases hxy : π x = y
  · subst hxy
    have hx' : x ∉ {z ∈ T | π z = π x} := fun h => hx (mem_filter.1 h).1
    simp only [↓reduceIte, card_insert_of_notMem hx', Nat.odd_add_one, not_true_eq_false,
      and_false, true_and, false_or]
  · have hyx : y ≠ π x := Ne.symm hxy
    simp [hxy, hyx]

/-- The mod-2 projection along the identity is the identity. -/
@[simp]
theorem projectSet_id [Fintype β] (T : Finset β) : projectSet id T = T := by
  ext y
  rw [mem_projectSet, show {x ∈ T | id x = y} = {x ∈ T | x = y} from rfl, filter_eq' T y]
  by_cases hy : y ∈ T <;> simp [hy]

omit [DecidableEq β] in
/-- **Pulling a character back along `π` projects the frequency set by `projectSet π`**:
`chi ℝ T (f ∘ π) = chi ℝ (projectSet π T) f`. -/
theorem chi_comp_eq_chi_projectSet (π : β → γ) (T : Finset β) (f : γ → Bool) :
    chi ℝ T (f ∘ π) = chi ℝ (projectSet π T) f := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert x T hx ih =>
    rw [projectSet_insert π hx, ← chi_mul_chi, chi_singleton, ← ih, chi_eq_prod_signVal,
      prod_insert hx, ← chi_eq_prod_signVal, Function.comp_apply, mul_comm]

end Projection

end Cslib.BitString
