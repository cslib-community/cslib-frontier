/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.Data.BitString.Affine
import Mathlib.Algebra.BigOperators.Option

/-!
# Pulling Boolean characters back along coordinate maps

For a map `π : β → γ`, the *mod-2 projection* `BitString.projectSet π T` of `T : Finset β`
contains the points of `γ` with an odd number of preimages in `T`. Pulling a character back
along `π` projects its frequency set: `chi T (f ∘ π) = chi (projectSet π T) f`
(`BitString.chi_comp_eq_chi_projectSet`) [Håstad][Hastad2001]. In particular, repeated
coordinates cancel in pairs; the coordinate map need not be injective.

Affine Boolean functions, read as signs, are characters multiplied by the sign of their
constant term. Adjoining a Boolean function of selected coordinates expands each new character
as a linear combination of old characters.

## Main results

* `Cslib.BitString.chi_comp_eq_chi_projectSet`: character pullback along any coordinate map.
* `Cslib.BitString.card_projectSet_le`: mod-2 projection never increases cardinality.
* `Cslib.BitString.chi_append_eq_sum`: adjoining a Boolean coordinate expands each character
  into a linear combination of the old characters, including repeated coordinate selections.

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

/-- An affine Boolean function, read as signs, is a character multiplied by the sign of its
constant term. -/
theorem exists_signVal_eq_mul_chi_of_isAffine
    {ι : Type*} [Finite ι] {f : (ι → Bool) → Bool} (hf : IsAffine f) :
    ∃ T : Finset ι, (fun x => signVal (f x)) = fun x => signVal (f 0) * chi ℝ T x := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨T, -, hT⟩ := exists_affine_of_add_add
    (M := (univ : Finset ι)) (fun x y h => congrArg f (funext fun i => h i (mem_univ i))) hf
  refine ⟨T, funext fun x => ?_⟩
  rw [hT x, Bool.add_eq_xor, signVal_xor, chi_eq_signVal_parityOn]
  congr 2
  exact (parityOn_eq_sum T x).symm

/-! ### Adjoining a Boolean coordinate -/

/-- A character of an `Option`-indexed vector splits into the new coordinate, when selected,
and the character of the old coordinates. -/
theorem chi_option_elim {κ : Type*} [Finite κ] [DecidableEq κ]
    (S : Finset (Option κ)) (b : Bool) (y : κ → Bool) :
    chi ℝ S (fun o => o.elim b y) =
      (if none ∈ S then signVal b else 1) * chi ℝ S.eraseNone y := by
  let := Fintype.ofFinite κ
  simp only [chi_eq_prod_univ, Fintype.prod_option, Option.elim_none, Option.elim_some,
    mem_eraseNone, signVal_eq_neg_one_pow]

/-- Adjoining `φ` of selected coordinates expands a character containing the new coordinate
into old characters. The map `args` may repeat coordinates. -/
theorem chi_append_eq_sum {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ] (φ : (α → Bool) → Bool) (args : α → κ)
    (S : Finset (Option κ)) (hnone : none ∈ S) (y : κ → Bool) :
    chi ℝ S (fun o => o.elim (φ (y ∘ args)) y) =
      ∑ T, fourierCoeff (fun z => signVal (φ z)) T *
        chi ℝ (symmDiff (projectSet args T) S.eraseNone) y := by
  rw [chi_option_elim, ite_eq_left hnone,
    ← sum_fourierCoeff_mul_chi (fun z => signVal (φ z)) (y ∘ args), sum_mul]
  apply sum_congr rfl
  intro T _
  rw [mul_assoc, chi_comp_eq_chi_projectSet, chi_mul_chi]

end Cslib.BitString
