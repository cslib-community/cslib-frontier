/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Foundations.BooleanAnalysis.Monotone

/-!
# Transitive-symmetric functions

A permutation `π` of the coordinates acts on inputs by `(x^π)ᵢ = x_{π(i)}` and on functions by
`f^π(x) = f(x^π)`. The permutations with `f^π = f` form the *automorphism group* `Aut(f)` of `f`
(`BitString.aut`) [O'Donnell, Exercise 1.30][ODonnell2014]. A Boolean function is
*transitive-symmetric* when for all coordinates `i` and `i'` some permutation in `Aut(f)` carries
`i` to `i'` [O'Donnell, Definition 2.10][ODonnell2014], that is, when `Aut(f)` acts transitively
on the coordinates [O'Donnell, Exercise 2.47][ODonnell2014]. We state it with Mathlib's
`MulAction.IsPretransitive (aut f) ι`, which unfolds to Definition 2.10 by
`BitString.isPretransitive_aut_iff`. Mathlib has no action of `Equiv.Perm ι` on the functions
`(ι → Bool) → β` whose stabilizer could serve as `Aut(f)`, so `aut f` is defined directly as a
subgroup.

A function of the weight is unchanged by every permutation
(`BitString.aut_eq_top_of_forall_weight_eq`, `BooleanFunction.IsSymmetric.aut_eq_top`), and a
function whose automorphism group contains every permutation is transitive-symmetric
(`BitString.isPretransitive_aut_of_eq_top`). So symmetric functions such as majority are
transitive-symmetric (`BooleanFunction.IsSymmetric.isPretransitive_aut`). Tribes is the book's
example of a transitive-symmetric function that is not symmetric.

Relabelling the coordinates relabels influences and Fourier coefficients
(`BitString.influence_comp_arrowCongr`, `BitString.fourierCoeff_comp_arrowCongr`), so an
automorphism `π` carries the influence of `i` and the coefficient on `S` to those of `π i` and
`π(S)` (`BitString.influence_apply_of_mem_aut`, `BitString.fourierCoeff_map_of_mem_aut`). Hence all
coordinates of a transitive-symmetric function have the same influence and the same degree-one
coefficient (`BitString.influence_signVal_eq_of_isPretransitive`,
`BitString.fourierCoeff_singleton_signVal_eq_of_isPretransitive`). Since permutations carry any
set to any other of the same size, a function of the weight has the same Fourier coefficient on
all sets of a given size (`BitString.fourierCoeff_eq_of_card_eq`). A monotone function on `n` bits
has total influence at most `√n` (`BitString.totalInfluence_le_sqrt_card_of_monotone`), so a
monotone transitive-symmetric function has every influence at most `1 / √n`
(`BitString.influence_signVal_le_one_div_sqrt_card_of_monotone_of_isPretransitive`)
[O'Donnell, Proposition 2.22][ODonnell2014].

## Usage

A permutation `π : Equiv.Perm ι` acts on inputs by `x ↦ fun j => x (π j)`, and `π ∈ aut f` means
`f (fun j => x (π j)) = f x` for every `x` (`BitString.mem_aut`); membership is decidable on a
finite cube. State transitive symmetry as the instance `MulAction.IsPretransitive (aut f) ι`.
Supply it with `have := hf.isPretransitive_aut` for `hf : f.IsSymmetric` (for example
`isSymmetric_majority`), with `BitString.isPretransitive_aut_of_eq_top` and
`BitString.aut_eq_top_of_forall_weight_eq` for a function of the weight of any codomain, or with
`BitString.isPretransitive_aut_iff.2 (by decide)` on a small cube. To pass an automorphism of a
Boolean `f` to `fun x => signVal (f x)`, use `BitString.aut_le_aut_comp signVal f`. Under the
instance, `BitString.influence_signVal_eq_of_isPretransitive f i i'` and
`BitString.fourierCoeff_singleton_signVal_eq_of_isPretransitive f i i'` equate the influences and
the degree-one coefficients of any two coordinates. The checked clients in
[CslibFrontierTests/BooleanAnalysisTransitiveSymmetric.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisTransitiveSymmetric.lean)
relabel dictators, use the transposition of the two bits of a conjunction, bound the influences
of majority, and show that `Tribes_{2,2}` is transitive-symmetric but not symmetric and that a
dictator on two bits is not transitive-symmetric.

## Main definitions

* `Cslib.BitString.aut`: the automorphism group of a function on the cube.

## Main results

* `Cslib.BitString.isPretransitive_aut_iff`: transitivity of the automorphism group is
  O'Donnell's transitive symmetry.
* `Cslib.BitString.aut_eq_top_of_forall_weight_eq`, `Cslib.BooleanFunction.IsSymmetric.aut_eq_top`:
  every permutation is an automorphism of a function of the weight.
* `Cslib.BitString.isPretransitive_aut_of_eq_top`,
  `Cslib.BooleanFunction.IsSymmetric.isPretransitive_aut`: such functions, in particular symmetric
  Boolean functions, are transitive-symmetric.
* `Cslib.BitString.influence_apply_of_mem_aut`, `Cslib.BitString.fourierCoeff_map_of_mem_aut`:
  automorphisms preserve influences and Fourier coefficients.
* `Cslib.BitString.fourierCoeff_eq_of_card_eq`: a function of the weight has the same Fourier
  coefficient on all sets of a given size.
* `Cslib.BitString.influence_signVal_eq_of_isPretransitive`,
  `Cslib.BitString.fourierCoeff_singleton_signVal_eq_of_isPretransitive`: all coordinates of a
  transitive-symmetric function have the same influence and degree-one coefficient.
* `Cslib.BitString.influence_signVal_le_one_div_sqrt_card_of_monotone_of_isPretransitive`:
  Proposition 2.22.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset

variable {ι β γ : Type*}

/-! ### The automorphism group -/

/-- The **automorphism group** `Aut(f)` of a function on the cube: the permutations `π` of the
coordinates with `f (x ∘ π) = f x` for every `x`, that is, `f^π = f` for the action
`(x^π)ᵢ = x_{π(i)}` [O'Donnell, Exercise 1.30][ODonnell2014]. -/
def aut (f : (ι → Bool) → β) : Subgroup (Equiv.Perm ι) where
  carrier := {π | ∀ x, f (fun j => x (π j)) = f x}
  mul_mem' {π σ} hπ hσ x := (hσ fun k => x (π k)).trans (hπ x)
  one_mem' _ := rfl
  inv_mem' {π} hπ x := by simpa using (hπ fun j => x (π⁻¹ j)).symm

/-- A permutation is an automorphism of `f` when it leaves `f` unchanged on every input. -/
@[simp] theorem mem_aut {f : (ι → Bool) → β} {π : Equiv.Perm ι} :
    π ∈ aut f ↔ ∀ x, f (fun j => x (π j)) = f x :=
  Iff.rfl

/-- An automorphism of `f` is an automorphism of every function of `f`. -/
theorem aut_le_aut_comp (h : β → γ) (f : (ι → Bool) → β) : aut f ≤ aut fun x => h (f x) :=
  fun _ hπ x => congrArg h (hπ x)

/-- **Transitive symmetry** [O'Donnell, Definition 2.10][ODonnell2014]: the automorphism group of
`f` acts transitively on the coordinates exactly when for all coordinates `i` and `i'` some
permutation `π` with `π i = i'` satisfies `f (x ∘ π) = f x` for every `x`. -/
theorem isPretransitive_aut_iff {f : (ι → Bool) → β} :
    MulAction.IsPretransitive (aut f) ι ↔
      ∀ i i' : ι, ∃ π : Equiv.Perm ι, π i = i' ∧ ∀ x, f (fun j => x (π j)) = f x := by
  refine ⟨fun h i i' => ?_, fun h => ⟨fun i i' => ?_⟩⟩
  · obtain ⟨⟨π, hπ⟩, rfl⟩ := MulAction.exists_smul_eq (aut f) i i'
    exact ⟨π, rfl, hπ⟩
  · obtain ⟨π, rfl, hπ⟩ := h i i'
    exact ⟨⟨π, hπ⟩, rfl⟩

/-- A function whose automorphism group contains every permutation is transitive-symmetric. -/
theorem isPretransitive_aut_of_eq_top {f : (ι → Bool) → β} (h : aut f = ⊤) :
    MulAction.IsPretransitive (aut f) ι := by
  classical
  exact ⟨fun i i' => ⟨⟨Equiv.swap i i', h ▸ Subgroup.mem_top _⟩, Equiv.swap_apply_left i i'⟩⟩

/-- An automorphism `π` of `f` is also unchanged by renaming the coordinates by `π⁻¹`. -/
private theorem comp_symm_of_mem_aut {f : (ι → Bool) → β} {π : Equiv.Perm ι} (hπ : π ∈ aut f) :
    (fun y => f fun j => y (π.symm j)) = f :=
  funext fun y => by simpa using (hπ fun j => y (π.symm j)).symm

section Fintype

variable [Fintype ι]

/-- **Functions of the weight are unchanged by every permutation**: if `f x` depends only on the
weight of `x`, every permutation of the coordinates is an automorphism of `f`. -/
theorem aut_eq_top_of_forall_weight_eq {f : (ι → Bool) → β}
    (hf : ∀ x y, weight x = weight y → f x = f y) : aut f = ⊤ :=
  eq_top_iff.2 fun π _ x => hf _ _ (weight_comp_equiv x π)

variable [DecidableEq ι]

instance [DecidableEq β] (f : (ι → Bool) → β) : DecidablePred (· ∈ aut f) :=
  fun _ => decidable_of_iff' _ mem_aut

end Fintype

/-- Every permutation of the coordinates is an automorphism of a symmetric function. -/
theorem _root_.Cslib.BooleanFunction.IsSymmetric.aut_eq_top {n : ℕ} {f : BooleanFunction n}
    (hf : f.IsSymmetric) : aut f = ⊤ :=
  aut_eq_top_of_forall_weight_eq hf

/-- **Symmetric functions are transitive-symmetric.** -/
theorem _root_.Cslib.BooleanFunction.IsSymmetric.isPretransitive_aut {n : ℕ}
    {f : BooleanFunction n} (hf : f.IsSymmetric) : MulAction.IsPretransitive (aut f) (Fin n) :=
  isPretransitive_aut_of_eq_top hf.aut_eq_top

/-! ### Invariance of influences and Fourier coefficients -/

variable [DecidableEq ι] [Fintype ι]

/-- **Automorphisms preserve influences**: an automorphism `π` of `g` carries the influence of
`i` on `g` to that of `π i`. -/
theorem influence_apply_of_mem_aut {g : (ι → Bool) → ℝ} {π : Equiv.Perm ι} (hπ : π ∈ aut g)
    (i : ι) : influence (π i) g = influence i g := by
  rw [← influence_comp_arrowCongr π i, comp_symm_of_mem_aut hπ]

/-- **Automorphisms preserve Fourier coefficients**: an automorphism `π` of `g` carries the Fourier
coefficient of `g` on `S` to its coefficient on `π(S)`, by
[O'Donnell, Exercise 1.30(a)][ODonnell2014] (`BitString.fourierCoeff_comp_arrowCongr`). -/
theorem fourierCoeff_map_of_mem_aut {g : (ι → Bool) → ℝ} {π : Equiv.Perm ι} (hπ : π ∈ aut g)
    (S : Finset ι) : fourierCoeff g (S.map π.toEmbedding) = fourierCoeff g S := by
  rw [← fourierCoeff_comp_arrowCongr π g S, comp_symm_of_mem_aut hπ]

/-- A function of the weight has the same Fourier coefficient on any two sets of the same size,
the observation O'Donnell uses to open Section 5.3 (after Exercise 1.30(a))
[O'Donnell, Section 5.3][ODonnell2014]. A permutation matching `S` with `S'` and their complements
with each other carries one set to the other, and every permutation is an automorphism. -/
theorem fourierCoeff_eq_of_card_eq {f : (ι → Bool) → ℝ}
    (hf : ∀ x y, weight x = weight y → f x = f y) {S S' : Finset ι} (h : #S = #S') :
    fourierCoeff f S = fourierCoeff f S' := by
  obtain ⟨e⟩ : Nonempty ({i // i ∈ S} ≃ {i // i ∈ S'}) := Fintype.card_eq.1 (by simpa using h)
  obtain ⟨e'⟩ : Nonempty ({i // i ∉ S} ≃ {i // i ∉ S'}) := Fintype.card_eq.1 (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
    simp [h])
  set π := e.subtypeCongr e'
  have hS : S.map π.toEmbedding = S' := eq_of_subset_of_card_le (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
    simp [π, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hx]) (by simp [h])
  rw [← hS, fourierCoeff_map_of_mem_aut (aut_eq_top_of_forall_weight_eq hf ▸ Subgroup.mem_top π)]

/-! ### Transitive-symmetric functions -/

variable (f : (ι → Bool) → Bool) [MulAction.IsPretransitive (aut f) ι]

/-- **All coordinates of a transitive-symmetric function have the same influence.** -/
theorem influence_signVal_eq_of_isPretransitive (i i' : ι) :
    influence i (fun x => signVal (f x)) = influence i' (fun x => signVal (f x)) := by
  obtain ⟨⟨π, hπ⟩, rfl⟩ := MulAction.exists_smul_eq (aut f) i i'
  exact (influence_apply_of_mem_aut (aut_le_aut_comp signVal f hπ) i).symm

/-- **All coordinates of a transitive-symmetric function have the same degree-one coefficient**,
the step `f̂(i) = f̂(i')` in [O'Donnell, proof of Proposition 2.22][ODonnell2014]. -/
theorem fourierCoeff_singleton_signVal_eq_of_isPretransitive (i i' : ι) :
    fourierCoeff (fun x => signVal (f x)) {i} = fourierCoeff (fun x => signVal (f x)) {i'} := by
  obtain ⟨⟨π, hπ⟩, rfl⟩ := MulAction.exists_smul_eq (aut f) i i'
  simpa using (fourierCoeff_map_of_mem_aut (aut_le_aut_comp signVal f hπ) {i}).symm

variable {f}

/-- **Monotone transitive-symmetric functions have small influences**: a monotone
transitive-symmetric Boolean function on `n` bits, read as signs, has every influence at most
`1 / √n` [O'Donnell, Proposition 2.22][ODonnell2014]. -/
theorem influence_signVal_le_one_div_sqrt_card_of_monotone_of_isPretransitive (hf : Monotone f)
    (i : ι) :
    influence i (fun x => signVal (f x)) ≤ 1 / √(Fintype.card ι) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.2 ⟨i⟩
  have h := totalInfluence_le_sqrt_card_of_monotone hf
  rw [totalInfluence, sum_congr rfl fun j _ => influence_signVal_eq_of_isPretransitive f j i,
    sum_const, card_univ, nsmul_eq_mul] at h
  have := Real.mul_self_sqrt hn.le
  rw [le_div_iff₀ (Real.sqrt_pos.2 hn)]
  nlinarith [Real.sqrt_pos.2 hn]

end Cslib.BitString
