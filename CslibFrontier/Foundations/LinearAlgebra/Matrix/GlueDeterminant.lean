/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate (Mathlib, beside Mathlib/LinearAlgebra/Matrix/Block.lean)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.LinearCombination

/-!
# Glued determinants, and expanding a determinant along rows `λ • v + e`

Let the rows and the columns of a square matrix fall into two groups. `Matrix.glue rg cg N₁ N₂`
has the entries of `N₁` where both the row and the column are in the first group, those of `N₂`
where both are in the second, and `0` elsewhere. Its determinant is `0` unless the two first groups
have the same size (`Matrix.det_glue_eq_zero_of_card_ne`), and in general it is a product of a
function of `N₁` and a function of `N₂` (`Matrix.exists_det_glue_eq_mul`).

A determinant whose rows indexed by `m` are `l r • v r + e r` is the sum over the sets `T` of these
rows of `∏_{r ∈ T} l r` times the determinant with the rows `v r` for `r ∈ T` and `e r` otherwise
(`Matrix.det_sumElim_smul_add`), by multilinearity.

## Main definitions

* `Matrix.glue`: the matrix glued from two blocks.

## Main results

* `Matrix.det_glue_eq_zero_of_card_ne`, `Matrix.exists_det_glue_eq_mul`.
* `Matrix.det_sumElim_smul_add`.
* `Matrix.dvd_det_sub`: matrices that are congruent modulo `d` entrywise have congruent
  determinants.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  module `Nc.Cross.Split` (for the proof of Proposition B.2)
-/

public section

namespace Matrix

open Finset

section glue

variable {ι R : Type*} [Zero R]

/-- The matrix with the entries of `N₁` in the rows and columns of the first group, those of `N₂`
in the rows and columns of the second, and zeros elsewhere. -/
def glue (rg cg : ι → Prop) [DecidablePred rg] [DecidablePred cg] (N₁ N₂ : Matrix ι ι R) :
    Matrix ι ι R :=
  of fun i j => if rg i then (if cg j then N₁ i j else 0) else (if cg j then 0 else N₂ i j)

@[simp] theorem glue_apply (rg cg : ι → Prop) [DecidablePred rg] [DecidablePred cg]
    (N₁ N₂ : Matrix ι ι R) (i j : ι) :
    glue rg cg N₁ N₂ i j =
      if rg i then (if cg j then N₁ i j else 0) else (if cg j then 0 else N₂ i j) := by
  rfl

end glue

section split

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

private theorem det_glue_eq_zero_of_card_lt (rg cg : ι → Prop) [DecidablePred rg] [DecidablePred cg]
    (N₁ N₂ : Matrix ι ι R) (h : (univ.filter cg).card < (univ.filter rg).card) :
    (glue rg cg N₁ N₂).det = 0 := by
  rw [det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  obtain ⟨j, hj⟩ : ∃ j, rg (σ j) ∧ ¬ cg j := by
    by_contra! hcon
    exact h.not_ge (Finset.card_le_card_of_injOn σ.symm
      (fun i hi => by simpa using hcon (σ.symm i) (by simpa using (Finset.mem_filter.1 hi).2))
      (fun _ _ _ _ hij => σ.symm.injective hij))
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [glue_apply, hj.1, hj.2]), smul_zero]

theorem det_glue_eq_zero_of_card_ne (rg cg : ι → Prop) [DecidablePred rg] [DecidablePred cg]
    (N₁ N₂ : Matrix ι ι R) (h : (univ.filter rg).card ≠ (univ.filter cg).card) :
    (glue rg cg N₁ N₂).det = 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [← det_transpose]
    have : (glue rg cg N₁ N₂)ᵀ = glue cg rg N₁ᵀ N₂ᵀ := by
      ext i j
      by_cases h1 : cg i <;> by_cases h2 : rg j <;> simp [glue_apply, h1, h2]
    rw [this]
    exact det_glue_eq_zero_of_card_lt cg rg _ _ h
  · exact det_glue_eq_zero_of_card_lt rg cg _ _ h

/-- A glued determinant is a product. -/
theorem exists_det_glue_eq_mul (rg cg : ι → Prop) [DecidablePred rg] [DecidablePred cg] :
    ∃ (α β : Matrix ι ι R → R), ∀ N₁ N₂, (glue rg cg N₁ N₂).det = α N₁ * β N₂ := by
  by_cases h : (univ.filter rg).card = (univ.filter cg).card
  swap
  · exact ⟨fun _ => 0, fun _ => 0,
      fun N₁ N₂ => by rw [det_glue_eq_zero_of_card_ne _ _ _ _ h, zero_mul]⟩
  have hc : Fintype.card {i // cg i} = Fintype.card {i // rg i} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, h]
  let e : {i // cg i} ≃ {i // rg i} := Fintype.equivOfCardEq hc
  let τ : Equiv.Perm ι := Equiv.extendSubtype e
  have h1 : ∀ i, cg i → rg (τ i) := fun i hi => Equiv.extendSubtype_mem e i hi
  have h2 : ∀ i, ¬ cg i → ¬ rg (τ i) := fun i hi => Equiv.extendSubtype_not_mem e i hi
  refine ⟨fun N₁ => ((Equiv.Perm.sign τ : ℤ) : R) * (toSquareBlockProp (N₁.submatrix τ id) cg).det,
    fun N₂ => (toSquareBlockProp (N₂.submatrix τ id) fun i => ¬ cg i).det, fun N₁ N₂ => ?_⟩
  have hp := det_permute τ (glue rg cg N₁ N₂)
  have hs : ((Equiv.Perm.sign τ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
  have hb : ((glue rg cg N₁ N₂).submatrix τ id).det =
      (toSquareBlockProp (N₁.submatrix τ id) cg).det *
        (toSquareBlockProp (N₂.submatrix τ id) fun i => ¬ cg i).det := by
    rw [twoBlockTriangular_det _ cg]
    · congr 1
      · congr 1
        ext i j
        simp [toSquareBlockProp, glue, h1 i i.property, j.property]
      · congr 1
        ext i j
        simp [toSquareBlockProp, glue, h2 i i.property, j.property]
    · intro i hi j hj
      simp [glue_apply, h2 i hi, hj]
  rw [hb] at hp
  linear_combination (-(glue rg cg N₁ N₂).det) * hs - ((Equiv.Perm.sign τ : ℤ) : R) * hp

end split

section expand

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] {R : Type*}
    [CommRing R]

/-- Expansion of a determinant in the rows `λ_r v_r + e_r`. -/
theorem det_sumElim_smul_add (P : n → (n ⊕ m) → R) (l : m → R) (v e : m → (n ⊕ m) → R) :
    (of (Sum.elim P (fun r => l r • v r + e r)) : Matrix (n ⊕ m) (n ⊕ m) R).det =
      ∑ T : Finset m, (∏ r ∈ T, l r) *
        (of (Sum.elim P (T.piecewise v e)) : Matrix (n ⊕ m) (n ⊕ m) R).det := by
  let g : (m → (n ⊕ m) → R) →ₘₗ[R] R :=
    (MultilinearMap.currySum (detRowAlternating (n := n ⊕ m) (R := R)).toMultilinearMap) P
  have h1 := g.map_add_univ (fun r => l r • v r) e
  have h2 (T : Finset m) : g (T.piecewise (fun r => l r • v r) e) =
      (∏ r ∈ T, l r) * g (T.piecewise v e) := by
    have h := g.map_piecewise_smul l (T.piecewise v e) T
    simp only [smul_eq_mul, RingHom.id_apply] at h
    rw [← h]
    congr 1
    ext r : 1
    by_cases hr : r ∈ T <;> simp [hr]
  calc (of (Sum.elim P (fun r => l r • v r + e r)) : Matrix (n ⊕ m) (n ⊕ m) R).det
      = g ((fun r => l r • v r) + e) := rfl
    _ = ∑ T : Finset m, g (T.piecewise (fun r => l r • v r) e) := h1
    _ = _ := Finset.sum_congr rfl fun T _ => h2 T

end expand

/-- Congruent matrices have congruent determinants. -/
theorem dvd_det_sub {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] (d : R)
    (M N : Matrix n n R)
    (h : ∀ i j, d ∣ M i j - N i j) : d ∣ M.det - N.det := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact h i j

end Matrix
