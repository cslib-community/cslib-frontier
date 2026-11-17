/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Naimark
public import Mathlib.Algebra.Order.Chebyshev

/-!
# The Gowers–Hatami theorem

Approximate representations of finite groups are close to exact ones. Gowers and Hatami prove
this for normalized Schatten norms, with a dilation of the dimension
[Gowers and Hatami, §6, Theorems 6.9 and 6.12][GowersHatami2017] (arXiv:1510.04085v2). The
*averaged* form, whose hypothesis and conclusion are averages over the group and whose dilation is
built from the regular representation, is due to de la Salle
[de la Salle, §1.5, Theorem 1.4][delaSalle2025] (arXiv:2204.07084v2), in a tracial von Neumann
algebra with constant `13`. This file proves the vector-state form used for rigidity of nonlocal
games, with constant `1`: let `f : G → U(ℂ^ι)` be unitaries and `ψ` a vector with

`E_{x,y} ‖(f(x) f(y) - f(xy)) ψ‖² ≤ ε`.

Then there are an isometry `V : ℂ^ι → ℂ^ι ⊗ ℂ^G` and an exact unitary representation `g` of `G` on
`ℂ^ι ⊗ ℂ^G` with

`E_y ‖(f(y) - Vᴴ g(y) V) ψ‖² ≤ ε`

(`Cslib.Quantum.gowers_hatami`, and `Cslib.Quantum.gowers_hatami_vector` in the state-dependent
norm of the vector state). The proof needs no representation theory: `g` is the right regular
representation on the second factor (`Cslib.Quantum.regularRep`), and
`V ψ = |G|^{-1/2} ∑_x f(x) ψ ⊗ |x⟩` (`Cslib.Quantum.ghIsometry`). Then
`Vᴴ g(y) V = E_z f(z)ᴴ f(zy)` (`Cslib.Quantum.ghIsometry_compress`), so
`(f(y) - Vᴴ g(y) V) ψ = E_z f(z)ᴴ (f(z) f(y) - f(zy)) ψ`, and the bound follows from the convexity
of `‖·‖²`. Unitaries that multiply exactly on `ψ` are recovered exactly
(`Cslib.Quantum.mulVec_eq_compress_of_mul`).

## Main definitions

* `Cslib.Quantum.regularRep`: the right regular representation on `ℂ^ι ⊗ ℂ^G`.
* `Cslib.Quantum.ghIsometry`: the Gowers–Hatami isometry.

## Main results

* `Cslib.Quantum.regularRep_mul`, `Cslib.Quantum.regularRep_one`,
  `Cslib.Quantum.conjTranspose_regularRep_mul`: `g` is a unitary representation.
* `Cslib.Quantum.conjTranspose_ghIsometry_mul`: `V` is an isometry.
* `Cslib.Quantum.gowers_hatami`, `Cslib.Quantum.gowers_hatami_vector`: the Gowers–Hatami theorem.
* `Cslib.Quantum.mulVec_eq_compress_of_mul`: exact representations are recovered exactly.

## References

* [W. T. Gowers and O. Hatami, *Inverse and stability theorems for approximate representations
  of finite groups*][GowersHatami2017]
* [M. de la Salle, *Spectral gap and stability for groups and non-local games*][delaSalle2025]
-/

@[expose] public section

namespace Cslib.Quantum

open Matrix Finset

variable {G ι : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype ι] [DecidableEq ι]

/-- The **right regular representation** on `ℂ^ι ⊗ ℂ^G`: `(g(y) w)(i, z) = w(i, z y)`. -/
def regularRep (y : G) : Matrix (ι × G) (ι × G) ℂ :=
  Matrix.of fun p q => if q = (p.1, p.2 * y) then 1 else 0

omit [Fintype G] [Fintype ι] in
theorem regularRep_apply (y : G) (p q : ι × G) :
    regularRep y p q = if q = (p.1, p.2 * y) then 1 else 0 :=
  rfl

theorem regularRep_mul_apply {n : Type*} (y : G) (M : Matrix (ι × G) n ℂ) (i : ι) (z : G)
    (j : n) : (regularRep (ι := ι) y * M) (i, z) j = M (i, z * y) j := by
  rw [Matrix.mul_apply, sum_eq_single (i, z * y)
    (fun q _ hq => by simp [regularRep_apply, hq]) (by simp)]
  simp [regularRep_apply]

theorem regularRep_mul (y y' : G) :
    regularRep (ι := ι) y * regularRep y' = regularRep (y * y') := by
  ext ⟨i, z⟩ q
  rw [regularRep_mul_apply]
  simp [regularRep_apply, mul_assoc]

omit [Fintype G] [Fintype ι] in
theorem regularRep_one : regularRep (ι := ι) (1 : G) = 1 := by
  ext p q
  rw [regularRep_apply, mul_one, Prod.mk.eta, Matrix.one_apply]
  by_cases h : q = p
  · simp [h]
  · simp [h, Ne.symm h]

omit [Fintype G] [Fintype ι] in
theorem conjTranspose_regularRep (y : G) :
    (regularRep (ι := ι) y)ᴴ = regularRep y⁻¹ := by
  ext ⟨i, z⟩ ⟨i', z'⟩
  rw [conjTranspose_apply, regularRep_apply, regularRep_apply]
  by_cases h : i = i' ∧ z = z' * y
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h₁ : ¬ ((i, z) = (i', z' * y)) := fun he => h (Prod.mk.inj he)
    have h₂ : ¬ ((i', z') = (i, z * y⁻¹)) := by
      intro he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact h ⟨rfl, by simp⟩
    simp only at h₁ h₂ ⊢
    simp [h₁, h₂]

/-- The regular representation is unitary. -/
theorem conjTranspose_regularRep_mul (y : G) :
    (regularRep (ι := ι) y)ᴴ * regularRep y = 1 := by
  rw [conjTranspose_regularRep, regularRep_mul, inv_mul_cancel, regularRep_one]

variable (f : G → Matrix ι ι ℂ)

/-- The **Gowers–Hatami isometry** `V ψ = |G|^{-1/2} ∑_x f(x) ψ ⊗ |x⟩`. -/
noncomputable def ghIsometry : Matrix (ι × G) ι ℂ :=
  Matrix.of fun p j => ((√(Fintype.card G))⁻¹ : ℝ) * f p.2 p.1 j

omit [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι] in
theorem ghIsometry_apply (p : ι × G) (j : ι) :
    ghIsometry f p j = ((√(Fintype.card G))⁻¹ : ℝ) * f p.2 p.1 j :=
  rfl

omit [Group G] [DecidableEq G] in
private theorem ghScale_sq : (((√(Fintype.card G))⁻¹ : ℝ) : ℂ) * (((√(Fintype.card G))⁻¹ : ℝ) : ℂ) =
    ((Fintype.card G : ℂ))⁻¹ := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  push_cast
  rfl

/-- `Vᴴ g(y) V = E_z f(z)ᴴ f(zy)`. -/
theorem ghIsometry_compress (y : G) :
    (ghIsometry f)ᴴ * regularRep y * ghIsometry f =
      ((Fintype.card G : ℂ))⁻¹ • ∑ z, (f z)ᴴ * f (z * y) := by
  ext j j'
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_prod_type, sum_comm, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [Matrix.mul_apply, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [regularRep_mul_apply, conjTranspose_apply, ghIsometry_apply, ghIsometry_apply,
    conjTranspose_apply, star_mul', Complex.star_def, Complex.conj_ofReal, ← ghScale_sq]
  ring

omit [DecidableEq G] in
/-- The Gowers–Hatami isometry is an isometry when the `f(x)` are unitary. -/
theorem conjTranspose_ghIsometry_mul (hf : ∀ x, (f x)ᴴ * f x = 1) :
    (ghIsometry f)ᴴ * ghIsometry f = 1 := by
  classical
  have h := ghIsometry_compress f 1
  simp only [regularRep_one, Matrix.mul_one, mul_one, hf, sum_const, card_univ] at h
  rw [h, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast
    Fintype.card_ne_zero), one_smul]

omit [DecidableEq G] [DecidableEq ι] in
/-- `‖(∑_x w_x)/|G|‖² ≤ (∑_x ‖w_x‖²)/|G|`. -/
private theorem norm_avg_sq_le (w : G → EuclideanSpace ℂ ι) :
    ‖((Fintype.card G : ℂ))⁻¹ • ∑ x, w x‖ ^ 2 ≤ ((Fintype.card G : ℝ))⁻¹ * ∑ x, ‖w x‖ ^ 2 := by
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have h₁ : ‖((Fintype.card G : ℂ))⁻¹ • ∑ x, w x‖ ≤ ((Fintype.card G : ℝ))⁻¹ * ∑ x, ‖w x‖ := by
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
  have h₂ := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun x => ‖w x‖)
  rw [card_univ] at h₂
  calc ‖((Fintype.card G : ℂ))⁻¹ • ∑ x, w x‖ ^ 2
      ≤ (((Fintype.card G : ℝ))⁻¹ * ∑ x, ‖w x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    _ = ((Fintype.card G : ℝ))⁻¹ ^ 2 * (∑ x, ‖w x‖) ^ 2 := by ring
    _ ≤ ((Fintype.card G : ℝ))⁻¹ ^ 2 * (Fintype.card G * ∑ x, ‖w x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h₂ (by positivity)
    _ = ((Fintype.card G : ℝ))⁻¹ * ∑ x, ‖w x‖ ^ 2 := by field_simp

/-- **The Gowers–Hatami theorem**, averaged form in a vector state
[de la Salle, §1.5, Theorem 1.4][delaSalle2025]: for unitaries `f(x)` and a vector `ψ`, the exact
representation `g` (`regularRep`) and the isometry `V` (`ghIsometry`) satisfy
`E_y ‖(f(y) - Vᴴ g(y) V) ψ‖² ≤ E_{x,y} ‖(f(x) f(y) - f(xy)) ψ‖²`. -/
theorem gowers_hatami (hf : ∀ x, (f x)ᴴ * f x = 1) (ψ : EuclideanSpace ℂ ι) :
    (∑ y, ‖(WithLp.toLp 2 ((f y - (ghIsometry f)ᴴ * regularRep y * ghIsometry f) *ᵥ ψ.ofLp) :
      EuclideanSpace ℂ ι)‖ ^ 2) / Fintype.card G ≤
    (∑ x, ∑ y, ‖(WithLp.toLp 2 ((f x * f y - f (x * y)) *ᵥ ψ.ofLp) :
      EuclideanSpace ℂ ι)‖ ^ 2) / (Fintype.card G) ^ 2 := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hf' : ∀ x, ((f x)ᴴ)ᴴ * (f x)ᴴ = 1 := fun x => by
    rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp (hf x)
  -- `f(y) - Vᴴ g(y) V = E_x f(x)ᴴ (f(x) f(y) - f(xy))`.
  have hdiff : ∀ y, f y - (ghIsometry f)ᴴ * regularRep y * ghIsometry f =
      ((Fintype.card G : ℂ))⁻¹ • ∑ x, (f x)ᴴ * (f x * f y - f (x * y)) := fun y => by
    rw [ghIsometry_compress]
    simp only [Matrix.mul_sub, ← Matrix.mul_assoc, hf, Matrix.one_mul, sum_sub_distrib, sum_const,
      card_univ, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have key : ∀ y, ‖(WithLp.toLp 2 ((f y - (ghIsometry f)ᴴ * regularRep y * ghIsometry f) *ᵥ
      ψ.ofLp) : EuclideanSpace ℂ ι)‖ ^ 2 ≤ ((Fintype.card G : ℝ))⁻¹ *
      ∑ x, ‖(WithLp.toLp 2 ((f x * f y - f (x * y)) *ᵥ ψ.ofLp) : EuclideanSpace ℂ ι)‖ ^ 2 := by
    intro y
    have hw : (WithLp.toLp 2 ((f y - (ghIsometry f)ᴴ * regularRep y * ghIsometry f) *ᵥ ψ.ofLp) :
        EuclideanSpace ℂ ι) = ((Fintype.card G : ℂ))⁻¹ • ∑ x, (WithLp.toLp 2
          ((f x)ᴴ *ᵥ ((f x * f y - f (x * y)) *ᵥ ψ.ofLp)) : EuclideanSpace ℂ ι) := by
      rw [hdiff, smul_mulVec, sum_mulVec, WithLp.toLp_smul, WithLp.toLp_sum]
      simp only [mulVec_mulVec]
    rw [hw]
    refine (norm_avg_sq_le _).trans (le_of_eq ?_)
    congr 1
    refine sum_congr rfl fun x _ => ?_
    have := norm_toLp_mulVec_of_conjTranspose_mul_self (hf' x)
      (WithLp.toLp 2 ((f x * f y - f (x * y)) *ᵥ ψ.ofLp))
    rw [WithLp.ofLp_toLp] at this
    rw [this]
  have hcR : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  calc (∑ y, ‖(WithLp.toLp 2 ((f y - (ghIsometry f)ᴴ * regularRep y * ghIsometry f) *ᵥ
        ψ.ofLp) : EuclideanSpace ℂ ι)‖ ^ 2) / Fintype.card G
      ≤ (∑ y, ((Fintype.card G : ℝ))⁻¹ * ∑ x, ‖(WithLp.toLp 2 ((f x * f y - f (x * y)) *ᵥ
          ψ.ofLp) : EuclideanSpace ℂ ι)‖ ^ 2) / Fintype.card G :=
        div_le_div_of_nonneg_right (sum_le_sum fun y _ => key y) hcR.le
    _ = _ := by
      rw [← mul_sum, sum_comm]
      field_simp

open scoped MatrixOrder in
/-- **The Gowers–Hatami theorem in the state calculus**: for the vector state of a unit vector
`ψ`, `E_y ‖f(y) - Vᴴ g(y) V‖²_ψ ≤ E_{x,y} ‖f(x) f(y) - f(xy)‖²_ψ`. -/
theorem gowers_hatami_vector (hf : ∀ x, (f x)ᴴ * f x = 1) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) :
    (∑ y, (AlgState.vector ψ hψ).norm
        (f y - (ghIsometry f)ᴴ * regularRep y * ghIsometry f) ^ 2) / Fintype.card G ≤
      (∑ x, ∑ y, (AlgState.vector ψ hψ).norm (f x * f y - f (x * y)) ^ 2) /
        (Fintype.card G) ^ 2 := by
  simp only [AlgState.norm_vector]
  exact gowers_hatami f hf ψ

/-- **Exact representations are recovered exactly**: if the unitaries `f(x)` multiply like `G` on
the vector `ψ`, then `f(y) ψ = Vᴴ g(y) V ψ` for every `y`. -/
theorem mulVec_eq_compress_of_mul (hf : ∀ x, (f x)ᴴ * f x = 1) (ψ : EuclideanSpace ℂ ι)
    (hrep : ∀ x y, (f x * f y) *ᵥ ψ.ofLp = f (x * y) *ᵥ ψ.ofLp) (y : G) :
    f y *ᵥ ψ.ofLp = ((ghIsometry f)ᴴ * regularRep y * ghIsometry f) *ᵥ ψ.ofLp := by
  have h := gowers_hatami f hf ψ
  simp only [sub_mulVec, hrep, sub_self, WithLp.toLp_zero, _root_.norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero, zero_div] at h
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hc, zero_mul] at h
  have hsum := (sum_eq_zero_iff_of_nonneg fun _ _ => by positivity).mp
    (le_antisymm h (by positivity)) y (mem_univ y)
  rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, WithLp.toLp_eq_zero] at hsum
  exact sub_eq_zero.mp hsum

end Cslib.Quantum
