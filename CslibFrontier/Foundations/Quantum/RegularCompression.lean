/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.AlgState
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.LinearAlgebra.Matrix.Permutation
import CslibFrontier.Foundations.Analysis.InnerProductSpace.PiL2

/-!
# Compression of the regular representation

A step toward the Gowers–Hatami stability theorem for approximate representations of finite
groups. Gowers and Hatami show that an approximate representation is close to an exact one after
adjusting the dimension, in normalized Schatten norms
[Gowers and Hatami, §6, Theorems 6.9 and 6.12][GowersHatami2017] (arXiv:1510.04085v2,
pp. 32–33); de la Salle's averaged version for unitarily invariant seminorms also bounds the
defect of the isometry, `‖P - w w*‖ ≤ 4ε`
[de la Salle, §1.5, Theorem 1.4][delaSalle2025] (arXiv:2204.07084v2, pp. 5–6). This file proves
the first step of both proofs, the compression of the regular representation, in the vector-state
form used for rigidity of nonlocal games; it follows the first paragraph of the proof of
[de la Salle, §1.5, Lemma 1.6][delaSalle2025] (p. 6). The dimension or isometry-defect control of
the full stability theorem is not formalized here.

Let `f : G → U(ℂ^ι)` be unitaries and `ψ` a vector. The right regular representation `g` on the
second factor of `ℂ^ι ⊗ ℂ^G` (`Cslib.Quantum.regularRep`, the permutation matrices of
`(i, z) ↦ (i, z y)`) and the isometry `V ψ = |G|^{-1/2} ∑_x f(x) ψ ⊗ |x⟩`
(`Cslib.Quantum.regularIsometry`) satisfy

`E_y ‖(f(y) - Vᴴ g(y) V) ψ‖² ≤ E_{x,y} ‖(f(x) f(y) - f(xy)) ψ‖²`

(`Cslib.Quantum.sum_norm_sub_compress_le`, and `Cslib.Quantum.sum_vector_norm_sub_compress_le` in
the state-dependent norm of the vector state). The proof needs no representation theory:
`Vᴴ g(y) V = E_z f(z)ᴴ f(zy)` (`Cslib.Quantum.regularIsometry_compress`), so
`(f(y) - Vᴴ g(y) V) ψ = E_z f(z)ᴴ (f(z) f(y) - f(zy)) ψ`, and the bound follows from the convexity
of `‖·‖²`. Before compressing, `V` intertwines `f` and `g` up to exactly the same error, for any
matrices `f(x)`: `E_y ‖(V f(y) - g(y) V) ψ‖² = E_{x,y} ‖(f(x) f(y) - f(xy)) ψ‖²`
(`Cslib.Quantum.sum_norm_regularIsometry_mul_sub_eq`). Unitaries that multiply exactly on `ψ` are
recovered exactly (`Cslib.Quantum.mulVec_eq_compress_of_mul`).

## Main definitions

* `Cslib.Quantum.regularRep`: the right regular representation on `ℂ^ι ⊗ ℂ^G`.
* `Cslib.Quantum.regularIsometry`: the averaging isometry.

## Main results

* `Cslib.Quantum.regularRep_mul`, `Cslib.Quantum.regularRep_one`,
  `Cslib.Quantum.conjTranspose_regularRep_mul`: `g` is a unitary representation.
* `Cslib.Quantum.conjTranspose_regularIsometry_mul`: `V` is an isometry.
* `Cslib.Quantum.sum_norm_regularIsometry_mul_sub_eq`: `V` intertwines `f` and `g` approximately.
* `Cslib.Quantum.sum_norm_sub_compress_le`, `Cslib.Quantum.sum_vector_norm_sub_compress_le`: the
  compression bound.
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

/-- The permutation `(i, z) ↦ (i, z y)` of `ι × G`. -/
def regularPerm (y : G) : Equiv.Perm (ι × G) :=
  Equiv.prodCongr (Equiv.refl ι) (Equiv.mulRight y)

omit [Fintype G] [DecidableEq G] [Fintype ι] [DecidableEq ι] in
private theorem regularPerm_mul (y y' : G) :
    regularPerm (ι := ι) (y * y') = regularPerm y' * regularPerm y := by
  ext p <;> simp [regularPerm, mul_assoc]

omit [Fintype G] [DecidableEq G] [Fintype ι] [DecidableEq ι] in
private theorem regularPerm_one : regularPerm (ι := ι) (1 : G) = 1 := by
  ext p <;> simp [regularPerm]

omit [Fintype G] [DecidableEq G] [Fintype ι] [DecidableEq ι] in
private theorem regularPerm_inv (y : G) : (regularPerm (ι := ι) y)⁻¹ = regularPerm y⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← regularPerm_mul, inv_mul_cancel, regularPerm_one]

/-- The **right regular representation** on `ℂ^ι ⊗ ℂ^G`, `(g(y) w)(i, z) = w(i, z y)`: the
permutation matrix of `(i, z) ↦ (i, z y)`. -/
def regularRep (y : G) : Matrix (ι × G) (ι × G) ℂ :=
  (regularPerm y).permMatrix ℂ

omit [Fintype G] [Fintype ι] in
theorem regularRep_apply (y : G) (p q : ι × G) :
    regularRep y p q = if q = (p.1, p.2 * y) then 1 else 0 := by
  simp [regularRep, regularPerm, PEquiv.toMatrix_apply, eq_comm]
  rfl

private theorem regularRep_mul_apply {n : Type*} (y : G) (M : Matrix (ι × G) n ℂ) (i : ι)
    (z : G) (j : n) : (regularRep (ι := ι) y * M) (i, z) j = M (i, z * y) j := by
  rw [Matrix.mul_apply, sum_eq_single (i, z * y)
    (fun q _ hq => by simp [regularRep_apply, hq]) (by simp)]
  simp [regularRep_apply]

theorem regularRep_mul (y y' : G) :
    regularRep (ι := ι) y * regularRep y' = regularRep (y * y') := by
  rw [regularRep, regularRep, regularRep, regularPerm_mul, permMatrix_mul]

omit [Fintype G] [Fintype ι] in
theorem regularRep_one : regularRep (ι := ι) (1 : G) = 1 := by
  rw [regularRep, regularPerm_one, permMatrix_one]

omit [Fintype G] [Fintype ι] in
theorem conjTranspose_regularRep (y : G) :
    (regularRep (ι := ι) y)ᴴ = regularRep y⁻¹ := by
  rw [regularRep, regularRep, conjTranspose_permMatrix, regularPerm_inv]

/-- The regular representation is unitary. -/
theorem conjTranspose_regularRep_mul (y : G) :
    (regularRep (ι := ι) y)ᴴ * regularRep y = 1 := by
  rw [conjTranspose_regularRep, regularRep_mul, inv_mul_cancel, regularRep_one]

variable (f : G → Matrix ι ι ℂ)

/-- The **averaging isometry** `V ψ = |G|^{-1/2} ∑_x f(x) ψ ⊗ |x⟩`. -/
noncomputable def regularIsometry : Matrix (ι × G) ι ℂ :=
  Matrix.of fun p j => ((√(Fintype.card G))⁻¹ : ℝ) * f p.2 p.1 j

omit [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι] in
theorem regularIsometry_apply (p : ι × G) (j : ι) :
    regularIsometry f p j = ((√(Fintype.card G))⁻¹ : ℝ) * f p.2 p.1 j :=
  rfl

omit [Group G] [DecidableEq G] in
private theorem regularScale_sq :
    (((√(Fintype.card G))⁻¹ : ℝ) : ℂ) * (((√(Fintype.card G))⁻¹ : ℝ) : ℂ) =
    ((Fintype.card G : ℂ))⁻¹ := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  push_cast
  rfl

/-- `Vᴴ g(y) V = E_z f(z)ᴴ f(zy)`. -/
theorem regularIsometry_compress (y : G) :
    (regularIsometry f)ᴴ * regularRep y * regularIsometry f =
      ((Fintype.card G : ℂ))⁻¹ • ∑ z, (f z)ᴴ * f (z * y) := by
  ext j j'
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_prod_type, sum_comm, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [Matrix.mul_apply, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [regularRep_mul_apply, conjTranspose_apply, regularIsometry_apply, regularIsometry_apply,
    conjTranspose_apply, star_mul', Complex.star_def, Complex.conj_ofReal, ← regularScale_sq]
  ring

omit [DecidableEq G] in
/-- The averaging isometry is an isometry when the `f(x)` are unitary. -/
theorem conjTranspose_regularIsometry_mul (hf : ∀ x, (f x)ᴴ * f x = 1) :
    (regularIsometry f)ᴴ * regularIsometry f = 1 := by
  classical
  have h := regularIsometry_compress f 1
  simp only [regularRep_one, Matrix.mul_one, mul_one, hf, sum_const, card_univ] at h
  rw [h, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast
    Fintype.card_ne_zero), one_smul]

/-- The rows of `V f(y) - g(y) V` are the multiplicative defects: row `(i, z)` is
`|G|^{-1/2} (f(z) f(y) - f(zy))_i`. -/
private theorem regularIsometry_mul_sub_apply (y : G) (i : ι) (z : G) (j : ι) :
    (regularIsometry f * f y - regularRep y * regularIsometry f : Matrix (ι × G) ι ℂ) (i, z) j =
      (((√(Fintype.card G))⁻¹ : ℝ) : ℂ) * (f z * f y - f (z * y)) i j := by
  rw [Matrix.sub_apply, regularRep_mul_apply, Matrix.mul_apply, Matrix.sub_apply, mul_sub,
    Matrix.mul_apply, mul_sum]
  simp only [regularIsometry_apply, mul_assoc]

/-- **The averaging isometry intertwines approximately**, for any matrices `f(x)`:
`E_y ‖(V f(y) - g(y) V) ψ‖² = E_{x,y} ‖(f(x) f(y) - f(xy)) ψ‖²`. -/
theorem sum_norm_regularIsometry_mul_sub_eq (ψ : EuclideanSpace ℂ ι) :
    (∑ y, ‖(WithLp.toLp 2 ((regularIsometry f * f y - regularRep y * regularIsometry f) *ᵥ
      ψ.ofLp) : EuclideanSpace ℂ (ι × G))‖ ^ 2) / Fintype.card G =
    (∑ x, ∑ y, ‖(WithLp.toLp 2 ((f x * f y - f (x * y)) *ᵥ ψ.ofLp) :
      EuclideanSpace ℂ ι)‖ ^ 2) / (Fintype.card G) ^ 2 := by
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hcsq : ((√(Fintype.card G))⁻¹ : ℝ) ^ 2 = ((Fintype.card G : ℝ))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hc.le]
  have hrow : ∀ y, ‖(WithLp.toLp 2 ((regularIsometry f * f y - regularRep y * regularIsometry f) *ᵥ
      ψ.ofLp) : EuclideanSpace ℂ (ι × G))‖ ^ 2 = ((Fintype.card G : ℝ))⁻¹ *
      ∑ z, ‖(WithLp.toLp 2 ((f z * f y - f (z * y)) *ᵥ ψ.ofLp) : EuclideanSpace ℂ ι)‖ ^ 2 := by
    intro y
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have : ((regularIsometry f * f y - regularRep y * regularIsometry f) *ᵥ ψ.ofLp) (i, z) =
        (((√(Fintype.card G))⁻¹ : ℝ) : ℂ) * (((f z * f y - f (z * y)) *ᵥ ψ.ofLp) i) := by
      simp only [mulVec, dotProduct, regularIsometry_mul_sub_apply, mul_sum, mul_assoc]
    simp only [this, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs, hcsq]
  simp only [hrow, ← mul_sum]
  rw [sum_comm]
  field_simp

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

/-- **Compression of the regular representation**, a step toward the Gowers–Hatami theorem
(the first paragraph of the proof of [de la Salle, §1.5, Lemma 1.6][delaSalle2025]): for unitaries
`f(x)` and a vector `ψ`, the exact representation `g` (`regularRep`) and the isometry `V`
(`regularIsometry`) satisfy `E_y ‖(f(y) - Vᴴ g(y) V) ψ‖² ≤ E_{x,y} ‖(f(x) f(y) - f(xy)) ψ‖²`. -/
theorem sum_norm_sub_compress_le (hf : ∀ x, (f x)ᴴ * f x = 1) (ψ : EuclideanSpace ℂ ι) :
    (∑ y, ‖(WithLp.toLp 2 ((f y - (regularIsometry f)ᴴ * regularRep y * regularIsometry f) *ᵥ
      ψ.ofLp) :
      EuclideanSpace ℂ ι)‖ ^ 2) / Fintype.card G ≤
    (∑ x, ∑ y, ‖(WithLp.toLp 2 ((f x * f y - f (x * y)) *ᵥ ψ.ofLp) :
      EuclideanSpace ℂ ι)‖ ^ 2) / (Fintype.card G) ^ 2 := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hf' : ∀ x, ((f x)ᴴ)ᴴ * (f x)ᴴ = 1 := fun x => by
    rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp (hf x)
  -- `f(y) - Vᴴ g(y) V = E_x f(x)ᴴ (f(x) f(y) - f(xy))`.
  have hdiff : ∀ y, f y - (regularIsometry f)ᴴ * regularRep y * regularIsometry f =
      ((Fintype.card G : ℂ))⁻¹ • ∑ x, (f x)ᴴ * (f x * f y - f (x * y)) := fun y => by
    rw [regularIsometry_compress]
    simp only [Matrix.mul_sub, ← Matrix.mul_assoc, hf, Matrix.one_mul, sum_sub_distrib, sum_const,
      card_univ, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have key : ∀ y, ‖(WithLp.toLp 2 ((f y - (regularIsometry f)ᴴ * regularRep y *
      regularIsometry f) *ᵥ
      ψ.ofLp) : EuclideanSpace ℂ ι)‖ ^ 2 ≤ ((Fintype.card G : ℝ))⁻¹ *
      ∑ x, ‖(WithLp.toLp 2 ((f x * f y - f (x * y)) *ᵥ ψ.ofLp) : EuclideanSpace ℂ ι)‖ ^ 2 := by
    intro y
    have hw : (WithLp.toLp 2 ((f y - (regularIsometry f)ᴴ * regularRep y * regularIsometry f) *ᵥ
        ψ.ofLp) :
        EuclideanSpace ℂ ι) = ((Fintype.card G : ℂ))⁻¹ • ∑ x, (WithLp.toLp 2
          ((f x)ᴴ *ᵥ ((f x * f y - f (x * y)) *ᵥ ψ.ofLp)) : EuclideanSpace ℂ ι) := by
      rw [hdiff, smul_mulVec, sum_mulVec, WithLp.toLp_smul, WithLp.toLp_sum]
      simp only [mulVec_mulVec]
    rw [hw]
    refine (norm_avg_sq_le _).trans (le_of_eq ?_)
    congr 1
    refine sum_congr rfl fun x _ => ?_
    have := Matrix.norm_toLp_mulVec_of_conjTranspose_mul_self (hf' x)
      (WithLp.toLp 2 ((f x * f y - f (x * y)) *ᵥ ψ.ofLp))
    rw [WithLp.ofLp_toLp] at this
    rw [this]
  have hcR : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  calc (∑ y, ‖(WithLp.toLp 2 ((f y - (regularIsometry f)ᴴ * regularRep y * regularIsometry f) *ᵥ
        ψ.ofLp) : EuclideanSpace ℂ ι)‖ ^ 2) / Fintype.card G
      ≤ (∑ y, ((Fintype.card G : ℝ))⁻¹ * ∑ x, ‖(WithLp.toLp 2 ((f x * f y - f (x * y)) *ᵥ
          ψ.ofLp) : EuclideanSpace ℂ ι)‖ ^ 2) / Fintype.card G :=
        div_le_div_of_nonneg_right (sum_le_sum fun y _ => key y) hcR.le
    _ = _ := by
      rw [← mul_sum, sum_comm]
      field_simp

open scoped MatrixOrder in
/-- **Compression of the regular representation in the state calculus**: for the vector state
of a unit vector `ψ`, `E_y ‖f(y) - Vᴴ g(y) V‖²_ψ ≤ E_{x,y} ‖f(x) f(y) - f(xy)‖²_ψ`. -/
theorem sum_vector_norm_sub_compress_le (hf : ∀ x, (f x)ᴴ * f x = 1) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) :
    (∑ y, (AlgState.vector ψ hψ).norm
        (f y - (regularIsometry f)ᴴ * regularRep y * regularIsometry f) ^ 2) / Fintype.card G ≤
      (∑ x, ∑ y, (AlgState.vector ψ hψ).norm (f x * f y - f (x * y)) ^ 2) /
        (Fintype.card G) ^ 2 := by
  simp only [AlgState.norm_vector]
  exact sum_norm_sub_compress_le f hf ψ

/-- **Exact representations are recovered exactly**: if the unitaries `f(x)` multiply like `G` on
the vector `ψ`, then `f(y) ψ = Vᴴ g(y) V ψ` for every `y`. -/
theorem mulVec_eq_compress_of_mul (hf : ∀ x, (f x)ᴴ * f x = 1) (ψ : EuclideanSpace ℂ ι)
    (hrep : ∀ x y, (f x * f y) *ᵥ ψ.ofLp = f (x * y) *ᵥ ψ.ofLp) (y : G) :
    f y *ᵥ ψ.ofLp = ((regularIsometry f)ᴴ * regularRep y * regularIsometry f) *ᵥ ψ.ofLp := by
  have h := sum_norm_sub_compress_le f hf ψ
  simp only [sub_mulVec, hrep, sub_self, WithLp.toLp_zero, _root_.norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero, zero_div] at h
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hc, zero_mul] at h
  have hsum := (sum_eq_zero_iff_of_nonneg fun _ _ => by positivity).mp
    (le_antisymm h (by positivity)) y (mem_univ y)
  rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, WithLp.toLp_eq_zero] at hsum
  exact sub_eq_zero.mp hsum

end Cslib.Quantum
