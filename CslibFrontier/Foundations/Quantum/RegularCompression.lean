/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.AlgState
public import CslibFrontier.Foundations.Quantum.Algebra.Expect
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
the first step of both proofs, the compression of the regular representation, in the
state-dependent form used for rigidity of nonlocal games; it follows the first paragraph of the
proof of [de la Salle, §1.5, Lemma 1.6][delaSalle2025] (p. 6). The dimension or isometry-defect
control of the full stability theorem is not formalized here; it is tracked in
[#6149](https://github.com/cslib-community/cslib-frontier/issues/6149) (milestone M2).

Let `f : G → U(ℂ^ι)` be unitaries and `φ` a state. The right regular representation `g` on the
second factor of `ℂ^ι ⊗ ℂ^G` (`Cslib.Quantum.regularRep`, the permutation matrices of
`(i, z) ↦ (i, z y)`) and the isometry `V ψ = |G|^{-1/2} ∑_x f(x) ψ ⊗ |x⟩`
(`Cslib.Quantum.regularIsometry`) satisfy

`E_y ‖f(y) - Vᴴ g(y) V‖²_φ ≤ E_{x,y} ‖f(x) f(y) - f(xy)‖²_φ`

in every state (`Cslib.Quantum.expect_norm_sub_compress_sq_le`; with sums, in a vector state,
`Cslib.Quantum.sum_vector_norm_sub_compress_le`). The proof needs no representation theory:
`Vᴴ g(y) V = E_z f(z)ᴴ f(zy)` (`Cslib.Quantum.regularIsometry_compress`), so
`f(y) - Vᴴ g(y) V = E_z f(z)ᴴ (f(z) f(y) - f(zy))`, and the bound is Jensen's inequality with
contractions for the state norm (`Cslib.Quantum.AlgState.norm_expect_mul_sq_le`). Before
compressing, `V` intertwines `f` and `g` up to exactly the same error, for any matrices `f(x)` and
vectors `ψ`: `E_y ‖(V f(y) - g(y) V) ψ‖² = E_{x,y} ‖(f(x) f(y) - f(xy)) ψ‖²`
(`Cslib.Quantum.sum_norm_regularIsometry_mul_sub_eq`). Exact representations are recovered exactly,
`Vᴴ g(y) V = f(y)` (`Cslib.Quantum.compress_eq_of_mul`).

## Main definitions

* `Cslib.Quantum.regularRep`: the right regular representation on `ℂ^ι ⊗ ℂ^G`.
* `Cslib.Quantum.regularIsometry`: the averaging isometry.

## Main results

* `Cslib.Quantum.regularRep_mul`, `Cslib.Quantum.regularRep_one`,
  `Cslib.Quantum.conjTranspose_regularRep_mul`: `g` is a unitary representation.
* `Cslib.Quantum.conjTranspose_regularIsometry_mul`: `V` is an isometry.
* `Cslib.Quantum.regularIsometry_mul_sub_gram`: the exact Gram matrix of the intertwining error.
* `Cslib.Quantum.sum_norm_regularIsometry_mul_sub_eq`: the intertwining error in a vector.
* `Cslib.Quantum.expect_norm_sub_compress_sq_le`: the compression bound, in every state.
* `Cslib.Quantum.sum_vector_norm_sub_compress_le`: the compression bound in a vector state.
* `Cslib.Quantum.compress_eq_of_mul`: exact representations are recovered exactly.

## References

* [W. T. Gowers and O. Hatami, *Inverse and stability theorems for approximate representations
  of finite groups*][GowersHatami2017]
* [M. de la Salle, *Spectral gap and stability for groups and non-local games*][delaSalle2025]
-/

@[expose] public section

namespace Cslib.Quantum

open Matrix Finset
open scoped BigOperators

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
  simp only [regularRep, regularPerm, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, eq_comm]
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

/-- **Compression of the regular representation**: `Vᴴ g(y) V = E_z f(z)ᴴ f(zy)`. -/
theorem regularIsometry_compress (y : G) :
    (regularIsometry f)ᴴ * regularRep y * regularIsometry f = 𝔼 z, (f z)ᴴ * f (z * y) := by
  rw [expect_univ, ← NNRat.cast_smul_eq_nnqsmul ℂ]
  push_cast
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
  simpa only [regularRep_one, Matrix.mul_one, mul_one, hf, Fintype.expect_const] using
    regularIsometry_compress f 1

/-- The rows of `V f(y) - g(y) V` are the multiplicative defects: row `(i, z)` is
`|G|^{-1/2} (f(z) f(y) - f(zy))_i`. -/
private theorem regularIsometry_mul_sub_apply (y : G) (i : ι) (z : G) (j : ι) :
    (regularIsometry f * f y - regularRep y * regularIsometry f : Matrix (ι × G) ι ℂ) (i, z) j =
      (((√(Fintype.card G))⁻¹ : ℝ) : ℂ) * (f z * f y - f (z * y)) i j := by
  rw [Matrix.sub_apply, regularRep_mul_apply, Matrix.mul_apply, Matrix.sub_apply, mul_sub,
    Matrix.mul_apply, mul_sum]
  simp only [regularIsometry_apply, mul_assoc]

/-- The squared error of the averaging isometry at a group element is the average
of the Gram matrices of the right multiplication defects at that element. -/
theorem regularIsometry_mul_sub_gram (y : G) :
    let D := regularIsometry f * f y - regularRep y * regularIsometry f
    Dᴴ * D = 𝔼 z, (f z * f y - f (z * y))ᴴ * (f z * f y - f (z * y)) := by
  intro D
  rw [expect_univ, ← NNRat.cast_smul_eq_nnqsmul ℂ]
  push_cast
  ext j k
  rw [Matrix.mul_apply, Fintype.sum_prod_type, sum_comm, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [Matrix.mul_apply, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [D, conjTranspose_apply, regularIsometry_mul_sub_apply, star_mul',
    Complex.star_def, Complex.conj_ofReal, ← regularScale_sq]
  ring

/-- **The averaging isometry intertwines approximately**, for any matrices `f(x)`:
`E_y ‖(V f(y) - g(y) V) ψ‖² = E_{x,y} ‖(f(x) f(y) - f(xy)) ψ‖²`. -/
theorem sum_norm_regularIsometry_mul_sub_eq (ψ : EuclideanSpace ℂ ι) :
    (∑ y, ‖(WithLp.toLp 2 ((regularIsometry f * f y - regularRep y * regularIsometry f) *ᵥ
      ψ.ofLp) : EuclideanSpace ℂ (ι × G))‖ ^ 2) / Fintype.card G =
    (∑ x, ∑ y, ‖(WithLp.toLp 2 ((f x * f y - f (x * y)) *ᵥ ψ.ofLp) :
      EuclideanSpace ℂ ι)‖ ^ 2) / (Fintype.card G) ^ 2 := by
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hrow (y : G) :
      ‖(WithLp.toLp 2 ((regularIsometry f * f y - regularRep y * regularIsometry f) *ᵥ
        ψ.ofLp) : EuclideanSpace ℂ (ι × G))‖ ^ 2 = ((Fintype.card G : ℝ))⁻¹ *
      ∑ z, ‖(WithLp.toLp 2 ((f z * f y - f (z * y)) *ᵥ ψ.ofLp) : EuclideanSpace ℂ ι)‖ ^ 2 := by
    rw [Matrix.norm_toLp_mulVec_sq_eq, regularIsometry_mul_sub_gram]
    simp only [Finset.expect, ← NNRat.cast_smul_eq_nnqsmul ℂ, smul_mulVec, dotProduct_smul,
      sum_mulVec, dotProduct_sum, smul_eq_mul, NNRat.cast_inv, NNRat.cast_natCast, card_univ]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]
    simp only [Matrix.norm_toLp_mulVec_sq_eq]
  simp only [hrow, ← mul_sum]
  rw [sum_comm]
  field_simp

open scoped MatrixOrder in
/-- **Compression of the regular representation**, a step toward the Gowers–Hatami theorem
(the first paragraph of the proof of [de la Salle, §1.5, Lemma 1.6][delaSalle2025]): for unitaries
`f(x)`, the exact representation `g` (`regularRep`) and the isometry `V` (`regularIsometry`)
satisfy, in every state `φ`,
`E_y ‖f(y) - Vᴴ g(y) V‖²_φ ≤ E_{x,y} ‖f(x) f(y) - f(xy)‖²_φ`. -/
theorem expect_norm_sub_compress_sq_le (φ : AlgState (Matrix ι ι ℂ))
    (hf : ∀ x, (f x)ᴴ * f x = 1) :
    𝔼 y, φ.norm (f y - (regularIsometry f)ᴴ * regularRep y * regularIsometry f) ^ 2 ≤
      𝔼 x, 𝔼 y, φ.norm (f x * f y - f (x * y)) ^ 2 := by
  rw [expect_comm]
  refine expect_le_expect fun y _ => ?_
  have hdiff : f y - (regularIsometry f)ᴴ * regularRep y * regularIsometry f =
      𝔼 x, (f x)ᴴ * (f x * f y - f (x * y)) := by
    simp only [regularIsometry_compress, Matrix.mul_sub, ← Matrix.mul_assoc, hf,
      Matrix.one_mul, expect_sub_distrib, expect_const univ_nonempty]
  rw [hdiff]
  exact φ.norm_expect_mul_sq_le _ fun x _ => by
    rw [star_eq_conjTranspose, conjTranspose_conjTranspose, mul_eq_one_comm.mp (hf x)]

open scoped MatrixOrder in
/-- The compression bound in a vector state, with sums: for a unit vector `ψ`,
`E_y ‖f(y) - Vᴴ g(y) V‖²_ψ ≤ E_{x,y} ‖f(x) f(y) - f(xy)‖²_ψ`. -/
theorem sum_vector_norm_sub_compress_le (hf : ∀ x, (f x)ᴴ * f x = 1) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) :
    (∑ y, (AlgState.vector ψ hψ).norm
        (f y - (regularIsometry f)ᴴ * regularRep y * regularIsometry f) ^ 2) / Fintype.card G ≤
      (∑ x, ∑ y, (AlgState.vector ψ hψ).norm (f x * f y - f (x * y)) ^ 2) /
        (Fintype.card G) ^ 2 := by
  simpa only [Fintype.expect_eq_sum_div_card, ← sum_div, div_div, ← sq] using
    expect_norm_sub_compress_sq_le f (AlgState.vector ψ hψ) hf

/-- **Exact representations are recovered exactly**: if the unitaries `f(x)` multiply like `G`,
then `Vᴴ g(y) V = f(y)` for every `y`. -/
theorem compress_eq_of_mul (hf : ∀ x, (f x)ᴴ * f x = 1) (hrep : ∀ x y, f x * f y = f (x * y))
    (y : G) : (regularIsometry f)ᴴ * regularRep y * regularIsometry f = f y := by
  simp only [regularIsometry_compress, ← hrep, ← Matrix.mul_assoc, hf, Matrix.one_mul,
    expect_const univ_nonempty]

end Cslib.Quantum
