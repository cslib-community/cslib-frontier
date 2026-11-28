/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# The resolvent kernel for quantum relative entropy

For positive semidefinite matrices `ρ` and `σ`, the operator on matrices
`X ↦ σ * X + t • (X * ρ)` is positive semidefinite for `t > 0`. Its inverse
quadratic form at `ρ` is the maximum of an affine function of the pair of inputs,
parametrized by a test matrix. This is the completing-the-square argument used in
[Ruskai, Section 2.4][Ruskai2007] (arXiv:quant-ph/0604206v1, printed pp. 4–5).

## Main definitions

* `relativeEntropyResolvent`: the quadratic form of the resolvent at the source matrix.

## Main results

* `relativeEntropyResolvent_eq_sum`: its spectral formula, valid for singular inputs.
* `relativeEntropyResolvent_sum_smul_le`: its joint convexity in the source and reference.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped ComplexOrder Kronecker MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def resolventMatrix (t : ℝ) (ρ σ : Matrix ι ι ℂ) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  (1 : Matrix ι ι ℂ) ⊗ₖ σ + t • (ρᵀ ⊗ₖ (1 : Matrix ι ι ℂ))

omit [Fintype ι] in
private theorem resolventMatrix_posSemidef {t : ℝ} (ht : 0 ≤ t)
    {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    (resolventMatrix t ρ σ).PosSemidef :=
  (PosSemidef.one.kronecker hσ).add ((hρ.transpose.kronecker PosSemidef.one).smul ht)

private theorem resolventMatrix_mulVec (t : ℝ) (ρ σ X : Matrix ι ι ℂ) :
    resolventMatrix t ρ σ *ᵥ X.vec = (σ * X + t • (X * ρ)).vec := by
  rw [resolventMatrix, add_mulVec, smul_mulVec, kronecker_mulVec_vec,
    kronecker_mulVec_vec, transpose_one, transpose_transpose, Matrix.mul_one, Matrix.one_mul,
    vec_add, vec_smul]

private noncomputable def quadraticObjective {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (b x : n → ℂ) : ℝ :=
  2 * (star x ⬝ᵥ b).re - (star x ⬝ᵥ A *ᵥ x).re

private theorem quadraticObjective_isGreatest {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {b y : n → ℂ} (hy : A *ᵥ y = b) :
    IsGreatest (Set.range (quadraticObjective A b)) ((star b ⬝ᵥ y).re) := by
  have hcross (x : n → ℂ) : (star y ⬝ᵥ A *ᵥ x).re = (star x ⬝ᵥ b).re := by
    rw [← hA.isHermitian.star_dotProduct_mulVec_comm x y, hy, Complex.star_def, Complex.conj_re]
  have hvalue : (star b ⬝ᵥ y).re = (star y ⬝ᵥ b).re := by
    calc
      _ = (star (star y ⬝ᵥ b)).re := by rw [star_dotProduct]
      _ = _ := Complex.conj_re _
  refine ⟨⟨y, by rw [quadraticObjective, hy, hvalue]; ring⟩, fun _ ⟨x, hx⟩ => ?_⟩
  have h : 0 ≤ (star (x - y) ⬝ᵥ A *ᵥ (x - y)).re := hA.re_dotProduct_nonneg (x - y)
  rw [star_sub, mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    Complex.sub_re, Complex.sub_re, Complex.sub_re, hcross, hy] at h
  rw [← hx, quadraticObjective, hvalue]; linarith

/-- The resolvent quadratic form at the source matrix. It is attained for positive semidefinite
source and reference and `0 < t`, even if their kernels are nontrivial. -/
noncomputable def relativeEntropyResolvent (t : ℝ) (ρ σ : Matrix ι ι ℂ) : ℝ :=
  ⨆ x : ι × ι → ℂ, quadraticObjective (resolventMatrix t ρ σ) ρ.vec x

private theorem eigenvectorUnitary_mul_diagonal {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A * (hA.eigenvectorUnitary : Matrix ι ι ℂ) =
      (hA.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
  simpa [Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, Function.comp_def] using
    congrArg (· * (hA.eigenvectorUnitary : Matrix ι ι ℂ)) hA.spectral_theorem

private theorem conjTranspose_eigenvectorUnitary_mul {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * A =
      diagonal (fun i => (hA.eigenvalues i : ℂ)) * (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  have h := congrArg conjTranspose (eigenvectorUnitary_mul_diagonal hA)
  rw [conjTranspose_mul, conjTranspose_mul, hA.eq, diagonal_conjTranspose] at h
  have hreal : star (fun i => (hA.eigenvalues i : ℂ)) = fun i => (hA.eigenvalues i : ℂ) := by
    funext i
    exact Complex.conj_ofReal _
  rwa [hreal] at h

private theorem trace_eigenbasis_pairing (U V : unitary (Matrix ι ι ℂ))
    (A B : Matrix ι ι ℂ) :
    (Aᴴ * ((V : Matrix ι ι ℂ) * B * (U : Matrix ι ι ℂ)ᴴ)).trace =
      (((V : Matrix ι ι ℂ)ᴴ * A * (U : Matrix ι ι ℂ))ᴴ * B).trace := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc]
  simpa only [← Matrix.mul_assoc] using
    Matrix.trace_mul_comm (Aᴴ * (V : Matrix ι ι ℂ) * B) ((U : Matrix ι ι ℂ)ᴴ)

omit [DecidableEq ι] in
private theorem trace_conjTranspose_mul_div_real (A : Matrix ι ι ℂ) (d : ι → ι → ℝ) :
    (Aᴴ * of (fun i j => A i j / (d i j : ℂ))).trace.re =
      ∑ j, ∑ i, Complex.normSq (A i j) / d i j := by
  simp only [Matrix.trace, diag_apply, Matrix.mul_apply, of_apply, conjTranspose_apply,
    Complex.re_sum]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  rw [← mul_div_assoc, Complex.star_def, mul_comm ((starRingEnd ℂ) (A i j)),
    Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_re]

private theorem resolvent_solution {t : ℝ} (ht : 0 < t)
    {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, resolventMatrix t ρ σ *ᵥ B.vec = ρ.vec ∧
      (ρᴴ * B).trace.re =
        ∑ j, ∑ i, hρ.isHermitian.eigenvalues j ^ 2 *
          Complex.normSq (((hσ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
            (hρ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) i j) /
          (hσ.isHermitian.eigenvalues i + t * hρ.isHermitian.eigenvalues j) := by
  let U : Matrix ι ι ℂ := hρ.isHermitian.eigenvectorUnitary
  let V : Matrix ι ι ℂ := hσ.isHermitian.eigenvectorUnitary
  let a := hρ.isHermitian.eigenvalues
  let b := hσ.isHermitian.eigenvalues
  let D := diagonal (fun j => (a j : ℂ))
  let E := diagonal (fun i => (b i : ℂ))
  let W := Vᴴ * U
  let C := Vᴴ * ρ * U
  let d (i j : ι) := b i + t * a j
  let M : Matrix ι ι ℂ := of (fun i j => C i j / (d i j : ℂ))
  have hentry (i j : ι) : C i j = W i j * (a j : ℂ) := by
    have : C = W * D := by
      rw [show C = Vᴴ * (ρ * U) from Matrix.mul_assoc ..,
        eigenvectorUnitary_mul_diagonal hρ.isHermitian, ← Matrix.mul_assoc]
    rw [this, mul_diagonal]
  refine ⟨V * M * Uᴴ, ?_, ?_⟩
  · have hdiag : E * M + t • (M * D) = C := by
      ext i j
      simp only [Matrix.add_apply, diagonal_mul, Matrix.smul_apply, mul_diagonal, E, D, M, of_apply]
      have he : (b i : ℂ) * (C i j / (d i j : ℂ)) + t • (C i j / (d i j : ℂ) * (a j : ℂ)) =
          (d i j : ℂ) * (C i j / (d i j : ℂ)) := by
        simp only [d, Complex.ofReal_add, Complex.ofReal_mul, Complex.real_smul]; ring
      rw [he]
      by_cases hd : d i j = 0
      · have ha : a j = 0 := by
          nlinarith [hσ.eigenvalues_nonneg i, hρ.eigenvalues_nonneg j,
            show b i + t * a j = 0 from hd]
        simp [hentry, ha, hd]
      · exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hd)
    rw [resolventMatrix_mulVec, vec_inj]
    calc
      σ * (V * M * Uᴴ) + t • (V * M * Uᴴ * ρ) =
          V * (E * M + t • (M * D)) * Uᴴ := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc σ V, eigenvectorUnitary_mul_diagonal hσ.isHermitian,
          conjTranspose_eigenvectorUnitary_mul hρ.isHermitian, Matrix.mul_assoc]
      _ = ρ := by
        rw [hdiag]
        have hV : V * Vᴴ = 1 := Unitary.coe_mul_star_self hσ.isHermitian.eigenvectorUnitary
        have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hρ.isHermitian.eigenvectorUnitary
        change V * (Vᴴ * ρ * U) * Uᴴ = ρ
        simp only [← Matrix.mul_assoc, hV, Matrix.one_mul]
        rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  · rw [trace_eigenbasis_pairing hρ.isHermitian.eigenvectorUnitary
      hσ.isHermitian.eigenvectorUnitary, trace_conjTranspose_mul_div_real]
    refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
    change Complex.normSq (C i j) / d i j = a j ^ 2 * Complex.normSq (W i j) / d i j
    rw [hentry, Complex.normSq_mul, Complex.normSq_ofReal, mul_comm, pow_two]

/-- In the two eigenbases the kernel uses the scalar denominator `σᵢ + t * ρⱼ`.
If this denominator is zero, the numerator is also zero. -/
theorem relativeEntropyResolvent_eq_sum {t : ℝ} (ht : 0 < t)
    {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    relativeEntropyResolvent t ρ σ =
      ∑ j, ∑ i, hρ.isHermitian.eigenvalues j ^ 2 *
        Complex.normSq (((hρ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
          (hσ.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)) j i) /
        (hσ.isHermitian.eigenvalues i + t * hρ.isHermitian.eigenvalues j) := by
  obtain ⟨B, hB, hv⟩ := resolvent_solution ht hρ hσ
  rw [relativeEntropyResolvent, iSup,
    (quadraticObjective_isGreatest (resolventMatrix_posSemidef ht.le hρ hσ) hB).csSup_eq,
    star_vec_dotProduct_vec, hv]
  let U : Matrix ι ι ℂ := hρ.isHermitian.eigenvectorUnitary
  let V : Matrix ι ι ℂ := hσ.isHermitian.eigenvectorUnitary
  have hW : Vᴴ * U = (Uᴴ * V)ᴴ := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  change _ * Complex.normSq ((Vᴴ * U) i j) / _ =
    _ * Complex.normSq ((Uᴴ * V) j i) / _
  rw [hW, conjTranspose_apply, Complex.star_def, Complex.normSq_conj]

private theorem quadraticObjective_resolvent (t : ℝ) (ρ σ X : Matrix ι ι ℂ) :
    quadraticObjective (resolventMatrix t ρ σ) ρ.vec X.vec =
      2 * (Xᴴ * ρ).trace.re - (Xᴴ * (σ * X + t • (X * ρ))).trace.re := by
  rw [quadraticObjective, resolventMatrix_mulVec, star_vec_dotProduct_vec, star_vec_dotProduct_vec]

/-- The resolvent is the attained supremum of its affine test-matrix objectives. -/
theorem relativeEntropyResolvent_isGreatest {t : ℝ} (ht : 0 < t)
    {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest
      (Set.range fun X : Matrix ι ι ℂ =>
        2 * (Xᴴ * ρ).trace.re - (Xᴴ * (σ * X + t • (X * ρ))).trace.re)
      (relativeEntropyResolvent t ρ σ) := by
  obtain ⟨B, hB, _⟩ := resolvent_solution ht hρ hσ
  have h := quadraticObjective_isGreatest (resolventMatrix_posSemidef ht.le hρ hσ) hB
  rw [relativeEntropyResolvent, iSup, h.csSup_eq]
  convert h using 1
  ext z
  simp only [Set.mem_range, ← quadraticObjective_resolvent]
  exact ⟨fun ⟨X, hX⟩ => ⟨X.vec, hX⟩, fun ⟨v, hv⟩ =>
    let ⟨X, hX⟩ := Matrix.vec_bijective.surjective v
    ⟨X, hX ▸ hv⟩⟩

/-- The resolvent kernel of a nonnegative weighted mixture is bounded by the weighted kernels
of its components. No normalization of the weights is needed. -/
theorem relativeEntropyResolvent_sum_smul_le {κ : Type*} [Fintype κ]
    {t : ℝ} (ht : 0 < t) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (ρ σ : κ → Matrix ι ι ℂ) (hρ : ∀ k, (ρ k).PosSemidef) (hσ : ∀ k, (σ k).PosSemidef) :
    relativeEntropyResolvent t (∑ k, w k • ρ k) (∑ k, w k • σ k) ≤
      ∑ k, w k * relativeEntropyResolvent t (ρ k) (σ k) := by
  rw [relativeEntropyResolvent]
  refine ciSup_le fun x => ?_
  obtain ⟨X, rfl⟩ := Matrix.vec_bijective.surjective x
  have hlin : quadraticObjective (resolventMatrix t (∑ k, w k • ρ k) (∑ k, w k • σ k))
      (∑ k, w k • ρ k).vec X.vec =
      ∑ k, w k * (2 * (Xᴴ * ρ k).trace.re - (Xᴴ * (σ k * X + t • (X * ρ k))).trace.re) := by
    simp only [quadraticObjective_resolvent, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_add,
      Matrix.mul_smul, Matrix.smul_mul, smul_sum, trace_sum, trace_add, trace_smul,
      Complex.re_sum, Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul]
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [hlin]
  exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
    ((relativeEntropyResolvent_isGreatest ht (hρ k) (hσ k)).2 ⟨X, rfl⟩) (hw k)

end Cslib.Quantum
