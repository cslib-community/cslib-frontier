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
  refine ⟨⟨y, ?_⟩, ?_⟩
  · rw [quadraticObjective, hy, hvalue]
    ring
  · rintro _ ⟨x, rfl⟩
    have h := hA.re_dotProduct_nonneg (x - y)
    change 0 ≤ (star (x - y) ⬝ᵥ A *ᵥ (x - y)).re at h
    rw [star_sub, mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      Complex.sub_re, Complex.sub_re, Complex.sub_re, hcross, hy] at h
    rw [quadraticObjective, hvalue]
    linarith

/-- The resolvent quadratic form at the source matrix. It is attained for positive semidefinite
source and reference and `0 < t`, even if their kernels are nontrivial. -/
noncomputable def relativeEntropyResolvent (t : ℝ) (ρ σ : Matrix ι ι ℂ) : ℝ :=
  ⨆ x : ι × ι → ℂ, quadraticObjective (resolventMatrix t ρ σ) ρ.vec x

private theorem eigenvectorUnitary_mul_diagonal {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A * (hA.eigenvectorUnitary : Matrix ι ι ℂ) =
      (hA.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
  let U := hA.eigenvectorUnitary
  let D := diagonal (fun i => (hA.eigenvalues i : ℂ))
  calc
    A * (U : Matrix ι ι ℂ) = Unitary.conjStarAlgAut ℂ _ U D * (U : Matrix ι ι ℂ) :=
      congrArg (· * (U : Matrix ι ι ℂ)) hA.spectral_theorem
    _ = (U : Matrix ι ι ℂ) * D := by
      rw [Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, Matrix.mul_assoc,
        Unitary.coe_star_mul_self, Matrix.mul_one]

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
  have hρU : ρ * U = U * D := eigenvectorUnitary_mul_diagonal hρ.isHermitian
  have hUρ : Uᴴ * ρ = D * Uᴴ := conjTranspose_eigenvectorUnitary_mul hρ.isHermitian
  have hσV : σ * V = V * E := eigenvectorUnitary_mul_diagonal hσ.isHermitian
  have hC : C = W * D := by rw [show C = Vᴴ * ρ * U from rfl, Matrix.mul_assoc, hρU,
    ← Matrix.mul_assoc]
  have hentry (i j : ι) : C i j = W i j * (a j : ℂ) := by
    rw [hC, mul_diagonal]
  have hV : V * Vᴴ = 1 := Unitary.coe_mul_star_self hσ.isHermitian.eigenvectorUnitary
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hρ.isHermitian.eigenvectorUnitary
  have hrecover : V * C * Uᴴ = ρ := by
    change V * (Vᴴ * ρ * U) * Uᴴ = ρ
    simp only [← Matrix.mul_assoc, hV, Matrix.one_mul]
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  refine ⟨V * M * Uᴴ, ?_, ?_⟩
  · have hdiag : E * M + t • (M * D) = C := by
      ext i j
      rw [Matrix.add_apply, diagonal_mul, Matrix.smul_apply, mul_diagonal]
      have he : ((b i : ℂ) * M i j + t • (M i j * (a j : ℂ))) =
          (d i j : ℂ) * M i j := by
        simp only [d, Complex.ofReal_add, Complex.ofReal_mul, Complex.real_smul]
        ring
      change (b i : ℂ) * M i j + t • (M i j * (a j : ℂ)) = C i j
      rw [he]
      change (d i j : ℂ) * (C i j / (d i j : ℂ)) = C i j
      by_cases hd : d i j = 0
      · have ha : a j = 0 := by
          have := hσ.eigenvalues_nonneg i
          have := hρ.eigenvalues_nonneg j
          change b i + t * a j = 0 at hd
          nlinarith
        simp [hentry, ha, hd]
      · exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hd)
    rw [resolventMatrix_mulVec, vec_inj]
    calc
      σ * (V * M * Uᴴ) + t • (V * M * Uᴴ * ρ) =
          V * (E * M + t • (M * D)) * Uᴴ := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc σ V, hσV, hUρ, Matrix.mul_assoc]
      _ = ρ := by rw [hdiag, hrecover]
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
  let pairing : Matrix ι ι ℂ →ₗ[ℝ] ℝ :=
    Complex.reLm.comp ((traceLinearMap ι ℝ ℂ).comp (mulLeftLinearMap ι ℝ Xᴴ))
  let f : Matrix ι ι ℂ →ₗ[ℝ] ℝ :=
    (2 : ℝ) • pairing - t • pairing.comp (mulLeftLinearMap ι ℝ X)
  let g : Matrix ι ι ℂ →ₗ[ℝ] ℝ := -(pairing.comp (mulRightLinearMap ι ℝ X))
  have hobj (A B : Matrix ι ι ℂ) :
      quadraticObjective (resolventMatrix t A B) A.vec X.vec = f A + g B := by
    rw [quadraticObjective_resolvent]
    change _ = 2 * (Xᴴ * A).trace.re - t * (Xᴴ * (X * A)).trace.re +
      -(Xᴴ * (B * X)).trace.re
    simp only [Matrix.mul_add, trace_add, Complex.add_re, Matrix.mul_smul, trace_smul,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hlin :
      quadraticObjective (resolventMatrix t (∑ k, w k • ρ k) (∑ k, w k • σ k))
        (∑ k, w k • ρ k).vec X.vec =
      ∑ k, w k * quadraticObjective (resolventMatrix t (ρ k) (σ k)) (ρ k).vec X.vec := by
    simp only [hobj, map_sum, map_smul, smul_eq_mul, mul_add, sum_add_distrib]
  rw [hlin]
  refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hw k)
  obtain ⟨B, hB, _⟩ := resolvent_solution ht (hρ k) (hσ k)
  have hmax := quadraticObjective_isGreatest (resolventMatrix_posSemidef ht.le (hρ k) (hσ k)) hB
  rw [relativeEntropyResolvent, iSup, hmax.csSup_eq]
  exact hmax.2 (Set.mem_range_self _)

end Cslib.Quantum
