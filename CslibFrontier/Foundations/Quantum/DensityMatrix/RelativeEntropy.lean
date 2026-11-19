/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PolarDecomposition
import CslibFrontier.Probability.Divergence

/-!
# Quantum relative entropy of finite density matrices

The finite value is the trace of the first state against the difference of the matrix logarithms.
It is finite precisely when the second state's kernel is contained in the first state's kernel.
Nonnegativity follows from classical Gibbs' inequality applied to the two distributions formed
from eigenvalues and squared overlaps of the eigenvectors. This supplies the nonnegativity
used in [Bavarian, Vidick and Yuen, Proposition 5.2][BavarianVidickYuen2022].

## Main results

* `exists_pmf_relativeEntropyReal_eq`: representation of the finite trace formula as a
  classical relative entropy.
* `relativeEntropy_nonneg`: Gibbs' inequality, including the infinite case.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The support of `ρ` is contained in that of `σ`, stated in terms of their kernels. -/
def SupportLE (ρ σ : Matrix ι ι ℂ) : Prop :=
  ∀ v : ι → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0

/-- The finite trace formula, with the logarithm assigned zero on the kernel. -/
noncomputable def relativeEntropyReal (ρ σ : Matrix ι ι ℂ) : ℝ :=
  (ρ * (cfc Real.log ρ - cfc Real.log σ)).trace.re

open Classical in
/-- Umegaki relative entropy in nats, taking value infinity on a support mismatch. -/
noncomputable def relativeEntropy (ρ σ : Matrix ι ι ℂ) : WithTop ℝ :=
  if SupportLE ρ σ then (relativeEntropyReal ρ σ : WithTop ℝ) else ⊤

theorem relativeEntropy_of_supportLE {ρ σ : Matrix ι ι ℂ} (h : SupportLE ρ σ) :
    relativeEntropy ρ σ = (relativeEntropyReal ρ σ : WithTop ℝ) := by
  simp only [relativeEntropy, ite_eq_left h]

theorem relativeEntropy_of_not_supportLE {ρ σ : Matrix ι ι ℂ} (h : ¬ SupportLE ρ σ) :
    relativeEntropy ρ σ = ⊤ := by
  simp only [relativeEntropy, ite_eq_right h]

private theorem trace_diagonal_mul_conj_re (a b : ι → ℝ) (W : Matrix ι ι ℂ) :
    (diagonal (fun i => (a i : ℂ)) * (W * diagonal (fun j => (b j : ℂ)) * Wᴴ)).trace.re =
      ∑ i, ∑ j, a i * b j * Complex.normSq (W i j) := by
  rw [Matrix.trace, Complex.re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [diag_apply, diagonal_mul, Matrix.mul_apply, Finset.mul_sum, Complex.re_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_diagonal, conjTranspose_apply]
  rw [show (a i : ℂ) * (W i j * (b j : ℂ) * star (W i j)) =
    ((a i : ℂ) * (b j : ℂ)) * (W i j * star (W i j)) by ring]
  rw [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.ofReal_re]

private theorem eigenvalues_sum_of_density {A : Matrix ι ι ℂ} (h : IsDensityMatrix A) :
    ∑ i, h.posSemidef.isHermitian.eigenvalues i = 1 := by
  have ht := h.posSemidef.isHermitian.trace_eq_sum_eigenvalues
  rw [h.trace_eq_one] at ht
  change (1 : ℂ) = ∑ i, (h.posSemidef.isHermitian.eigenvalues i : ℂ) at ht
  exact_mod_cast ht.symm

private theorem sum_normSq_row (W : Matrix ι ι ℂ) (h : W * Wᴴ = 1) (i : ι) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h' := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) h
  simpa only [Matrix.mul_apply, conjTranspose_apply, Complex.star_def, Complex.mul_conj,
    Complex.re_sum, Complex.ofReal_re, Matrix.one_apply_eq, Complex.one_re] using h'

private theorem sum_normSq_col (W : Matrix ι ι ℂ) (h : Wᴴ * W = 1) (j : ι) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have h' : Wᴴ * Wᴴᴴ = 1 := by rwa [conjTranspose_conjTranspose]
  have hr := sum_normSq_row Wᴴ h' j
  simpa only [conjTranspose_apply, Complex.star_def, Complex.normSq_conj] using hr

/-- The trace pairing with a spectral function can be evaluated in the two eigenbases. -/
private theorem trace_mul_cfc_re (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℝ) :
    (A * cfc f B).trace.re = ∑ i, ∑ j, hA.eigenvalues i * f (hB.eigenvalues j) *
      Complex.normSq (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
        (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i j) := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let D := diagonal (fun i => (hA.eigenvalues i : ℂ))
  let E := diagonal (fun j => (f (hB.eigenvalues j) : ℂ))
  let W : Matrix ι ι ℂ := (U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ)
  have hD : A = Unitary.conjStarAlgAut ℂ _ U D := hA.spectral_theorem
  have hE : cfc f B = Unitary.conjStarAlgAut ℂ _ V E := hB.cfc_eq f
  have htrace : (A * cfc f B).trace = (D * (W * E * Wᴴ)).trace := by
    rw [hD, hE, ← trace_conjStarAlgAut (star U), map_mul]
    simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_eq_conjTranspose,
      conjTranspose_conjTranspose]
    have hu : (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ) = 1 := Unitary.coe_star_mul_self U
    simp only [← Matrix.mul_assoc]
    rw [hu, Matrix.one_mul, Matrix.mul_assoc D (U : Matrix ι ι ℂ)ᴴ (U : Matrix ι ι ℂ),
      hu, Matrix.mul_one]
    simp only [W, conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc]
  rw [htrace]
  exact trace_diagonal_mul_conj_re _ _ _


private theorem eigenvalue_mul_overlap_eq_zero {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hs : SupportLE A B) (i j : ι)
    (hj : hB.eigenvalues j = 0) :
    hA.eigenvalues i * Complex.normSq (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
        (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i j) = 0 := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let D := diagonal (fun k => (hA.eigenvalues k : ℂ))
  have hBv := hB.mulVec_eigenvectorBasis j
  rw [hj] at hBv
  have hAv : A *ᵥ (fun k => (V : Matrix ι ι ℂ) k j) = 0 := by
    apply hs
    simpa only [V, IsHermitian.eigenvectorUnitary_apply, RCLike.ofReal_zero, zero_smul]
      using hBv
  have hcol (k : ι) : (A * (V : Matrix ι ι ℂ)) k j = 0 :=
    congrFun hAv k
  have hAU : (U : Matrix ι ι ℂ)ᴴ * A = D * (U : Matrix ι ι ℂ)ᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    change (U : Matrix ι ι ℂ)ᴴ * Unitary.conjStarAlgAut ℂ _ U D = _
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      show (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ) = 1 from Unitary.coe_star_mul_self U,
      Matrix.one_mul]
  have hmat : D * ((U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ)) =
      (U : Matrix ι ι ℂ)ᴴ * (A * (V : Matrix ι ι ℂ)) := by
    rw [← Matrix.mul_assoc, ← hAU, Matrix.mul_assoc]
  have hz := congrArg (fun M : Matrix ι ι ℂ => M i j) hmat
  change (D * ((U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ))) i j =
    ((U : Matrix ι ι ℂ)ᴴ * (A * (V : Matrix ι ι ℂ))) i j at hz
  dsimp only [D] at hz
  rw [diagonal_mul, Matrix.mul_apply (M := (U : Matrix ι ι ℂ)ᴴ)
    (N := A * (V : Matrix ι ι ℂ))] at hz
  simp only [hcol, mul_zero, Finset.sum_const_zero] at hz
  rcases mul_eq_zero.mp hz with ha | hw
  · have ha' : hA.eigenvalues i = 0 := Complex.ofReal_eq_zero.mp ha
    rw [ha', zero_mul]
  · change _ * Complex.normSq (((U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ)) i j) = _
    rw [hw, Complex.normSq_zero, mul_zero]

/-- The finite trace formula equals the classical divergence of the two distributions
obtained by weighting squared eigenbasis overlaps with the two sets of eigenvalues. -/
theorem exists_pmf_relativeEntropyReal_eq {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ)
    (hσ : IsDensityMatrix σ) (hs : SupportLE ρ σ) :
    ∃ p q : PMF (ι × ι), p.support ⊆ q.support ∧
      relativeEntropyReal ρ σ = ∑ z, (p z).toReal * Real.log ((p z).toReal / (q z).toReal) := by
  let hA := hρ.posSemidef.isHermitian
  let hB := hσ.posSemidef.isHermitian
  let a := hA.eigenvalues
  let b := hB.eigenvalues
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let W : Matrix ι ι ℂ := (U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ)
  let w (i j : ι) := Complex.normSq (W i j)
  have ha : ∀ i, 0 ≤ a i := hρ.posSemidef.eigenvalues_nonneg
  have hb : ∀ j, 0 ≤ b j := hσ.posSemidef.eigenvalues_nonneg
  have hw (i j : ι) : 0 ≤ w i j := Complex.normSq_nonneg _
  have hrow (i : ι) : ∑ j, w i j = 1 := by
    apply sum_normSq_row
    simp only [W, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (V : Matrix ι ι ℂ) (V : Matrix ι ι ℂ)ᴴ (U : Matrix ι ι ℂ),
      show (V : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)ᴴ = 1 from Unitary.coe_mul_star_self V,
      Matrix.one_mul]
    exact Unitary.coe_star_mul_self U
  have hcol (j : ι) : ∑ i, w i j = 1 := by
    apply sum_normSq_col
    simp only [W, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix ι ι ℂ) (U : Matrix ι ι ℂ)ᴴ (V : Matrix ι ι ℂ),
      show (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 from Unitary.coe_mul_star_self U,
      Matrix.one_mul]
    exact Unitary.coe_star_mul_self V
  let p : PMF (ι × ι) := PMF.ofFintype (fun z => ENNReal.ofReal (a z.1 * w z.1 z.2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => mul_nonneg (ha _) (hw _ _)),
      Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hrow, mul_one,
      show ∑ i, a i = 1 from eigenvalues_sum_of_density hρ, ENNReal.ofReal_one])
  let q : PMF (ι × ι) := PMF.ofFintype (fun z => ENNReal.ofReal (b z.2 * w z.1 z.2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => mul_nonneg (hb _) (hw _ _)),
      Fintype.sum_prod_type, Finset.sum_comm]
    simp only [← Finset.mul_sum, hcol, mul_one,
      show ∑ j, b j = 1 from eigenvalues_sum_of_density hσ, ENNReal.ofReal_one])
  have hp (i j : ι) : (p (i, j)).toReal = a i * w i j := by
    dsimp only [p]
    rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (mul_nonneg (ha _) (hw _ _))]
  have hq (i j : ι) : (q (i, j)).toReal = b j * w i j := by
    dsimp only [q]
    rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (mul_nonneg (hb _) (hw _ _))]
  have hsupp : p.support ⊆ q.support := by
    rintro ⟨i, j⟩ hi
    have hp' : a i * w i j ≠ 0 := by
      rw [← hp]
      exact ENNReal.toReal_ne_zero.mpr ⟨hi, PMF.apply_ne_top _ _⟩
    have hb' : b j ≠ 0 := fun hz => hp' (eigenvalue_mul_overlap_eq_zero hA hB hs i j hz)
    have hq' : (q (i, j)).toReal ≠ 0 := by
      rw [hq]
      exact mul_ne_zero hb' (right_ne_zero_of_mul hp')
    exact (ENNReal.toReal_ne_zero.mp hq').1
  refine ⟨p, q, hsupp, ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [hp, hq]
  have hterm (i j : ι) : a i * w i j * Real.log (a i * w i j / (b j * w i j)) =
      (a i * Real.log (a i) - a i * Real.log (b j)) * w i j := by
    by_cases hz : a i * w i j = 0
    · rcases mul_eq_zero.mp hz with hz' | hz'
      · simp [hz']
      · simp [hz']
    · have hb' : b j ≠ 0 := fun hz' => hz (eigenvalue_mul_overlap_eq_zero hA hB hs i j hz')
      rw [mul_div_mul_right _ _ (right_ne_zero_of_mul hz),
        Real.log_div (left_ne_zero_of_mul hz) hb']
      ring
  simp only [hterm, sub_mul, Finset.sum_sub_distrib]
  have hself : (ρ * cfc Real.log ρ).trace.re = ∑ i, a i * Real.log (a i) := by
    rw [trace_mul_cfc_re _ _ hA hA]
    change (∑ i, ∑ j, a i * Real.log (a j) *
      Complex.normSq (((U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ)) i j)) = _
    rw [show (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ) = 1 from Unitary.coe_star_mul_self U]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  unfold relativeEntropyReal
  rw [mul_sub, trace_sub, Complex.sub_re, hself, trace_mul_cfc_re _ _ hA hB]
  simp only [← Finset.mul_sum, hrow, mul_one]
  rfl

/-- Finite quantum relative entropy is nonnegative whenever the supports are compatible. -/
theorem relativeEntropyReal_nonneg {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ)
    (hσ : IsDensityMatrix σ) (hs : SupportLE ρ σ) : 0 ≤ relativeEntropyReal ρ σ := by
  obtain ⟨p, q, hsub, he⟩ := exists_pmf_relativeEntropyReal_eq hρ hσ hs
  rw [he]
  exact Cslib.Probability.PMF.sum_mul_log_div_nonneg hsub

@[simp] theorem relativeEntropy_self (ρ : Matrix ι ι ℂ) : relativeEntropy ρ ρ = 0 := by
  rw [relativeEntropy_of_supportLE (fun _ h => h), relativeEntropyReal, sub_self,
    Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
  rfl

/-- Quantum relative entropy is nonnegative, with an infinite value if the support test fails. -/
theorem relativeEntropy_nonneg {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ)
    (hσ : IsDensityMatrix σ) : 0 ≤ relativeEntropy ρ σ := by
  by_cases h : SupportLE ρ σ
  · rw [relativeEntropy_of_supportLE h]
    exact_mod_cast relativeEntropyReal_nonneg hρ hσ h
  · rw [relativeEntropy_of_not_supportLE h]
    exact le_top

end Cslib.Quantum
