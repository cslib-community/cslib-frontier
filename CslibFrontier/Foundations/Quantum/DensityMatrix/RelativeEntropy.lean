/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.PurificationOverlap
public import CslibFrontier.Probability.Hellinger
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefKernel
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PolarDecomposition
import CslibFrontier.Probability.ChiSquare
import CslibFrontier.Probability.Divergence

/-!
# Quantum relative entropy of finite density matrices

The finite value is the trace of the first state against the difference of the matrix logarithms.
It is finite precisely when the second state's kernel is contained in the first state's kernel.
Nonnegativity follows from classical Gibbs' inequality applied to the two distributions formed
from eigenvalues and squared overlaps of the eigenvectors. This supplies the nonnegativity
used in [Bavarian, Vidick and Yuen, Proposition 5.2][BavarianVidickYuen2022].
The same distributions identify their Bhattacharyya coefficient with the trace overlap of
the two positive square roots. This controls fidelity and the squared error of aligning
purifications using a local unitary.

## Main results

* `exists_pmf_relativeEntropyReal_eq`: representation of the finite trace formula as a
  classical relative entropy, with an exact formula for the overlap coefficient.
* `relativeEntropy_nonneg`: Gibbs' inequality, including the infinite case.
* `exp_neg_half_relativeEntropyReal_le_rootFidelity`: the entropy lower bound on fidelity.
* `exists_localUnitary_norm_sub_sq_le_relativeEntropy`: relative entropy bounds alignment error.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped MatrixOrder ComplexOrder Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The support of `ρ` is contained in that of `σ`, stated in terms of their kernels. -/
@[expose] def SupportLE (ρ σ : Matrix ι ι ℂ) : Prop :=
  ∀ v : ι → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0

omit [DecidableEq ι] in
/-- Every matrix has its own support. -/
protected theorem SupportLE.refl (ρ : Matrix ι ι ℂ) : SupportLE ρ ρ :=
  fun _ h => h

omit [DecidableEq ι] in
/-- Support inclusion is preserved by nonnegative weighted sums of the pairs when the
reference matrices are positive semidefinite. -/
theorem SupportLE.sum_smul {κ : Type*} [Fintype κ] (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k)
    {ρ σ : κ → Matrix ι ι ℂ} (hσ : ∀ k, (σ k).PosSemidef) (hs : ∀ k, SupportLE (ρ k) (σ k)) :
    SupportLE (∑ k, w k • ρ k) (∑ k, w k • σ k) := by
  intro x hx
  have hzero := (mulVec_sum_smul_eq_zero_iff univ w σ
    (fun k _ => hw k) (fun k _ => hσ k) x).mp hx
  rw [sum_mulVec]
  refine sum_eq_zero fun k hk => ?_
  rw [smul_mulVec]
  by_cases hwk : w k = 0
  · rw [hwk, zero_smul]
  · rw [hs k x (hzero k hk hwk), smul_zero]

/-- The finite trace formula, with the logarithm assigned zero on the kernel. -/
@[expose] noncomputable def relativeEntropyReal (ρ σ : Matrix ι ι ℂ) : ℝ :=
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

/-- The trace pairing of two spectral functions can be evaluated in the two eigenbases. -/
private theorem trace_cfc_mul_cfc_re (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f g : ℝ → ℝ) :
    (cfc f A * cfc g B).trace.re = ∑ i, ∑ j, f (hA.eigenvalues i) * g (hB.eigenvalues j) *
      Complex.normSq (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
        (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i j) := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let D := diagonal (fun i => (f (hA.eigenvalues i) : ℂ))
  let E := diagonal (fun j => (g (hB.eigenvalues j) : ℂ))
  let W : Matrix ι ι ℂ := (U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ)
  have hD : cfc f A = Unitary.conjStarAlgAut ℂ _ U D := hA.cfc_eq f
  have hE : cfc g B = Unitary.conjStarAlgAut ℂ _ V E := hB.cfc_eq g
  have htrace : (cfc f A * cfc g B).trace = (D * (W * E * Wᴴ)).trace := by
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

private theorem trace_mul_cfc_re (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℝ) :
    (A * cfc f B).trace.re = ∑ i, ∑ j, hA.eigenvalues i * f (hB.eigenvalues j) *
      Complex.normSq (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
        (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i j) := by
  have h := trace_cfc_mul_cfc_re A B hA hB id f
  rw [cfc_id (p := IsSelfAdjoint) ℝ A hA] at h
  exact h

private theorem sqrt_eq_cfc_real_sqrt (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    CFC.sqrt A = cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA.nonneg, cfcₙ_eq_cfc (hf0 := Real.sqrt_zero)]

/-- A source eigenvalue weighted by its overlap with a reference kernel vector vanishes
under support inclusion. -/
theorem eigenvalue_mul_overlap_eq_zero_of_supportLE {A B : Matrix ι ι ℂ}
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

/-- The squared overlaps with the eigenbasis of the second matrix sum to one in each row. -/
theorem sum_eigenbasis_overlap_row {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : ι) :
    (∑ j, Complex.normSq (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
      (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i j)) = 1 := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  apply sum_normSq_row
  change ((U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ)) *
    ((U : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ))ᴴ = 1
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (V : Matrix ι ι ℂ) (V : Matrix ι ι ℂ)ᴴ (U : Matrix ι ι ℂ),
    show (V : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)ᴴ = 1 from Unitary.coe_mul_star_self V,
    Matrix.one_mul]
  exact Unitary.coe_star_mul_self U

/-- The finite trace formula expressed in the eigenbases of its two arguments. -/
theorem relativeEntropyReal_eq_sum_eigenbasis {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    relativeEntropyReal A B = ∑ i, ∑ j,
      (hA.eigenvalues i * Real.log (hA.eigenvalues i) -
        hA.eigenvalues i * Real.log (hB.eigenvalues j)) *
        Complex.normSq (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
          (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i j) := by
  have hself : (A * cfc Real.log A).trace.re =
      ∑ i, hA.eigenvalues i * Real.log (hA.eigenvalues i) := by
    rw [trace_mul_cfc_re _ _ hA hA,
      show (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1
        from Unitary.coe_star_mul_self hA.eigenvectorUnitary]
    refine sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  rw [relativeEntropyReal, mul_sub, trace_sub, Complex.sub_re, hself, trace_mul_cfc_re _ _ hA hB]
  simp only [sub_mul, sum_sub_distrib, ← Finset.mul_sum, sum_eigenbasis_overlap_row, mul_one]

private theorem trace_mul_log_smul_re {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hs : SupportLE A B) {b : ℝ} (hb : 0 < b) :
    (A * cfc Real.log (b • B)).trace.re =
      (A * cfc Real.log B).trace.re + Real.log b * A.trace.re := by
  have hc := cfc_comp_const_mul (p := IsSelfAdjoint) b Real.log B
    (((B.finite_real_spectrum).image _).continuousOn Real.log) hB
  rw [← hc, trace_mul_cfc_re _ _ hA hB, trace_mul_cfc_re _ _ hA hB]
  let a := hA.eigenvalues
  let e := hB.eigenvalues
  let w (i j : ι) := Complex.normSq
    (((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hB.eigenvectorUnitary : Matrix ι ι ℂ)) i j)
  have ht (i j : ι) : a i * Real.log (b * e j) * w i j =
      a i * Real.log (e j) * w i j + Real.log b * (a i * w i j) := by
    by_cases hj : e j = 0
    · have hz : a i * w i j = 0 := eigenvalue_mul_overlap_eq_zero_of_supportLE hA hB hs i j hj
      simp only [hj, mul_zero, Real.log_zero, zero_mul, hz, add_zero]
    · rw [Real.log_mul hb.ne' hj]
      ring
  have hsum : (∑ i, ∑ j, a i * w i j) = A.trace.re := by
    have h := trace_mul_cfc_re A B hA hB (fun _ => 1)
    rw [cfc_const (p := IsSelfAdjoint) 1 B hB, map_one, Matrix.mul_one] at h
    simpa only [mul_one, a, w] using h.symm
  change (∑ i, ∑ j, a i * Real.log (b * e j) * w i j) =
    (∑ i, ∑ j, a i * Real.log (e j) * w i j) + Real.log b * A.trace.re
  rw [← hsum]
  simp only [ht, Finset.sum_add_distrib, Finset.mul_sum]

/-- Positive scalar weights contribute a classical log likelihood to the block entropy. -/
theorem relativeEntropyReal_smul {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ)
    (hσ : IsDensityMatrix σ) (hs : SupportLE ρ σ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    relativeEntropyReal (a • ρ) (b • σ) =
      a * (Real.log (a / b) + relativeEntropyReal ρ σ) := by
  unfold relativeEntropyReal
  rw [Matrix.smul_mul, trace_smul]
  change ((a : ℂ) * (ρ * (cfc Real.log (a • ρ) - cfc Real.log (b • σ))).trace).re = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    mul_sub, trace_sub, Complex.sub_re]
  rw [trace_mul_log_smul_re hρ.posSemidef.isHermitian hρ.posSemidef.isHermitian
      (fun _ h => h) ha,
    trace_mul_log_smul_re hρ.posSemidef.isHermitian hσ.posSemidef.isHermitian hs hb,
    hρ.trace_eq_one, Complex.one_re, mul_one, mul_one, Real.log_div ha.ne' hb.ne']
  ring

/-- Weight the squared eigenbasis overlaps by the two sets of eigenvalues. The resulting
distributions give the finite trace formula and the square-root trace overlap. -/
theorem exists_pmf_relativeEntropyReal_eq {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ)
    (hσ : IsDensityMatrix σ) (hs : SupportLE ρ σ) :
    ∃ p q : PMF (ι × ι), p.support ⊆ q.support ∧
      relativeEntropyReal ρ σ = (∑ z, (p z).toReal * Real.log ((p z).toReal / (q z).toReal)) ∧
      Cslib.Probability.PMF.bhattacharyya p q = (CFC.sqrt ρ * CFC.sqrt σ).trace.re := by
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
  have hrow (i : ι) : ∑ j, w i j = 1 := sum_eigenbasis_overlap_row hA hB i
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
    have hb' : b j ≠ 0 := fun hz =>
      hp' (eigenvalue_mul_overlap_eq_zero_of_supportLE hA hB hs i j hz)
    have hq' : (q (i, j)).toReal ≠ 0 := by
      rw [hq]
      exact mul_ne_zero hb' (right_ne_zero_of_mul hp')
    exact (ENNReal.toReal_ne_zero.mp hq').1
  refine ⟨p, q, hsupp, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp only [hp, hq]
    have hterm (i j : ι) : a i * w i j * Real.log (a i * w i j / (b j * w i j)) =
        (a i * Real.log (a i) - a i * Real.log (b j)) * w i j := by
      by_cases hz : a i * w i j = 0
      · rcases mul_eq_zero.mp hz with hz' | hz'
        · simp [hz']
        · simp [hz']
      · have hb' : b j ≠ 0 := fun hz' =>
          hz (eigenvalue_mul_overlap_eq_zero_of_supportLE hA hB hs i j hz')
        rw [mul_div_mul_right _ _ (right_ne_zero_of_mul hz),
          Real.log_div (left_ne_zero_of_mul hz) hb']
        ring
    rw [relativeEntropyReal_eq_sum_eigenbasis hA hB]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => (hterm i j).symm
  · rw [Cslib.Probability.PMF.bhattacharyya_eq_sum, Fintype.sum_prod_type,
      sqrt_eq_cfc_real_sqrt _ hρ.posSemidef, sqrt_eq_cfc_real_sqrt _ hσ.posSemidef,
      trace_cfc_mul_cfc_re _ _ hA hB]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hp, hq]
    change Real.sqrt ((a i * w i j) * (b j * w i j)) =
      Real.sqrt (a i) * Real.sqrt (b j) * w i j
    rw [show (a i * w i j) * (b j * w i j) = (a i * b j) * (w i j) ^ 2 by ring,
      Real.sqrt_mul (mul_nonneg (ha i) (hb j)), Real.sqrt_mul (ha i), Real.sqrt_sq (hw i j)]

/-- Finite quantum relative entropy is nonnegative whenever the supports are compatible. -/
theorem relativeEntropyReal_nonneg {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ)
    (hσ : IsDensityMatrix σ) (hs : SupportLE ρ σ) : 0 ≤ relativeEntropyReal ρ σ := by
  obtain ⟨p, q, hsub, he, _⟩ := exists_pmf_relativeEntropyReal_eq hρ hσ hs
  rw [he]
  exact Cslib.Probability.PMF.sum_mul_log_div_nonneg hsub

@[simp] theorem relativeEntropy_self (ρ : Matrix ι ι ℂ) : relativeEntropy ρ ρ = 0 := by
  rw [relativeEntropy_of_supportLE (SupportLE.refl ρ), relativeEntropyReal, sub_self,
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

/-- When relative entropy is finite, fidelity is at least the exponential of minus half
the entropy in nats. -/
theorem exp_neg_half_relativeEntropyReal_le_rootFidelity {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) (hs : SupportLE ρ σ) :
    Real.exp (-relativeEntropyReal ρ σ / 2) ≤ rootFidelity ρ σ := by
  obtain ⟨p, q, hsub, hKL, hBC⟩ := exists_pmf_relativeEntropyReal_eq hρ hσ hs
  rw [hKL]
  apply (Cslib.Probability.PMF.exp_neg_half_sum_mul_log_div_le_bhattacharyya hsub).trans
  rw [hBC]
  have h := re_trace_conjTranspose_mul_le_traceNorm (CFC.sqrt ρ * CFC.sqrt σ) 1 (one_mem _)
  rwa [conjTranspose_one, Matrix.one_mul] at h

/-- Twice one minus the unsquared fidelity is at most the quantum relative entropy. -/
theorem two_mul_one_sub_rootFidelity_le_relativeEntropy {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    ((2 * (1 - rootFidelity ρ σ) : ℝ) : WithTop ℝ) ≤ relativeEntropy ρ σ := by
  by_cases hs : SupportLE ρ σ
  · rw [relativeEntropy_of_supportLE hs, WithTop.coe_le_coe]
    linarith [exp_neg_half_relativeEntropyReal_le_rootFidelity hρ hσ hs,
      Real.add_one_le_exp (-relativeEntropyReal ρ σ / 2)]
  · rw [relativeEntropy_of_not_supportLE hs]
    exact le_top

/-- Two unit purifications can be aligned with squared error at most the relative entropy
of their left reduced states. -/
theorem exists_localUnitary_norm_sub_sq_le_relativeEntropy {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ψ φ : EuclideanSpace ℂ (ι × κ)) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ∃ U ∈ unitaryGroup κ ℂ,
      ((‖WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ ψ.ofLp) - φ‖ ^ 2 : ℝ) : WithTop ℝ) ≤
        relativeEntropy (partialTraceRight (pureState ψ)) (partialTraceRight (pureState φ)) := by
  obtain ⟨U, hU, he⟩ := exists_localUnitary_norm_sub_sq_eq ψ φ hψ hφ
  exact ⟨U, hU, he ▸ two_mul_one_sub_rootFidelity_le_relativeEntropy
    (isDensityMatrix_pureState hψ).partialTraceRight
    (isDensityMatrix_pureState hφ).partialTraceRight⟩

end Cslib.Quantum
