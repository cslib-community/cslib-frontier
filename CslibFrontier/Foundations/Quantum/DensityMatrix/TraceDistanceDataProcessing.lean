/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.FidelityTraceDistance
public import CslibFrontier.Foundations.Quantum.DensityMatrix.PartialTracePairing
public import CslibFrontier.Foundations.Quantum.POVM.Density
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefTrace
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Data processing and Helstrom characterization for trace distance

For quantum states `ρ, σ` on `ℂ^ι`, `Cslib.Quantum.traceDistance ρ σ = (ρ - σ).traceNorm / 2`
(`CslibFrontier/Foundations/Quantum/DensityMatrix/FidelityTraceDistance.lean`) generalizes classical
total variation distance. Using `Matrix.traceNorm_eq_max_re_trace`
(`CslibFrontier/Foundations/LinearAlgebra/Matrix/PolarDecomposition.lean`), this file proves:

* **Norm and metric laws** (`Matrix.traceNorm_add_le`, `Matrix.traceNorm_eq_zero_iff`,
  `Cslib.Quantum.traceDistance_triangle`, `Cslib.Quantum.traceDistance_sum_smul_le`): `traceNorm`
  is a norm on matrices (nonnegative, zero iff zero, homogeneous, subadditive), making
  `traceDistance` a `[0, 1]`-valued metric on density matrices that is jointly convex in mixtures.
* **Data-processing inequality under CPTP maps** (`Cslib.Quantum.traceDistance_densityConj`,
  `Cslib.Quantum.traceDistance_partialTraceRight_le`, `Cslib.Quantum.traceDistance_kraus_le`):
  conjugation by any rectangular isometry `V` (`Vᴴ * V = 1`) preserves `traceNorm` and
  `traceDistance` exactly, partial trace over either factor contracts `traceNorm` and
  `traceDistance`, and Stinespring dilation yields contractivity under arbitrary CPTP Kraus
  families `{Kⱼ}_{j ∈ s}` with `∑_{j ∈ s} Kⱼᴴ Kⱼ = 1`.
* **Operational POVM characterization and Holevo–Helstrom theorem**
  (`Cslib.Quantum.POVM.half_sum_abs_densityProb_sub_le_traceDistance`,
  `Cslib.Quantum.helstromPOVM`, `Cslib.Quantum.helstromPOVM_half_sum_abs_densityProb_sub`,
  `Cslib.Quantum.helstrom_success_le`, `Cslib.Quantum.helstromPOVM_success`,
  [de Wolf][deWolf2019], Chapter 15): for every finite-outcome `M : POVM A ι`, the classical total
  variation distance `½ ∑_a |M.densityProb ρ a - M.densityProb σ a|` between outcome distributions
  is at most `traceDistance ρ σ`. For Hermitian `ρ - σ` with `ρ.trace.re = σ.trace.re` (in
  particular any two density matrices), the two-outcome projective measurement `helstromPOVM`
  built from the spectral sign observable of `ρ - σ` attains `traceDistance ρ σ`, achieving the
  optimal equal-prior discrimination probability `½ + ½ traceDistance ρ σ`.

## Main definitions

* `Cslib.Quantum.helstromObservable`: the `±1` spectral sign observable of Hermitian `ρ - σ`.
* `Cslib.Quantum.helstromPOVM`: the two-outcome projective Helstrom measurement distinguishing `ρ`
  from `σ`.

## Main results

* `Matrix.traceNorm_nonneg`, `Matrix.traceNorm_eq_zero_iff`, `Matrix.traceNorm_smul`,
  `Matrix.traceNorm_add_le`: norm properties of `Matrix.traceNorm`.
* `Matrix.traceNorm_isometry_conj`: `(V * A * Vᴴ).traceNorm = A.traceNorm` when `Vᴴ * V = 1`.
* `Matrix.IsHermitian.traceNorm_eq_sum_abs_eigenvalues`: for Hermitian `H`, `H.traceNorm` is the sum
  of absolute eigenvalues.
* `Cslib.Quantum.traceDistance_eq_zero_iff`, `Cslib.Quantum.traceDistance_comm`,
  `Cslib.Quantum.traceDistance_triangle`, `Cslib.Quantum.traceDistance_le_one`,
  `Cslib.Quantum.traceDistance_sum_smul_le`: metric and joint-convexity laws for `traceDistance`.
* `Cslib.Quantum.traceDistance_densityConj`, `Cslib.Quantum.traceDistance_partialTraceRight_le`,
  `Cslib.Quantum.traceDistance_partialTraceLeft_le`, `Cslib.Quantum.traceDistance_kraus_le`:
  invariance under rectangular isometries and data processing under partial trace and CPTP Kraus
  channels.
* `Cslib.Quantum.POVM.half_sum_abs_densityProb_sub_le_traceDistance`,
  `Cslib.Quantum.helstromPOVM_half_sum_abs_densityProb_sub`,
  `Cslib.Quantum.helstrom_success_le`, `Cslib.Quantum.helstromPOVM_success`: operational POVM
  characterization of `traceDistance` and Holevo–Helstrom optimal state discrimination.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

open scoped MatrixOrder ComplexOrder Kronecker

/-! ### Norm, isometric invariance, and spectral formula for `Matrix.traceNorm` -/

namespace Matrix

section TraceNorm

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-- The trace norm of any rectangular matrix is nonnegative. -/
theorem traceNorm_nonneg [DecidableEq n] (A : Matrix m n ℂ) : 0 ≤ A.traceNorm := by
  unfold traceNorm
  exact (Complex.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))).trace_nonneg).1

/-- The zero matrix has trace norm zero. -/
@[simp] theorem traceNorm_zero [DecidableEq n] : (0 : Matrix m n ℂ).traceNorm = 0 := by
  unfold traceNorm
  simp [CFC.sqrt_zero]

/-- A rectangular matrix has trace norm zero if and only if it is zero. -/
theorem traceNorm_eq_zero_iff [DecidableEq n] (A : Matrix m n ℂ) : A.traceNorm = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, traceNorm_zero]⟩
  let B := CFC.sqrt (Aᴴ * A)
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have htr : B.trace = 0 := Complex.ext h (Complex.nonneg_iff.mp hB.trace_nonneg).2.symm
  have hB0 : B = 0 := by
    simpa only [Matrix.mul_one] using
      (hB.trace_mul_eq_zero_iff PosSemidef.one).mp (by simpa only [Matrix.mul_one] using htr)
  have hAA : Aᴴ * A = 0 := by
    rw [← CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self A).nonneg]
    change B * B = 0
    rw [hB0, Matrix.mul_zero]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [hAA, trace_zero])

/-- Negation preserves the trace norm. -/
@[simp] theorem traceNorm_neg [DecidableEq n] (A : Matrix m n ℂ) :
    (-A).traceNorm = A.traceNorm := by
  unfold traceNorm
  rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

/-- The trace norm is absolutely homogeneous under complex scalar multiplication. -/
theorem traceNorm_smul [DecidableEq n] (c : ℂ) (A : Matrix m n ℂ) :
    (c • A).traceNorm = ‖c‖ * A.traceNorm := by
  unfold traceNorm
  let H := CFC.sqrt (Aᴴ * A)
  have hH : H.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hgram : (c • A)ᴴ * (c • A) = (‖c‖ ^ 2 : ℝ) • (Aᴴ * A) := by
    ext i j
    simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
      Complex.real_smul, smul_eq_mul, Complex.star_def, Complex.ofReal_pow]
    rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hsqrt : CFC.sqrt ((c • A)ᴴ * (c • A)) = ‖c‖ • H := by
    rw [hgram]
    apply CFC.sqrt_unique _ (hH.smul (norm_nonneg c)).nonneg
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← sq]
    congr 1
    exact CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self A).nonneg
  rw [hsqrt, trace_smul, Complex.smul_re, smul_eq_mul]

/-- **Triangle inequality for the trace norm** of square matrices. -/
theorem traceNorm_add_le [DecidableEq n] (A B : Matrix n n ℂ) :
    (A + B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  obtain ⟨U, hU, hAB, _⟩ := traceNorm_eq_max_re_trace (A + B)
  have hA := re_trace_conjTranspose_mul_le_traceNorm A U hU
  have hB := re_trace_conjTranspose_mul_le_traceNorm B U hU
  rw [Matrix.mul_add, trace_add, Complex.add_re] at hAB
  linarith

/-- Left-multiplying by a rectangular isometry `V` (`Vᴴ * V = 1`) preserves the trace norm. -/
theorem traceNorm_isometry_mul [DecidableEq m] [DecidableEq n] {V : Matrix p m ℂ}
    (hV : Vᴴ * V = 1) (A : Matrix m n ℂ) :
    (V * A).traceNorm = A.traceNorm := by
  unfold traceNorm
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V A, hV, Matrix.one_mul]

/-- Conjugating a square matrix by a rectangular isometry `V` (`Vᴴ * V = 1`) preserves the trace
norm. -/
theorem traceNorm_isometry_conj [DecidableEq m] [DecidableEq p] {V : Matrix p m ℂ}
    (hV : Vᴴ * V = 1) (A : Matrix m m ℂ) :
    (V * A * Vᴴ).traceNorm = A.traceNorm := by
  calc
    (V * A * Vᴴ).traceNorm = (V * A * Vᴴ)ᴴ.traceNorm := (traceNorm_conjTranspose _).symm
    _ = (V * (V * A)ᴴ).traceNorm := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    _ = (V * A)ᴴ.traceNorm := traceNorm_isometry_mul hV (V * A)ᴴ
    _ = (V * A).traceNorm := traceNorm_conjTranspose _
    _ = A.traceNorm := traceNorm_isometry_mul hV A

/-- The trace norm of a Hermitian matrix is the sum of the absolute values of its eigenvalues. -/
theorem IsHermitian.traceNorm_eq_sum_abs_eigenvalues [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) : H.traceNorm = ∑ i : n, |hH.eigenvalues i| := by
  let U := star hH.eigenvectorUnitary
  let e := hH.eigenvalues
  let D : Matrix n n ℂ := diagonal fun i => (e i : ℂ)
  have hUD : Unitary.conjStarAlgAut ℂ _ U H = D := hH.conjStarAlgAut_star_eigenvectorUnitary
  rw [← traceNorm_conjStarAlgAut U H, hUD]
  unfold traceNorm
  let Aabs : Matrix n n ℂ := diagonal fun i => ((|e i| : ℝ) : ℂ)
  have hAabs_psd : Aabs.PosSemidef := by
    let R : Matrix n n ℂ := diagonal fun i => (Real.sqrt |e i| : ℂ)
    have hR : Rᴴ * R = Aabs := by
      unfold R Aabs
      rw [diagonal_conjTranspose, diagonal_mul_diagonal]
      congr 1
      funext i
      rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (abs_nonneg _)]
    exact hR ▸ posSemidef_conjTranspose_mul_self R
  have hsqrt : CFC.sqrt (Dᴴ * D) = Aabs := by
    apply CFC.sqrt_unique _ hAabs_psd.nonneg
    unfold Aabs D
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, abs_mul_abs_self]
  rw [hsqrt]
  unfold Aabs
  rw [trace_diagonal, Complex.re_sum]
  simp only [Complex.ofReal_re]
  rfl

end TraceNorm

end Matrix

namespace Cslib.Quantum

open Matrix Finset

/-! ### Metric and joint-convexity laws for `traceDistance` -/

section MetricAndConvexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Trace distance is nonnegative. -/
theorem traceDistance_nonneg (ρ σ : Matrix ι ι ℂ) : 0 ≤ traceDistance ρ σ :=
  div_nonneg (traceNorm_nonneg _) (by norm_num)

/-- Trace distance from a matrix to itself is zero. -/
@[simp] theorem traceDistance_self (ρ : Matrix ι ι ℂ) : traceDistance ρ ρ = 0 := by
  simp [traceDistance]

/-- Trace distance vanishes if and only if the two matrices are equal. -/
theorem traceDistance_eq_zero_iff (ρ σ : Matrix ι ι ℂ) :
    traceDistance ρ σ = 0 ↔ ρ = σ := by
  rw [traceDistance, div_eq_zero_iff]
  simp only [OfNat.ofNat_ne_zero, or_false, traceNorm_eq_zero_iff, sub_eq_zero]

/-- Trace distance is symmetric. -/
theorem traceDistance_comm (ρ σ : Matrix ι ι ℂ) :
    traceDistance ρ σ = traceDistance σ ρ := by
  unfold traceDistance
  rw [← neg_sub σ ρ, traceNorm_neg]

/-- **Triangle inequality** for trace distance. -/
theorem traceDistance_triangle (ρ τ σ : Matrix ι ι ℂ) :
    traceDistance ρ σ ≤ traceDistance ρ τ + traceDistance τ σ := by
  unfold traceDistance
  have hsub : ρ - σ = (ρ - τ) + (τ - σ) := by abel
  have h := traceNorm_add_le (ρ - τ) (τ - σ)
  rw [← hsub] at h
  linarith

/-- Trace distance between any two density matrices is at most `1`. -/
theorem traceDistance_le_one {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    traceDistance ρ σ ≤ 1 := by
  have hub := traceDistance_le_sqrt_one_sub_rootFidelity_sq hρ hσ
  have hsq : 1 - rootFidelity ρ σ ^ 2 ≤ 1 := by linarith [sq_nonneg (rootFidelity ρ σ)]
  exact hub.trans (Real.sqrt_le_one.mpr hsq)

private theorem traceNorm_finset_sum_le {α : Type*} (s : Finset α) (f : α → Matrix ι ι ℂ) :
    (∑ x ∈ s, f x).traceNorm ≤ ∑ x ∈ s, (f x).traceNorm := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (traceNorm_add_le _ _).trans (add_le_add_right ih _)

/-- **Joint convexity (sublinearity) of trace distance** over nonnegative real mixtures. -/
theorem traceDistance_sum_smul_le {α : Type*} (s : Finset α) (p : α → ℝ)
    (hp : ∀ x ∈ s, 0 ≤ p x) (ρ σ : α → Matrix ι ι ℂ) :
    traceDistance (∑ x ∈ s, (p x : ℂ) • ρ x) (∑ x ∈ s, (p x : ℂ) • σ x) ≤
      ∑ x ∈ s, p x * traceDistance (ρ x) (σ x) := by
  unfold traceDistance
  rw [← Finset.sum_sub_distrib]
  have hrew : (∑ x ∈ s, ((p x : ℂ) • ρ x - (p x : ℂ) • σ x)) =
      ∑ x ∈ s, (p x : ℂ) • (ρ x - σ x) :=
    Finset.sum_congr rfl fun x _ => (smul_sub (p x : ℂ) (ρ x) (σ x)).symm
  rw [hrew]
  have hsum := traceNorm_finset_sum_le s (fun x => (p x : ℂ) • (ρ x - σ x))
  have hterm : (∑ x ∈ s, ((p x : ℂ) • (ρ x - σ x)).traceNorm) =
      ∑ x ∈ s, p x * (ρ x - σ x).traceNorm := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [traceNorm_smul, Complex.norm_of_nonneg (hp x hx)]
  rw [hterm] at hsum
  have hdiv : (∑ x ∈ s, p x * ((ρ x - σ x).traceNorm / 2)) =
      (∑ x ∈ s, p x * (ρ x - σ x).traceNorm) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => (mul_div_assoc _ _ _).symm
  rw [hdiv]
  exact div_le_div_of_nonneg_right hsum (by norm_num)

end MetricAndConvexity

/-! ### Data-processing inequality under isometries, partial trace, and CPTP Kraus channels -/

section DataProcessing

/-- Conjugation `densityConj V` by a rectangular isometry `V` (`Vᴴ * V = 1`) preserves trace
distance exactly. -/
theorem traceDistance_densityConj {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {V : Matrix ι' ι ℂ} (hV : Vᴴ * V = 1)
    (ρ σ : Matrix ι ι ℂ) :
    traceDistance (densityConj V ρ) (densityConj V σ) = traceDistance ρ σ := by
  unfold traceDistance
  rw [← map_sub, densityConj_apply, traceNorm_isometry_conj hV]

/-- Unitary evolution preserves trace distance. -/
theorem traceDistance_conj_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ unitaryGroup ι ℂ) (ρ σ : Matrix ι ι ℂ) :
    traceDistance (U * ρ * Uᴴ) (U * σ * Uᴴ) = traceDistance ρ σ := by
  have hUU : Uᴴ * U = 1 := (mem_unitaryGroup_iff').mp hU
  simpa only [densityConj_apply] using traceDistance_densityConj hUU ρ σ

/-- Tracing out the second register cannot increase the trace norm. -/
theorem traceNorm_partialTraceRight_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (Δ : Matrix (ι × κ) (ι × κ) ℂ) :
    (partialTraceRight Δ).traceNorm ≤ Δ.traceNorm := by
  obtain ⟨U, hU, hval, _⟩ := traceNorm_eq_max_re_trace (partialTraceRight Δ)
  let W : Matrix (ι × κ) (ι × κ) ℂ := U ⊗ₖ (1 : Matrix κ κ ℂ)
  have hW : W ∈ unitaryGroup (ι × κ) ℂ := kronecker_mem_unitary hU (one_mem _)
  have htr : (Wᴴ * Δ).trace = (Uᴴ * partialTraceRight Δ).trace := by
    dsimp only [W]
    rw [conjTranspose_kronecker, conjTranspose_one, trace_kronecker_one_mul]
  have hub := re_trace_conjTranspose_mul_le_traceNorm Δ W hW
  rw [htr] at hub
  linarith

/-- Tracing out the first register cannot increase the trace norm. -/
theorem traceNorm_partialTraceLeft_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (Δ : Matrix (ι × κ) (ι × κ) ℂ) :
    (partialTraceLeft Δ).traceNorm ≤ Δ.traceNorm := by
  obtain ⟨U, hU, hval, _⟩ := traceNorm_eq_max_re_trace (partialTraceLeft Δ)
  let W : Matrix (ι × κ) (ι × κ) ℂ := (1 : Matrix ι ι ℂ) ⊗ₖ U
  have hW : W ∈ unitaryGroup (ι × κ) ℂ := kronecker_mem_unitary (one_mem _) hU
  have htr : (Wᴴ * Δ).trace = (Uᴴ * partialTraceLeft Δ).trace := by
    simp only [W, conjTranspose_kronecker, conjTranspose_one, Matrix.trace, diag_apply,
      Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply, Matrix.one_apply,
      partialTraceLeft_apply, ite_mul, one_mul, zero_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    calc
      (∑ i : ι, ∑ j : ι, ∑ l : κ, if i = j then Uᴴ k l * Δ (j, l) (i, k) else 0)
          = ∑ i : ι, ∑ l : κ, ∑ j : ι, if i = j then Uᴴ k l * Δ (j, l) (i, k) else 0 :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ i : ι, ∑ l : κ, Uᴴ k l * Δ (i, l) (i, k) := by simp
      _ = ∑ l : κ, ∑ i : ι, Uᴴ k l * Δ (i, l) (i, k) := Finset.sum_comm
  have hub := re_trace_conjTranspose_mul_le_traceNorm Δ W hW
  rw [htr] at hub
  linarith

/-- **Data processing of trace distance under right partial trace**: discarding the second
register cannot increase trace distance. -/
theorem traceDistance_partialTraceRight_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (ρ σ : Matrix (ι × κ) (ι × κ) ℂ) :
    traceDistance (partialTraceRight ρ) (partialTraceRight σ) ≤ traceDistance ρ σ := by
  unfold traceDistance
  have hsub : partialTraceRight ρ - partialTraceRight σ = partialTraceRight (ρ - σ) := by
    ext i j
    simp [Finset.sum_sub_distrib]
  rw [hsub]
  exact div_le_div_of_nonneg_right (traceNorm_partialTraceRight_le (ρ - σ)) (by norm_num)

/-- **Data processing of trace distance under left partial trace**: discarding the first
register cannot increase trace distance. -/
theorem traceDistance_partialTraceLeft_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (ρ σ : Matrix (ι × κ) (ι × κ) ℂ) :
    traceDistance (partialTraceLeft ρ) (partialTraceLeft σ) ≤ traceDistance ρ σ := by
  unfold traceDistance
  have hsub : partialTraceLeft ρ - partialTraceLeft σ = partialTraceLeft (ρ - σ) := by
    ext k k'
    simp [Finset.sum_sub_distrib]
  rw [hsub]
  exact div_le_div_of_nonneg_right (traceNorm_partialTraceLeft_le (ρ - σ)) (by norm_num)

/-- **Contractivity of trace norm under CPTP Kraus maps**: for any finite family `{Kⱼ}_{j ∈ s}`
with `∑_{j ∈ s} Kⱼᴴ Kⱼ = 1` and any square matrix `Δ`, `(∑_{j ∈ s} Kⱼ Δ Kⱼᴴ).traceNorm ≤
Δ.traceNorm`. -/
theorem traceNorm_kraus_le {ι ι' α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (s : Finset α) (K : α → Matrix ι' ι ℂ)
    (hK : ∑ j ∈ s, (K j)ᴴ * K j = 1) (Δ : Matrix ι ι ℂ) :
    (∑ j ∈ s, K j * Δ * (K j)ᴴ).traceNorm ≤ Δ.traceNorm := by
  classical
  let V : Matrix (ι' × ↥s) ι ℂ := fun ⟨p, j⟩ i => K j.1 p i
  have hV : Vᴴ * V = 1 := by
    ext i₁ i₂
    have hlhs : (Vᴴ * V) i₁ i₂ = ∑ p : ι', ∑ j : ↥s, star (K j.1 p i₁) * K j.1 p i₂ := by
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      rfl
    have hcomm : (∑ p : ι', ∑ j : ↥s, star (K j.1 p i₁) * K j.1 p i₂) =
        ∑ j : ↥s, ∑ p : ι', star (K j.1 p i₁) * K j.1 p i₂ := Finset.sum_comm
    have hcoe : (∑ j : ↥s, ∑ p : ι', star (K j.1 p i₁) * K j.1 p i₂) =
        ∑ x ∈ s, ∑ p : ι', star (K x p i₁) * K x p i₂ :=
      Finset.sum_coe_sort s (fun x => ∑ p : ι', star (K x p i₁) * K x p i₂)
    have hsum : (∑ x ∈ s, ∑ p : ι', star (K x p i₁) * K x p i₂) =
        (∑ x ∈ s, (K x)ᴴ * K x) i₁ i₂ := by
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun x _ => rfl
    exact hlhs.trans (hcomm.trans (hcoe.trans (hsum.trans (by rw [hK]))))
  have hpt : partialTraceRight (V * Δ * Vᴴ) = ∑ j ∈ s, K j * Δ * (K j)ᴴ := by
    ext p₁ p₂
    rw [partialTraceRight_apply, ← Finset.sum_coe_sort s, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_apply, conjTranspose_apply]
    rfl
  rw [← hpt, ← traceNorm_isometry_conj hV Δ]
  exact traceNorm_partialTraceRight_le (V * Δ * Vᴴ)

/-- **Data-processing inequality for trace distance under CPTP Kraus channels**: for any finite
family `{Kⱼ}_{j ∈ s}` with `∑_{j ∈ s} Kⱼᴴ Kⱼ = 1` and any matrices `ρ, σ`,
`traceDistance (∑_{j ∈ s} Kⱼ ρ Kⱼᴴ) (∑_{j ∈ s} Kⱼ σ Kⱼᴴ) ≤ traceDistance ρ σ`. -/
theorem traceDistance_kraus_le {ι ι' α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (s : Finset α) (K : α → Matrix ι' ι ℂ)
    (hK : ∑ j ∈ s, (K j)ᴴ * K j = 1) (ρ σ : Matrix ι ι ℂ) :
    traceDistance (∑ j ∈ s, K j * ρ * (K j)ᴴ) (∑ j ∈ s, K j * σ * (K j)ᴴ) ≤
      traceDistance ρ σ := by
  unfold traceDistance
  have hsub : (∑ j ∈ s, K j * ρ * (K j)ᴴ) - (∑ j ∈ s, K j * σ * (K j)ᴴ) =
      ∑ j ∈ s, K j * (ρ - σ) * (K j)ᴴ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hsub]
  exact div_le_div_of_nonneg_right (traceNorm_kraus_le s K hK (ρ - σ)) (by norm_num)

end DataProcessing

/-! ### Operational POVM characterization and the Holevo–Helstrom theorem -/

section Helstrom

variable {A ι : Type*} [Fintype A] [Fintype ι] [DecidableEq ι]

/-- **POVM distinguishability bound**: for every finite-outcome `M : POVM A ι` and matrices `ρ, σ`,
half the `ℓ₁` (total variation) distance between `M.densityProb ρ` and `M.densityProb σ` is at
most `traceDistance ρ σ`. -/
theorem POVM.half_sum_abs_densityProb_sub_le_traceDistance (M : POVM A ι)
    (ρ σ : Matrix ι ι ℂ) :
    (1 / 2 : ℝ) * ∑ a : A, |M.densityProb ρ a - M.densityProb σ a| ≤ traceDistance ρ σ := by
  let Δ := ρ - σ
  let H := CFC.sqrt (Δᴴ * Δ)
  have hH_psd : H.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hH_herm : Hᴴ = H := hH_psd.isHermitian.eq
  obtain ⟨U, hU, hUH⟩ := Δ.exists_unitary_polar
  let Q := CFC.sqrt H
  have hQ_herm : Qᴴ = Q := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian.eq
  have hQ2 : Q * Q = H := CFC.sqrt_mul_sqrt_self _ hH_psd.nonneg
  have hterm (a : A) :
      2 * |M.densityProb ρ a - M.densityProb σ a| ≤
        (M.effect a * H).trace.re + ((Uᴴ * M.effect a * U) * H).trace.re := by
    let E := M.effect a
    have hE_psd : E.PosSemidef := M.posSemidef a
    let P := CFC.sqrt E
    have hP_herm : Pᴴ = P := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg E)).isHermitian.eq
    have hP2 : P * P = E := CFC.sqrt_mul_sqrt_self _ hE_psd.nonneg
    let X := Q * P
    let Y := Q * Uᴴ * P
    have hXX : (X * Xᴴ).trace = (E * H).trace := by
      dsimp only [X]
      rw [conjTranspose_mul, hP_herm, hQ_herm, Matrix.mul_assoc, ← Matrix.mul_assoc P P Q, hP2,
        trace_mul_comm Q, Matrix.mul_assoc, hQ2]
    have hYY : (Y * Yᴴ).trace = ((Uᴴ * E * U) * H).trace := by
      dsimp only [Y]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP_herm, hQ_herm, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P P, hP2, trace_mul_comm Q]
      simp only [Matrix.mul_assoc, hQ2]
    have hXY : (X * Yᴴ).trace = (E * Δ).trace := by
      dsimp only [X, Y]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP_herm, hQ_herm, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P P, hP2, trace_mul_comm Q]
      simp only [Matrix.mul_assoc, hQ2]
      rw [show U * H = Δ from hUH]
    have hYX_re : (Y * Xᴴ).trace.re = (E * Δ).trace.re := by
      calc
        (Y * Xᴴ).trace.re = (star (Y * Xᴴ).trace).re := (Complex.conj_re _).symm
        _ = (Y * Xᴴ)ᴴ.trace.re := by rw [trace_conjTranspose]
        _ = (E * Δ).trace.re := by rw [conjTranspose_mul, conjTranspose_conjTranspose, hXY]
    have hdiff : M.densityProb ρ a - M.densityProb σ a = (E * Δ).trace.re := by
      simp only [POVM.densityProb, E, Δ, Matrix.mul_sub, trace_sub, Complex.sub_re]
    have hpos₁ := (Complex.nonneg_iff.mp (posSemidef_self_mul_conjTranspose (X - Y)).trace_nonneg).1
    have hpos₂ := (Complex.nonneg_iff.mp (posSemidef_self_mul_conjTranspose (X + Y)).trace_nonneg).1
    rw [conjTranspose_sub, sub_mul, mul_sub, mul_sub, trace_sub, trace_sub, trace_sub,
      Complex.sub_re, Complex.sub_re, Complex.sub_re, hXX, hYY, hXY, hYX_re] at hpos₁
    rw [conjTranspose_add, add_mul, mul_add, mul_add, trace_add, trace_add, trace_add,
      Complex.add_re, Complex.add_re, Complex.add_re, hXX, hYY, hXY, hYX_re] at hpos₂
    rw [hdiff]
    rcases le_total 0 (E * Δ).trace.re with hge | hle
    · rw [abs_of_nonneg hge]; linarith
    · rw [abs_of_nonpos hle]; linarith
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hterm a
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hsum₁ : (∑ a : A, (M.effect a * H).trace.re) = Δ.traceNorm := by
    rw [← Complex.re_sum, ← trace_sum, ← Finset.sum_mul, M.sum_effect, Matrix.one_mul]
    rfl
  have hsum₂ : (∑ a : A, ((Uᴴ * M.effect a * U) * H).trace.re) = Δ.traceNorm := by
    have hUU : Uᴴ * U = 1 := (mem_unitaryGroup_iff').mp hU
    rw [← Complex.re_sum, ← trace_sum, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
      M.sum_effect, Matrix.mul_one, hUU, Matrix.one_mul]
    rfl
  rw [hsum₁, hsum₂] at hsum
  unfold traceDistance
  linarith

/-- For any POVM `M : POVM A ι`, outcome event `S : Finset A`, and density matrices `ρ, σ`, the
probability of observing an outcome in `S` differs between `ρ` and `σ` by at most
`traceDistance ρ σ`. -/
theorem POVM.abs_sum_densityProb_sub_le_traceDistance (M : POVM A ι) (S : Finset A)
    {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    |(∑ a ∈ S, M.densityProb ρ a) - ∑ a ∈ S, M.densityProb σ a| ≤ traceDistance ρ σ := by
  classical
  let d (a : A) : ℝ := M.densityProb ρ a - M.densityProb σ a
  have hsum_zero : ∑ a : A, d a = 0 := by
    simp only [d, Finset.sum_sub_distrib, M.sum_densityProb, hρ.trace_eq_one, hσ.trace_eq_one,
      sub_self]
  have hsplit := Finset.sum_add_sum_compl S d
  rw [hsum_zero] at hsplit
  have hSc : ∑ a ∈ Sᶜ, d a = -∑ a ∈ S, d a := eq_neg_of_add_eq_zero_right hsplit
  have htri₁ : |∑ a ∈ S, d a| ≤ ∑ a ∈ S, |d a| := Finset.abs_sum_le_sum_abs d S
  have htri₂ : |∑ a ∈ S, d a| ≤ ∑ a ∈ Sᶜ, |d a| := by
    rw [← abs_neg, ← hSc]
    exact Finset.abs_sum_le_sum_abs d Sᶜ
  have htot : ∑ a ∈ S, |d a| + ∑ a ∈ Sᶜ, |d a| = ∑ a : A, |d a| :=
    Finset.sum_add_sum_compl S (fun a => |d a|)
  have hub := M.half_sum_abs_densityProb_sub_le_traceDistance ρ σ
  have hrew : (∑ a ∈ S, M.densityProb ρ a) - ∑ a ∈ S, M.densityProb σ a = ∑ a ∈ S, d a :=
    (Finset.sum_sub_distrib _ _).symm
  rw [hrew]
  linarith

/-- The `±1` spectral sign observable of Hermitian `ρ - σ`, equal to `+1` on the nonnegative
eigenspace of `ρ - σ` and `-1` on the negative eigenspace. -/
@[expose] noncomputable def helstromObservable {ρ σ : Matrix ι ι ℂ} (hΔ : (ρ - σ).IsHermitian) :
    Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ hΔ.eigenvectorUnitary
    (diagonal fun i : ι => if 0 ≤ hΔ.eigenvalues i then (1 : ℂ) else -1)

/-- `helstromObservable` is Hermitian. -/
theorem isHermitian_helstromObservable {ρ σ : Matrix ι ι ℂ} (hΔ : (ρ - σ).IsHermitian) :
    (helstromObservable hΔ).IsHermitian := by
  unfold helstromObservable
  rw [Unitary.conjStarAlgAut_apply]
  change ((hΔ.eigenvectorUnitary : Matrix ι ι ℂ) * _ *
    ((hΔ.eigenvectorUnitary : Matrix ι ι ℂ))ᴴ).IsHermitian
  have hdiag :
      (diagonal fun i : ι => if 0 ≤ hΔ.eigenvalues i then (1 : ℂ) else -1).IsHermitian := by
    rw [IsHermitian, diagonal_conjTranspose]
    congr 1
    funext i
    by_cases hi : 0 ≤ hΔ.eigenvalues i <;> simp [hi]
  rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hdiag.eq,
    Matrix.mul_assoc]

/-- `helstromObservable` squares to the identity. -/
theorem helstromObservable_mul_self {ρ σ : Matrix ι ι ℂ} (hΔ : (ρ - σ).IsHermitian) :
    helstromObservable hΔ * helstromObservable hΔ = 1 := by
  unfold helstromObservable
  rw [← map_mul]
  have hdiag : (diagonal fun i : ι => if 0 ≤ hΔ.eigenvalues i then (1 : ℂ) else -1) *
      (diagonal fun i : ι => if 0 ≤ hΔ.eigenvalues i then (1 : ℂ) else -1) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    by_cases hi : 0 ≤ hΔ.eigenvalues i <;> simp [hi]
  rw [hdiag, map_one]

/-- The two-outcome projective **Helstrom POVM** distinguishing `ρ` (outcome `false`) from `σ`
(outcome `true`), built as `POVM.ofObservable` of `helstromObservable`. -/
@[expose] noncomputable def helstromPOVM {ρ σ : Matrix ι ι ℂ} (hΔ : (ρ - σ).IsHermitian) :
    POVM Bool ι :=
  POVM.ofObservable (helstromObservable hΔ)
    (isHermitian_helstromObservable hΔ) (helstromObservable_mul_self hΔ)

@[simp] theorem helstromPOVM_effect {ρ σ : Matrix ι ι ℂ} (hΔ : (ρ - σ).IsHermitian) (b : Bool) :
    (helstromPOVM hΔ).effect b =
      bif b then (2⁻¹ : ℂ) • (1 - helstromObservable hΔ)
      else (2⁻¹ : ℂ) • (1 + helstromObservable hΔ) :=
  POVM.ofObservable_effect _ _ _ b

/-- Pairing `helstromObservable` with `ρ - σ` recovers the trace norm `(ρ - σ).traceNorm`. -/
theorem re_trace_helstromObservable_mul_sub {ρ σ : Matrix ι ι ℂ} (hΔ : (ρ - σ).IsHermitian) :
    (helstromObservable hΔ * (ρ - σ)).trace.re = (ρ - σ).traceNorm := by
  let U := hΔ.eigenvectorUnitary
  let e := hΔ.eigenvalues
  let S : Matrix ι ι ℂ := diagonal fun i => if 0 ≤ e i then (1 : ℂ) else -1
  have hinv : Unitary.conjStarAlgAut ℂ _ (star U) (helstromObservable hΔ) = S := by
    unfold helstromObservable
    rw [Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star]
    change star (U : Matrix ι ι ℂ) * ((U : Matrix ι ι ℂ) * S * star (U : Matrix ι ι ℂ)) *
      (U : Matrix ι ι ℂ) = S
    simp only [← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]
    rw [Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
  rw [← trace_conjStarAlgAut (star U) (helstromObservable hΔ * (ρ - σ)), map_mul, hinv,
    hΔ.conjStarAlgAut_star_eigenvectorUnitary]
  change (S * diagonal fun i => (e i : ℂ)).trace.re = _
  rw [hΔ.traceNorm_eq_sum_abs_eigenvalues]
  unfold S
  rw [diagonal_mul_diagonal, trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : 0 ≤ e i
  · simp only [hi, ↓reduceIte, one_mul, Complex.ofReal_re]
    exact (abs_of_nonneg hi).symm
  · have hlt : e i < 0 := lt_of_not_ge hi
    simp only [hi, ↓reduceIte, neg_mul, one_mul, Complex.neg_re, Complex.ofReal_re]
    exact (abs_of_neg hlt).symm

/-- On Hermitian matrices with equal real trace (in particular density matrices), `helstromPOVM`
achieves probability gap `traceDistance ρ σ` on outcome `false`. -/
theorem helstromPOVM_densityProb_sub_false {ρ σ : Matrix ι ι ℂ} (hΔ : (ρ - σ).IsHermitian)
    (htr : ρ.trace.re = σ.trace.re) :
    (helstromPOVM hΔ).densityProb ρ false - (helstromPOVM hΔ).densityProb σ false =
      traceDistance ρ σ := by
  have hsub : (ρ - σ).trace.re = 0 := by rw [trace_sub, Complex.sub_re, htr, sub_self]
  simp only [POVM.densityProb, helstromPOVM_effect, Bool.cond_false]
  rw [← Complex.sub_re, ← trace_sub, ← Matrix.mul_sub, Matrix.smul_mul, Matrix.add_mul,
    Matrix.one_mul, trace_smul, trace_add]
  have hre : ((2⁻¹ : ℂ) * ((ρ - σ).trace + (helstromObservable hΔ * (ρ - σ)).trace)).re =
      ((ρ - σ).trace.re + (helstromObservable hΔ * (ρ - σ)).trace.re) / 2 := by
    simp [Complex.mul_re]
    ring
  rw [smul_eq_mul, hre, hsub, zero_add, re_trace_helstromObservable_mul_sub]
  rfl

/-- **Attainment in the operational POVM characterization of trace distance**: on Hermitian
matrices with equal real trace (in particular density matrices), `helstromPOVM` attains
`½ ∑_b |P_ρ(b) - P_σ(b)| = traceDistance ρ σ`. -/
theorem helstromPOVM_half_sum_abs_densityProb_sub {ρ σ : Matrix ι ι ℂ}
    (hΔ : (ρ - σ).IsHermitian) (htr : ρ.trace.re = σ.trace.re) :
    (1 / 2 : ℝ) * ∑ b : Bool, |(helstromPOVM hΔ).densityProb ρ b -
        (helstromPOVM hΔ).densityProb σ b| =
      traceDistance ρ σ := by
  have hfalse := helstromPOVM_densityProb_sub_false hΔ htr
  have hsum_ρ := (helstromPOVM hΔ).sum_densityProb ρ
  have hsum_σ := (helstromPOVM hΔ).sum_densityProb σ
  rw [Fintype.sum_bool] at hsum_ρ hsum_σ ⊢
  have htrue : (helstromPOVM hΔ).densityProb ρ true - (helstromPOVM hΔ).densityProb σ true =
      -traceDistance ρ σ := by linarith
  have hnn := traceDistance_nonneg ρ σ
  rw [hfalse, htrue, abs_of_nonneg hnn, abs_neg, abs_of_nonneg hnn]
  ring

/-- **Holevo–Helstrom upper bound** ([de Wolf][deWolf2019], Chapter 15): for any two density
matrices `ρ, σ` and any two-outcome `M : POVM Bool ι` guessing `false` for `ρ` and `true` for `σ`,
the equal-prior success probability is at most `½ + ½ traceDistance ρ σ`. -/
theorem helstrom_success_le (M : POVM Bool ι) {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    (1 / 2 : ℝ) * (M.densityProb ρ false + M.densityProb σ true) ≤
      1 / 2 + traceDistance ρ σ / 2 := by
  have hsum_σ := M.sum_densityProb σ
  rw [Fintype.sum_bool, hσ.trace_eq_one, Complex.one_re] at hsum_σ
  have hub := M.abs_sum_densityProb_sub_le_traceDistance {false} hρ hσ
  simp only [Finset.sum_singleton] at hub
  have hle : M.densityProb ρ false - M.densityProb σ false ≤ traceDistance ρ σ :=
    (le_abs_self _).trans hub
  linarith

/-- **Holevo–Helstrom attainment**: for any two density matrices `ρ, σ`, `helstromPOVM` achieves
equal-prior discrimination probability `½ + ½ traceDistance ρ σ`. -/
theorem helstromPOVM_success {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    let hΔ := hρ.posSemidef.isHermitian.sub hσ.posSemidef.isHermitian
    (1 / 2 : ℝ) * ((helstromPOVM hΔ).densityProb ρ false +
        (helstromPOVM hΔ).densityProb σ true) =
      1 / 2 + traceDistance ρ σ / 2 := by
  intro hΔ
  have hsum_σ := (helstromPOVM hΔ).sum_densityProb σ
  rw [Fintype.sum_bool, hσ.trace_eq_one, Complex.one_re] at hsum_σ
  have htr : ρ.trace.re = σ.trace.re := by rw [hρ.trace_eq_one, hσ.trace_eq_one]
  have hfalse := helstromPOVM_densityProb_sub_false hΔ htr
  linarith

end Helstrom

end Cslib.Quantum
