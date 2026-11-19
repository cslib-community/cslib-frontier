/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Schmidt
public import CslibFrontier.Foundations.Quantum.Algebra.SpectralRounding
import CslibFrontier.Foundations.Quantum.Algebra.CStar

/-!
# Projective rounding of almost-synchronous strategies

The finite spectral mixture of [Vidick, Theorem 3.1][Vidick2022] in Schmidt coordinates.
The mixture exactly recovers the reduced density. On each nonempty cut the component has the
uniform Schmidt spectrum and projective effects. The error is the normalized squared column
error on that cut.
-/

public section

open Matrix Finset Cslib.Quantum
open scoped MatrixOrder ComplexOrder

namespace Cslib.PCP.QuantumStrategy

variable {ι X A : Type*}

local notation "Cuts" => {s : Finset ι // Finset.Nonempty s}

private theorem cut_card_pos (s : Cuts) : 0 < (s.val.card : ℝ) := by
  exact_mod_cast card_pos.mpr s.property

private theorem mul_card_inv_cancel (s : Cuts) (x : ℝ) :
    x * (s.val.card : ℝ) * (s.val.card : ℝ)⁻¹ = x := by
  rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (cut_card_pos s)), mul_one]

variable [Fintype ι]

/-- The probability weight of a cut is its width times its dimension. -/
noncomputable def spectralCutWeight (d : ι → ℝ) (s : Cuts) : ℝ :=
  diagonalCutWidth d s * s.val.card

/-- The totally mixed state on the cut, as a density matrix on the original space. -/
@[expose] noncomputable def spectralCutDensity [DecidableEq ι] (s : Cuts) : Matrix ι ι ℂ :=
  (s.val.card : ℝ)⁻¹ • diagonal (fun i => if i ∈ s.val then (1 : ℂ) else 0)

theorem spectralCutWeight_nonneg (d : ι → ℝ) (s : Cuts) : 0 ≤ spectralCutWeight d s :=
  mul_nonneg (diagonalCutWidth_nonneg d s) (by positivity)

theorem sum_spectralCutWeight (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1) :
    ∑ s : Cuts, spectralCutWeight d s = 1 := by
  unfold spectralCutWeight
  rw [sum_diagonalCutWidth_card d hd, htrace]

theorem diagonal_eq_sum_spectralCutDensity [DecidableEq ι] (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    diagonal (fun i => (d i : ℂ)) = ∑ s : Cuts, spectralCutWeight d s • spectralCutDensity s := by
  rw [diagonal_eq_sum_diagonalCutWidth d hd]
  refine sum_congr rfl fun s _ => ?_
  unfold spectralCutWeight spectralCutDensity
  rw [smul_smul, mul_card_inv_cancel]

variable [DecidableEq ι]

omit [Fintype ι] in
private theorem spectralCutDensity_eq_diagonal (s : Cuts) : spectralCutDensity s =
    diagonal (fun i => if i ∈ s.val then (↑((s.val.card : ℝ)⁻¹) : ℂ) else 0) := by
  ext i j
  by_cases hij : i = j
  · subst j
    unfold spectralCutDensity
    rw [Matrix.smul_apply, diagonal_apply_eq, diagonal_apply_eq, Complex.real_smul]
    split_ifs <;> simp
  · simp [spectralCutDensity, Matrix.smul_apply, diagonal_apply_ne _ hij]

/-- A nonempty cut carries the totally mixed density on its retained coordinates. -/
theorem spectralCutDensity_isDensityMatrix (s : Cuts) :
    IsDensityMatrix (spectralCutDensity s) := by
  rw [spectralCutDensity_eq_diagonal]
  constructor
  · rw [posSemidef_diagonal_iff]
    intro i
    by_cases hi : i ∈ s.val
    · simpa only [ite_eq_left hi] using
        (Complex.zero_le_real.mpr (inv_nonneg.mpr (cut_card_pos s).le))
    · simp [hi]
  · rw [trace_diagonal, ← sum_filter]
    rw [show univ.filter (· ∈ s.val) = s.val by ext; simp]
    rw [sum_const, nsmul_eq_mul]
    have hn : ((s.val.card : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (cut_card_pos s))
    rw [Complex.ofReal_natCast] at hn
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
    exact mul_inv_cancel₀ hn

/-- Extend a cut matrix by zero in both coordinates. -/
@[expose] noncomputable def extendCutMatrix (s : Finset ι)
    (B : Matrix {i : ι // i ∈ s} {i : ι // i ∈ s} ℂ) : Matrix ι ι ℂ :=
  fun i j => if hi : i ∈ s then if hj : j ∈ s then B ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

omit [Fintype ι] in
theorem star_extendCutMatrix (s : Finset ι)
    (B : Matrix {i : ι // i ∈ s} {i : ι // i ∈ s} ℂ) :
    star (extendCutMatrix s B) = extendCutMatrix s (star B) := by
  ext i j
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp [extendCutMatrix, star_apply, hi, hj]

/-- Normalized column error equals the expectation of the squared operator error
in the totally mixed state on the cut. -/
theorem cutColumnError_div_card_eq (s : Cuts) (T : Matrix ι ι ℂ)
    (B : Matrix {i : ι // i ∈ s.val} {i : ι // i ∈ s.val} ℂ) :
    Measurement.cutColumnError s.val T B / (s.val.card : ℝ) =
      (Matrix.trace (star (T - extendCutMatrix s.val B) * (T - extendCutMatrix s.val B) *
        spectralCutDensity s)).re := by
  let C := T - extendCutMatrix s.val B
  have hentry (i : ι) :
      ((star C * C * spectralCutDensity s) i i).re =
        if i ∈ s.val then (∑ j, ‖C j i‖ ^ 2) * (s.val.card : ℝ)⁻¹ else 0 := by
    rw [spectralCutDensity_eq_diagonal, mul_diagonal]
    by_cases hi : i ∈ s.val
    · rw [ite_eq_left hi, ite_eq_left hi, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, re_star_mul_self_diag]
    · simp [hi]
  calc
    _ = (∑ j : s.val, ∑ i, ‖C i j.val‖ ^ 2) * (s.val.card : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]
      congr 1
      unfold Measurement.cutColumnError
      refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
      change ‖T i j.val - (if hi : i ∈ s.val then B ⟨i, hi⟩ j else 0)‖ ^ 2 =
        ‖T i j.val - extendCutMatrix s.val B i j.val‖ ^ 2
      by_cases hi : i ∈ s.val <;> simp [extendCutMatrix, hi, j.property]
    _ = _ := by
      change _ = (Matrix.trace (star C * C * spectralCutDensity s)).re
      simp only [Matrix.trace, diag_apply, Complex.re_sum, hentry, ← sum_filter]
      rw [show univ.filter (· ∈ s.val) = s.val by ext; simp,
        Finset.sum_coe_sort s.val (fun j => ∑ i, ‖C i j‖ ^ 2), Finset.sum_mul]

variable [Fintype A]

/-- The symmetric strategy on a cut with uniform squared Schmidt coefficients.
When its supplied measurements are projective, this is a projective maximally entangled
strategy. -/
noncomputable def ofSpectralCut (s : Cuts)
    (M : X → Measurement A (Matrix {i : ι // i ∈ s.val} {i : ι // i ∈ s.val} ℂ)) :
    QuantumStrategy X X A A {i : ι // i ∈ s.val} {i : ι // i ∈ s.val} :=
  ofSchmidt (fun _ => (s.val.card : ℝ)⁻¹) (fun _ => inv_nonneg.mpr (cut_card_pos s).le)
    (by
      simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
      exact mul_inv_cancel₀ (ne_of_gt (cut_card_pos s)))
    (fun x => ⟨(M x).effect, fun a => Matrix.nonneg_iff_posSemidef.mp ((M x).nonneg a),
      (M x).sum_effect⟩)

omit [Fintype ι] in
@[simp] theorem ofSpectralCut_alice_effect (s : Cuts)
    (M : X → Measurement A (Matrix {i : ι // i ∈ s.val} {i : ι // i ∈ s.val} ℂ))
    (x : X) (a : A) : ((ofSpectralCut s M).alice x).effect a = (M x).effect a := by
  unfold ofSpectralCut
  rw [ofSchmidt_alice_effect]

omit [Fintype ι] in
@[simp] theorem ofSpectralCut_bob_effect (s : Cuts)
    (M : X → Measurement A (Matrix {i : ι // i ∈ s.val} {i : ι // i ∈ s.val} ℂ))
    (x : X) (a : A) : ((ofSpectralCut s M).bob x).effect a = ((M x).effect a)ᵀ := by
  unfold ofSpectralCut
  rw [ofSchmidt_bob_effect]

omit [Fintype ι] in
theorem partialTraceRight_pureState_ofSpectralCut (s : Cuts)
    (M : X → Measurement A (Matrix {i : ι // i ∈ s.val} {i : ι // i ∈ s.val} ℂ)) :
    extendCutMatrix s.val (partialTraceRight (pureState (ofSpectralCut s M).state)) =
      spectralCutDensity s := by
  unfold ofSpectralCut
  rw [ofSchmidt_state, partialTraceRight_pureState_schmidtVector]
  · ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i ∈ s.val <;>
        simp [extendCutMatrix, spectralCutDensity, hi, Matrix.smul_apply, Complex.real_smul]
    · by_cases hi : i ∈ s.val <;> by_cases hj : j ∈ s.val
      all_goals simp [extendCutMatrix, spectralCutDensity, hi, hj, Matrix.smul_apply,
        hij, Subtype.ext_iff]
  · exact fun _ => inv_nonneg.mpr (cut_card_pos s).le

omit [Fintype ι] in
/-- The cut strategy's joint probabilities are the normalized trace of the product. -/
theorem ofSpectralCut_prob_eq_trace (s : Cuts)
    (M : X → Measurement A (Matrix {i : ι // i ∈ s.val} {i : ι // i ∈ s.val} ℂ))
    (x y : X) (a b : A) :
    (ofSpectralCut s M).prob x y a b =
      (s.val.card : ℝ)⁻¹ * (Matrix.trace ((M x).effect a * (M y).effect b)).re := by
  unfold ofSpectralCut
  rw [prob_ofSchmidt_const _ (inv_nonneg.mpr (cut_card_pos s).le)]

omit [Fintype ι] in
open scoped Matrix.Norms.L2Operator in
/-- Projective strategies on a uniform cut give zero probability to unequal answers
on a repeated question. -/
theorem ofSpectralCut_prob_eq_zero (s : Cuts)
    (M : X → Measurement A (Matrix {i : ι // i ∈ s.val} {i : ι // i ∈ s.val} ℂ))
    (hM : ∀ x, (M x).IsProjective) (x : X) {a b : A} (hab : a ≠ b) :
    (ofSpectralCut s M).prob x x a b = 0 := by
  rw [ofSpectralCut_prob_eq_trace, (hM x).mul_eq_zero hab, Matrix.trace_zero, Complex.zero_re,
    mul_zero]

/-- Matching-answer agreement in a Schmidt strategy is the geometric-mean-weighted
agreement of its Alice POVM. -/
theorem sum_prob_same_ofSchmidt (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1)
    (M : X → POVM A ι) (x : X) :
    (∑ a, (ofSchmidt d hd htrace M).prob x x a a) = (M x).toMeasurement.schmidtAgreement d := by
  simp_rw [prob_ofSchmidt_same, Measurement.schmidtAgreement, POVM.toMeasurement_effect, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_comm

variable [Fintype X]


/-- Vidick's finite projective mixture for a symmetric strategy in its Schmidt basis.
The probabilities of the cuts and the component densities depend only on the input spectrum.
Direct orthogonalization of the compressed POVMs gives the bound 9δ + 10√(2δ). -/
theorem exists_projective_spectral_mixture (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (htrace : ∑ i, d i = 1) (M : X → POVM A ι) (ν : PMF X) :
    let S := ofSchmidt d hd htrace M
    let δ := ∑ x, (ν x).toReal * (1 - ∑ a, S.prob x x a a)
    ∃ T : (s : Cuts) → QuantumStrategy X X A A
      {i : ι // i ∈ s.val} {i : ι // i ∈ s.val},
      (∀ s x a, ((T s).alice x).effect a * ((T s).alice x).effect a = ((T s).alice x).effect a) ∧
      (∀ s x a, ((T s).bob x).effect a * ((T s).bob x).effect a = ((T s).bob x).effect a) ∧
      (∀ s x a b, a ≠ b → (T s).prob x x a b = 0) ∧
      (∀ s x y a b, (T s).prob x y a b =
        (s.val.card : ℝ)⁻¹ *
          (Matrix.trace (((T s).alice x).effect a * ((T s).alice y).effect b)).re) ∧
      (∀ s : Cuts, extendCutMatrix s.val (partialTraceRight (pureState (T s).state)) =
        spectralCutDensity s) ∧
      (∀ s : Cuts, 0 ≤ spectralCutWeight d s) ∧
      (∑ s : Cuts, spectralCutWeight d s) = 1 ∧
      partialTraceRight (pureState S.state) =
        ∑ s : Cuts, spectralCutWeight d s • spectralCutDensity s ∧
      (∑ x, (ν x).toReal * ∑ s : Cuts, spectralCutWeight d s *
        ∑ a, let E := (M x).effect a - extendCutMatrix s.val (((T s).alice x).effect a)
             (Matrix.trace (E * E * spectralCutDensity s)).re) ≤
        9 * δ + 10 * Real.sqrt (2 * δ) := by
  intro S δ
  have hagree (x : X) : (∑ a, S.prob x x a a) = (M x).toMeasurement.schmidtAgreement d :=
    sum_prob_same_ofSchmidt d hd htrace M x
  obtain ⟨R, hR, hround⟩ :=
    Measurement.exists_projective_cutColumnError_average_le
      (fun x => (M x).toMeasurement) ν d hd htrace
  let T (s : Cuts) := ofSpectralCut s (fun x => R x s)
  refine ⟨T, ?_, ?_, ?_, ?_, fun s => partialTraceRight_pureState_ofSpectralCut s _,
    spectralCutWeight_nonneg d, sum_spectralCutWeight d hd htrace, ?_, ?_⟩
  · intro s x a
    simpa only [T, ofSpectralCut_alice_effect] using hR x s a
  · intro s x a
    simpa only [T, ofSpectralCut_bob_effect, transpose_mul] using
      congrArg Matrix.transpose (hR x s a)
  · intro s x a b hab
    exact ofSpectralCut_prob_eq_zero s (fun x => R x s) (fun x => hR x s) x hab
  · intro s x y a b
    simpa only [T, ofSpectralCut_alice_effect] using
      ofSpectralCut_prob_eq_trace s (fun x => R x s) x y a b
  · dsimp only [S]
    rw [ofSchmidt_state, partialTraceRight_pureState_schmidtVector d hd,
      diagonal_eq_sum_spectralCutDensity d hd]
  · have herr (x : X) (s : Cuts) (a : A) :
        let E := (M x).effect a - extendCutMatrix s.val ((R x s).effect a)
        (Matrix.trace (E * E * spectralCutDensity s)).re =
          Measurement.cutColumnError s.val ((M x).effect a) ((R x s).effect a) /
            (s.val.card : ℝ) := by
      have ha := ((M x).posSemidef a).isHermitian.isSelfAdjoint
      have hb := (Matrix.nonneg_iff_posSemidef.mp ((R x s).nonneg a)).isHermitian.isSelfAdjoint
      rw [cutColumnError_div_card_eq, star_sub, star_extendCutMatrix, ha.star_eq, hb.star_eq]
    simp_rw [T, ofSpectralCut_alice_effect, herr, ← sum_div]
    have hweight (s : Cuts) (c : ℝ) :
        spectralCutWeight d s * (c / (s.val.card : ℝ)) = diagonalCutWidth d s * c := by
      unfold spectralCutWeight
      rw [div_eq_mul_inv]
      calc
        _ = (diagonalCutWidth d s * s.val.card * (s.val.card : ℝ)⁻¹) * c := by ring
        _ = _ := by rw [mul_card_inv_cancel]
    simp_rw [hweight]
    dsimp only [δ]
    simp_rw [hagree]
    simpa only [POVM.toMeasurement_effect] using hround

end Cslib.PCP.QuantumStrategy
