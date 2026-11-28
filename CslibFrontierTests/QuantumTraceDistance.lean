/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.Quantum.Bell
public import CslibFrontier.Foundations.Quantum.DensityMatrix.TraceDistanceDataProcessing
public import CslibFrontier.Foundations.Quantum.Pauli
public import CslibFrontierTests.QuantumState

/-!
# Tests for trace-distance data processing and Holevo–Helstrom discrimination

Concrete witnesses and boundary checks for
`CslibFrontier.Foundations.Quantum.DensityMatrix.TraceDistanceDataProcessing`:

1. Orthogonal pure states `|0⟩, |1⟩` have trace distance `1` and perfect Holevo–Helstrom
   discrimination probability `1`.
2. Non-orthogonal pure states `|0⟩, |+⟩` have exact trace distance `√2 / 2`; `helstromPOVM`
   attains optimal equal-prior success `(2 + √2) / 4`, strictly beating computational-basis
   measurement (`3 / 4`).
3. Computational-basis dephasing `{|b⟩⟨b|}` strictly contracts trace distance on `|+⟩, |-⟩` from
   `1` to `0`, witnessing strict inequality in `traceDistance_kraus_le`.
4. Rectangular isometric embedding `ℂ^Bool → ℂ^(Bool × Fin 3)` preserves `traceDistance`
   (`traceDistance_densityConj`), while discarding a qubit strictly contracts `traceDistance`
   between an EPR pair `|Φ⁺⟩⟨Φ⁺|` and the classically correlated mixture
   `½ (|00⟩⟨00| + |11⟩⟨11|)` (`traceDistance_partialTraceRight_le`).
5. On unnormalized positive matrices `ρ = I_2` (`Tr ρ = 2`) and `σ = 0` (`Tr σ = 0`),
   `traceDistance ρ σ = 1` while `helstromPOVM` has outcome-`false` weight difference `2 ≠ 1`,
   showing the equal-trace hypothesis `ρ.trace.re = σ.trace.re` in
   `helstromPOVM_densityProb_sub_false` is necessary.
-/

public section

namespace CslibFrontierTests.QuantumTraceDistance

open Cslib.Quantum CslibFrontierTests.QuantumProtocols Matrix Finset
open scoped MatrixOrder ComplexOrder

/-! ### Orthogonal pure states `|0⟩` and `|1⟩` -/

theorem traceDistance_ket_false_ket_true :
    traceDistance (pureState (ket false)) (pureState (ket true)) = 1 := by
  have hub := traceDistance_le_one
    (isDensityMatrix_pureState (norm_ket false)) (isDensityMatrix_pureState (norm_ket true))
  have hlb := POVM.basis.half_sum_abs_densityProb_sub_le_traceDistance
    (pureState (ket false)) (pureState (ket true))
  rw [Fintype.sum_bool, POVM.densityProb_basis, POVM.densityProb_basis,
    POVM.densityProb_basis, POVM.densityProb_basis] at hlb
  simp only [pureState_apply, ket_apply, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false,
    star_one, mul_one, star_zero, mul_zero, Complex.one_re, Complex.zero_re] at hlb
  norm_num at hlb
  linarith

-- Orthogonal states are perfectly distinguishable under equal priors.
example :
    let hρ := isDensityMatrix_pureState (norm_ket false)
    let hσ := isDensityMatrix_pureState (norm_ket true)
    let hΔ := hρ.posSemidef.isHermitian.sub hσ.posSemidef.isHermitian
    (1 / 2 : ℝ) * ((helstromPOVM hΔ).densityProb (pureState (ket false)) false +
        (helstromPOVM hΔ).densityProb (pureState (ket true)) true) = 1 := by
  intro hρ hσ hΔ
  rw [helstromPOVM_success hρ hσ, traceDistance_ket_false_ket_true]
  norm_num

/-! ### Non-orthogonal states `|0⟩` and `|+⟩`: exact `√2 / 2` distance and Helstrom advantage -/

private theorem pureState_plus_apply (b c : Bool) :
    pureState plus b c = (2⁻¹ : ℂ) := by
  rw [pureState_apply, plus_apply, plus_apply, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem traceDistance_ket_false_plus :
    traceDistance (pureState (ket false)) (pureState plus) = Real.sqrt 2 / 2 := by
  let Δ : Matrix Bool Bool ℂ := pureState (ket false) - pureState plus
  have hΔ_entry (b c : Bool) : Δ b c = (if b = false ∧ c = false then 1 else 0) - (2⁻¹ : ℂ) := by
    dsimp only [Δ]
    rw [Matrix.sub_apply, pureState_plus_apply, pureState_apply, ket_apply]
    cases b <;> cases c <;> simp
  have hgram : Δᴴ * Δ = (2⁻¹ : ℂ) • (1 : Matrix Bool Bool ℂ) := by
    ext b c
    rw [Matrix.mul_apply, Fintype.sum_bool]
    simp only [conjTranspose_apply, hΔ_entry]
    cases b <;> cases c <;> norm_num
  let S : Matrix Bool Bool ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ)
  have hS_psd : S.PosSemidef := by
    dsimp only [S]
    rw [Complex.coe_smul]
    exact PosSemidef.one.smul (inv_nonneg.mpr (Real.sqrt_nonneg 2))
  have hsqrt : CFC.sqrt (Δᴴ * Δ) = S := by
    rw [hgram]
    apply CFC.sqrt_unique _ hS_psd.nonneg
    dsimp only [S]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  unfold traceDistance Matrix.traceNorm
  change (CFC.sqrt (Δᴴ * Δ)).trace.re / 2 = Real.sqrt 2 / 2
  rw [hsqrt]
  dsimp only [S]
  rw [trace_smul, trace_one, Fintype.card_bool, smul_eq_mul]
  simp only [Nat.cast_ofNat, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  have h2 : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
    have hne : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    calc
      (Real.sqrt 2)⁻¹ * 2 = (Real.sqrt 2)⁻¹ * (Real.sqrt 2 * Real.sqrt 2) := by
        rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      _ = Real.sqrt 2 := inv_mul_cancel_left₀ hne (Real.sqrt 2)
  rw [h2]

-- Computational-basis readout succeeds on `|0⟩` vs `|+⟩` with probability `3 / 4`, strictly
-- below the Holevo–Helstrom optimum `(2 + √2) / 4`.
theorem basis_success_ket_false_plus :
    (1 / 2 : ℝ) * (POVM.basis.densityProb (pureState (ket false)) false +
      POVM.basis.densityProb (pureState plus) true) = 3 / 4 := by
  rw [POVM.densityProb_basis, POVM.densityProb_basis, pureState_plus_apply]
  simp only [pureState_apply, ket_apply, ↓reduceIte, star_one, mul_one, Complex.one_re]
  norm_num

example :
    let hρ := isDensityMatrix_pureState (norm_ket false)
    let hσ := isDensityMatrix_pureState norm_plus
    let hΔ := hρ.posSemidef.isHermitian.sub hσ.posSemidef.isHermitian
    (1 / 2 : ℝ) * (POVM.basis.densityProb (pureState (ket false)) false +
        POVM.basis.densityProb (pureState plus) true) <
      (1 / 2 : ℝ) * ((helstromPOVM hΔ).densityProb (pureState (ket false)) false +
        (helstromPOVM hΔ).densityProb (pureState plus) true) := by
  intro hρ hσ hΔ
  rw [basis_success_ket_false_plus, helstromPOVM_success hρ hσ, traceDistance_ket_false_plus]
  have hgt : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-! ### Strict contraction under computational-basis dephasing (`traceDistance_kraus_le`) -/

/-- The state `|-⟩ = H|1⟩ = (|0⟩ - |1⟩)/√2`. -/
noncomputable def minus : EuclideanSpace ℂ Bool :=
  unitaryEquiv ⟨Gate.hadamardMatrix, Gate.hadamardMatrix_mem_unitaryGroup⟩ (ket true)

theorem minus_apply (b : Bool) :
    minus.ofLp b = if b then -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  rw [minus, unitaryEquiv_apply, Gate.hadamardMatrix_mulVec]
  cases b <;> simp

/-- Computational-basis projection Kraus operators `K_b = |b⟩⟨b|`. -/
def dephaseKraus (b : Bool) : Matrix Bool Bool ℂ :=
  Matrix.single b b 1

theorem sum_dephaseKraus_conjTranspose_mul :
    ∑ b : Bool, (dephaseKraus b)ᴴ * dephaseKraus b = 1 := by
  ext i j
  rw [Matrix.sum_apply, Fintype.sum_bool]
  cases i <;> cases j <;>
    simp [dephaseKraus, Matrix.mul_apply, Matrix.single_apply]

-- Dephasing collapses both `|+⟩⟨+|` and `|-⟩⟨-|` to the maximally mixed state `I / 2`, strictly
-- contracting their trace distance from `1` to `0`.
example :
    traceDistance
        (∑ b : Bool, dephaseKraus b * pureState plus * (dephaseKraus b)ᴴ)
        (∑ b : Bool, dephaseKraus b * pureState minus * (dephaseKraus b)ᴴ) = 0 ∧
      traceDistance (pureState plus) (pureState minus) = 1 := by
  have hdeph_diag (ρ : Matrix Bool Bool ℂ) (hdiag : ∀ b, ρ b b = (2⁻¹ : ℂ)) :
      (∑ b : Bool, dephaseKraus b * ρ * (dephaseKraus b)ᴴ) =
        (2⁻¹ : ℂ) • (1 : Matrix Bool Bool ℂ) := by
    ext i j
    rw [Matrix.sum_apply, Fintype.sum_bool]
    simp only [dephaseKraus, Matrix.mul_apply, Fintype.sum_bool, conjTranspose_apply,
      Matrix.single_apply]
    cases i <;> cases j <;> simp [hdiag]
  have hminus_diag (b : Bool) : pureState minus b b = (2⁻¹ : ℂ) := by
    rw [pureState_apply, minus_apply]
    cases b <;>
      simp [Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hH_plus : pureState plus =
      Gate.hadamardMatrix * pureState (ket false) * Gate.hadamardMatrixᴴ := by
    rw [← densityConj_apply, densityConj_pureState]
    congr 1
    ext b
    rw [plus_apply]
    cases b <;> simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Gate.hadamardMatrix_mulVec]
  have hH_minus : pureState minus =
      Gate.hadamardMatrix * pureState (ket true) * Gate.hadamardMatrixᴴ := by
    rw [← densityConj_apply, densityConj_pureState]
    rfl
  refine ⟨by
      rw [hdeph_diag _ (fun b => pureState_plus_apply b b), hdeph_diag _ hminus_diag,
        traceDistance_self],
    ?_⟩
  rw [hH_plus, hH_minus, traceDistance_conj_unitary Gate.hadamardMatrix_mem_unitaryGroup,
    traceDistance_ket_false_ket_true]

/-! ### Isometric invariance and strict contraction under partial trace -/

/-- Rectangular isometric embedding `b ↦ (b, 0)` of one qubit into a `2 × 3`-dimensional space. -/
def embedQubitToSix : Matrix (Bool × Fin 3) Bool ℂ :=
  fun bk c => if bk.1 = c ∧ bk.2 = 0 then 1 else 0

theorem embedQubitToSix_isometry : embedQubitToSixᴴ * embedQubitToSix = 1 := by
  ext b c
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  cases b <;> cases c <;>
    simp [embedQubitToSix, Fin.sum_univ_three]

example (ρ σ : Matrix Bool Bool ℂ) :
    traceDistance (densityConj embedQubitToSix ρ) (densityConj embedQubitToSix σ) =
      traceDistance ρ σ :=
  traceDistance_densityConj embedQubitToSix_isometry ρ σ

/-- The classically correlated two-qubit state `½ (|00⟩⟨00| + |11⟩⟨11|)`. -/
noncomputable def classicalCorrelated : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (2⁻¹ : ℂ) • (pureState (ket (false, false)) + pureState (ket (true, true)))

-- Discarding the second qubit maps both the EPR pair `|Φ⁺⟩⟨Φ⁺|` and `classicalCorrelated` to
-- `I / 2` (marginal trace distance `0`), while their joint trace distance is strictly positive.
example :
    traceDistance (partialTraceRight (pureState bell))
        (partialTraceRight classicalCorrelated) = 0 ∧
      0 < traceDistance (pureState bell) classicalCorrelated := by
  have hbell_pt : partialTraceRight (pureState bell) = (2⁻¹ : ℂ) • (1 : Matrix Bool Bool ℂ) := by
    rw [bell_eq_maxEntangled, partialTraceRight_pureState_maxEntangled, Fintype.card_bool,
      Nat.cast_ofNat]
  have hcc_pt : partialTraceRight classicalCorrelated = (2⁻¹ : ℂ) • (1 : Matrix Bool Bool ℂ) := by
    ext i j
    cases i <;> cases j <;>
      simp [classicalCorrelated, partialTraceRight_apply, pureState_apply, ket_apply]
  refine ⟨by rw [hbell_pt, hcc_pt, traceDistance_self], ?_⟩
  have hne : pureState bell ≠ classicalCorrelated := by
    intro h
    have hentry := congrFun (congrFun h (false, false)) (true, true)
    simp only [classicalCorrelated, pureState_apply, bell_apply, ket_apply, ↓reduceIte,
      Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false, and_self, star_zero, mul_zero,
      zero_mul, add_zero, smul_zero, Matrix.smul_apply, Matrix.add_apply] at hentry
    have hinv_ne : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by
      rw [ Ne, Complex.ofReal_eq_zero, inv_eq_zero]
      exact Real.sqrt_ne_zero'.mpr (by norm_num)
    rcases mul_eq_zero.mp hentry with h1 | h2
    · exact hinv_ne h1
    · exact hinv_ne (star_eq_zero.mp h2)
  exact lt_of_le_of_ne (traceDistance_nonneg _ _)
    (Ne.symm ((traceDistance_eq_zero_iff _ _).not.mpr hne))

/-! ### Boundary check: necessity of equal trace in `helstromPOVM_densityProb_sub_false` -/

-- For unequal-trace positive matrices `ρ = I_2` (`Tr ρ = 2`) and `σ = 0` (`Tr σ = 0`),
-- `traceDistance ρ σ = 1` whereas `(helstromPOVM hΔ).densityProb ρ false -
-- (helstromPOVM hΔ).densityProb σ false = 2 ≠ 1`, confirming `htr : ρ.trace.re = σ.trace.re`
-- cannot be dropped.
example :
    let ρ : Matrix Bool Bool ℂ := 1
    let σ : Matrix Bool Bool ℂ := 0
    let hΔ : (ρ - σ).IsHermitian :=
      PosSemidef.one.isHermitian.sub PosSemidef.zero.isHermitian
    traceDistance ρ σ = 1 ∧
      (helstromPOVM hΔ).densityProb ρ false - (helstromPOVM hΔ).densityProb σ false = 2 := by
  intro ρ σ hΔ
  have hnorm : (ρ - σ).traceNorm = 2 := by
    dsimp only [ρ, σ]
    rw [sub_zero]
    unfold Matrix.traceNorm
    rw [conjTranspose_one, Matrix.one_mul, CFC.sqrt_one, trace_one, Fintype.card_bool]
    norm_num
  have htd : traceDistance ρ σ = 1 := by
    unfold traceDistance
    rw [hnorm]
    norm_num
  have heig (b : Bool) : 0 ≤ hΔ.eigenvalues b := by
    have hpsd : (ρ - σ).PosSemidef := by
      dsimp only [ρ, σ]
      rw [sub_zero]
      exact PosSemidef.one
    exact hpsd.eigenvalues_nonneg b
  have hobs : helstromObservable hΔ = 1 := by
    unfold helstromObservable
    have hdiag :
        (diagonal fun b : Bool => if 0 ≤ hΔ.eigenvalues b then (1 : ℂ) else -1) = 1 := by
      rw [← diagonal_one]
      congr 1
      funext b
      simp [heig b]
    rw [hdiag, map_one]
  refine ⟨htd, ?_⟩
  simp only [POVM.densityProb, helstromPOVM_effect, Bool.cond_false, hobs, ρ, σ, Matrix.mul_one,
    Matrix.mul_zero, trace_zero, Complex.zero_re, sub_zero, trace_smul, trace_add, trace_one,
    Fintype.card_bool, smul_eq_mul]
  norm_num

end CslibFrontierTests.QuantumTraceDistance
