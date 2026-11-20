/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Foundations.Quantum.Bell
import CslibFrontier.Foundations.Quantum.DensityMatrix.QuantumRaz
import CslibFrontier.Probability.PMF.Uniform

/-! The coordinate information bound for two correlated classical labels. -/

namespace CslibFrontierTests.QuantumRaz

open Cslib.Quantum Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Cslib.Probability.PMF (pi uniformOfFintype uniformOfFintype_apply)

-- The input law can correlate the labels arbitrarily. The conditional block is a
-- rank-one qubit state chosen by the first label.
example (p : PMF (Fin 2 → Bool)) (q : Fin 2 → PMF Bool) :
    let ρ (z : Fin 2 → Bool) := pureState (ket (z 0))
    mutualInformation (classicalQuantumMarginal p ρ (fun z => z 0)) +
      mutualInformation (classicalQuantumMarginal p ρ (fun z => z 1)) ≤
      relativeEntropy (classicalQuantumState p ρ)
        (classicalQuantumState (pi q) (fun _ => pureState (ket false))) := by
  dsimp only
  simpa only [Fin.sum_univ_two] using
    sum_mutualInformation_classicalQuantumMarginal_le_relativeEntropy (fun _ : Fin 2 => Bool) p
      (fun z => isDensityMatrix_pureState (norm_ket (z 0))) q
      (isDensityMatrix_pureState (norm_ket false))

private noncomputable def maximallyMixedQubit : Matrix Bool Bool ℂ :=
  (1 / 2 : ℝ) • 1

private theorem maximallyMixedQubit_density : IsDensityMatrix maximallyMixedQubit := by
  constructor
  · exact PosSemidef.one.smul (by norm_num)
  · rw [maximallyMixedQubit, trace_smul, trace_one, Fintype.card_bool]
    norm_num [Complex.real_smul]

private theorem supportLE_maximallyMixedQubit (A : Matrix Bool Bool ℂ) :
    SupportLE A maximallyMixedQubit := by
  intro x hx
  have hz : x = 0 := by
    simpa [maximallyMixedQubit, smul_mulVec, show (1 / 2 : ℝ) ≠ 0 by norm_num] using hx
  rw [hz, mulVec_zero]

private theorem uniformBool_weight (b : Bool) :
    ((uniformOfFintype Bool) b).toReal = 1 / 2 := by
  rw [uniformOfFintype_apply, Fintype.card_bool, ENNReal.toReal_inv]
  norm_num

private theorem uniformQubit_marginal :
    partialTraceRight (classicalQuantumState (uniformOfFintype Bool)
      (fun b => pureState (ket b))) = maximallyMixedQubit := by
  rw [partialTraceRight_classicalQuantumState, Fintype.sum_bool]
  simp only [uniformBool_weight]
  ext i j
  cases i <;> cases j <;>
    norm_num [maximallyMixedQubit, pureState_apply, ket_apply, Matrix.one_apply,
      Matrix.smul_apply, Complex.real_smul]

private theorem qubit_relativeEntropy_mixed (b : Bool) :
    relativeEntropyReal (pureState (ket b)) maximallyMixedQubit = Real.log 2 := by
  let P := pureState (ket b)
  have hP : IsIdempotentElem P := by
    change P * P = P
    ext i j
    cases i <;> cases j <;> cases b <;>
      simp [P, Matrix.mul_apply, pureState_apply, ket_apply]
  have hlogP : cfc Real.log P = 0 := by
    rw [← cfc_const_zero ℝ P]
    apply cfc_congr
    intro x hx
    rcases Set.mem_insert_iff.mp (hP.spectrum_subset ℝ hx) with h | h
    · simp [h]
    · simp [Set.mem_singleton_iff.mp h]
  have hlogM : cfc Real.log maximallyMixedQubit =
      (Real.log (1 / 2 : ℝ)) • (1 : Matrix Bool Bool ℂ) := by
    simp only [maximallyMixedQubit, ← Algebra.algebraMap_eq_smul_one, cfc_algebraMap]
  change relativeEntropyReal P maximallyMixedQubit = _
  rw [relativeEntropyReal, hlogP, hlogM, zero_sub, mul_neg, mul_smul_comm, Matrix.mul_one,
    trace_neg, trace_smul, (isDensityMatrix_pureState (norm_ket b)).trace_eq_one]
  simp only [Complex.real_smul, mul_one, Complex.neg_re, Complex.ofReal_re]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub, neg_neg]

private theorem uniformQubit_information :
    mutualInformation (classicalQuantumState (uniformOfFintype Bool)
      (fun b => pureState (ket b))) = (Real.log 2 : WithTop ℝ) := by
  rw [mutualInformation_classicalQuantumState_eq_coe_sum _
      (fun b => isDensityMatrix_pureState (norm_ket b)), uniformQubit_marginal]
  simp_rw [qubit_relativeEntropy_mixed]
  rw [← Finset.sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]

private noncomputable def uniformBitTuple : PMF (Fin 1 → Bool) :=
  pi fun _ => uniformOfFintype Bool

private theorem uniformBitTuple_marginal :
    classicalQuantumMarginal uniformBitTuple (fun z => pureState (ket (z 0))) (fun z => z 0) =
      classicalQuantumState (uniformOfFintype Bool) (fun b => pureState (ket b)) := by
  rw [classicalQuantumMarginal, classicalQuantumState]
  congr 1
  funext b
  rw [Finset.sum_filter]
  let e := Equiv.funUnique (Fin 1) Bool
  calc
    _ = ∑ a : Bool, if a = b then ((uniformOfFintype Bool) a).toReal •
          pureState (ket a) else 0 := by
      apply Fintype.sum_equiv e
      intro z
      have hmass : uniformBitTuple z = (uniformOfFintype Bool) (z 0) := by
        simp [uniformBitTuple, pi]
      simp [hmass, e, Equiv.funUnique, Equiv.piUnique]
    _ = _ := by simp

/-- A uniform bit encoded in orthogonal qubit states has positive information and finite
relative entropy to a full-rank product reference. -/
example :
    let ρ (z : Fin 1 → Bool) := pureState (ket (z 0))
    let I := mutualInformation (classicalQuantumMarginal uniformBitTuple ρ (fun z => z 0))
    let D := relativeEntropy (classicalQuantumState uniformBitTuple ρ)
      (classicalQuantumState uniformBitTuple (fun _ => maximallyMixedQubit))
    0 < I ∧ I ≤ D ∧ D < ⊤ := by
  dsimp only
  have hρ (z : Fin 1 → Bool) := isDensityMatrix_pureState (norm_ket (z 0))
  refine ⟨?_, ?_, ?_⟩
  · rw [uniformBitTuple_marginal, uniformQubit_information]
    exact WithTop.coe_pos.mpr (Real.log_pos (by norm_num))
  · simpa only [Fin.sum_univ_one, uniformBitTuple] using
      sum_mutualInformation_classicalQuantumMarginal_le_relativeEntropy (fun _ : Fin 1 => Bool)
        uniformBitTuple hρ (fun _ => uniformOfFintype Bool) maximallyMixedQubit_density
  · have hs := (supportLE_classicalQuantumState_iff uniformBitTuple uniformBitTuple hρ).mpr
        ⟨fun _ h => h, fun z _ => supportLE_maximallyMixedQubit (pureState (ket (z 0)))⟩
    rw [relativeEntropy_of_supportLE hs]
    exact WithTop.coe_lt_top _

end CslibFrontierTests.QuantumRaz
