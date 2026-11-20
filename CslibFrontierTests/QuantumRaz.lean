/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Foundations.Quantum.Bell
import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumConditioning
import CslibFrontier.Foundations.Quantum.DensityMatrix.QuantumRaz
import CslibFrontier.Probability.PMF.Coin
import CslibFrontier.Probability.PMF.Uniform

/-! The coordinate information bound for two correlated classical labels. -/

namespace CslibFrontierTests.QuantumRaz

open Cslib.Quantum Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Cslib.Probability.PMF (bind_map_prodMk_apply coin coin_apply_toReal conditionalSnd
  conditionalSnd_bind_pair map_fst_bind_pair mem_support_uniformOfFintype pi pi_apply
  uniformOfFintype uniformOfFintype_apply)

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

-- Both the reference question law and the reference density can depend on the
-- transcript. The source may assign zero mass to either transcript.
example (p : PMF (Bool × (Fin 1 → Bool))) (q : PMF Bool) (r : Bool → Fin 1 → PMF Bool) :
    let ρ (z : Bool × (Fin 1 → Bool)) := pureState (ket (z.2 0))
    (∑ t, (((p.map Prod.fst) t).toReal : WithTop ℝ) *
      mutualInformation (classicalQuantumMarginal (conditionalSnd p t)
        (fun y => ρ (t, y)) (fun y => y 0))) ≤
      relativeEntropy (classicalQuantumState p ρ)
        (classicalQuantumState (q.bind fun t => (pi (r t)).map (t, ·))
          (fun (t, _) => pureState (ket t))) := by
  dsimp only
  simpa only [Fin.sum_univ_one, Function.comp_def] using
    sum_weighted_coordinate_mutualInformation_le_relativeEntropy (fun _ : Fin 1 => Bool) p
      (fun z => isDensityMatrix_pureState (norm_ket (z.2 0))) q r
      (fun t => isDensityMatrix_pureState (norm_ket t))

private noncomputable def transcriptBitSource : PMF (Bool × (Fin 1 → Bool)) :=
  (uniformOfFintype Bool).bind fun t => uniformBitTuple.map (t, ·)

private noncomputable def transcriptBitReference (t : Bool) (_ : Fin 1) : PMF Bool :=
  if t then coin ⟨1 / 4, by constructor <;> norm_num⟩ else uniformOfFintype Bool

private theorem transcriptBitReference_support (t b : Bool) :
    b ∈ (transcriptBitReference t 0).support := by
  cases t
  · exact mem_support_uniformOfFintype b
  · rw [PMF.mem_support_iff]
    intro hzero
    have h := congrArg ENNReal.toReal hzero
    change (coin ⟨1 / 4, _⟩ b).toReal = (0 : ENNReal).toReal at h
    rw [coin_apply_toReal, ENNReal.toReal_zero] at h
    cases b <;> norm_num at h

/-- Both transcripts have positive source weight and encode a bit in orthogonal states.
The reference changes its question law with the transcript and has finite divergence. -/
example :
    let ρ (z : Bool × (Fin 1 → Bool)) := pureState (ket (z.2 0))
    let q := uniformOfFintype Bool
    let I := ∑ t, (((transcriptBitSource.map Prod.fst) t).toReal : WithTop ℝ) *
      mutualInformation (classicalQuantumMarginal (conditionalSnd transcriptBitSource t)
        (fun y => ρ (t, y)) (fun y => y 0))
    let D := relativeEntropy (classicalQuantumState transcriptBitSource ρ)
      (classicalQuantumState (q.bind fun t => (pi (transcriptBitReference t)).map (t, ·))
        (fun _ => maximallyMixedQubit))
    0 < I ∧ I ≤ D ∧ D < ⊤ := by
  dsimp only
  have hρ (z : Bool × (Fin 1 → Bool)) := isDensityMatrix_pureState (norm_ket (z.2 0))
  refine ⟨?_, ?_, ?_⟩
  · have hcond (t : Bool) : conditionalSnd transcriptBitSource t = uniformBitTuple :=
      conditionalSnd_bind_pair _ _ t (mem_support_uniformOfFintype t)
    rw [show transcriptBitSource.map Prod.fst = uniformOfFintype Bool from
      map_fst_bind_pair _ _, Fintype.sum_bool]
    simp only [hcond, uniformBitTuple_marginal, uniformQubit_information, uniformBool_weight]
    rw [← WithTop.coe_mul, ← WithTop.coe_add, WithTop.coe_pos]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · simpa only [Fin.sum_univ_one, Function.comp_def] using
      sum_weighted_coordinate_mutualInformation_le_relativeEntropy (fun _ : Fin 1 => Bool)
        transcriptBitSource hρ (uniformOfFintype Bool) transcriptBitReference
        (fun _ => maximallyMixedQubit_density)
  · refine (relativeEntropy_of_supportLE ?_).trans_lt (WithTop.coe_lt_top _)
    refine (supportLE_classicalQuantumState_iff _ _ hρ).mpr
      ⟨?_, fun z _ => supportLE_maximallyMixedQubit (pureState (ket (z.2 0)))⟩
    rintro ⟨t, z⟩ _
    rw [PMF.mem_support_iff, bind_map_prodMk_apply, pi_apply, Fin.prod_univ_one]
    exact mul_ne_zero (mem_support_uniformOfFintype t) (transcriptBitReference_support t (z 0))

-- A pure classical label gives one supported block. The other block contributes
-- zero regardless of the fallback density.
example :
    ∃ ρ : Bool → Matrix Bool Bool ℂ, (∀ b, IsDensityMatrix (ρ b)) ∧
      classicalQuantumState (PMF.pure false) ρ =
        blockDiagonal (fun b => if b then 0 else pureState (ket false)) := by
  let A (b : Bool) := if b then 0 else pureState (ket false)
  have hρ := isDensityMatrix_pureState (norm_ket false)
  have hA (b : Bool) : (A b).PosSemidef := by
    cases b
    · exact hρ.posSemidef
    · exact PosSemidef.zero
  have ht (b : Bool) : (A b).trace.re = ((PMF.pure false) b).toReal := by
    cases b <;> simp [A, hρ.trace_eq_one, PMF.pure_apply]
  obtain ⟨ρ, hρ', _, he⟩ := exists_classicalQuantumState_eq_blockDiagonal
    (PMF.pure false) A hA ht (isDensityMatrix_pureState (norm_ket true))
  exact ⟨ρ, hρ', he⟩

end CslibFrontierTests.QuantumRaz
