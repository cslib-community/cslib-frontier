/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.Correctness
import CslibFrontierTests.Crypto.MLKEMFixture
import Mathlib.Tactic.FinCases

/-! Checked clients for the source-shaped ML-KEM K-PKE core-noise correctness bridge. -/

public section

namespace CslibFrontierTests.Crypto.MLKEMCorrectness

open Cslib Cslib.Crypto Cslib.Crypto.MLKEM Cslib.Crypto.Protocols Cslib.Probability
open CslibFrontierTests.Crypto.MLKEM

/-! The finite FIPS parameter records leave exactly the advertised radius after scalar
compression. These are arithmetic facts, not numerical decryption-failure bounds. -/

example : scalarCompressionAllowance mlkem512 = 104 ∧
    727 + scalarCompressionAllowance mlkem512 ≤ 831 ∧ 4 * 831 + 2 < mlkem512.q := by
  decide

example : scalarCompressionAllowance mlkem768 = 104 ∧
    727 + scalarCompressionAllowance mlkem768 ≤ 831 ∧ 4 * 831 + 2 < mlkem768.q := by
  decide

example : scalarCompressionAllowance mlkem1024 = 52 ∧
    779 + scalarCompressionAllowance mlkem1024 ≤ 831 ∧ 4 * 831 + 2 < mlkem1024.q := by
  decide

local instance : NeZero mlkem512.q := ⟨by decide⟩

/-- The intended standard-parameter API: any checked upper bound on the exact event gives the
matching K-PKE `DeltaCorrect` bound. -/
example {δ : ℝ} (hδ : coreNoiseFailureProbability mlkem512 727 ≤ δ) :
    (toExplicitCoinPKE mlkem512).DeltaCorrect δ :=
  deltaCorrect_of_coreNoiseFailureProbability_le mlkem512 (T := 727) (B := 831)
    (by decide) (by decide) hδ

/-! The following positive and negative witnesses are supported by the actual experiment. With
zero matrix, secrets, and vector errors, the core noise is `e₂`; for `η₂ = 1`, both `[1, 0]`
and `[0, 0]` are supported CBD outputs. At threshold zero they give `true` and `false`. -/

def zeroA : Matrix (Fin toy.k) (Fin toy.k) (Fin toy.n → ZMod toy.q) := 0

def zeroVec : Fin toy.k → Fin toy.n → ZMod toy.q := 0

def oneCoreNoiseE₂ : Fin toy.n → ZMod toy.q := ![1, 0]

def zeroCoreNoiseE₂ : Fin toy.n → ZMod toy.q := 0

private theorem zeroPoly_mem_samplePolyCBD (η : ℕ) :
    (0 : Fin toy.n → ZMod toy.q) ∈
      (ProbComp.eval (samplePolyCBD toy.n toy.q η)).support := by
  simp only [samplePolyCBD, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  refine ⟨(0 : Fin toy.n → ℤ), ?_, ?_⟩
  · rw [ProbComp.mem_support_replicateFin_iff]
    intro i
    exact (ProbComp.mem_support_sampleCenteredBinomial_iff η 0).2 (by simp)
  · funext i
    simp

private theorem oneCoreNoiseE₂_mem_samplePolyCBD :
    oneCoreNoiseE₂ ∈
      (ProbComp.eval (samplePolyCBD toy.n toy.q toy.η₂)).support := by
  simp only [samplePolyCBD, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  refine ⟨(![(1 : ℤ), 0]), ?_, ?_⟩
  · rw [ProbComp.mem_support_replicateFin_iff]
    intro i
    fin_cases i <;>
      apply (ProbComp.mem_support_sampleCenteredBinomial_iff toy.η₂ _).2 <;>
      decide
  · funext i
    fin_cases i <;> decide

private theorem zeroVec_mem_sampleVecCBD (η : ℕ) :
    zeroVec ∈ (ProbComp.eval (sampleVecCBD toy.k toy.n toy.q η)).support := by
  rw [sampleVecCBD, ProbComp.mem_support_replicateFin_iff]
  intro i
  exact zeroPoly_mem_samplePolyCBD η

private theorem coinsWith_mem_sampleCoins (e₂ : Fin toy.n → ZMod toy.q)
    (he₂ : e₂ ∈ (ProbComp.eval (samplePolyCBD toy.n toy.q toy.η₂)).support) :
    (zeroVec, zeroVec, e₂) ∈ (ProbComp.eval (sampleCoins toy)).support := by
  simp only [sampleCoins, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  exact ⟨zeroVec, zeroVec_mem_sampleVecCBD toy.η₁,
    zeroVec, zeroVec_mem_sampleVecCBD toy.η₂, e₂, he₂, rfl⟩

private theorem zeroA_mem_uniform :
    zeroA ∈ (ProbComp.eval
      (ProbComp.uniform (Matrix (Fin toy.k) (Fin toy.k) (Fin toy.n → ZMod toy.q)))).support := by
  rw [ProbComp.eval_uniform]
  exact PMF.mem_support_uniformOfFintype zeroA

private theorem decision_mem_coreNoiseFailureExperiment
    (e₂ : Fin toy.n → ZMod toy.q)
    (he₂ : e₂ ∈ (ProbComp.eval (samplePolyCBD toy.n toy.q toy.η₂)).support) :
    decide (coreNoiseFailure toy 0 zeroA zeroVec zeroVec zeroVec zeroVec e₂) ∈
      (ProbComp.eval (coreNoiseFailureExperiment toy 0)).support := by
  simp only [coreNoiseFailureExperiment, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  exact ⟨zeroA, zeroA_mem_uniform, zeroVec, zeroVec_mem_sampleVecCBD toy.η₁,
    zeroVec, zeroVec_mem_sampleVecCBD toy.η₁, (zeroVec, zeroVec, e₂),
    coinsWith_mem_sampleCoins e₂ he₂, rfl⟩

/-- A supported `e₂ = [1, 0]` draw makes the threshold-zero core-noise event occur. -/
example : true ∈ (ProbComp.eval (coreNoiseFailureExperiment toy 0)).support := by
  simpa only [show decide
      (coreNoiseFailure toy 0 zeroA zeroVec zeroVec zeroVec zeroVec oneCoreNoiseE₂) = true by
        decide] using
    decision_mem_coreNoiseFailureExperiment oneCoreNoiseE₂
      oneCoreNoiseE₂_mem_samplePolyCBD

/-- A supported all-zero draw makes the same threshold-zero core-noise event not occur. -/
example : false ∈ (ProbComp.eval (coreNoiseFailureExperiment toy 0)).support := by
  simpa only [show decide
      (coreNoiseFailure toy 0 zeroA zeroVec zeroVec zeroVec zeroVec zeroCoreNoiseE₂) = false by
        decide] using
    decision_mem_coreNoiseFailureExperiment zeroCoreNoiseE₂
      (zeroPoly_mem_samplePolyCBD toy.η₂)

end CslibFrontierTests.Crypto.MLKEMCorrectness
