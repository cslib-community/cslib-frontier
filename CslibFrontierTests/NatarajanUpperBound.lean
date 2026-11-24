/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.MachineLearning.PACLearning.NatarajanAgnostic
public import CslibFrontier.MachineLearning.PACLearning.NatarajanUpperBound
public import CslibFrontierTests.NatarajanDimension

/-!
# Checks for multiclass realizable and agnostic PAC sample-complexity upper bounds

Exercises `CslibFrontier.MachineLearning.PACLearning.NatarajanUpperBound` and
`CslibFrontier.MachineLearning.PACLearning.NatarajanAgnostic` as ordinary `module` clients:

* **Sample-size specializations:** `natarajanSampleSize` at `k = 1` and `k = 2`.
* **Countable infinite multiclass domains (`k = 3`):** realizable and agnostic PAC learnability,
  uniform convergence, ERM learnability, and explicit sample-complexity upper bounds for
  `pointIndicators ℕ 3` (`Ndim = 1`) and `orderedThresholds3` (`Ndim = 2`).
-/

public section

namespace CslibFrontierTests.NatarajanUpperBound

open MeasureTheory
open scoped NNReal
open Cslib.MachineLearning.PACLearning
open CslibFrontierTests.NatarajanDimension

/-- With `k = 1` label, `log 1 = 0` so `natarajanSampleSize` simplifies to `vcSampleSize`. -/
example (d : ℕ) (ε δ : ℝ) : natarajanSampleSize d 1 ε δ = vcSampleSize d ε δ := by
  simp [natarajanSampleSize, vcSampleSize]

/-- With `k = 2` labels, `natarajanSampleSize` equals `vcSampleSize` at rescaled confidence
`δ / 4 ^ d`. -/
example (d : ℕ) (ε : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    natarajanSampleSize d 2 ε δ = vcSampleSize d ε (δ / 4 ^ d) := by
  rw [natarajanSampleSize_eq_vcSampleSize d (by positivity) ε hδ]
  congr 2
  norm_num [pow_mul]

private noncomputable def quarter : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 4, by norm_num, by norm_num⟩

/-! ### `pointIndicators ℕ 3` (`k = 3`, `Ndim = 1`) on countable infinite domain `ℕ` -/

theorem hasFiniteNatarajanDim_pointIndicators_nat_three :
    HasFiniteNatarajanDim (pointIndicators ℕ 3) := by
  rw [HasFiniteNatarajanDim, natarajanDim_pointIndicators (b := (1 : Fin 3)) (by decide)]
  exact ENat.one_ne_top

example : IsPACLearnable (pointIndicators ℕ 3) (realizableDistributions (pointIndicators ℕ 3)) :=
  isPACLearnable_realizableDistributions_of_hasFiniteNatarajanDim
    hasFiniteNatarajanDim_pointIndicators_nat_three

example : HasUniformConvergence (pointIndicators ℕ 3) Set.univ :=
  hasUniformConvergence_univ_of_hasFiniteNatarajanDim
    hasFiniteNatarajanDim_pointIndicators_nat_three

example : IsERMLearnable (pointIndicators ℕ 3) Set.univ :=
  (hasUniformConvergence_univ_of_hasFiniteNatarajanDim
    hasFiniteNatarajanDim_pointIndicators_nat_three).isERMLearnable

example : IsPACLearnable (pointIndicators ℕ 3) Set.univ :=
  isPACLearnable_univ_of_hasFiniteNatarajanDim
    hasFiniteNatarajanDim_pointIndicators_nat_three

/-- Realizable sample-complexity upper bound for `pointIndicators ℕ 3` at `ε = δ = 1/4`, unfolding
`natarajanDim = 1` and `Fintype.card (Fin 3) = 3`. -/
example :
    sampleComplexity IsPACLearnerFor (pointIndicators ℕ 3) quarter quarter
        (realizableDistributions (pointIndicators ℕ 3)) ≤
      ⌈natarajanSampleSize 1 3 (1 / 4) (1 / 4)⌉₊ := by
  have hdim := untop_natarajanDim_eq hasFiniteNatarajanDim_pointIndicators_nat_three
    (natarajanDim_pointIndicators (b := (1 : Fin 3)) (by decide))
  simpa [hdim, Fintype.card_fin, quarter] using
    sampleComplexity_realizableDistributions_le_of_hasFiniteNatarajanDim
      hasFiniteNatarajanDim_pointIndicators_nat_three quarter quarter

/-- Agnostic sample-complexity upper bound for `pointIndicators ℕ 3` at `ε = δ = 1/4`, unfolding
`natarajanDim = 1` and `Fintype.card (Fin 3) = 3`. -/
example :
    sampleComplexity IsPACLearnerFor (pointIndicators ℕ 3) quarter quarter Set.univ ≤
      ⌈natarajanAgnosticSampleSize 1 3 (1 / 8) (1 / 4)⌉₊ := by
  have hdim := untop_natarajanDim_eq hasFiniteNatarajanDim_pointIndicators_nat_three
    (natarajanDim_pointIndicators (b := (1 : Fin 3)) (by decide))
  have hq : ((quarter.val : ℝ) / 2) = 1 / 8 := by norm_num [quarter]
  have hcard : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
  have h := sampleComplexity_univ_le_of_hasFiniteNatarajanDim
    hasFiniteNatarajanDim_pointIndicators_nat_three quarter quarter
  rw [hdim, hcard, hq] at h
  simpa [quarter] using h

/-! ### `orderedThresholds3` (`k = 3`, `Ndim = 2`) on `ℤ` -/

theorem hasFiniteNatarajanDim_orderedThresholds3 : HasFiniteNatarajanDim orderedThresholds3 := by
  rw [HasFiniteNatarajanDim, natarajanDim_orderedThresholds3]
  exact ENat.natCast_ne_top 2

example : IsPACLearnable orderedThresholds3 (realizableDistributions orderedThresholds3) :=
  isPACLearnable_realizableDistributions_of_hasFiniteNatarajanDim
    hasFiniteNatarajanDim_orderedThresholds3

example : IsPACLearnable orderedThresholds3 Set.univ :=
  isPACLearnable_univ_of_hasFiniteNatarajanDim hasFiniteNatarajanDim_orderedThresholds3

example :
    sampleComplexity IsPACLearnerFor orderedThresholds3 quarter quarter
        (realizableDistributions orderedThresholds3) ≤
      ⌈natarajanSampleSize 2 3 (1 / 4) (1 / 4)⌉₊ := by
  have hdim := untop_natarajanDim_eq hasFiniteNatarajanDim_orderedThresholds3
    natarajanDim_orderedThresholds3
  simpa [hdim, Fintype.card_fin, quarter] using
    sampleComplexity_realizableDistributions_le_of_hasFiniteNatarajanDim
      hasFiniteNatarajanDim_orderedThresholds3 quarter quarter

end CslibFrontierTests.NatarajanUpperBound
