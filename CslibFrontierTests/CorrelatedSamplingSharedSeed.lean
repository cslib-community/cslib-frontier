/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Probability.CorrelatedSampling.SharedSeed
import CslibFrontier.Probability.PMF.Coin

/-! # Correlated sampling from a distribution-independent seed

* A party holding a point mass outputs it almost surely.
* Parties holding the same distribution never disagree, by the `2δ` bound with `δ = 0`.
* For coins of bias `1 / 2` and `1 / 4`, `δ = 1 / 4`, and the parties disagree with probability
  at most `1 / 2`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.CorrelatedSamplingSharedSeed

open Cslib.Probability.CorrelatedSampling MeasureTheory
open Cslib.Probability.PMF (coin coin_apply_toReal)
open scoped Cslib.Probability.PMF ENNReal

/-- A party holding the point mass on `true` outputs `true` with probability one. -/
example : (seed Bool).map (seedSample (PMF.pure true)) {true} = 1 := by
  rw [map_seedSample, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp

/-- Parties holding the same distribution disagree with probability `2 · 0`. -/
example (P : PMF Bool) : (seed Bool).real {ω | seedSample P ω ≠ seedSample P ω} ≤ 0 :=
  (seedSample_disagree_le P P).trans_eq (by rw [dist_self, mul_zero])

/-- Coins of bias `1 / 2` and `1 / 4` are at statistical distance `1 / 4`, so the parties holding
them disagree with probability at most `1 / 2`. -/
example : (seed Bool).real {ω | seedSample (coin ⟨1 / 2, by norm_num, by norm_num⟩) ω ≠
    seedSample (coin ⟨1 / 4, by norm_num, by norm_num⟩) ω} ≤ 1 / 2 := by
  have h : dist (coin ⟨1 / 2, by norm_num, by norm_num⟩)
      (coin ⟨1 / 4, by norm_num, by norm_num⟩) = 1 / 4 := by
    rw [Cslib.Probability.PMF.dist_eq, Fintype.sum_bool, coin_apply_toReal,
      coin_apply_toReal, coin_apply_toReal, coin_apply_toReal]
    norm_num [abs_of_nonneg, abs_of_nonpos]
  refine (seedSample_disagree_le _ _).trans_eq ?_
  rw [h]
  norm_num

end CslibFrontierTests.CorrelatedSamplingSharedSeed
