/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Foundations.Data.Finset.Markov

/-!
# Markov's inequality for uniform draws

A bound on nonnegative scores gives a probability bound for the complement of a finite
set, when the scores outside that set are at least a positive threshold.

## Main results

* `Cslib.Probability.PMF.uniform_compl_finset_le_of_sum`: the probability bound.
-/

public section

namespace Cslib.Probability.PMF

open Finset

/-- Markov's inequality for the complement of a set under a uniform finite draw. -/
theorem uniform_compl_finset_le_of_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (good : Finset ι) (f : ι → ℝ) {threshold bound : ℝ} (ht : 0 < threshold)
    (hf : ∀ i, 0 ≤ f i) (hbad : ∀ i ∉ good, threshold ≤ f i)
    (hbound : ∑ i, f i ≤ bound) :
    ((uniformOfFintype ι).toOuterMeasure {i | i ∉ good}).toReal ≤
      bound / ((Fintype.card ι : ℝ) * threshold) := by
  classical
  have hm : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [toOuterMeasure_uniformOfFintype_toReal, le_div_iff₀ (mul_pos hm ht)]
  rw [← mul_assoc, div_mul_cancel₀ _ hm.ne']
  exact (card_filter_mul_le_sum univ (fun i => i ∉ good) f (fun i _ => hf i)
    (fun i _ => hbad i)).trans hbound

end Cslib.Probability.PMF
