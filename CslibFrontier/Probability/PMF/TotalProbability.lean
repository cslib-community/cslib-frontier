/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.SupportTsum
import CslibFrontier.Tactic.ENNRealToReal

/-!
# Total probability with two cases

Split the outcomes of a random first stage `p` by a set `pre`. If the continuation `kernel`
reaches `event` with probability at most `a₁` from the supported outcomes in `pre` and at most
`a₂` from the other supported outcomes, then `p.bind kernel` reaches `event` with probability at
most `P(pre) * a₁ + P(preᶜ) * a₂`. This refines `toOuterMeasure_bind_failure_le`, which bounds the
second case by `1` and drops the factor `P(pre)`. It is the step of an induction on a budget in
which an outcome outside `pre` does not end the run but uses more of the budget, as when a search
repeats a failed attempt.

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_bind_le_mul_add_mul`: the bound in `ℝ≥0∞`.
* `Cslib.Probability.PMF.toOuterMeasure_bind_toReal_le_mul_add_mul`: the bound in `ℝ`, for
  nonnegative `a₁` and `a₂`.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β : Type*}

/-- **Total probability with two cases.** If the continuation reaches `event` with probability at
most `a₁` after a supported outcome in `pre` and at most `a₂` after any other supported outcome,
then the bind reaches `event` with probability at most `P(pre) * a₁ + P(preᶜ) * a₂`. -/
theorem toOuterMeasure_bind_le_mul_add_mul (p : PMF α) (kernel : α → PMF β) (pre : Set α)
    (event : Set β) {a₁ a₂ : ℝ≥0∞}
    (hpre : ∀ a ∈ p.support, a ∈ pre → (kernel a).toOuterMeasure event ≤ a₁)
    (hnot : ∀ a ∈ p.support, a ∉ pre → (kernel a).toOuterMeasure event ≤ a₂) :
    (p.bind kernel).toOuterMeasure event ≤
      p.toOuterMeasure pre * a₁ + p.toOuterMeasure preᶜ * a₂ := by
  classical
  rw [PMF.toOuterMeasure_bind_apply, toOuterMeasure_eq_tsum_mul_indicator p pre,
    toOuterMeasure_eq_tsum_mul_indicator p preᶜ, ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_mul_right, ← tsum_add]
  simp only [mul_assoc, ← mul_add]
  refine tsum_mul_mono_support p fun a hs => ?_
  by_cases ha : a ∈ pre
  · simpa [Set.indicator_of_mem ha, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr ha)] using
      hpre a hs ha
  · simpa [Set.indicator_of_notMem ha, Set.indicator_of_mem (Set.mem_compl ha)] using hnot a hs ha

/-- **Total probability with two cases**, in `ℝ`: if the continuation reaches `event` with
probability at most `a₁ ≥ 0` after a supported outcome in `pre` and at most `a₂ ≥ 0` after any
other supported outcome, then the bind reaches `event` with probability at most
`P(pre) * a₁ + P(preᶜ) * a₂`. -/
theorem toOuterMeasure_bind_toReal_le_mul_add_mul (p : PMF α) (kernel : α → PMF β) (pre : Set α)
    (event : Set β) {a₁ a₂ : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂)
    (hpre : ∀ a ∈ p.support, a ∈ pre → ((kernel a).toOuterMeasure event).toReal ≤ a₁)
    (hnot : ∀ a ∈ p.support, a ∉ pre → ((kernel a).toOuterMeasure event).toReal ≤ a₂) :
    ((p.bind kernel).toOuterMeasure event).toReal ≤
      (p.toOuterMeasure pre).toReal * a₁ + (p.toOuterMeasure preᶜ).toReal * a₂ := by
  have hle := toOuterMeasure_bind_le_mul_add_mul p kernel pre event
    (fun a hs ha => (ENNReal.le_ofReal_iff_toReal_le (toOuterMeasure_ne_top _ _) h₁).mpr
      (hpre a hs ha))
    (fun a hs ha => (ENNReal.le_ofReal_iff_toReal_le (toOuterMeasure_ne_top _ _) h₂).mpr
      (hnot a hs ha))
  ennreal_to_real using hle

end Cslib.Probability.PMF
