/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Tactic.ENNRealToReal

/-!
# Retained success across two probabilistic branches

A first branch may establish success; a conditional second branch may recover from its failure.
If each relevant branch hits with probability at least `1 / s` and the second retains every
first-branch success, the final hit probability is at least `2 / (s + 1)`. The continuation may
depend on the first outcome, so no independence or finite ambient type is assumed.

## Main results

* `two_branch_hit_prob_ge`: conditional recovery and retention give the two-branch recurrence.
* `one_sub_sq_one_sub_inv_ge`: its elementary extended-nonnegative arithmetic inequality.

## References

Generalized from Renfei Zhou's Karger–Stein success rule over `ProbComp`. Runtime and query
budgets are separate execution obligations.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

/-- Elementary recurrence `2 / (s + 1) ≤ 1 - (1 - 1 / s) ^ 2` in `ℝ≥0∞` for `1 ≤ s`, derived from
`(2 * s - 1) * (s + 1) = 2 * s ^ 2 + s - 1 ≥ 2 * s ^ 2`. -/
theorem one_sub_sq_one_sub_inv_ge {s : ℕ} (hs : 1 ≤ s) :
    (2 : ℝ≥0∞) / ((s + 1 : ℕ) : ℝ≥0∞) ≤ 1 - (1 - (1 : ℝ≥0∞) / (s : ℝ≥0∞)) ^ 2 := by
  -- `ennreal_to_real` splits the two truncated subtractions with `h₁` and `h₂`.
  have h₁ : (1 : ℝ≥0∞) / s ≤ 1 := by
    rw [ENNReal.div_le_iff (by positivity) (by finiteness), one_mul]
    exact_mod_cast hs
  have h₂ : (1 - (1 : ℝ≥0∞) / s) ^ 2 ≤ 1 := pow_le_one₀ zero_le tsub_le_self
  ennreal_to_real
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  rw [div_le_iff₀ (by positivity)]
  push_cast
  field_simp
  nlinarith

/-- If the first branch hits with probability at least `1 / s`, its hits are retained, and
conditional recovery has the same lower bound on every supported miss, the two-stage result
hits with probability at least `2 / (s + 1)`. -/
theorem two_branch_hit_prob_ge {α β γ : Type*} (m₁ : PMF α) (m₂ : α → PMF β)
    (f : α → β → γ) (hit₁ : Set α) (hit : Set γ) {s : ℕ} (hs : 1 ≤ s)
    (hb₁ : (1 : ℝ≥0∞) / (s : ℝ≥0∞) ≤ m₁.toOuterMeasure hit₁)
    (hprop₁ : ∀ a ∈ m₁.support, a ∈ hit₁ → ∀ b ∈ (m₂ a).support, f a b ∈ hit)
    (hb₂ : ∀ a ∈ m₁.support, a ∉ hit₁ →
      (1 : ℝ≥0∞) / (s : ℝ≥0∞) ≤ ((m₂ a).map (f a)).toOuterMeasure hit) :
    (2 : ℝ≥0∞) / ((s + 1 : ℕ) : ℝ≥0∞) ≤
      (m₁.bind fun a => (m₂ a).map (f a)).toOuterMeasure hit := by
  let p := m₁.bind fun a => (m₂ a).map (f a)
  have hcompl_le : p.toOuterMeasure hitᶜ ≤ (1 - (1 : ℝ≥0∞) / (s : ℝ≥0∞)) ^ 2 := by
    dsimp only [p]
    rw [sq]
    refine toOuterMeasure_bind_le_mul_ennreal m₁ (fun a => (m₂ a).map (f a))
      hit₁ᶜ hitᶜ (toOuterMeasure_compl_le_one_sub m₁ hit₁ hb₁) ?_ ?_
    · intro a ha ha_miss
      exact toOuterMeasure_compl_le_one_sub _ hit (hb₂ a ha ha_miss)
    · intro a ha ha_not_miss
      have ha_hit : a ∈ hit₁ := not_not.mp ha_not_miss
      rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
      refine tsum_eq_zero_iff.mpr fun b => ?_
      by_cases hb : b ∈ (m₂ a).support
      · have hmem : f a b ∈ hit := hprop₁ a ha ha_hit b hb
        have hnot : b ∉ f a ⁻¹' hitᶜ := fun hc => hc hmem
        exact Set.indicator_of_notMem hnot _
      · have hp0 : m₂ a b = 0 := by simpa only [PMF.mem_support_iff, not_not] using hb
        simp [hp0]
  have hsum := toOuterMeasure_add_compl_ennreal p hit
  have hhit_ge : 1 - (1 - (1 : ℝ≥0∞) / (s : ℝ≥0∞)) ^ 2 ≤ p.toOuterMeasure hit := by
    refine tsub_le_iff_right.mpr ?_
    calc
      (1 : ℝ≥0∞) = p.toOuterMeasure hit + p.toOuterMeasure hitᶜ := hsum.symm
      _ ≤ p.toOuterMeasure hit + (1 - (1 : ℝ≥0∞) / (s : ℝ≥0∞)) ^ 2 := by gcongr
  exact (one_sub_sq_one_sub_inv_ge hs).trans hhit_ge

end Cslib.Probability.PMF
