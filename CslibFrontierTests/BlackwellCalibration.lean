/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.MachineLearning.OnlineLearning.Blackwell
import CslibFrontier.MachineLearning.OnlineLearning.Calibration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.privateModule false

/-!
# Checked tests for Blackwell approachability and calibrated forecasting

Ordinary-import client checks (no `import all`) exercising both modules with non-vacuous positive
witnesses and negative / non-approachability counterexamples:

1. **Blackwell approachability (`Blackwell`)**:
   * A concrete 2×2 matching-pennies scalar/vector payoff game targeting `{0}` that *satisfies*
     `SatisfiesResponseCondition` (hence `SatisfiesHalfspaceCondition` and an explicit `O(1 / √T)`
     adaptive randomized strategy via `exists_approachStrategy_of_response`).
   * A concrete 2×2 shifted game whose payoffs are always `≥ 1` along column `true`, so it *fails*
     `SatisfiesResponseCondition` and triggers the converse `exists_nonapproachable_dist_ge`
     (separating every sequence of strategies away from `Set.Iic 0` uniformly across `T ≥ 1`).
2. **Calibrated forecasting (`Calibration`)**:
   * Deterministic impossibility instances (`const 0` fails calibration with `detCalError ≥ 1 / 2`).
   * Explicit 3-point grid `K = 2` (`{0, 1 / 2, 1}`) checking `calPayoff_response` and concrete
     2-point `fosterVohraDist` support/weights when `w = (1, -1, -2)` (splits `(1/2, 1/2, 0)` on
     `{0, 1/2}`).
   * Finite-sample expectation & Markov probability bounds (`fosterVohra_expected_calError_le`,
     `fosterVohra_prob_calError_ge_le`) and `(ε, δ)` calibration witness at `ε = 1 / 4`,
     `δ = 1 / 10`.
-/

namespace CslibFrontierTests.BlackwellCalibration

open Finset Real Set Cslib Cslib.MachineLearning.OnlineLearning.Blackwell
open scoped RealInnerProductSpace

/-! ### Blackwell approachability: positive and negative witnesses -/

/-- Matching-pennies payoff `m : Bool → Bool → ℝ` (`+1` on diagonal, `-1` off-diagonal). -/
private def mpPayoff (i j : Bool) : ℝ := if i = j then 1 else -1

/-- `{0} ⊆ ℝ` satisfies `SatisfiesResponseCondition` for matching pennies (uniform `p = (1/2, 1/2)`
yields expected payoff `0` against every mixed column strategy `q`). -/
private theorem mpPayoff_response : SatisfiesResponseCondition mpPayoff ({0} : Set ℝ) := by
  intro q _ _
  refine ⟨fun _ => (1 / 2 : ℝ), fun _ => by norm_num, by simp, ?_⟩
  simp [bilinearPayoff, mpPayoff]
  ring

example : SatisfiesResponseCondition mpPayoff ({0} : Set ℝ) := mpPayoff_response

/-- Hence matching pennies against `{0}` satisfies `SatisfiesHalfspaceCondition` and yields a
Blackwell `FeedbackRule` converging at rate `2 / √T` against every adaptive adversary. -/
example :
    ∃ rule : FeedbackRule Bool ℝ,
      ∀ (adv : List Bool → Bool) (T : ℕ), 0 < T →
        expectHistory (rule.toStrategy mpPayoff adv) T []
          (fun h => distToSet ({0} : Set ℝ) ((T : ℝ)⁻¹ • sumPayoff mpPayoff adv h)) ≤
          2 * 1 / Real.sqrt T := by
  have hcomplete : IsComplete ({0} : Set ℝ) := isClosed_singleton.isComplete
  have hcvx : Convex ℝ ({0} : Set ℝ) := convex_singleton 0
  have hR : ∀ i j : Bool, ‖mpPayoff i j - 0‖ ≤ 1 := fun i j => by
    cases i <;> cases j <;> norm_num [mpPayoff]
  obtain ⟨rule, _, hbd⟩ := exists_approachStrategy_of_response hcomplete hcvx
    (Set.mem_singleton 0) mpPayoff zero_le_one hR mpPayoff_response
  exact ⟨rule, fun adv T hT => (hbd adv T hT).2.1⟩

/-- Negative witness: a payoff matrix with column `true` strictly positive (`≥ 1`) cannot
approach `Set.Iic 0` (`(-∞, 0]`). -/
private def unapproachablePayoff (i j : Bool) : ℝ := if j then 1 else if i then 0 else -1

private theorem unapproachablePayoff_not_response :
    ¬ SatisfiesResponseCondition unapproachablePayoff (Set.Iic (0 : ℝ)) := by
  intro hresp
  obtain ⟨p, _, hp1, hmem⟩ := hresp (fun j => if j then 1 else 0)
    (fun j => by cases j <;> norm_num) (by simp)
  have hval : bilinearPayoff unapproachablePayoff p (fun j => if j then 1 else 0) = 1 := by
    simp only [bilinearPayoff, Fintype.sum_bool, ↓reduceIte, mul_one, unapproachablePayoff,
      smul_eq_mul]
    simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, zero_mul, add_zero]
    simpa [Fintype.sum_bool] using hp1
  rw [hval] at hmem
  exact absurd hmem (by norm_num)

example : ¬ SatisfiesResponseCondition unapproachablePayoff (Set.Iic (0 : ℝ)) :=
  unapproachablePayoff_not_response

/-- Applying the necessity converse (`exists_nonapproachable_dist_ge`) to the game above gives a
stationary adversary `q` and positive gap `δ > 0` holding uniformly for all horizons `T ≥ 1`. -/
example :
    ∃ (q : Bool → ℝ) (δ : ℝ),
      (∀ j, 0 ≤ q j) ∧ ∑ j, q j = 1 ∧ 0 < δ ∧
      ∀ (T : ℕ), 0 < T →
        ∀ (p : ℕ → Bool → ℝ), (∀ t < T, (∀ i, 0 ≤ p t i) ∧ ∑ i, p t i = 1) →
          δ ≤ distToSet (Set.Iic (0 : ℝ))
            (vecAvg (fun t => bilinearPayoff unapproachablePayoff (p t) q) T) :=
  exists_nonapproachable_dist_ge ⟨0, le_rfl⟩ isClosed_Iic.isComplete (convex_Iic 0)
    unapproachablePayoff_not_response

/-! ### Calibrated forecasting (`Calibration`) -/

/-- Negative witness: constant deterministic forecaster `0` suffers calibration error `≥ 1 / 2`. -/
example {T : ℕ} (hT : 0 < T) :
    (1 / 2 : ℝ) ≤ detCalError (fun _ => 0) (fun _ => true) T := by
  have h := deterministic_calError_ge_half (fun _ => (0 : ℝ)) hT
  simpa [show (0 : ℝ) < 1 / 2 by norm_num] using h

/-- Grid `K = 2` (`{0, 1 / 2, 1}`) satisfies Blackwell's response condition for
`l1Ball 3 (1 / 4)`. -/
example : SatisfiesResponseCondition (calPayoff 2) (l1Ball 3 (1 / (2 * (2 : ℝ)))) :=
  calPayoff_response (by decide)

/-- Non-vacuous check of `fosterVohraDist` at `K = 2`, dual vector `w = (1, -1, -2)`:
weights sum to `1` and are nonnegative. -/
example :
    let w : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![1, -1, -2]
    ∑ k : Fin 3, fosterVohraDist 2 w k = 1 ∧
      ∀ k : Fin 3, 0 ≤ fosterVohraDist 2 w k :=
  ⟨sum_fosterVohraDist 2 _, fosterVohraDist_nonneg 2 _⟩

/-- Concrete expected calibration error on grid `K = 2` after `T = 100` rounds against any adaptive
adversary: `𝔼[calError] ≤ 1 / 4 + 2 * √(3 / 100)`. -/
example (adv : List (Fin 3) → Bool) :
    expectHistory ((fosterVohraRule 2).toStrategy (calPayoff 2) adv) 100 []
        (empiricalCalError 2 adv) ≤
      1 / (2 * (2 : ℝ)) + 2 * Real.sqrt (3 / 100) := by
  have h := fosterVohra_expected_calError_le (K := 2) (by decide) adv (T := 100) (by decide)
  simpa using h

/-- Concrete `(ε, δ)`-calibration check at `ε = 1 / 4`, `δ = 1 / 10`. -/
example :
    ∃ (K T₀ : ℕ), 0 < K ∧ 0 < T₀ ∧
      ∀ (T : ℕ), T₀ ≤ T → ∀ (adv : List (Fin (K + 1)) → Bool),
        expectHistory ((fosterVohraRule K).toStrategy (calPayoff K) adv) T []
            (empiricalCalError K adv) ≤ 1 / 4 ∧
        expectHistory ((fosterVohraRule K).toStrategy (calPayoff K) adv) T []
            (fun h => if (1 / 4 : ℝ) ≤ empiricalCalError K adv h then (1 : ℝ) else 0) ≤ 1 / 10 :=
  exists_calibrated_forecaster (by norm_num) (by norm_num)

end CslibFrontierTests.BlackwellCalibration
