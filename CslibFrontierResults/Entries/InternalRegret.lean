/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.MachineLearning.OnlineLearning.ConstantSum
import CslibFrontier.MachineLearning.OnlineLearning.InternalRegret

/-!
# Collected results: modification-rule regret, separations, and constant-sum games (NRTV Chapter 4)
-/

register_result "blum-mansour-constant-sum-average-loss" where
  title := "Average loss of an external-regret learner in a two-player constant-sum game"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.9",
      locator := "Chapter 4, §4.4.2, p. 89" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.average_loss_le_of_isMinimaxValue,
    Cslib.MachineLearning.OnlineLearning.Experts.constantSum_col_average_loss_le
  ]
  scope := "In any finite two-player constant-sum game s₁ + s₂ = c where s₁ has minimax value v₁ \
    (Cslib.Probability.IsMinimaxValue s₁ v₁, so player 2's transposed loss matrix swap s₂ has \
    minimax value v₂ = c - v₁), if player 1 (resp. player 2) plays for T > 0 rounds with external \
    regret at most R against its realized expected stage losses, its average expected loss against \
    any sequence of mixed opponent strategies is at most v₁ + R / T (resp. (c - v₁) + R / T)."

register_result "blum-mansour-swap-le-card-mul-internal" where
  title := "Swap regret is at most N times internal regret"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Exercise 4.1",
      locator := "Chapter 4, Exercises, p. 101" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.modRegret_univ_le_card_mul_internalRules
  ]
  scope := "For every finite action type ι of cardinality N, arbitrary round weights \
    p : ℕ → ι → ℝ, arbitrary real loss sequences ℓ : ℕ → ι → ℝ, and every horizon T : ℕ, \
    modRegret Set.univ p ℓ T ≤ N * modRegret (internalRules ι) p ℓ T."

register_result "blum-mansour-unbounded-swap-to-external-ratio" where
  title := "Unbounded ratio between swap regret and external regret for N = 3"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Exercise 4.2",
      locator := "Chapter 4, Exercises, p. 101" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.exists_modRegret_const_zero_and_univ_eq,
    Cslib.MachineLearning.OnlineLearning.Experts.exists_unbounded_modRegret_univ_div_const
  ]
  scope := "On Fin 3 (N = 3) with deterministic {0, 1} play and {0, 1} loss sequences: over \
    T = 6 m rounds, external regret is 0 while swap regret equals 3 m for arbitrary m : ℕ; over \
    T = 6 m + 1 rounds, external regret is strictly positive (= 1) while swap regret / external \
    regret exceeds any prescribed real bound M."

register_result "blum-mansour-dominated-action-weight-bounds" where
  title := "Multiplicative-update weight decay on ε-dominated actions versus low external regret"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Exercise 4.8",
      locator := "Chapter 4, Exercises, p. 101 (with §4.4.4, pp. 91–92)" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.sum_prob_hedgeFactor_le_of_dominated,
    Cslib.MachineLearning.OnlineLearning.Experts.sum_prob_mwFactor_le_of_dominated,
    Cslib.MachineLearning.OnlineLearning.Experts.exists_nonpos_external_regret_dominated_weight
  ]
  scope := "Under hedgeFactor η (covering [0, 1] Randomized Weighted Majority via \
    η = -log(1 - η')), total cumulative weight over any horizon T on an action ε-dominated by a \
    mixed strategy is at most 1 / (1 - exp(-η ε)). Under Polynomial Weights mwFactor η \
    (coinciding with {0, 1}-RWM), total cumulative weight over T rounds on an action \
    pure-ε-dominated by k (with 0 ≤ ℓ s k) is at most 1 / (η ε). Conversely, on Fin 3 over 2 m \
    rounds with ε ∈ [0, 1 / 2], deterministic play can achieve nonpositive external regret while \
    placing cumulative weight m (time-average 1 / 2) on an ε-dominated action."
