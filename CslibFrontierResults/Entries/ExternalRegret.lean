/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.MachineLearning.OnlineLearning.Greedy
import CslibFrontier.MachineLearning.OnlineLearning.LowerBounds
import CslibFrontier.MachineLearning.OnlineLearning.MultiplicativeWeights

/-!
# Collected results: external regret algorithms and lower bounds (NRTV Chapter 4, §4.3)
-/

register_result "blum-mansour-dynamic-regret-lower-bound" where
  title := "Lower bound on dynamic regret against all action sequences G_all"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.1",
      locator := "Chapter 4, §4.3, pp. 82–83" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.exists_dynamic_regret_ge
  ]
  scope := "For every causal online algorithm on [0, 1] loss histories (IsOnlineAlgorithm H) over \
    N ≥ 1 experts and every horizon T, there exist a {0, 1} loss sequence ℓ and an action sequence \
    g : ℕ → ι whose cumulative loss is 0 while H incurs expected loss at least T * (1 - 1 / N)."

register_result "blum-mansour-greedy-loss-bound" where
  title := "Deterministic Greedy (Follow-the-Leader) cumulative loss bound"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.2",
      locator := "Chapter 4, §4.3.1, p. 83" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.greedy_loss_le,
    Cslib.MachineLearning.OnlineLearning.Experts.greedyPlay_loss_le
  ]
  scope := "Any sequence picking a minimum cumulative-loss leader x t ∈ leaders ℓ t (in \
    particular greedyPlay breaking ties by a linear order) on any [0, 1]-valued loss sequence \
    over a finite nonempty action space of size N satisfies ∑ t < T, ℓ t (x t) ≤ \
    N * minCumLoss ℓ T + (N - 1). Generalizes the source's {0, 1} statement to [0, 1] losses."

register_result "blum-mansour-deterministic-lower-bound" where
  title := "Deterministic online algorithm external-regret lower bound"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.3",
      locator := "Chapter 4, §4.3.1, pp. 83–84" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.exists_deterministic_loss_eq_and_minCumLoss_eq
  ]
  scope := "For every causal deterministic online learner on [0, 1] loss histories over N ≥ 1 \
    experts and every horizon T, there exists a {0, 1} loss sequence on which the learner suffers \
    total loss T while the best fixed expert suffers exact cumulative loss ⌊T / N⌋."

register_result "blum-mansour-rand-greedy-loss-bound" where
  title := "Randomized Greedy logarithmic cumulative loss bound"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.4",
      locator := "Chapter 4, §4.3.1, p. 84" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.randGreedy_loss_le_log
  ]
  scope := "Binary {0, 1} loss sequences on a finite nonempty action space of size N. Playing \
    uniformly over current minimum-loss leaders (randGreedyProb) satisfies \
    L_RG^T ≤ ln N + (1 + ln N) * minCumLoss ℓ T."

register_result "blum-mansour-rwm-loss-bound" where
  title := "Randomized Weighted Majority and Multiplicative Weights (Polynomial Weights) external \
    regret bounds"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorems 4.5 and 4.6",
      locator := "Chapter 4, §§4.3.2–4.3.3, pp. 85–87" },
    { paper := AroraHazanKale2012,
      theorem := "Theorem 2.1",
      locator := "Section 2" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.mw_regret_le_sq,
    Cslib.MachineLearning.OnlineLearning.Experts.mw_regret_le,
    Cslib.MachineLearning.OnlineLearning.Experts.mw_regret_le_sqrt_of_mem_Icc
  ]
  scope := "Multiplicative weights prob (mwFactor η) with mwFactor η x = 1 - η * x is Blum and \
    Mansour's Polynomial Weights algorithm (§4.3.3, p. 86) and Arora–Hazan–Kale's Multiplicative \
    Weights (§2), coinciding with Randomized Weighted Majority (1 - η) ^ ℓ (§4.3.2, p. 85) on \
    binary {0, 1} losses. For 0 < η and η * ℓ t i ≤ 1 / 2 (in particular 0 < η ≤ 1 / 2 on [0, 1] \
    losses), mw_regret_le_sq gives the second-order bound L_PW^T ≤ L_i^T + η ∑ t < T, (ℓ t i)^2 \
    + ln N / η for every expert i (Theorem 4.6 first display with Q_i^T, p. 87). For 0 < η ≤ \
    1 / 2 and losses in [-1, 1], mw_regret_le gives L_MW^T ≤ L_i^T + η ∑ t < T, |ℓ t i| + ln N / η \
    (Arora–Hazan–Kale Theorem 2.1, and Theorem 4.5 first display (1 + η) L_i^T + ln N / η on \
    {0, 1} losses, p. 85). For [0, 1] losses and every horizon T : ℕ, mw_regret_le_sqrt_of_mem_Icc \
    with η = min √(ln N / T) (1 / 2) gives L_PW^T ≤ L_i^T + 2 √(T ln N) (Theorems 4.5 and 4.6 \
    second displays, pp. 85, 87)."

register_result "blum-mansour-short-horizon-lower-bound" where
  title := "Short-horizon stochastic external-regret lower bound (2^T ≤ N)"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.7",
      locator := "Chapter 4, §4.3.4, pp. 87–88" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.exists_stochastic_loss_eq_half_minCumLoss_zero
  ]
  scope := "Whenever 2 ^ T ≤ N (in particular for all T < log₂ N), there exists a uniform \
    distribution over Fin T → Bool of {0, 1} loss sequences such that minCumLoss (ℓ w) T = 0 \
    holds on every realization while every causal online algorithm (IsOnlineAlgorithm H) incurs \
    expected loss T / 2."

register_result "blum-mansour-two-experts-lower-bound" where
  title := "Two-expert Ω(√T) stochastic external-regret lower bound"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.8",
      locator := "Chapter 4, §4.3.4, p. 88" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.exists_two_experts_stochastic_regret_ge
  ]
  scope := "For N ≥ 2 experts (in particular N = 2) and any horizon T : ℕ, under uniform \
    Fin T → Bool fair-coin {0, 1} losses, every causal online algorithm (IsOnlineAlgorithm H) \
    incurs expected loss T / 2 and expected external regret at least (1 / (2 e)) √T."

register_result "blum-mansour-sqrt-log-lower-bound" where
  title := "General Ω(√(T log N)) stochastic external-regret lower bound"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Exercise 4.5",
      locator := "Chapter 4, Exercises, p. 101" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.exists_stochastic_regret_ge_sqrt_mul_log
  ]
  scope := "For N ≥ 2 experts and T ≥ ⌊log₂ N⌋ (in particular for all T ≥ N), there exists a \
    uniform distribution over Fin T → Bool of {0, 1} loss sequences under which every online \
    algorithm (IsOnlineAlgorithm H) incurs expected external regret at least \
    (1 / (4 e)) √(T ln N)."
