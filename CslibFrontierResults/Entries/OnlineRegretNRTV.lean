/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.MachineLearning.OnlineLearning.Bandit
import CslibFrontier.MachineLearning.OnlineLearning.ConstantSum
import CslibFrontier.MachineLearning.OnlineLearning.FPL
import CslibFrontier.MachineLearning.OnlineLearning.Greedy
import CslibFrontier.MachineLearning.OnlineLearning.InternalRegret
import CslibFrontier.MachineLearning.OnlineLearning.LowerBounds
import CslibFrontier.Probability.BitString.Khintchine

/-!
# Collected results: NRTV Chapter 4 online learning, regret minimization, and bandits
-/

register_result "bitstring-khintchine-l1-lower-bound" where
  title := "Elementary Khintchine L1 lower bound for Rademacher sums (constant 1 / √3)"
  topic := "probability"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.8 and Exercise 4.5 (discrepancy L1 lower-bound ingredient)",
      locator := "Chapter 4, §4.3.4, p. 88, and p. 101" }
  ]
  theorems := [
    Cslib.BitString.sum_sq_div_three_le_sq_expect_abs_sum_mul_signVal,
    Cslib.BitString.sqrt_sum_sq_div_three_le_expect_abs_sum_mul_signVal,
    Cslib.BitString.sqrt_card_div_three_le_expect_abs_sum_signVal
  ]
  scope := "Finite uniform Rademacher sums Y = ∑ i, a i * signVal (x i) over x : ι → Bool. \
    Interpolates the second moment between the first and fourth moments via Cauchy–Schwarz \
    using 𝔼 Y^4 ≤ 3 (𝔼 Y^2)^2 from Probability/BitString/Rademacher.lean, giving the \
    elementary constant 1 / √3 rather than Szarek's sharp 1 / √2."

register_result "blum-mansour-greedy-loss-bound" where
  title := "Deterministic Greedy (FTL) cumulative loss bound"
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
    N * minCumLoss ℓ T + (N - 1). Generalizes the source's {0, 1} statement to [0, 1] losses. \
    Semantic real-valued bound; no running time is charged."

register_result "blum-mansour-rand-greedy-loss-bound" where
  title := "Randomized Greedy harmonic and logarithmic cumulative loss bounds"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.4",
      locator := "Chapter 4, §4.3.1, p. 84" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.randGreedy_loss_le_harmonic,
    Cslib.MachineLearning.OnlineLearning.Experts.randGreedy_loss_le_log
  ]
  scope := "Binary {0, 1} loss sequences on a finite nonempty action space of size N. Uniform \
    play over current minimum-loss leaders (randGreedyProb) satisfies the harmonic bound \
    (H_N - 1) + H_N * minCumLoss ℓ T and hence ln N + (1 + ln N) * minCumLoss ℓ T. Unlike \
    Theorem 4.2, the exact-tie algorithm requires {0, 1} losses (arbitrary [0, 1] perturbations \
    can force singleton leader sets)."

register_result "blum-mansour-rwm-loss-bound" where
  title := "Randomized Weighted Majority regret bounds and second-order counterexample"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.5 and Exercise 4.3",
      locator := "Chapter 4, §4.3.2, pp. 85–86, and p. 101" },
    { paper := LittlestoneWarmuth1994,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.rwm_loss_le,
    Cslib.MachineLearning.OnlineLearning.Experts.rwm_loss_le_tunedStep,
    Cslib.MachineLearning.OnlineLearning.Experts.rwm_loss_le_sqrt_minCumLoss,
    Cslib.MachineLearning.OnlineLearning.Experts.exists_rwm_gt_pw_sq_bound
  ]
  scope := "Update factor rwmFactor η x = (1 - η) ^ x on [0, 1] losses over a finite action space \
    of size N. For 0 < η ≤ 1 / 2, L_RWM ≤ (1 + η) * L_k + ln N / η; for N ≥ 2 and every T : ℕ, \
    the capped step size tunedStep (ln N) T gives L_RWM ≤ minCumLoss ℓ T + 2 √(T ln N), and \
    tunedStep (ln N) L_min gives the first-order bound L_min + 2 √(L_min ln N) + 2 ln N (the \
    source remark on p. 85 omits the + 2 ln N term needed when L_min = 0). \
    exists_rwm_gt_pw_sq_bound shows that unlike Polynomial Weights, rwmFactor violates the \
    comparator-second-order inequality L ≤ L_k + η Q_k + ln N / η from Theorem 4.6 on [0, 1] \
    losses (Exercise 4.3)."

register_result "blum-mansour-payoff-mw-bound" where
  title := "Modified Polynomial Weights regret bound for payoffs in [-1, +1]"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Exercise 4.4",
      locator := "Chapter 4, p. 101" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.mw_payoff_ge_sub_sq,
    Cslib.MachineLearning.OnlineLearning.Experts.mw_payoff_ge_sub_sqrt_qmax
  ]
  scope := "Multiplicative update mwPayoffFactor η x = 1 + η * x for payoff maximization with \
    g s j ≥ -1 (in particular [-1, 1]). Achieves total expected payoff at least \
    ∑ t < T, g t k - η ∑ t < T, g t k ^ 2 - ln N / η for 0 < η ≤ 1 / 2, and with \
    η = tunedStep (ln N) Q_max at least ∑ t < T, g t k - (2 √(Q_max ln N) + 2 ln N) whenever \
    ∑ t < T, g t k ^ 2 ≤ Q_max."

register_result "anytime-hedge-regret-bound" where
  title := "Horizon-free decreasing-step-size Hedge external regret bound"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Unknown-horizon regret note (Theorem 4.5 / Theorem 4.6 footnote)",
      locator := "Chapter 4, pp. 85 and 87" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.anytimeHedge_regret_le
  ]
  scope := "Decreasing step sizes η_t = √(ln N / (t + 1)) on [0, 1] losses over N ≥ 2 experts. \
    Satisfies external regret at most 3 √(T ln N) simultaneously for every horizon T : ℕ without \
    doubling tricks or advance knowledge of T. Real-valued weights; no running time is charged."

register_result "blum-mansour-dominated-weights" where
  title := "RWM and PW assign small weight to ε-dominated actions, unlike low external regret"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Exercise 4.8",
      locator := "Chapter 4, p. 101" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.rwm_prob_le_of_dominated_mixed,
    Cslib.MachineLearning.OnlineLearning.Experts.rwm_sum_prob_le_of_dominated_mixed,
    Cslib.MachineLearning.OnlineLearning.Experts.mw_prob_le_of_dominated,
    Cslib.MachineLearning.OnlineLearning.Experts.mw_sum_prob_le_of_dominated,
    Cslib.MachineLearning.OnlineLearning.Experts.exists_low_external_regret_dominated_weight
  ]
  scope := "Pure-strategy (PW/mwFactor) and mixed-strategy (RWM/rwmFactor) exponential decay bounds \
    on the probability assigned to an ε-dominated action j, giving cumulative weight at most \
    1 / (η * ε) over any horizon T : ℕ (average weight ≤ 1 / (T * η * ε)). Counterexample on \
    Fin 3 over 2 * m rounds shows that deterministic low-external-regret play can incur nonpositive \
    external regret while placing time-average weight 1 / 2 on an ε-dominated action (ε ≤ 1 / 2)."

register_result "blum-mansour-internal-swap-regret" where
  title := "Internal vs. swap regret relations and O(√(T N log N)) Polynomial Weights bound"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Exercises 4.1, 4.2, and 4.6",
      locator := "Chapter 4, §4.2, pp. 81–82, and p. 101" },
    { paper := BlumMansour2007,
      theorem := "Corollary 7",
      locator := "p. 1313" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.swapRegret_le_card_mul_internalRegret,
    Cslib.MachineLearning.OnlineLearning.Experts.exists_swapRegret_eq_pred_card_mul_internalRegret,
    Cslib.MachineLearning.OnlineLearning.Experts.exists_externalRegret_zero_and_swapRegret_eq,
    Cslib.MachineLearning.OnlineLearning.Experts.exists_unbounded_swapRegret_div_externalRegret,
    Cslib.MachineLearning.OnlineLearning.Experts.swapRegret_blumMansourProb_le_sqrt,
    Cslib.MachineLearning.OnlineLearning.Experts.blumMansourPW_swap_regret_le_sqrt
  ]
  scope := "Memoryless modification-rule framework on a finite action space of size N. Proves \
    swapRegret ≤ N * internalRegret (with N - 1 tightness witness for N ≥ 2), constructs the \
    N = 3 unbounded swap/external regret separation (both exact externalRegret = 0 with \
    swapRegret = 3 m and externalRegret = 1 with arbitrarily large swapRegret), and bridges \
    the 2 √(T N ln N) swap-regret bound to both Hedge (T ≥ N ln N, losses in [-1, 1]) and \
    Polynomial Weights copies (T ≥ 4 N ln N, losses in [0, 1]). Stationary vectors are chosen \
    classically; no running time is charged."

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
  scope := "For every causal online algorithm (IsOnlineAlg H) on N ≥ 1 experts and every horizon \
    T, there exist a {0, 1} loss sequence ℓ and action sequence g : ℕ → ι whose cumulative loss \
    is 0 while H incurs expected loss at least T * (1 - 1 / N)."

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
  scope := "For every causal deterministic online learner on N ≥ 1 experts and horizon T, there \
    exists a {0, 1} loss sequence on which the learner suffers total loss T while the best fixed \
    expert suffers exact loss ⌊T / N⌋ (matching both the printed equality in Theorem 4.3 and the \
    matching upper bound of Theorem 4.2)."

register_result "blum-mansour-stochastic-lower-bounds" where
  title := "Stochastic external-regret lower bounds: short-horizon, Ω(√T), and Ω(√(T log N))"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorems 4.7 and 4.8 and Exercise 4.5",
      locator := "Chapter 4, §4.3.4, pp. 87–88, and p. 101" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.exists_stochastic_loss_eq_half_minCumLoss_zero,
    Cslib.MachineLearning.OnlineLearning.Experts.exists_two_experts_stochastic_regret_ge,
    Cslib.MachineLearning.OnlineLearning.Experts.exists_stochastic_regret_ge_sqrt_mul_log,
    Cslib.MachineLearning.OnlineLearning.Experts.exists_stochastic_regret_ge_sqrt_mul_log_of_card_le
  ]
  scope := "Uniform finite distributions over binary {0, 1} loss sequences against all causal \
    online algorithms (IsOnlineAlg H). For 2 ^ T ≤ N (Theorem 4.7), every H has expected loss \
    T / 2 while minCumLoss = 0 deterministically. For N ≥ 2 (Theorem 4.8), i.i.d. fair-coin \
    losses yield expected regret at least (1 / (2 √3)) * √T. For N ≥ 2 and T ≥ ⌊log₂ N⌋ (hence \
    all T ≥ N, Exercise 4.5), block-embedded hypercube coins give expected regret at least \
    (1 / (4 √3)) * √(T * ln N) via Khintchine's L1 lower bound."

register_result "blum-mansour-constant-sum-no-regret" where
  title := "External regret in constant-sum games and online-learning proof of the minimax theorem"
  topic := "game theory"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.9 and Section 4.4.2 (minimax theorem proof)",
      locator := "Chapter 4, §4.4, pp. 88–90" },
    { paper := vonNeumann1928,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.constantSum_row_average_loss_le,
    Cslib.MachineLearning.OnlineLearning.Experts.constantSum_col_average_loss_le,
    Cslib.MachineLearning.OnlineLearning.Experts.constantSum_average_loss_mem_Icc,
    Cslib.MachineLearning.OnlineLearning.Experts.maxminValue_eq_minmaxValue,
    Cslib.MachineLearning.OnlineLearning.Experts.isMinimaxValue_minmaxValue_of_noRegret
  ]
  scope := "Finite two-player constant-sum matrix games s₁ + s₂ = c with arbitrary opponent \
    mixed-strategy sequences. In addition to the Theorem 4.9 average-loss bounds, establishes \
    von Neumann's minimax theorem (maxminValue M = minmaxValue M and attainment of \
    IsMinimaxValue M (minmaxValue M)) directly from coupled anytimeHedgeProb self-play and \
    compactness of StdSimplex ℝ without invoking LP duality or Sion's theorem. Note the print \
    swap of min/max in v_min^1 on p. 89 of the source; the proof follows the text's intended \
    definition max_q min_i E_{j~q}[s₁(i, j)]."

register_result "kalai-vempala-fpl-regret" where
  title := "Follow the Perturbed Leader expected regret bound"
  topic := "online learning"
  sources := [
    { paper := KalaiVempala2005,
      theorem := unverified,
      locator := unverified },
    { paper := BlumMansour2007AGT,
      theorem := "Section 4.7.1 discussion of large action spaces",
      locator := "Chapter 4, §4.7.1, p. 98" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.FPL.fpl_regret_le,
    Cslib.MachineLearning.OnlineLearning.FPL.fpl_regret_le_of_l1_diam,
    Cslib.MachineLearning.OnlineLearning.FPL.fpl_regret_le_sqrt,
    Cslib.MachineLearning.OnlineLearning.FPL.fpl_experts_regret_le_sqrt
  ]
  scope := "Online linear optimization over a finite decision set α embedded via vectors \
    v : α → ι → ℝ under uniform cube perturbation on [0, 1 / ε]^ι (Lebesgue measure on ℝ^ι). \
    Bounded via FTRL and cube translation-overlap volume to D / ε + ε R A T (2 √(D R A T) when \
    tuned); on the N-expert simplex with [0, 1] losses this specializes to 2 √(N T). No \
    optimization-oracle running time is charged; the standalone Kalai–Vempala 2005 journal PDF \
    was not separately re-audited."

register_result "blum-mansour-bandit-block-reduction" where
  title :=
    "Block-exploration reduction from partial-information (bandit) to full-information learning"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.17",
      locator := "Chapter 4, §4.6, pp. 94–96" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.blockFullInfo_loss_le,
    Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_expected_loss_le_mul,
    Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_expected_loss_le,
    Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_expected_loss_le_optimal,
    Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_expected_loss_le_book,
    Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_expected_loss_le_book_log,
    Cslib.MachineLearning.OnlineLearning.Experts.mabRWM_expected_loss_le,
    Cslib.MachineLearning.OnlineLearning.Experts.mabAnytimeHedge_expected_loss_le,
    Cslib.MachineLearning.OnlineLearning.Experts.mabRWM_uniformInj_expected_loss_le
  ]
  scope := "Finite nonempty action space of size N and arbitrary [0, 1]-valued oblivious loss \
    sequences (without requiring block count K to divide horizon T; leftover tail rounds play the \
    uniform distribution). Parameterized by any collision-free ExplorationSchedule ι m Ω with \
    uniform marginals (instantiated both by all embeddings ι ↪ Fin m and by cyclic shifts on \
    Fin m). Balanced tuning K = ⌊(T / N)^{2/3} (ln N)^{1/3}⌋ yields explicit regret at most \
    (3 / 2 + C √2) T^{2/3} (N ln N)^{1/3} for all N ≥ 2 and all T : ℕ ((9 / 2) with RWM, 6 with \
    anytime Hedge); the textbook tuning K = ⌊(T / N)^{2/3}⌋ gives \
    (3 / 2 + C √2 √(ln N)) T^{2/3} N^{1/3} (and (3 + 2 C) T^{2/3} N^{1/3} ln N) for T ≥ N ≥ 2. \
    Partial-information causality is certified by mabPlay_bandit_congr; \
    no running time is charged."
