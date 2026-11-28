/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.PredictionMarket.LMSR
import CslibFrontier.GameTheory.PredictionMarket.NoTrade
import CslibFrontier.GameTheory.PredictionMarket.OrderMatching

/-!
# Collected results: prediction market no-trade, order matching, and conditional LMSR
-/

register_result "nrtv-prediction-market-no-trade-agreement" where
  title := "Aumann agreement, fully revealing REE, and Milgrom–Stokey no-trade theorem"
  topic := "game theory"
  sources := [
    { paper := PennockSami2007,
      theorem := "Section 26.2.2.3 (Rational expectations, fully revealing REE, and no-trade)",
      locator := "Chapter 26, §26.2.1–§26.2.2.3, Defs. 26.1–26.2, pp. 653–657; §26.7, p. 671" }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.aumann_agreement,
    Cslib.GameTheory.PredictionMarket.aumann_agreement_at,
    Cslib.GameTheory.PredictionMarket.condExp_infoWithPrice_eq_omniscient_of_isFullyRevealing,
    Cslib.GameTheory.PredictionMarket.isREE_commonValue_iff_omniscient_of_isFullyRevealing,
    Cslib.GameTheory.PredictionMarket.milgrom_stokey_no_trade
  ]
  scope := "Finite state space Ω with nonnegative common prior P : Ω → ℝ and information \
    partitions modeled as Setoid Ω. Section 26.2.2.3 of Pennock–Sami (2007) presents fully \
    revealing rational expectations equilibria and no-trade results in prose and cites Aumann \
    (1976) and Milgrom–Stokey (1982) in §26.7; here Aumann's agreement theorem, the omniscient-\
    forecast characterization of fully revealing REE, and the finite-agent Milgrom–Stokey \
    no-trade theorem (for risk-neutral zero-sum interim individually rational trades on a \
    common-knowledge event) are formalized in full, with posterior conditions quantified over \
    positive-probability states 0 < P ω to avoid null-cell division artifacts."

register_result "nrtv-divisible-order-matching-conp-complete" where
  title := "Divisible compound order matching with unlimited base events is coNP-complete"
  topic := "game theory"
  sources := [
    { paper := PennockSami2007,
      theorem := "Theorem 26.6(ii)",
      locator := "Chapter 26, §26.3.1, Definitions 26.3 & 26.5, Theorem 26.6(ii), pp. 659–661" }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.hasDivisibleMatch_iff_exists_pos_sum,
    Cslib.GameTheory.PredictionMarket.not_hasDivisibleMatch_iff_exists_small_farkas,
    Cslib.GameTheory.PredictionMarket.not_hasDivisibleMatch_iff_exists_small_subset,
    Cslib.GameTheory.PredictionMarket.polyTimeReducible_UNSAT_DivisibleOrderMatching,
    Cslib.GameTheory.PredictionMarket.DivisibleOrderMatching_coNPHard,
    Cslib.GameTheory.PredictionMarket.DivisibleOrderMatching_mem_coNP,
    Cslib.GameTheory.PredictionMarket.DivisibleOrderMatching_coNPComplete
  ]
  scope := "Compound conditional orders CompoundOrder with rational quantities/prices and CNF \
    event/conditioning formulas over ℕ (encoded by encOrderList = encList encCompoundOrder). \
    Proves full native multi-tape Turing-machine coNP-completeness (both UNSAT ≤ₚ \
    DivisibleOrderMatching and a polynomial-time integer Farkas certificate verifier on at most \
    O.length states via Farkas' lemma and Matrix.exists_int_nonneg_mulVec_eq), plus the LP \
    objective equivalence of Theorem 26.6(i). Polynomial-time LP solving on Turing machines for \
    Theorem 26.6(i) (O(log n) base securities) and Theorem 26.7 (indivisible matching) remain \
    open under #7789."

register_result "nrtv-lmsr-conditional-securities" where
  title := "Conditional LMSR cost function, integral pricing, and post-trade share update"
  topic := "game theory"
  sources := [
    { paper := PennockSami2007,
      theorem := "Exercise 26.3",
      locator := "Chapter 26, Exercise 26.3, pp. 674–675" }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.hasDerivAt_lmsrCondCost_shift,
    Cslib.GameTheory.PredictionMarket.integral_lmsrCondPrice_eq_sub_lmsrCondCost,
    Cslib.GameTheory.PredictionMarket.lmsrCost_lmsrCondUpdate_sub,
    Cslib.GameTheory.PredictionMarket.lmsrTraderPayoff_lmsrCondUpdate,
    Cslib.GameTheory.PredictionMarket.lmsrPrice_lmsrCondUpdate_of_notMem
  ]
  scope := "Any finite outcome space Ω with DecidableEq Ω, liquidity parameter b > 0, event \
    φ : Finset Ω, and nonempty conditioning event ψ : Finset Ω. Proves both Exercise 26.3(a) \
    (integrating the Bayes-rule instantaneous price of S_{φ|ψ} from 0 to δ equals \
    C_ψ(q + δ · 1_φ) - C_ψ(q)) and Exercise 26.3(b) (the updated share vector lmsrCondUpdate \
    adds δ on φ ∩ ψ, 0 on ψ \\ φ, and the conditional cost outside ψ, yielding exact refund-on-\
    cancellation payoff and leaving prices outside ψ unchanged)."
