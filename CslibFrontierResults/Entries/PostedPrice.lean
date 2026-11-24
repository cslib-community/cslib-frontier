/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Mechanism.PostedPrice
import CslibFrontier.Probability.OptimalStopping.ProphetSample

/-!
# Collected results: single-sample prophet inequality, posted-price auctions, and Bulow–Klemperer
-/

open Cslib.GameTheory.SingleParameter

register_result "single-sample-prophet-inequality" where
  title := "Single-sample prophet inequality with randomized tie-breaking"
  topic := "optimal stopping"
  sources := [
    { paper := RubinsteinWangWeinberg2020,
      theorem := "Theorem 1",
      locator := "arXiv:1911.07945v2, §1 p. 1, §2 p. 2, and §3 Observation 3, Propositions 4–5 \
        and Proof of Theorem 1, pp. 3–4" }
  ]
  theorems := [
    Cslib.Probability.OptimalStopping.Prophet.expectedMax_le_two_mul_singleSampleExpectedReward,
    Cslib.Probability.OptimalStopping.Prophet.expectedMax_le_two_mul_singleSampleExpectedReward_perm
  ]
  scope := "For n independent ℝ≥0-valued discrete laws μ : Fin n → PMF ℝ≥0 (no finiteness or \
    atom-freeness needed; E[max] may be ⊤), given one offline sample s ~ piFin μ and an \
    independent uniform permutation π : Equiv.Perm (Fin (2 * n)) breaking exact value ties \
    lexicographically, the online stopping rule singleSampleRule s π achieves expected reward \
    at least (1/2) · expectedMax (List.ofFn μ) under any arrival permutation."

register_result "sequential-posted-price-welfare" where
  title := "Sequential posted-price auctions: group strategy-proofness and 1/2 welfare bounds"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2013CS364A,
      theorem := "Theorem 2.1",
      locator := "Lecture #6 (9 October 2013), §2, pp. 2–4" },
    { paper := ChawlaHartlineMalecSivan2010,
      theorem := "Section 2.2 and Appendix D.2 (gap-of-2 example)",
      locator := "arXiv:0907.2435v2, §2.2 p. 4 and Appendix D.2 p. 19" },
    { paper := RubinsteinWangWeinberg2020,
      theorem := "Theorem 1 (posted-price specialization)",
      locator := "arXiv:1911.07945v2, §1 p. 1" }
  ]
  theorems := [
    PostedPrice.postedPrice_isDSIC,
    PostedPrice.postedPrice_isIR,
    PostedPrice.postedPrice_isGroupStrategyProof,
    PostedPrice.postedPrice_strongGroupStrategyProof,
    PostedPrice.expectedWelfare_vickrey_le_two_mul_postedPrice_half,
    PostedPrice.exists_expectedWelfare_vickrey_le_two_mul_postedPrice,
    PostedPrice.expectedWelfare_vickrey_le_two_mul_singleSamplePostedPrice,
    PostedPrice.exists_postedPrice_revenue_lt
  ]
  scope := "Single-item sequential posted-price mechanisms on finite linearly ordered bidder \
    sets. Weak group strategy-proofness holds unconditionally on nonnegative profiles; strong \
    group strategy-proofness holds away from indifference ties v i = p i. Welfare 1/2 bounds \
    hold on independent PMF ℝ≥0 valuations for the balanced price E[max]/2, a Samuel-Cahn \
    median price, and the prior-independent single-sample price max_j s_j, with matching \
    2-bidder tightness on both welfare and revenue."

register_result "sequential-posted-price-revenue" where
  title := "Non-i.i.d. regular single-item revenue 1/2-approximation by sequential posted pricing"
  topic := "game theory"
  sources := [
    { paper := ChawlaHartlineMalecSivan2010,
      theorem := "Theorem 10 (k = 1 single-item case)",
      locator := "arXiv:0907.2435v2, §5.2 p. 9 and Appendix D.2 p. 19" },
    { paper := Roughgarden2013CS364A,
      theorem := "Section 3 (Prophet-based posted-price single-item auction)",
      locator := "Lecture #6 (9 October 2013), §3, pp. 4–5" }
  ]
  theorems := [
    Cslib.GameTheory.SingleParameter.PostedPrice.integral_sum_payment_le_two_mul_virtualPostedPrices
  ]
  scope := "For independent (not necessarily identical) bidders on a finite linearly ordered \
    index set ι, each with a regular valuation distribution μ i having positive interior \
    density f i on [0, h i] (HasValueDensity, IsRegular), posting bidder-specific inverse \
    virtual prices reservePrice (φ_i - t) at t = E[max_i φ_i(v_i)⁺] / 2 yields a DSIC, IR \
    sequential posted-price mechanism whose expected revenue is at least 1/2 that of every \
    DSIC, IR, measurable single-item mechanism."

register_result "bulow-klemperer-theorem" where
  title := "Bulow–Klemperer theorem: (n + 1)-bidder Vickrey beats optimal n-bidder revenue"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2013CS364A,
      theorem := "Theorem 4.1",
      locator := "Lecture #6 (9 October 2013), §4, pp. 5–6" },
    { paper := BulowKlemperer1996,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.SingleParameter.PostedPrice.bulow_klemperer
  ]
  scope := "For any n : ℕ and i.i.d. regular valuation distribution μ with positive interior \
    density f on [0, h] (HasValueDensity, IsRegular), the prior-independent (n + 1)-bidder \
    Vickrey auction with zero reserve achieves expected revenue at least that of every DSIC, \
    IR, measurable n-bidder single-item mechanism."
