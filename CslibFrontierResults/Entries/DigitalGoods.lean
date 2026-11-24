/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Mechanism.DigitalGoods.ProfitExtraction

register_result "hartline-karlin-2007-profit-extract-correct" where
  title := "Correctness and truthfulness of ProfitExtract_R for digital goods"
  topic := "algorithmic game theory"
  sources := [
    { paper := HartlineKarlin2007,
      theorem := "Exercise 13.10 (Definition 13.40)",
      locator := "§13.4.4, p. 347; Exercises, p. 361" }
  ]
  theorems := [
    Cslib.GameTheory.SingleParameter.DigitalGoods.profitExtractOn_isDSIC,
    Cslib.GameTheory.SingleParameter.DigitalGoods.profitExtractOn_isIR,
    Cslib.GameTheory.SingleParameter.DigitalGoods.profitExtractOn_isNormalized,
    Cslib.GameTheory.SingleParameter.DigitalGoods.sum_payment_profitExtractOn,
    Cslib.GameTheory.SingleParameter.DigitalGoods.sum_payment_profitExtract_of_le
  ]
  scope := "Single-parameter zero-cost digital goods auctions over a finite bidder type ι \
    ([Fintype ι] [DecidableEq ι]) with nonnegative real bids (0 ≤ b : ι → ℝ). The target profit \
    R : ℝ is unrestricted for incentive compatibility (for R < 0, profitExtractOn allocates 0 \
    and charges 0; for R = 0 on a nonempty subset s, all bidders in s win at price 0). The exact \
    profit extraction theorems require 0 ≤ R and give total payment R when R ≤ ℱ(b_s) and 0 \
    when ℱ(b_s) < R. The benchmark ℱ (`optimalProfitOn` / `optimalProfit`) is defined without \
    sorting as a maximum over candidate bids and proved equal to the book's order-statistic \
    formula max_{1 ≤ k ≤ |ι|} k · v_(k) in `singlePriceProfitOn_eq_sup_orderStatistic`. \
    Truthfulness and individual rationality are derived via the existing `criticalBidMechanism` \
    API. No running-time claim is made."

register_result "hartline-karlin-2007-rspe-competitive-ratio" where
  title := "Exact 4-competitiveness of Random Sampling Profit Extraction (RSPE)"
  topic := "algorithmic game theory"
  sources := [
    { paper := HartlineKarlin2007,
      theorem := "Theorem 13.42 (Definitions 13.33, 13.34, 13.41)",
      locator := "§13.4.5, p. 348 (tight instance referenced from §13.4.2, pp. 345–346)" }
  ]
  theorems := [
    Cslib.GameTheory.SingleParameter.DigitalGoods.rspe_isDSIC,
    Cslib.GameTheory.SingleParameter.DigitalGoods.rspe_isIR,
    Cslib.GameTheory.SingleParameter.DigitalGoods.rspe_truthfulInExpectation,
    Cslib.GameTheory.SingleParameter.DigitalGoods.rspe_isCompetitive,
    Cslib.GameTheory.SingleParameter.DigitalGoods.exists_rspe_tight,
    Cslib.GameTheory.SingleParameter.DigitalGoods.isLeast_rspe_competitiveRatio
  ]
  scope := "Finite bidder types ι ([Fintype ι] [DecidableEq ι]) with nonnegative real bid profiles \
    0 ≤ b : ι → ℝ. Randomized partitioning by independent fair coin flips is modeled as a family \
    of deterministic `SingleParameter.Mechanism ι` indexed by the subset `s : Finset ι` of bidders \
    placed in the first part, with expectation given by Mathlib's `Finset.expect` (`𝔼 s : Finset \
    ι, ...`, uniform over all 2^|ι| subsets). Universal truthfulness (`rspe_isDSIC`) holds per \
    partition, yielding truthfulness in expectation (`rspe_truthfulInExpectation`, Definition \
    13.5, p. 334). Competitive ratio `IsCompetitive` is stated in multiplicative form \
    (`0 ≤ β ∧ ∀ b, 0 ≤ b → bench b ≤ β * profit b`) to avoid `0 / 0`. Exact tightness (`4` is \
    least) holds for every `ι` with `2 ≤ Fintype.card ι` via the two-bid profile with bids `1` \
    and `2` padded with `0`s. Two printed inaccuracies on p. 348 are repaired: the informal \
    paragraph prints `ℱ⁽²⁾` instead of `ℱ` for `R', R''`, and the proof claims exact realized \
    profit `min(R', R'')`, whereas `R' = R'' > 0` yields `2 * R'` (`sum_payment_rspe_eq`). No \
    running-time claim is made."
