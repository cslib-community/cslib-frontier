/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Mechanism.DigitalGoods.ConsensusEstimation
import CslibFrontier.GameTheory.Mechanism.DigitalGoods.LowerBounds

register_result "hartline-karlin-2007-symmetric-deterministic-impossibility" where
  title := "Impossibility and exact n-bidder bound for symmetric deterministic digital goods \
    auctions"
  topic := "algorithmic game theory"
  sources := [
    { paper := HartlineKarlin2007,
      theorem := "Theorem 13.24 and Corollary 13.35",
      locator := "§13.3.1, pp. 340–341 (Footnote 1, Theorem 13.24); §13.4.2, p. 345 \
        (Corollary 13.35)" }
  ]
  theorems := [
    Cslib.GameTheory.SingleParameter.DigitalGoods.exists_not_approx_symmetric_deterministic,
    Cslib.GameTheory.SingleParameter.DigitalGoods.card_le_of_isCompetitive_symmetric,
    Cslib.GameTheory.SingleParameter.DigitalGoods.not_exists_const_competitive_symmetric,
    Cslib.GameTheory.SingleParameter.DigitalGoods.isLeast_symmetricSecondPrice_competitiveRatio
  ]
  scope := "Single-parameter zero-cost digital goods auctions over finite bidder types with \
    nonnegative real bids, binary deterministic allocations (`IsBinary`), DSIC (`IsDSIC`), \
    individual rationality (`IsIR`), and permutation invariance (`IsSymmetric`, Footnote 1, \
    p. 340). `exists_not_approx_symmetric_deterministic` (Theorem 13.24) gives, for every β > 0 \
    and γ : ℝ, explicit n ≥ 2 and h ≥ 1 such that every symmetric deterministic DSIC, IR auction \
    on `Fin n` earns strictly less than `ℱ(b) / β - h * γ` on some bid profile in `[1, h]ⁿ`. \
    `card_le_of_isCompetitive_symmetric` proves the exact n-bidder lower bound `n ≤ β` against \
    `ℱ⁽²⁾`, yielding Corollary 13.35 (`not_exists_const_competitive_symmetric`) and exact \
    tightness for every `n ≥ 2` via `symmetricSecondPrice` \
    (`isLeast_symmetricSecondPrice_competitiveRatio`). Normalization is not required for the lower \
    bounds. No running-time claim is made."

register_result "hartline-karlin-2007-digital-goods-lower-bounds" where
  title := "Randomized competitive lower bounds (2 for n = 2, 13/6 for n = 3) and no best \
    2-bidder auction"
  topic := "algorithmic game theory"
  sources := [
    { paper := HartlineKarlin2007,
      theorem := "Lemma 13.38, n = 3 lower bound 13/6, and Exercise 13.8",
      locator := "§13.4.3, pp. 346–347; Exercises, p. 361 (Exercise 13.8)" }
  ]
  theorems := [
    Cslib.GameTheory.SingleParameter.DigitalGoods.two_le_of_isCompetitive_two,
    Cslib.GameTheory.SingleParameter.DigitalGoods.thirteen_div_six_le_of_isCompetitive_three,
    Cslib.GameTheory.SingleParameter.DigitalGoods.exists_strictly_higher_profit_two
  ]
  scope := "Truthful-in-expectation digital goods auctions (Definition 13.5, p. 334), represented \
    directly as `SingleParameter.Mechanism ι` satisfying `IsDSIC`, `IsIR`, and `IsUnitAlloc` \
    (allocations in `[0, 1]` on nonnegative bids), which subsumes all deterministic and \
    universally truthful randomized digital goods auctions. `two_le_of_isCompetitive_two` \
    (Lemma 13.38) proves `2 ≤ β` for `|ι| = 2` (tight via `symmetricSecondPrice`), \
    `thirteen_div_six_le_of_isCompetitive_three` proves `13 / 6 ≤ β` for `|ι| = 3`, and \
    `exists_strictly_higher_profit_two` (Exercise 13.8) exhibits a deterministic DSIC, IR, \
    normalized posted-price auction strictly beating `M` on some nonnegative 2-bidder profile. \
    The proofs use a discrete fine-grid equal-revenue distribution with Abel summation rather than \
    unbounded continuous expectations. The general-n asymptotic lower bound `2.42` of Theorem \
    13.37 (p. 346) is not formalized here and remains open under `#7789`. No running-time claim is \
    made."

register_result "hartline-karlin-2007-limited-supply-reduction" where
  title := "Reduction from β-competitive digital goods auctions to k-unit limited-supply auctions"
  topic := "algorithmic game theory"
  sources := [
    { paper := HartlineKarlin2007,
      theorem := "Exercise 13.9",
      locator := "Exercises, p. 361 (Exercise 13.9)" }
  ]
  theorems := [
    Cslib.GameTheory.SingleParameter.DigitalGoods.limitedSupplyMechanism_isDSIC,
    Cslib.GameTheory.SingleParameter.DigitalGoods.limitedSupplyMechanism_isIR,
    Cslib.GameTheory.SingleParameter.DigitalGoods.limitedSupplyMechanism_isNormalized,
    Cslib.GameTheory.SingleParameter.DigitalGoods.sum_limitedSupplyAlloc_le,
    Cslib.GameTheory.SingleParameter.DigitalGoods.limitedSupplyAlloc_mem_multiUnitFeasible,
    Cslib.GameTheory.SingleParameter.DigitalGoods.limitedSupplyMechanism_isCompetitive
  ]
  scope := "Finite linearly ordered bidder types `[Fintype ι] [LinearOrder ι]` with `k : ℕ` \
    identical units and benchmark `ℱ⁽²˒ᵏ⁾(v) = max_{2 ≤ m ≤ min k |ι|} m · v_(m)` \
    (`optimalProfitTwoLimited`, `0` when `min k |ι| < 2`). Given any DSIC, normalized, \
    `[0, 1]`-allocated digital goods auction `A` on `Fin (min k |ι|)` that is `β`-competitive \
    against `ℱ⁽²⁾`, `limitedSupplyMechanism k A` runs `A` on the top `min k |ι|` bidders (ordered \
    by their original index to preserve DSIC even for asymmetric `A`) and applies Myerson's \
    payment rule, yielding a DSIC, IR, normalized `k`-unit auction (binary and in \
    `MultiUnit.multiUnitFeasible k` whenever `A` is binary) that is `β`-competitive against \
    `ℱ⁽²˒ᵏ⁾`. No running-time claim is made."

register_result "hartline-karlin-2007-cepe" where
  title := "Consensus Estimate Profit Extraction (CEPE) competitiveness and truthfulness with high \
    probability"
  topic := "algorithmic game theory"
  sources := [
    { paper := HartlineKarlin2007,
      theorem := "Lemmas 13.47–13.48, Theorem 13.49, and Exercise 13.11 (Definitions 13.43–13.46)",
      locator := "§13.4.6, pp. 349–350 (Footnote 2); Exercises, p. 361 (Exercise 13.11)" }
  ]
  theorems := [
    Cslib.GameTheory.SingleParameter.DigitalGoods.volume_real_roundDown_consensus,
    Cslib.GameTheory.SingleParameter.DigitalGoods.roundDown_isRhoConsensus,
    Cslib.GameTheory.SingleParameter.DigitalGoods.integral_roundDown,
    Cslib.GameTheory.SingleParameter.DigitalGoods.roundDown_isBetaEstimate,
    Cslib.GameTheory.SingleParameter.DigitalGoods.cepeDet_optimal_response_of_consensus,
    Cslib.GameTheory.SingleParameter.DigitalGoods.cepeExpectedProfit_eq,
    Cslib.GameTheory.SingleParameter.DigitalGoods.cepe_isCompetitive,
    Cslib.GameTheory.SingleParameter.DigitalGoods.cepe_truthful_measure_ge,
    Cslib.GameTheory.SingleParameter.DigitalGoods.cepe_isTruthfulWithHighProbAt,
    Cslib.GameTheory.SingleParameter.DigitalGoods.cepeDigitalGoods_isCompetitive,
    Cslib.GameTheory.SingleParameter.DigitalGoods.cepeDigitalGoods_truthful_of_winners
  ]
  scope := "Randomization over `U ~ Uniform[0, 1]` is modeled via Lebesgue measure `volume.real` \
    and interval integrals on `[0, 1]`. `volume_real_roundDown_consensus` and \
    `roundDown_isRhoConsensus` prove Lemma 13.47 (exact consensus measure `1 - log_α ρ` for \
    `1 < α`, `1 ≤ ρ ≤ α`, `0 < V`). `integral_roundDown` and `roundDown_isBetaEstimate` prove \
    Lemma 13.48 (exact expectation `V / ((α * Real.log α) / (α - 1))`). \
    `cepeDet_optimal_response_of_consensus` proves Exercise 13.11(a) assuming the profit \
    extractor `PE R` is DSIC and normalized with allocations antitone in `R ≥ 0` (capturing \
    monotone-in-`R` offered prices in `[0, ∞]`, Footnote 2, p. 350). `cepeExpectedProfit_eq`, \
    `cepe_isCompetitive`, `cepe_truthful_measure_ge`, and `cepe_isTruthfulWithHighProbAt` prove \
    Theorem 13.49 and Exercise 13.11(b) for an arbitrary seller cost function `c : (ι → ℝ) → ℝ` \
    and exact profit extractor `PE`. Instantiating with `ℱ⁽²⁾` and `profitExtract` gives \
    `cepeDigitalGoods_isCompetitive` and `cepeDigitalGoods_truthful_of_winners` (`1 - O(1/m)` \
    truthfulness for `m ≥ 3` winners with `m / (m - 1) ≤ α`; the `m = 2` boundary where removing \
    one winner can drop `ℱ⁽²⁾` to `0` is checked in tests). No running-time claim is made."
