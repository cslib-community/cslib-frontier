/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Mechanism.Domains
import CslibFrontier.GameTheory.Mechanism.Indirect
import CslibFrontier.GameTheory.Mechanism.MultiUnit
import CslibFrontier.GameTheory.Mechanism.Randomized
import CslibFrontier.GameTheory.SocialChoice.GibbardSatterthwaiteReduction

/-!
# Collected results: indirect mechanisms, revelation principles, and multi-unit auctions
-/

open Cslib.GameTheory

register_result "gibbard-satterthwaite-nisan-reduction" where
  title := "Single-voter monotonicity and Nisan's reduction from Gibbard–Satterthwaite to Arrow"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Proposition 9.6, Lemma 9.10, and Lemma 9.11",
      locator := "§9.2.3–9.2.4, pp. 214–215" }
  ]
  theorems := [
    SocialChoice.SocialChoiceFunction.isSingleMonotone_iff_isStrategyProof,
    SocialChoice.SocialChoiceFunction.isSingleMonotone_iff_isMaskinMonotone,
    SocialChoice.SocialChoiceFunction.nisanSWF_antisymm,
    SocialChoice.SocialChoiceFunction.toWeakRanking_nisanRanking,
    SocialChoice.SocialChoiceFunction.nisanSWF_isPareto_and_isIIA_and_not_isDictatorial
  ]
  scope := "Single-voter monotonicity (Definition 9.5) is equivalent to strategy-proofness on \
    arbitrary voter and alternative types, and for finite electorates [Finite V] also to Maskin \
    monotonicity. For finite V and any strategy-proof social choice function f onto A, Nisan's \
    extension nisanSWF (a ≤_P b ↔ f (P.toTopSet {a, b}) = a, Definition 9.9) defines an \
    antisymmetric weak ranking (equivalently strict Ranking A via nisanRanking, Lemma 9.10) \
    satisfying weak Pareto (under [Nonempty V] or [Nontrivial A], discharging the implicit \
    n ≥ 1 assumption when |A| = 1), IIA, and preservation of dictators (Lemma 9.11). Note that \
    Nisan's x ≺ y denotes 'y preferred to x' (Prefers y x)."

register_result "vcg-restricted-domains-and-feasible-bridge" where
  title := "Restricted-domain Groves/VCG and feasible-set bridge to single-parameter auctions"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Theorem 9.17, Lemma 9.20, and §9.3.5.1",
      locator := "§9.3.4–9.3.5.1, pp. 219–220" },
    { paper := Groves1973, theorem := unverified, locator := unverified },
    { paper := Clarke1971, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.Mechanism.groves_isDSICOn,
    Cslib.GameTheory.Mechanism.vcg_noPositiveTransfersOn,
    Cslib.GameTheory.Mechanism.vcg_isIROn,
    Cslib.GameTheory.SingleParameter.Mechanism.isDSIC_iff_isDSICOn_toMechanismOn,
    Cslib.GameTheory.SingleParameter.Mechanism.isIR_iff_isIROn_toMechanismOn,
    Cslib.GameTheory.SingleParameter.Vickrey.vcg_singleItemFeasible_allocation,
    Cslib.GameTheory.SingleParameter.Vickrey.vcg_singleItemFeasible_payment
  ]
  scope := "Direct quasilinear mechanisms on restricted valuation domains V : ι → Set (Ω → ℝ): \
    Groves mechanisms are DSIC on V whenever the outcome rule maximizes welfare on V, and VCG \
    with Clarke pivot payments (finite nonempty Ω) has nonnegative payments on V and satisfies \
    IsIROn V when valuations in V are nonnegative. SingleParameter.Mechanism.toMechanismOn \
    embeds single-parameter mechanisms whose allocations lie in X : Set (ι → ℝ) directly into \
    Mechanism ι X with IsDSICOn / IsIROn equivalences on Mechanism.linearDomain Subtype.val \
    (assuming each bidder has some outcome in X with nonzero coordinate), and specializing \
    Mechanism.vcg to Vickrey.singleItemFeasible recovers Vickrey.mechanism on nonnegative bids."

register_result "randomized-mechanisms-universal-vs-expectation" where
  title := "Universal truthfulness implies truthfulness in expectation, and separation on Bool"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Definition 9.38 and §9.5.6",
      locator := "§9.5.6, pp. 231–232" }
  ]
  theorems := [
    RandomizedMechanism.IsUniversallyDSICOn.isTruthfulInExpectationOn,
    RandomizedMechanism.IsUniversallyDSICOn.isTruthfulInExpectationOn_of_support_finite,
    RandomizedMechanism.exists_isTruthfulInExpectation_not_isUniversallyDSIC
  ]
  scope := "Randomized mechanisms modeled as PMF (Mechanism ι Ω) (discrete countable distributions \
    over deterministic direct mechanisms). Under summability of utilities across R.dist (automatic \
    for finite support or bounded utilities), universal DSIC on V implies truthfulness in \
    expectation on V. Conversely, coinFlipMechanism on Unit and Bool has support of size 2, is \
    truthful in expectation on Set.univ, and fails IsUniversallyDSICOn even on nonnegative \
    valuations."

register_result "revelation-principle-dominant" where
  title := "Dominant-strategy and ex-post-Nash revelation principles for indirect mechanisms"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Proposition 9.23, Proposition 9.25, and Corollary 9.26",
      locator := "§9.4.1–9.4.2, pp. 223–225" },
    { paper := DasguptaHammondMaskin1979, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.IncompleteInfoGame.IsExPostNash.isDominantStrategyEquilibrium_restrictRange,
    Cslib.GameTheory.IndirectMechanism.revelation_isTruthful,
    Cslib.GameTheory.IndirectMechanism.exists_truthful_of_implementsInDominantStrategies,
    Cslib.GameTheory.IndirectMechanism.revelation_isTruthful_of_isExPostNash,
    Cslib.GameTheory.IndirectMechanism.exists_truthful_of_implementsInExPostNash,
    Cslib.GameTheory.IndirectMechanism.toMechanism_isDSICOn_of_isExPostNash
  ]
  scope := "For arbitrary player, type, action, and outcome types (no finiteness assumptions \
    beyond [DecidableEq ι] for Function.update): restricting each player's action space X i to \
    Set.range (s i) turns any ex-post Nash equilibrium s into a dominant-strategy equilibrium \
    (Proposition 9.23), and composing an indirect quasilinear mechanism M with a dominant-strategy \
    or ex-post-Nash equilibrium s yields a truthful direct mechanism M.revelation s implementing \
    the same outcome rule with identical equilibrium payments (Proposition 9.25 and Corollary \
    9.26), as well as an IsDSICOn V direct Mechanism ι Ω on valuation domains."

register_result "revelation-principle-bayesian" where
  title := "Bayesian revelation principle and multi-parameter Bayes–Nash bridge"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Proposition 9.44 (and §9.6.1)",
      locator := "§9.6.1, p. 234" },
    { paper := Myerson1981, theorem := unverified, locator := unverified },
    { paper := Harsanyi1967, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.BayesianGame.isBayesNash_of_isExPostNash,
    Cslib.GameTheory.SingleParameter.Mechanism.isBayesNash_iff_toBayesianGame,
    Cslib.GameTheory.BayesianMechanism.revelation_isTruthful,
    Cslib.GameTheory.BayesianMechanism.revelation_interimPayment_eq,
    Cslib.GameTheory.BayesianMechanism.exists_truthful_of_implementsInBayesNash,
    Cslib.GameTheory.IndirectMechanism.toMechanism_isBICOn
  ]
  scope := "Finite player set [Fintype ι] [DecidableEq ι] with general measurable type spaces T i \
    and independent prior measures prior i (including discrete PMF priors via BayesianGame.ofPMF \
    and bridged to SingleParameter.Mechanism.IsBayesNash via toBayesianGame under integrability on \
    Icc 0 (h j)). Composing an indirect BayesianMechanism M with a Bayes–Nash equilibrium s yields \
    a truthful direct BayesianMechanism M.revelation s preserving priors, valuations, implemented \
    outcomes, ex-post equilibrium payments, and interim expected payments (Proposition 9.44), and \
    induces an IsBICOn μ V direct Mechanism ι Ω on valuation domains."

register_result "multi-unit-vickrey-auction" where
  title := "Multi-unit k-item (k + 1)-st price truthfulness vs (j + 1)-st price manipulability"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "§9.3.5.4 (Multiunit auctions)",
      locator := "§9.3.5.4, p. 221" },
    { paper := Vickrey1961, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.SingleParameter.MultiUnit.isWelfareMaximizing_allocation,
    Cslib.GameTheory.SingleParameter.MultiUnit.criticalBidMechanism_eq_on_nonneg,
    Cslib.GameTheory.SingleParameter.MultiUnit.mechanism_payment_eq_myersonPayment,
    Cslib.GameTheory.SingleParameter.MultiUnit.mechanism_isDSIC,
    Cslib.GameTheory.SingleParameter.MultiUnit.mechanism_isIR,
    Cslib.GameTheory.SingleParameter.MultiUnit.not_isDSIC_nextBidMechanism
  ]
  scope := "Single-minded unit-demand bidders [LinearOrder ι] [Fintype ι] competing for k \
    identical items (multiUnitFeasible k = {x | (∀ i, x i ∈ {0, 1}) ∧ ∑ i, x i ≤ k}), with ties \
    broken toward smaller indices matching Vickrey.Wins. Top-k allocation maximizes welfare on \
    nonnegative bids; charging every winner the uniform (k + 1)-st highest bid (0 when |ι| ≤ k) \
    agrees with criticalBidMechanism and myerson on nonnegative bids and is DSIC, IR, and \
    normalized, whereas charging the j-th highest bidder (1 ≤ j ≤ k) the (j + 1)-st highest bid \
    (nextBidMechanism k) fails IsDSIC whenever 2 ≤ k and 2 ≤ Fintype.card ι (tight bounds via \
    nextBidMechanism_one_eq_mechanism and nextBidMechanism_isDSIC_of_card_le_one)."
