/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Mechanism.Indirect
import CslibFrontier.GameTheory.Mechanism.VCG
import CslibFrontier.GameTheory.SocialChoice.GibbardSatterthwaiteReduction

/-!
# Collected results: VCG on restricted domains, Gibbard–Satterthwaite, and revelation principles
-/

open Cslib.GameTheory

register_result "gibbard-satterthwaite-single-monotonicity" where
  title := "Single-voter monotonicity is equivalent to strategy-proofness"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Proposition 9.6",
      locator := "§9.2.4, p. 214" }
  ]
  theorems := [
    SocialChoice.SocialChoiceFunction.isSingleMonotone_iff_isStrategyProof,
    SocialChoice.SocialChoiceFunction.isSingleMonotone_iff_isMaskinMonotone
  ]
  scope := "Proposition 9.6 proves that single-voter monotonicity (Definition 9.5) is equivalent \
    to strategy-proofness (incentive compatibility) on arbitrary voter and alternative types \
    (isSingleMonotone_iff_isStrategyProof); isSingleMonotone_iff_isMaskinMonotone is a derived \
    finite-electorate [Finite V] corollary composing Proposition 9.6 with the library's \
    isStrategyProof_iff_isMaskinMonotone. Note that Nisan's x ≺ y denotes 'y preferred to x' \
    (Prefers y x)."

register_result "gibbard-satterthwaite-nisan-swf-order" where
  title := "Nisan's pairwise-top extension defines a strict social welfare function"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Lemma 9.10",
      locator := "§9.2.4, p. 215" }
  ]
  theorems := [
    SocialChoice.SocialChoiceFunction.nisanSWF_antisymm,
    SocialChoice.SocialChoiceFunction.toWeakRanking_nisanRanking
  ]
  scope := "For finite V and any strategy-proof social choice function f onto A, Nisan's \
    extension nisanSWF (a ≽_P b ↔ f (P.toTopSet {a, b}) = a, Definition 9.9) defines a total, \
    transitive, antisymmetric weak ranking—equivalently a strict Ranking A via nisanRanking."

register_result "gibbard-satterthwaite-nisan-swf-properties" where
  title := "Nisan's induced social welfare function is Pareto, IIA, and preserves dictators"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Lemma 9.11",
      locator := "§9.2.4, p. 215" }
  ]
  theorems := [
    SocialChoice.SocialChoiceFunction.nisanSWF_isPareto,
    SocialChoice.SocialChoiceFunction.nisanSWF_isPareto_of_nontrivial,
    SocialChoice.SocialChoiceFunction.nisanSWF_isIIA,
    SocialChoice.SocialChoiceFunction.nisanSWF_isDictator_iff,
    SocialChoice.SocialChoiceFunction.nisanSWF_isDictatorial_iff
  ]
  scope := "For finite V and any strategy-proof social choice function f onto A, Nisan's \
    extension nisanSWF (a ≽_P b ↔ f (P.toTopSet {a, b}) = a, Definition 9.9) satisfies \
    unanimity / weak Pareto (under [Nonempty V] or [Nontrivial A], discharging the source's \
    implicit n ≥ 1 assumption when |A| = 1) and independence of irrelevant alternatives. \
    Where Lemma 9.11 concludes non-dictatorship of F given non-dictatorship of f (using one \
    direction), nisanSWF_isDictator_iff and nisanSWF_isDictatorial_iff give the strengthening \
    to a full equivalence (↔) between dictators of nisanSWF and dictators of f."

register_result "vcg-groves-dsic-restricted-domain" where
  title := "Groves and VCG mechanisms are DSIC on restricted valuation domains"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Theorem 9.17",
      locator := "§9.3.3, p. 219" },
    { paper := Groves1973, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.Mechanism.groves_isDSICOn,
    Cslib.GameTheory.Mechanism.vcg_isDSICOn
  ]
  scope := "Direct quasilinear mechanisms on restricted valuation domains V : ι → Set (Ω → ℝ) \
    with finitely many agents [Fintype ι] [DecidableEq ι]: any Groves mechanism whose outcome \
    rule maximizes reported welfare on V and whose pivots are independent of agent i's report on \
    V is dominant-strategy incentive compatible on V (IsDSICOn V), in particular VCG with Clarke \
    pivot payments on a finite nonempty outcome type Ω."

register_result "vcg-clarke-pivot-properties-restricted-domain" where
  title := "VCG with Clarke pivot makes no positive transfers and is individually rational on \
    nonnegative domains"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Lemma 9.20",
      locator := "§9.3.4, pp. 219–220" },
    { paper := Clarke1971, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.Mechanism.vcg_noPositiveTransfersOn,
    Cslib.GameTheory.Mechanism.vcg_isIROn
  ]
  scope := "For finite agents [Fintype ι] [DecidableEq ι] and finite nonempty outcomes Ω, VCG \
    with Clarke pivot payments makes no positive transfers on every domain V \
    (NoPositiveTransfersOn V), and whenever the outcome rule maximizes welfare on V and every \
    valuation in every V i is nonnegative, VCG is ex-post individually rational on V (IsIROn V)."

register_result "revelation-principle-restrict-range" where
  title := "Restricting action spaces to equilibrium ranges turns ex-post Nash into dominant \
    strategies"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Proposition 9.23",
      locator := "§9.4.1, p. 223" }
  ]
  theorems := [
    Cslib.GameTheory.IncompleteInfoGame.IsExPostNash.isDominantStrategyEquilibrium_restrictRange
  ]
  scope := "For arbitrary player, type, and action spaces (with [DecidableEq ι] for \
    Function.update): restricting each player's action space X i to Set.range (s i) turns any \
    ex-post Nash equilibrium s of an IncompleteInfoGame into a dominant-strategy equilibrium."

register_result "revelation-principle-dominant" where
  title := "Dominant-strategy revelation principle for indirect mechanisms"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Proposition 9.25",
      locator := "§9.4.3, pp. 224–225" },
    { paper := DasguptaHammondMaskin1979, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.IndirectMechanism.revelation_isTruthful,
    Cslib.GameTheory.IndirectMechanism.exists_truthful_of_implementsInDominantStrategies
  ]
  scope := "For arbitrary player, type, action, and outcome types (with [DecidableEq ι]): \
    composing an indirect quasilinear mechanism M with a dominant-strategy equilibrium s yields \
    a truthful direct mechanism M.revelation s implementing the same social choice function with \
    identical equilibrium payments."

register_result "revelation-principle-ex-post-nash" where
  title := "Ex-post-Nash revelation principle for indirect mechanisms"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Corollary 9.26",
      locator := "§9.4.3, p. 225" }
  ]
  theorems := [
    Cslib.GameTheory.IndirectMechanism.revelation_isTruthful_of_isExPostNash,
    Cslib.GameTheory.IndirectMechanism.exists_truthful_of_implementsInExPostNash,
    Cslib.GameTheory.IndirectMechanism.toMechanism_isDSICOn_of_isExPostNash
  ]
  scope := "For arbitrary player, type, action, and outcome types (with [DecidableEq ι]): \
    composing an indirect quasilinear mechanism M with an ex-post Nash equilibrium s yields a \
    truthful direct mechanism M.revelation s implementing the same social choice function with \
    identical equilibrium payments (via Proposition 9.23), and induces an IsDSICOn V direct \
    Mechanism ι Ω on valuation domains."

register_result "revelation-principle-bayesian" where
  title := "Bayesian revelation principle for indirect mechanisms"
  topic := "game theory"
  sources := [
    { paper := Nisan2007,
      theorem := "Proposition 9.44",
      locator := "§9.6.1, p. 234" },
    { paper := Myerson1981, theorem := unverified, locator := unverified },
    { paper := Harsanyi1967, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.BayesianMechanism.exists_truthful_of_implementsInBayesNash,
    Cslib.GameTheory.BayesianMechanism.revelation_integral_payment_eq
  ]
  scope := "Finite player set [Fintype ι] [DecidableEq ι] with measurable type spaces T i and \
    independent probability priors [∀ i, IsProbabilityMeasure (M.prior i)]. Under integrable \
    interim utilities (ImplementsInBayesNash, Definition 9.42), composing an indirect \
    BayesianMechanism M with an implementing Bayes–Nash equilibrium s yields a truthful direct \
    BayesianMechanism D = M.revelation s with probability priors, integrable truthful interim \
    utilities, identical implemented outcome f, identical ex-post and interim payment integrals, \
    and—whenever player i's equilibrium payment in M is product-measure integrable—integrable \
    ex-ante payment in D with identical ex-ante expected payment (equal by Fubini to the prior \
    expectation of interim payments via revelation_integral_payment_eq). All-types interim-payment \
    slice integrability is given separately in exists_truthful_hasIntegrableInterimPayment; \
    derived from the general measure-theoretic integral-preservation steps revelation_isTruthful, \
    revelation_interimPayment_eq, and IndirectMechanism.toMechanism_isBICOn."
