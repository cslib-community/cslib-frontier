/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.ResourceAllocation.KellyMechanism
import CslibFrontier.GameTheory.ResourceAllocation.SSVCG

/-!
# Collected results: Kelly proportional allocation and SSVCG mechanisms (NRTV Ch. 21)

Registers the headline theorems of Chapter 21 of Nisan–Roughgarden–Tardos–Vazirani ([Johari2007])
and Johari–Tsitsiklis ([JohariTsitsiklis2004]) / Kelly ([Kelly1997]) formalized in
`CslibFrontier.GameTheory.ResourceAllocation.KellyMechanism` and
`CslibFrontier.GameTheory.ResourceAllocation.SSVCG`.
-/

section
open Cslib.GameTheory

register_result "kelly-competitive-equilibrium-welfare" where
  title := "Existence and welfare optimality of Kelly price-taking competitive equilibrium"
  topic := "algorithmic game theory"
  sources := [
    { paper := Johari2007,
      theorem := "Theorem 21.1",
      locator := "Chapter 21, §21.2 (pp. 543–568)" },
    { paper := Kelly1997,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    KellyGame.IsCompetitiveEquilibrium.isSocialOptimum,
    KellyGame.exists_isCompetitiveEquilibrium,
    KellyGame.existsUnique_isCompetitiveEquilibrium_of_strictConcaveOn
  ]
  scope := "Single infinitely divisible resource of positive capacity C > 0 shared among a finite \
    nonempty user set ι. KellyGame.IsCompetitiveEquilibrium.isSocialOptimum proves the First \
    Welfare Theorem for every price-taking competitive equilibrium without concavity or \
    differentiability assumptions. KellyGame.exists_isCompetitiveEquilibrium proves existence of \
    a competitive equilibrium (w, μ) whose allocation solves SYSTEM under IsAdmissibleUtility \
    (concave, strictly increasing, differentiable within [0, ∞), matching Assumption 1 of \
    [Johari2007] §21.2; C¹ continuity on (0, ∞) is automatic for differentiable concave \
    functions). KellyGame.existsUnique_isCompetitiveEquilibrium_of_strictConcaveOn establishes \
    uniqueness when utilities are strictly concave on [0, ∞)."

register_result "kelly-nash-existence-uniqueness-game" where
  title := "Existence, uniqueness, GAME potential, and variational inequality for Kelly Nash \
    equilibria"
  topic := "algorithmic game theory"
  sources := [
    { paper := Johari2007,
      theorem := "Theorem 21.2 and Corollary 21.3",
      locator := "Chapter 21, §21.2 (pp. 543–568)" },
    { paper := JohariTsitsiklis2004,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    KellyGame.existsUnique_isNashEquilibrium,
    KellyGame.IsNashEquilibrium.variational_inequality
  ]
  scope := "Single divisible resource of positive capacity C > 0 with at least two users \
    (2 ≤ Fintype.card ι) and admissible utilities IsAdmissibleUtility (Assumption 1 of \
    [Johari2007] §21.2). KellyGame.existsUnique_isNashEquilibrium proves existence and uniqueness \
    of the price-anticipating Nash equilibrium w and shows its allocation d = G.allocation w \
    uniquely maximizes the strictly concave GAME objective ∑_i Û_i(d_i) where \
    Û_i(x) = (1 - x / C) U_i(x) + (1 / C) ∫_0^x U_i(z) dz. \
    KellyGame.IsNashEquilibrium.variational_inequality establishes the corresponding variational \
    inequality ∑_i U_i'(d_i) (1 - d_i / C) (x_i - d_i) ≤ 0 for all feasible x. Single-link model \
    only; multi-link network extensions are not included."

register_result "johari-tsitsiklis-kelly-three-fourths-efficiency" where
  title := "Johari–Tsitsiklis 3/4 worst-case efficiency guarantee and tightness for Kelly's \
    proportional allocation mechanism"
  topic := "algorithmic game theory"
  sources := [
    { paper := Johari2007,
      theorem := "Theorem 21.4",
      locator := "Chapter 21, §21.2 (pp. 543–568)" },
    { paper := JohariTsitsiklis2004,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    KellyGame.IsNashEquilibrium.three_fourths_welfare_le,
    KellyGame.exists_nash_welfare_lt_three_fourths_add
  ]
  scope := "Single divisible resource of positive capacity C > 0 with finite user set ι and \
    admissible utilities IsAdmissibleUtility satisfying U_i(0) ≥ 0. \
    KellyGame.IsNashEquilibrium.three_fourths_welfare_le proves 3 / 4 * G.welfare x ≤ \
    G.welfare (G.allocation w) for every Nash equilibrium w and every feasible allocation x \
    (inefficiency ratio at most 4/3). KellyGame.exists_nash_welfare_lt_three_fourths_add proves \
    tightness to within every ε > 0 using the explicit (n + 1)-user linear-utility family \
    kellyTightGame n whose unique Nash equilibrium attains welfare 3/4 + 1 / (4 (2 n - 1)) \
    against optimal welfare 1. Single-link model only; general network routing extensions are not \
    included."

register_result "ssvcg-nash-characterization-and-efficiency" where
  title := "Scalar Strategy VCG Nash characterization, efficient equilibrium existence, bluff \
    equilibrium, and full efficiency under infinite initial slope"
  topic := "algorithmic game theory"
  sources := [
    { paper := Johari2007,
      theorem := "Lemma 21.11, Corollary 21.12, Example 21.13, and Proposition 21.14",
      locator := "Chapter 21, §21.4 (pp. 543–568)" }
  ]
  theorems := [
    SSVCGMechanism.isNashEquilibrium_iff,
    SSVCGMechanism.exists_efficient_isNashEquilibrium,
    exists_bluff_isNashEquilibrium,
    SSVCGMechanism.isSocialOptimum_of_isNashEquilibrium_of_infiniteSlope
  ]
  scope := "Single divisible resource of positive capacity C > 0 with an admissible \
    single-parameter surrogate family IsSSVCGSurrogateFamily (Assumption 2 of [Johari2007] \
    §21.4). SSVCGMechanism.isNashEquilibrium_iff characterizes Nash equilibria via unilateral \
    hybrid welfare maximization; SSVCGMechanism.exists_efficient_isNashEquilibrium establishes \
    PoS = 1 for admissible utilities; exists_bluff_isNashEquilibrium exhibits a concrete 2-user \
    inefficient bluff Nash equilibrium on U(x) = log (1 + x); and \
    SSVCGMechanism.isSocialOptimum_of_isNashEquilibrium_of_infiniteSlope proves PoA = 1 whenever \
    all users satisfy HasInfiniteInitialSlope (U_i'(x) → +∞ as x → 0⁺)."

end
