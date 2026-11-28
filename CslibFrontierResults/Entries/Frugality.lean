/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Mechanism.Frugality

register_result "hartline-karlin-2007-vcg-frugality-matroid" where
  title := "Matroid characterization of VCG frugality ratio 1 and spanning-tree auctions"
  topic := "algorithmic game theory"
  sources := [
    { paper := HartlineKarlin2007,
      theorem := "Theorem 13.53 and Exercise 13.12 (Example 13.51, Definition 13.52)",
      locator := "§13.5, pp. 351–353; Exercises, p. 361" }
  ]
  theorems := [
    Cslib.GameTheory.Mechanism.Frugality.vcgTotalPay_eq_cheapestNash_of_isMatroidBaseFamily,
    Cslib.GameTheory.Mechanism.Frugality.vcg_hasFrugalityRatioLe_one_iff_isMatroidBaseFamily,
    Cslib.GameTheory.Mechanism.Frugality.isMatroidBaseFamily_iff_exists_matroid,
    Cslib.GameTheory.Mechanism.Frugality.spanningTreeFamily_isMatroidBaseFamily,
    Cslib.GameTheory.Mechanism.Frugality.vcg_spanningTree_hasFrugalityRatioLe_one
  ]
  scope := "Set-system procurement auctions on a finite agent type E ([Fintype E] [DecidableEq E]) \
    with nonempty, monopoly-free feasible family F : Finset (Finset E) and nonnegative real cost \
    profiles (0 ≤ c : E → ℝ). The pay-your-bid Nash benchmark N(c) (`cheapestNash`) is the infimum \
    of total payments over restricted pure Nash equilibria where non-winners bid truthfully and \
    ties break in favor of efficiency (Footnote 3, p. 352; exact unilateral-deviation equivalence \
    proved in `isPayYourBidNash_iff_pureNash`). Frugality ratio `HasFrugalityRatioLe` is stated in \
    multiplicative form (0 ≤ ρ ∧ ∀ c, 0 ≤ c → M.totalPay c ≤ ρ * cheapestNash F c) to avoid 0 / 0; \
    since `cheapestNash F c ≤ (vcgMechanism F hF hmono).totalPay c` always holds \
    (`cheapestNash_le_vcgTotalPay`), frugality \
    ratio ≤ 1 is equivalent to exact equality for every nonnegative cost profile. The converse of \
    Theorem 13.53 explicitly requires `IsAntichain (· ⊆ ·) F` (minimal feasible sets, matching the \
    underlying clutter setting; without it, adding a redundant superset such as `{0, 2}` to \
    `{{0}, {1}}` keeps VCG at frugality ratio 1 on nonnegative costs, witnessed in \
    `CslibFrontierTests.GameTheory.Frugality`). Exercise 13.12 applies Theorem 13.53 to the \
    spanning-tree family of any finite connected bridgeless (equivalently 2-edge-connected) simple \
    graph. No running-time claim is made."

register_result "hartline-karlin-2007-two-paths-frugality" where
  title := "Ω(√(nn')) frugality lower bound and √(nn')-frugal auction on two disjoint paths"
  topic := "algorithmic game theory"
  sources := [
    { paper := HartlineKarlin2007,
      theorem := "Theorem 13.54 and weighted path auction",
      locator := "§13.5, p. 351; §13.5.1.1, pp. 353–354" }
  ]
  theorems := [
    Cslib.GameTheory.Mechanism.Frugality.vcgTotalPay_twoDisjointPaths_zero_one,
    Cslib.GameTheory.Mechanism.Frugality.twoDisjointPaths_frugality_lower_bound,
    Cslib.GameTheory.Mechanism.Frugality.le_of_hasFrugalityRatioLe_twoDisjointPaths,
    Cslib.GameTheory.Mechanism.Frugality.sqrtWeightedPathMechanism_isDSIC,
    Cslib.GameTheory.Mechanism.Frugality.sqrtWeightedPathMechanism_isIR,
    Cslib.GameTheory.Mechanism.Frugality.sqrtWeightedPathMechanism_hasFrugalityRatioLe
  ]
  scope := "Deterministic DSIC, individually rational, losers-paid-zero procurement mechanisms on \
    the two vertex-disjoint paths set system `twoDisjointPaths n n'` of lengths n, n' ≥ 1 over \
    nonnegative real cost profiles. Theorem 13.54 is proved with the explicit constant 1 / 2 and \
    positive benchmark (`0 < cheapestNash`), yielding `(1 / 2) * √(n * n') ≤ ρ` for any frugality \
    ratio bound `ρ`. The weighted threshold auction `sqrtWeightedPathMechanism` minimizes \
    `√|P| · c(P)` and achieves frugality ratio at most `√(n * n')`, matching the lower bound \
    within a factor of 2. Only deterministic mechanisms are formalized (the book remarks on p. 353 \
    that Theorem 13.54 generalizes to randomized mechanisms). No running-time claim is made."
