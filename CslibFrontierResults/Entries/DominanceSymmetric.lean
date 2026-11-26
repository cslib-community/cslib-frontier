/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Strategic.ApproxNash
import CslibFrontier.GameTheory.Strategic.Correlated
import CslibFrontier.GameTheory.Strategic.Dominance
import CslibFrontier.GameTheory.Strategic.Symmetric

/-!
# Collected results: strategic dominance, approximate Nash equilibria, and symmetric games
-/

namespace CslibFrontierResults.Entries.DominanceSymmetric

register_result "nash-symmetric-existence" where
  title := "Symmetric mixed Nash equilibrium existence for finite player-symmetric games"
  topic := "game theory"
  sources := [
    { paper := Nash1951, theorem := "Theorem 2", locator := "p. 289" },
    { paper := Papadimitriou2007, theorem := unverified,
      locator := "Example 2.2, pp. 30–31, and Section 2.3.1, p. 34" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.IsSymmetric.exists_isSymmetricMixedNash
  ]
  scope := "Specializes the full game-automorphism invariance of Nash (1951), Theorem 2, \
    printed p. 289 to interchangeable players on a common nonempty finite action type A: \
    finite n-player cost-minimization games whose costs satisfy G.cost i (s ∘ π) = \
    G.cost (π i) s for every player permutation π admit a mixed strategy x : A → ℝ whose \
    constant profile (fun _ => x) is a mixed Nash equilibrium. Proved nonconstructively via \
    Brouwer's fixed-point theorem applied to CostGame.nashMap on a single simplex (handling \
    empty player sets directly). The two-player bimatrix specialization \
    BimatrixGame.IsSymmetric.exists_isSymmetricNash in Bimatrix/Symmetric.lean follows directly \
    via toSymmCostGame (not duplicated as a separate entry because register_result requires a \
    single defining module)."

register_result "small-support-approx-nash" where
  title := "Existence of uniform-multiset small-support ε-approximate Nash equilibria"
  topic := "game theory"
  sources := [
    { paper := TardosVazirani2007, theorem := "Exercise 1.6", locator := "p. 27" }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixGame.exists_uniformMultiset_isApproxNash_of_lt,
    Cslib.GameTheory.BimatrixGame.exists_uniformMultiset_isApproxNash,
    Cslib.GameTheory.BimatrixGame.exists_uniformMultiset_isApproxNash_of_nonneg
  ]
  scope := "Game-theoretic small-support existence with an explicit sample size (no machine \
    running-time claim). For any finite nonempty rectangular bimatrix game G : BimatrixGame M N \
    with payoffs in [0, 1] and any ε > 0, proves that for every integer \
    k > 2 ln(2(|M| + |N|)) / ε² — and concretely at \
    k = lmmSampleSize M N ε = ⌊2 ln(2(|M| + |N|)) / ε²⌋₊ + 1 — there exist multisets \
    m₁ : Multiset M and m₂ : Multiset N of size k whose uniform distributions (uniformMultiset) \
    form an additive ε-approximate Nash equilibrium. Scaling unnormalized nonnegative payoffs \
    in [0, K] (K ≥ 0) yields an (ε * K)-approximate Nash equilibrium at the same multiset size, \
    matching Exercise 1.6's payoff convention directly. Proved by independent k-sample Hoeffding \
    concentration (pi_sum_abs_sub_mean_ge_card_mul) around an exact Nash equilibrium following \
    the sampling argument of Lipton, Markakis, and Mehta (2003), Section 3 (whose Theorem 1 \
    starts from each specified exact Nash equilibrium and also approximates both of its payoffs; \
    see also Papadimitriou 2007, Section 2.6.6, p. 45)."

register_result "dmp-half-nash" where
  title := "Daskalakis–Mehta–Papadimitriou 1/2-approximate Nash equilibrium theorem"
  topic := "game theory"
  sources := [
    { paper := DaskalakisMehtaPapadimitriou2006, theorem := "Theorem 1",
      locator := "Section 3" },
    { paper := Papadimitriou2007, theorem := unverified,
      locator := "Section 2.6.6, p. 45" }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixGame.isApproxNash_half_dmp,
    Cslib.GameTheory.BimatrixGame.exists_dmp_half_isApproxNash
  ]
  scope := "Covers the game-theoretic additive 1/2 output and existence guarantee of \
    Daskalakis, Mehta, and Papadimitriou (2006), Section 3, Theorem 1 (without machine running \
    time), using the same two successive pure best responses and [0, 1] payoffs: for any finite \
    bimatrix game with payoffs in [0, 1], any pure row i₀, any pure best response j₀ of \
    player 2 to i₀, and any pure best response i₁ of player 1 to j₀, the pair \
    ((1/2) e_{i₀} + (1/2) e_{i₁}, e_{j₀}) is an additive (1/2)-approximate Nash equilibrium. \
    Papadimitriou (2007), Section 2.6.6, p. 45 cites the (1/2)-approximate existence result \
    without printing the explicit two-step construction."

register_result "dominant-strategy-equilibrium" where
  title := "Dominant-strategy equilibria are pure Nash equilibria and strictly dominant \
    equilibria are unique"
  topic := "game theory"
  sources := [
    { paper := TardosVazirani2007, theorem := unverified,
      locator := "Sections 1.3.1–1.3.3, pp. 10–12" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.IsDominantEquilibrium.isPureNash,
    Cslib.GameTheory.CostGame.IsStrictlyDominantEquilibrium.eq_of_isPureNash
  ]
  scope := "Strategic cost-minimization games: Tardos and Vazirani (2007), Sections 1.3.1–1.3.3, \
    pp. 10–12 define dominant-strategy solutions and pure Nash equilibria and state that every \
    dominant-strategy equilibrium is a pure Nash equilibrium (IsDominantEquilibrium.isPureNash) \
    and that every strictly dominant equilibrium is the unique pure Nash equilibrium \
    (IsStrictlyDominantEquilibrium.eq_of_isPureNash). The companion mixed-support and \
    iterated-deletion theorems in Strategic/Dominance.lean — zero mixed-Nash weight on strictly \
    dominated strategies (IsMixedNash.eq_zero_of_isStrictlyDominated), mixed-Nash uniqueness of \
    strictly dominant equilibria (IsStrictlyDominantEquilibrium.eq_single_of_isMixedNash), and \
    bidirectional pure and mixed Nash equilibrium preservation under subset restriction and \
    iterated deletion of strictly dominated strategies (isPureNash_iff_restrict, \
    isMixedNash_iff_restrict, IDoSDS.isPureNash_iff, IDoSDS.isMixedNash_iff_restrict, \
    IDoSDS.isPureNash_iff_eq_of_singleton, IDoSDS.isMixedNash_iff_eq_single_of_singleton, where \
    each IDoSDSStep requires every removed strategy to be strictly dominated in the restricted \
    game by a surviving pure strategy in B i) — are derived library extensions not stated in \
    Sections 1.3.1–1.3.3 and are left unregistered."

register_result "swap-regret-dominated-decay" where
  title := "Swap regret bounds the time-averaged weight on ε-strictly dominated actions"
  topic := "game theory"
  sources := [
    { paper := BlumMansour2007AGT, theorem := "Theorem 4.13",
      locator := "Section 4.4.4, pp. 91–92" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.timeAverage_weight_isEpsStrictlyDominatedMixed_set_le,
    Cslib.GameTheory.CostGame.timeAverage_weight_isEpsStrictlyDominatedMixed_le
  ]
  scope := "Finite cost-minimization games over a horizon T > 0: if every player plays mixed \
    strategies p t and player i has swap regret at most R against its realized deviationCost \
    sequence, then the time-averaged probability mass player i places on any set D of \
    ε-strictly dominated actions (ε > 0, dominated by mixed — and hence in particular pure — \
    strategies) — and in particular on any single ε-strictly dominated action — is at most \
    R / (ε * T)."

register_result "correlated-equilibrium-convexity" where
  title := "Convexity of correlated equilibria and convex combinations of Nash equilibria"
  topic := "game theory"
  sources := [
    { paper := TardosVazirani2007, theorem := unverified,
      locator := "Section 1.3.6, pp. 14–15" },
    { paper := Papadimitriou2007, theorem := unverified,
      locator := "Section 2.7, pp. 45–47" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.IsCorrelatedEquilibrium.convexCombPair,
    Cslib.GameTheory.CostGame.isConvexSet_isCorrelatedEquilibrium,
    Cslib.GameTheory.CostGame.isCorrelatedEquilibrium_iConvexComb_mixedNash,
    Cslib.GameTheory.CostGame.convex_correlatedEquilibriumPolytope
  ]
  scope := "Strategic cost-minimization games: {σ | G.IsCorrelatedEquilibrium σ} is convex in \
    Convexity.StdSimplex ℝ (∀ i, S i) (and Convex ℝ in probability-vector coordinates on finite \
    games), so binary and arbitrary finitely supported convex combinations of correlated \
    equilibria — and of mixed Nash product distributions — are correlated equilibria."

end CslibFrontierResults.Entries.DominanceSymmetric
