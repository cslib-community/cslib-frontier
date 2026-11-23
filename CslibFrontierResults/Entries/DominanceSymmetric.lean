/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Bimatrix.Symmetric
import CslibFrontier.GameTheory.Strategic.ApproxNash
import CslibFrontier.GameTheory.Strategic.Dominance
import CslibFrontier.GameTheory.Strategic.Symmetric

/-!
# Collected results: strategic dominance, approximate Nash equilibria, and symmetric games
-/

namespace CslibFrontierResults.Entries.DominanceSymmetric

register_result "nash-symmetric-existence" where
  title := "Nash's symmetric equilibrium theorem for finite symmetric games"
  topic := "game theory"
  sources := [
    { paper := Nash1951, theorem := unverified, locator := unverified },
    { paper := Papadimitriou2007, theorem := unverified,
      locator := "Example 2.2, pp. 30–31, and Section 2.3.1, p. 34" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.IsSymmetric.exists_isSymmetricMixedNash
  ]
  scope := "Finite n-player cost-minimization games sharing a common nonempty finite strategy type \
    A whose costs satisfy G.cost i (s ∘ π) = G.cost (π i) s for every player permutation π. \
    Establishes existence of a single mixed strategy x : A → ℝ whose constant profile (fun _ => x) \
    is a mixed Nash equilibrium, proved via Brouwer's fixed-point theorem on a single simplex \
    (handling empty player sets directly). Nonconstructive."

register_result "nash-symmetric-existence-bimatrix" where
  title := "Every finite nonempty symmetric bimatrix game has a symmetric Nash equilibrium"
  topic := "game theory"
  sources := [
    { paper := Nash1951, theorem := unverified, locator := unverified },
    { paper := Papadimitriou2007, theorem := unverified,
      locator := "Example 2.2, pp. 30–31, and Section 2.3.1, p. 34" }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixGame.IsSymmetric.exists_isSymmetricNash
  ]
  scope := "Two-player bimatrix payoff games G : BimatrixGame M M with G.B = G.Aᵀ on a finite \
    nonempty strategy type M; derived from CostGame.IsSymmetric.exists_isSymmetricMixedNash via \
    the shared-strategy embedding toSymmCostGame."

register_result "gale-kuhn-tucker-symmetric-nash" where
  title := "Reduction from general two-player Nash equilibrium to symmetric Nash equilibrium"
  topic := "game theory"
  sources := [
    { paper := Papadimitriou2007, theorem := "Theorem 2.4",
      locator := "Section 2.3.1, p. 34" },
    { paper := GaleKuhnTucker1950, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixGame.symmReduction_pos_and_isNash,
    Cslib.GameTheory.BimatrixGame.isSymmetricNash_symmReduction_of_isNash,
    Cslib.GameTheory.BimatrixGame.exists_addConst_symmReduction,
    Cslib.GameTheory.BimatrixGame.gktGame_isNash_proj,
    Cslib.GameTheory.BimatrixGame.gktGame_unit_eq_zero,
    Cslib.GameTheory.BimatrixGame.gktGame_recovery
  ]
  scope := "Covers both Papadimitriou's two-block symmetrization symmReduction G = \
    ofSymmetric [[0, A], [Bᵀ, 0]] on M ⊕ N (proving a two-way correspondence between Nash \
    equilibria of G and symmetric Nash equilibria of symmReduction G whenever A > 0 and B > 0, \
    plus a uniform constant-shift corollary for arbitrary-sign finite games via addConst) \
    and the three-block Gale–Kuhn–Tucker game gktGame G = ofSymmetric [[0, A, -1], [Bᵀ, 0, 1], \
    [1, -1, 0]] on M ⊕ N ⊕ Unit (proving positive M and N block masses and Nash equilibrium \
    recovery of normalized projections whenever A > 0 and B > 0, plus zero weight on Unit under \
    1 ≤ B, which is sharp as witnessed by A = [[100]], B = [[1/10]]). Mathematical reduction \
    between equilibrium sets; polynomial-time Turing/PPAD encoding is not claimed here."

register_result "lipton-markakis-mehta-approx-nash" where
  title := "Lipton–Markakis–Mehta uniform-multiset ε-approximate Nash equilibrium theorem"
  topic := "game theory"
  sources := [
    { paper := TardosVazirani2007, theorem := "Exercise 1.6", locator := "p. 27" },
    { paper := Papadimitriou2007, theorem := unverified,
      locator := "Section 2.6.6, p. 45" },
    { paper := LiptonMarkakisMehta2003, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixGame.exists_uniformMultiset_isApproxNash_of_lt,
    Cslib.GameTheory.BimatrixGame.exists_uniformMultiset_isApproxNash,
    Cslib.GameTheory.BimatrixGame.exists_uniformMultiset_isApproxNash_of_nonneg
  ]
  scope := "For any finite nonempty bimatrix game G : BimatrixGame M N with payoffs in [0, 1] \
    and any ε > 0, proves that for every integer k > 2 ln(2(|M| + |N|)) / ε² — and concretely at \
    k = lmmSampleSize M N ε = ⌊2 ln(2(|M| + |N|)) / ε²⌋₊ + 1 — there exist multisets \
    m₁ : Multiset M and m₂ : Multiset N of size k whose uniform distributions (uniformMultiset) \
    form an additive ε-approximate Nash equilibrium. For unnormalized nonnegative payoffs in \
    [0, K] (K ≥ 0), scaling yields an (ε * K)-approximate Nash equilibrium at the same multiset \
    size, matching Exercise 1.6 directly. Proved by independent k-sample Hoeffding concentration \
    (pi_sum_abs_sub_mean_ge) around an exact Nash equilibrium."

register_result "dmp-half-nash" where
  title := "Daskalakis–Mehta–Papadimitriou 1/2-approximate Nash equilibrium theorem"
  topic := "game theory"
  sources := [
    { paper := Papadimitriou2007, theorem := unverified,
      locator := "Section 2.6.6, p. 45" },
    { paper := DaskalakisMehtaPapadimitriou2006, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixGame.isApproxNash_half_dmp,
    Cslib.GameTheory.BimatrixGame.exists_dmp_half_isApproxNash
  ]
  scope := "For any finite bimatrix game with payoffs in [0, 1], any pure row i₀, any pure best \
    response j₀ of player 2 to i₀, and any pure best response i₁ of player 1 to j₀, the pair \
    ((1/2) e_{i₀} + (1/2) e_{i₁}, e_{j₀}) is an additive (1/2)-approximate Nash equilibrium."

register_result "iterated-strict-dominance" where
  title := "Dominant strategies and iterated deletion of strictly dominated strategies"
  topic := "game theory"
  sources := [
    { paper := TardosVazirani2007, theorem := unverified,
      locator := "Sections 1.3.1–1.3.3, pp. 10–12" },
    { paper := DodisRabin2007, theorem := "Definition 8.8",
      locator := "Section 8.5.2, p. 200" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.IsDominantEquilibrium.isPureNash,
    Cslib.GameTheory.CostGame.IsStrictlyDominantEquilibrium.eq_of_isPureNash,
    Cslib.GameTheory.CostGame.IsStrictlyDominantEquilibrium.eq_single_of_isMixedNash,
    Cslib.GameTheory.CostGame.IsMixedNash.eq_zero_of_isStrictlyDominated,
    Cslib.GameTheory.CostGame.isPureNash_iff_restrict,
    Cslib.GameTheory.CostGame.isMixedNash_iff_restrict,
    Cslib.GameTheory.CostGame.IDoSDS.isPureNash_iff,
    Cslib.GameTheory.CostGame.IDoSDS.isMixedNash_iff_restrict,
    Cslib.GameTheory.CostGame.IDoSDS.isPureNash_iff_eq_of_singleton,
    Cslib.GameTheory.CostGame.IDoSDS.isMixedNash_iff_eq_single_of_singleton,
    Cslib.GameTheory.CostGame.idowds_idowdsSeq
  ]
  scope := "Strategic cost-minimization games: dominant equilibria are pure Nash equilibria, \
    strictly dominant equilibria are unique pure and mixed Nash equilibria, strictly dominated \
    strategies receive zero weight in every mixed Nash equilibrium, and iterated deletion of \
    strictly dominated strategies (IDoSDS) preserves both pure and mixed Nash equilibria in both \
    directions, so a singleton survivor is the unique pure and mixed Nash equilibrium. Also \
    connects the simultaneous IDoWDS sequence (Dodis–Rabin Definition 8.8) to the relational \
    order-dependent closure IDoWDS."

register_result "swap-regret-dominated-decay" where
  title := "Swap regret bounds the time-averaged weight on ε-strictly dominated actions"
  topic := "game theory"
  sources := [
    { paper := BlumMansour2007AGT, theorem := "Theorem 4.13",
      locator := "Section 4.4.4, pp. 91–92" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.timeAverage_weight_isEpsStrictlyDominatedMixed_set_le,
    Cslib.GameTheory.CostGame.timeAverage_weight_isEpsStrictlyDominatedMixed_le,
    Cslib.GameTheory.CostGame.timeAverage_weight_isEpsStrictlyDominated_set_le,
    Cslib.GameTheory.CostGame.timeAverage_weight_isEpsStrictlyDominated_le
  ]
  scope := "Finite cost-minimization games over a horizon T > 0: if every player plays mixed \
    strategies p t and player i has swap regret at most R against its realized deviationCost \
    sequence, then the time-averaged probability mass player i places on any set D of \
    ε-strictly dominated actions (ε > 0, dominated either by pure strategies or by mixed \
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
    Cslib.GameTheory.CostGame.isCorrelatedEquilibrium_iConvexComb,
    Cslib.GameTheory.CostGame.isCorrelatedEquilibrium_iConvexComb_mixedNash,
    Cslib.GameTheory.CostGame.convex_correlatedEquilibriumPolytope
  ]
  scope := "Strategic cost-minimization games: {σ | G.IsCorrelatedEquilibrium σ} is convex in \
    Convexity.StdSimplex ℝ (∀ i, S i) (and Convex ℝ in probability-vector coordinates on finite \
    games), so binary and arbitrary finitely supported convex combinations of correlated \
    equilibria — and of mixed Nash product distributions — are correlated equilibria."

end CslibFrontierResults.Entries.DominanceSymmetric
