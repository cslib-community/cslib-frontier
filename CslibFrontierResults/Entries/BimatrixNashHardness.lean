/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Bimatrix.NashHardness

/-!
# Collected results: NP-hardness of Nash equilibrium decision problems
-/

register_result "papadimitriou-gilboa-zemel-nash-np-hardness" where
  title := "NP-hardness of six Nash equilibrium decision problems in symmetric two-player games"
  topic := "game theory"
  sources := [
    { paper := Papadimitriou2007, theorem := "Theorem 2.3", locator := "Section 2.2.2, p. 33" }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixCode.SymGameHasTwoNash_npHard,
    Cslib.GameTheory.BimatrixCode.SymGameHasNashPayoffGe_npHard,
    Cslib.GameTheory.BimatrixCode.SymGameHasNashTotalPayoffGe_npHard,
    Cslib.GameTheory.BimatrixCode.SymGameHasNashSupportGt_npHard,
    Cslib.GameTheory.BimatrixCode.SymGameHasNashSupportContains_npHard,
    Cslib.GameTheory.BimatrixCode.SymGameHasNashSupportOmits_npHard
  ]
  scope := "Explicitly presented symmetric two-player rational bimatrix games encoded on \
    BimatrixCode under encBimatrix (well-formed square games with B = Aᵀ), paired with binary \
    rational payoff thresholds (encBimatrixThresholdInstance), binary natural support-size bounds \
    (encBimatrixSupportBoundInstance), or binary natural strategy indices \
    (encBimatrixStrategyIndexInstance). Via the exact mixed Nash equilibrium classification \
    BimatrixGame.isNash_gilboaZemelGame_iff (covering symmetric and asymmetric equilibria for \
    N ≥ 2) on the Conitzer–Sandholm symmetric game for a 3-variable-padded CNF formula, proves \
    native multi-tape Turing-machine polynomial-time many-one reductions from SAT giving NPHard \
    for all six bullets of Theorem 2.3 (second Nash equilibrium, player-1 payoff lower bound, \
    total payoff lower bound, support size strictly above a bound, support containing a given \
    strategy, and support omitting a given strategy). Native multi-tape NP membership (InNP, \
    completing NP-completeness) remains open under #7789."
