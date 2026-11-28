/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Evolutionary.CliqueHardness

/-!
# Collected results: computational complexity of evolutionarily stable strategies
-/

register_result "suri-ess-clique-bound" where
  title := "Payoff upper bound and equality characterization in Nisan's clique game"
  topic := "game theory"
  sources := [
    { paper := Suri2007, theorem := "Lemma 29.3", locator := "Section 29.2, p. 721" }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixGame.payoff₁_self_cliqueESSGame_le,
    Cslib.GameTheory.BimatrixGame.payoff₁_self_cliqueESSGame_eq_iff
  ]
  scope := "Finite simple graphs G : SimpleGraph V and parameters k : ℕ in Nisan's symmetric game \
    BimatrixGame.cliqueESSGame G k on Option V (none = strategy 0, some v = vertex v). Proves \
    that every mixed strategy s with s none = 0 satisfies F(s|s) ≤ 1 - 1 / (2 * G.cliqueNum), \
    with equality iff s is the uniform distribution on a G.cliqueNum-clique. Also proves \
    Lemmas 29.4–29.7 (including Exercise 29.5) and the combined characterization that \
    cliqueESSGame G k has an ESS iff G.cliqueNum ≠ k (for 0 < k)."

register_result "suri-ess-existence-hardness" where
  title := "Deciding existence of an evolutionarily stable strategy is NP-hard and coNP-hard"
  topic := "game theory"
  sources := [
    { paper := Suri2007, theorem := "Theorem 29.8", locator := "Section 29.2, p. 723" }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixCode.SymGameHasESS_npHard,
    Cslib.GameTheory.BimatrixCode.SymGameHasESS_coNPHard
  ]
  scope := "Explicitly presented symmetric two-player rational bimatrix games encoded on \
    BimatrixCode under encBimatrix (SymGameHasESS: well-formed square games with B = Aᵀ admitting \
    an ESS). Proves native multi-tape Turing-machine polynomial-time many-one reductions \
    Clique ≤ₚ SymGameHasESS (via G ⊔ K_{k-1} with binary k capped at |V(G)|) and \
    UNSAT ≤ₚ SymGameHasESS (via the complement of Karp's SAT.toIndependentSet graph), giving both \
    NPHard and coNPHard with no uncertified efficiency hypotheses."

register_result "suri-ess-recognition-hardness" where
  title := "Recognizing whether a given strategy is evolutionarily stable is coNP-hard"
  topic := "game theory"
  sources := [
    { paper := Suri2007, theorem := "Theorem 29.9", locator := "Section 29.2, p. 723" }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixCode.SymGameIsESS_coNPHard
  ]
  scope := "Explicitly presented symmetric two-player rational bimatrix games paired with a \
    rational candidate strategy vector on SymGameStrategyInstance under \
    encSymGameStrategyInstance (SymGameIsESS: well-formed square games with B = Aᵀ and a strategy \
    list of length game.rows forming an ESS). Proves a native multi-tape Turing-machine \
    polynomial-time many-one reduction Cliqueᶜ ≤ₚ SymGameIsESS via Nisan's game with pure \
    strategy none, giving coNPHard with no uncertified efficiency hypotheses."
