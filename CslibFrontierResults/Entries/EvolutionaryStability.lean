/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Evolutionary.Basic

/-!
# Collected results: evolutionarily stable strategies
-/

register_result "suri-ess-nash-characterization" where
  title := "Evolutionarily stable strategies refine symmetric Nash equilibria"
  topic := "game theory"
  sources := [
    { paper := Suri2007, theorem := "Theorem 29.2", locator := "Section 29.1.1, p. 719" }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixGame.isESS_iff_isNash_and_forall_lt
  ]
  scope := "Finite two-player symmetric bimatrix games G : BimatrixGame α α with G.B = G.Aᵀ \
    and fitness function F(s | t) = G.payoff₁ s t. Proves that a strategy s : α → ℝ is an \
    evolutionarily stable strategy (BimatrixGame.IsESS, Definition 29.1, with mutant-dependent \
    invasion threshold ε₀ > 0) if and only if (s, s) is a Nash equilibrium (G.IsNash s s) and \
    every best response t ≠ s to s satisfies G.payoff₁ t t < G.payoff₁ s t. The 2×2 \
    characterizations and Hawks and Doves examples in Evolutionary.Basic are unregistered; \
    Section 29.2 clique hardness (Theorems 29.8–29.9) is registered separately in \
    EvolutionaryCliqueHardness, while Section 29.3 routing dynamics (Theorem 29.12) and \
    Section 29.4 graphical ESS (Theorem 29.16) remain open under #7789."
