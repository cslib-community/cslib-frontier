/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.Probability.Combinatorics.BinomialRandomGraph.EdgeConcentration
import CslibFrontier.GameTheory.Evolutionary.GraphESS

/-!
# Collected results: evolutionary game theory over graphs
-/

open Cslib.GameTheory.BimatrixGame

register_result "bollobas-random-graph-non-neighborhood" where
  title := "Non-neighborhood size bound for large vertex subsets in binomial random graphs"
  topic := "probability"
  sources := [
    { paper := Suri2007, theorem := "Theorem 29.18 (Bollobás 2001, Theorem 2.15)",
      locator := "Section 29.4.1, p. 731, and Equation (29.8), p. 732" }
  ]
  theorems := [
    SimpleGraph.binomialRandom_real_exists_large_nonNeighborhood_le,
    SimpleGraph.tendsto_binomialRandom_real_forall_nonNeighborhood_le
  ]
  scope := "Finite binomial random graphs G(V, p) (`SimpleGraph.binomialRandom`). For any finite \
    vertex type V with n = |V| ≥ 1, p : unitInterval, δ > 0, and C with 3 log n ≤ δ p n, \
    3 log (e / δ) ≤ C, and C ≤ u p, proves that the probability that there exists U : Finset V \
    with u ≤ #U whose outside non-neighborhood {x ∉ U | Disjoint (G.neighborSet x) U} has size \
    at least δ n is at most exp (-(C δ n / 3)) (sharpening the constant 1/6 in Equation (29.8) \
    to 1/3). Also proves the asymptotic Theorem 29.18 statement for #U = ⌈C n / p n⌉₊ as \
    C n * δ n * n → ∞."

register_result "suri-graph-ess-fitness-concentration" where
  title := "Uniform neighborhood fitness concentration over adversarial mutant sets in G(n, p)"
  topic := "game theory"
  sources := [
    { paper := Suri2007, theorem := "Lemma 29.17", locator := "Section 29.4.1, p. 731" }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixGame.tendsto_binomialRandom_real_forall_abnormalFitness_additive_le,
    Cslib.GameTheory.BimatrixGame.tendsto_binomialRandom_real_forall_abnormalFitness_mul_le
  ]
  scope := "Proved unconditionally (without taking Lemma 29.17 as an assumption) from \
    SimpleGraph.binomialRandom_real_exists_many_badDegree_le simultaneously over all adversarial \
    mutant sets M : Finset (Fin n) with linear incumbent and mutant shares in G(Fin n, p n) when \
    p n = Ω(1 / n ^ c) and 0 ≤ c < 1. The additive form holds for arbitrary real payoff matrices \
    with at most 4 * ⌈log n / p n⌉₊ abnormal vertices; the multiplicative (1 ± τ) form matches \
    the printed bound 24 * log n / (τ ^ 2 * p n) for strictly positive payoff matrices 0 < F.A i j \
    (which ensures positivity of the target fitnesses) and 0 < τ < 1 / 6."

register_result "suri-graph-ess-random-graphs" where
  title := "Random graphs preserve classical evolutionarily stable strategies against adversarial \
    mutations"
  topic := "game theory"
  sources := [
    { paper := Suri2007, theorem := "Theorem 29.16 and complete-graph characterization",
      locator := "Section 29.4, pp. 729–733" }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixGame.binomialRandom_infinitePi_isGraphESS,
    Cslib.GameTheory.BimatrixGame.isGraphESS_complete_iff,
    Cslib.GameTheory.BimatrixGame.IsESS.isGraphESS_complete,
    Cslib.GameTheory.BimatrixGame.IsGraphESS.isESS_of_complete,
    Cslib.GameTheory.BimatrixGame.exists_isGraphESS_complete_not_isESS
  ]
  scope := "Finite two-player bimatrix games F : BimatrixGame α α (arbitrary real payoffs) under \
    Definitions 29.13–29.15 (Contracts, IsEpsLinear, IsGraphESS) on loopless simple graphs. \
    Proves Theorem 29.16 unconditionally almost surely (`∀ᵐ`) under Measure.infinitePi (fun n => \
    G(Fin n, p n)) for p n = Ω(1 / n ^ c), c < 1, simultaneously over all mixed mutant \
    strategies t ≠ s and all adversarial ε_t-linear mutant families. Also proves the exact \
    characterization on the loopless complete-graph family {K_n}: every classical ESS is a graph \
    ESS on {K_n}, every graph ESS on {K_n} is a symmetric Nash equilibrium and a classical ESS \
    whenever no mutant ties both F(t|s) = F(s|s) and F(t|t) = F(s|t) with F(s|s) < F(s|t), and \
    exhibits the symmetric constant-column counterexample !![0, 1; 0, 1] showing that the \
    unguarded loopless converse claimed on pp. 732–733 fails."

register_result "suri-graph-ess-adversarial-survivor" where
  title := "Adversarial mutant sets can contain a mutant strictly outperforming all incumbent \
    neighbors"
  topic := "game theory"
  sources := [
    { paper := Suri2007, theorem := "Exercise 29.7", locator := "Exercises, p. 736" }
  ]
  theorems := [
    exists_game_adversarial_linear_mutant_beats_all_incumbent_neighbors,
    exists_game_adversarial_mutant_beats_all_incumbent_neighbors,
    IsESS.eventually_forall_graphFitness_lt_complete
  ]
  scope := "Witnessed by the symmetric 2 × 2 positive-payoff game survivorWitnessGame = \
    !![3, 2; 3, 1] with classical ESS ![1, 0] and mutant ![0, 1]. For any p n = Ω(1 / n ^ c) \
    (c < 1) bounded away from 1 (∃ q < 1, ∀ᶠ n, p n ≤ q), proves almost surely (`∀ᵐ`) that for \
    every ε' > 0 an adversary constructs an ε'-linear mutant family containing a mutant with at \
    least one incumbent neighbor and strictly higher fitness than all of its incumbent neighbors. \
    Also proves the unconstrained-size version (singleton mutant, cf. Vickery 1987, p. 734) w.h.p. \
    for all p n = Ω(1 / n ^ c) including p = 1, and proves via \
    IsESS.eventually_forall_graphFitness_lt_complete that bounding p away from 1 is necessary for \
    linear-size mutant sets."
