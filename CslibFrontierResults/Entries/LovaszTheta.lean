/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.LovaszTheta
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Pentagon
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.OddCycle

/-!
# Collected results: Lovász theta function, Shannon capacity of C₅, and odd cycles
-/

register_result "lovasz-theta-sandwich" where
  title := "Sandwich theorem: α(G) ≤ ϑ(G) ≤ χ(Gᶜ)"
  topic := "extremal combinatorics"
  sources := [
    { paper := Knuth1994, theorem := "Sandwich inequality (4.9)",
      locator := "arXiv:math/9312214, §4, display (4.9) (with §1 Lemma (1.1) and §5 (5.2))" }
  ]
  theorems := [
    SimpleGraph.indepNum_le_lovaszTheta,
    SimpleGraph.lovaszTheta_le_chromaticNumber_compl,
    SimpleGraph.lovaszTheta_le_of_cliqueCover
  ]
  scope := "Any finite simple graph G : SimpleGraph V with [Finite V], where lovaszTheta G is the \
    unweighted infimum inf_{u, c} max_v 1 / ⟪c, u v⟫² over finite-dimensional orthonormal \
    representations u (orthogonal on distinct nonadjacent vertices) and unit handles c. The \
    fractional clique cover number κ(G) between ϑ(G) and χ(Gᶜ) in (4.9) is not defined here, and \
    polynomial-time computability of ϑ via semidefinite programming / ellipsoid is open (#2998)."

register_result "lovasz-theta-shannon-bound" where
  title := "Lovász's upper bound on Shannon capacity: Θ(G) ≤ ϑ(G)"
  topic := "extremal combinatorics"
  sources := [
    { paper := Lovasz1979Shannon, theorem := unverified, locator := unverified }
  ]
  theorems := [SimpleGraph.shannonCapacity_le_lovaszTheta]
  scope := "Any finite simple graph G : SimpleGraph V with [Finite V], where shannonCapacity G = \
    ⨆ k, α(G.strongPow (k + 1))^(1/(k + 1)) equals lim α(Gᵏ)^(1/k) by Fekete's lemma \
    (SimpleGraph.tendsto_shannonCapacity). Proved via submultiplicativity \
    lovaszTheta_strongProd_le (the upper half of Knuth1994 §20 (20.5)); exact multiplicativity \
    ϑ(G ⊠ H) = ϑ(G) ϑ(H) and SDP/eigenvalue characterizations remain open (#2998)."

register_result "lovasz-theta-complement-product" where
  title := "Complement lower bound: |V| ≤ ϑ(G) ϑ(Gᶜ)"
  topic := "extremal combinatorics"
  sources := [
    { paper := Knuth1994, theorem := "Lemma 23, display (23.2) (unit weights)",
      locator := "arXiv:math/9312214, §23, display (23.2) with w = w' = 1" }
  ]
  theorems := [SimpleGraph.natCard_le_lovaszTheta_mul_lovaszTheta_compl]
  scope := "Any finite simple graph G : SimpleGraph V with [Finite V], unweighted case w = w' = 1 \
    of Knuth1994 (23.2). Proved without semidefinite duality from the diagonal independent set \
    |V| ≤ α(G ⊠ Gᶜ) (SimpleGraph.natCard_le_indepNum_strongProd_compl), indepNum_le_lovaszTheta, \
    and lovaszTheta_strongProd_le. Equality ϑ(G) ϑ(Gᶜ) = |V| for general vertex-transitive graphs \
    (Knuth1994 §25) remains open (#2998)."

register_result "lovasz-shannon-capacity-pentagon" where
  title := "The Shannon capacity and Lovász theta of the pentagon: Θ(C₅) = ϑ(C₅) = √5"
  topic := "extremal combinatorics"
  sources := [
    { paper := Lovasz1979Shannon, theorem := unverified, locator := unverified },
    { paper := Shannon1956, theorem := unverified, locator := unverified },
    { paper := Knuth1994, theorem := "§22, pentagon value ϑ(C₅) = √5",
      locator := "arXiv:math/9312214, §22, immediately following (22.12) (for ϑ(C₅) = √5)" }
  ]
  theorems := [
    SimpleGraph.shannonCapacity_cycleGraph_five,
    SimpleGraph.tendsto_indepNum_strongPow_cycleGraph_five,
    SimpleGraph.lovaszTheta_cycleGraph_five
  ]
  scope := "Unconditional exact values for SimpleGraph.cycleGraph 5 on Fin 5: lower bound √5 ≤ \
    Θ(C₅) from Shannon's five-vertex independent set {(i, 2i mod 5)} in C₅ ⊠ C₅ and upper bound \
    ϑ(C₅) ≤ √5 from Lovász's three-dimensional umbrella pentagonUmbrella."

register_result "lovasz-theta-odd-cycles" where
  title := "Exact Lovász theta of odd cycles and their complements"
  topic := "extremal combinatorics"
  sources := [
    { paper := Knuth1994, theorem := "§22, displays (22.11)–(22.12) and §23",
      locator := "arXiv:math/9312214, §22, displays (22.2)–(22.12), and §23" },
    { paper := Lovasz1979Shannon, theorem := unverified, locator := unverified }
  ]
  theorems := [
    SimpleGraph.lovaszTheta_cycleGraph_of_odd,
    SimpleGraph.lovaszTheta_compl_cycleGraph_of_odd,
    SimpleGraph.lovaszTheta_cycleGraph_mul_compl_of_odd
  ]
  scope := "All odd n ≥ 3 for SimpleGraph.cycleGraph n on Fin n: \
    ϑ(Cₙ) = n cos(π/n)/(1 + cos(π/n)), ϑ(Cₙᶜ) = (1 + cos(π/n))/cos(π/n), and \
    ϑ(Cₙ) ϑ(Cₙᶜ) = n. Proved elementarily without SDP duality via the 3D umbrella \
    oddCycleComplUmbrella for Cₙᶜ, the 2n-coordinate Fourier representation oddCycleFourier for \
    Cₙ (reindexing Knuth's (22.6)–(22.9) frequencies from π(n - 1)/n to 2πk/n), and \
    |V| ≤ ϑ(G) ϑ(Gᶜ). SimpleGraph.shannonCapacity_cycleGraph_le_of_odd follows immediately as a \
    corollary."
