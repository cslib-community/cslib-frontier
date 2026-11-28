/-
Copyright (c) 2026 Josh Liebow-Feeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Liebow-Feeser
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.ProofSystem.Optimal

/-!
# Collected results: optimal and p-optimal proof systems
-/

register_result "krajicek-pudlak-optimal-proof-system-np-subsets" where
  title := "Optimal proof systems simulate all proof systems and have polynomial proofs on every \
    NP subset"
  topic := "proof complexity"
  sources := [
    { paper := KrajicekPudlak1989,
      theorem := "§0 (common lower bound, optimality, NP = coNP) and Theorem 2.1(i), (2) → (3)",
      locator := "Journal of Symbolic Logic 54(3), 1989, §0 printed p. 1063, §1 pp. 1065–1066, \
        §2 Statements (2), (3), (7) and Theorem 2.1(i)–(ii) printed pp. 1066–1067 \
        (author scan https://karlin.mff.cuni.cz/~krajicek/scan10.pdf, PDF pp. 1, 3–5)" }
  ]
  theorems := [
    Cslib.Complexity.ProofSystem.pSimulates_join_iff,
    Cslib.Complexity.ProofSystem.simulates_join_iff,
    Cslib.Complexity.ProofSystem.IsPOptimal.isOptimal,
    Cslib.Complexity.ProofSystem.PolynomiallyBounded.isOptimal,
    Cslib.Complexity.ProofSystem.IsOptimal.polynomiallyBounded_UNSAT_iff_NP_eq_coNP,
    Cslib.Complexity.ProofSystem.IsOptimal.polyBounded_on_NP_subset,
    Cslib.Complexity.ProofSystem.exists_isOptimal_UNSAT_of_NP_eq_coNP
  ]
  scope := "Formalizes optimal (IsOptimal) and p-optimal (IsPOptimal) Cook–Reckhow proof systems \
    for arbitrary sets L with binary encoding enc : α ↪ List Bool, reusing \
    Cslib.Complexity.ProofSystem.Simulates and PSimulates. Simulation direction: Krajíček–Pudlák \
    write P ≤ Q for 'P simulates Q' (optimal = least element; common lower bound of two systems), \
    whereas Simulates / PSimulates place the simulating system on the left, so join is a binary \
    upper bound and optimal systems are greatest elements. Propositional statements use UNSAT \
    refutations (encCNF) rather than TAUT, matching \
    ProofSystem.NP_eq_coNP_iff_exists_polynomiallyBounded. polyBounded_on_NP_subset formalizes \
    only the forward direction (2) → (3) of Theorem 2.1(i) (every NP subset X ⊆ L has \
    polynomially bounded P-proofs, assuming a Decoder enc); the converse (3) → (2) via padding is \
    not included. Unconditional existence of an optimal or p-optimal proof system for UNSAT is \
    open and not claimed; conditional existence is proved for nonempty decodable NP sets (hence \
    UNSAT under NP = coNP) and p-optimal existence for nonempty decodable sets in P."
