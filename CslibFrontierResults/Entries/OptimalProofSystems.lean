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
  title := "Optimal proof systems exist for UNSAT iff some system is polynomially bounded on \
    every NP subset"
  topic := "proof complexity"
  sources := [
    { paper := KrajicekPudlak1989,
      theorem := "§0 (common lower bound, optimality, NP = coNP) and Theorem 2.1(i), (2) ↔ (3)",
      locator := "Journal of Symbolic Logic 54(3), 1989, §0 printed p. 1063, §1 pp. 1065–1066, \
        §2 Statements (2), (3), (7), Theorem 2.1(i), and implication diagram printed \
        pp. 1066–1067; Part 2 proofs of (2) → (3) and (3) → (5) → (4) → (1) → (2) printed \
        pp. 1070–1071 (author scan https://karlin.mff.cuni.cz/~krajicek/scan10.pdf, PDF pp. 1, \
        3–5, 8–9)" }
  ]
  theorems := [
    Cslib.Complexity.ProofSystem.join_simulates_left,
    Cslib.Complexity.ProofSystem.join_simulates_right,
    Cslib.Complexity.ProofSystem.pSimulates_join_iff,
    Cslib.Complexity.ProofSystem.simulates_join_iff,
    Cslib.Complexity.ProofSystem.IsPOptimal.isOptimal,
    Cslib.Complexity.ProofSystem.PolynomiallyBounded.isOptimal,
    Cslib.Complexity.ProofSystem.IsOptimal.polynomiallyBounded_UNSAT_iff_NP_eq_coNP,
    Cslib.Complexity.ProofSystem.IsOptimal.polyBounded_on_NP_subset,
    Cslib.Complexity.ProofSystem.exists_isOptimal_iff_of_paddable,
    Cslib.Complexity.ProofSystem.exists_isOptimal_UNSAT_iff,
    Cslib.Complexity.ProofSystem.exists_isOptimal_UNSAT_of_NP_eq_coNP
  ]
  scope := "Direct source correspondences and analogues vs. derived library facts for optimal \
    (IsOptimal) and p-optimal (IsPOptimal) Cook–Reckhow proof systems over sets L with binary \
    encoding enc : α ↪ List Bool. Direct source support: (1) join_simulates_left / \
    join_simulates_right realize the §0 (p. 1063) common-bound observation: Krajíček–Pudlák write \
    P ≤ Q for 'P simulates Q' (common lower bound, optimal = least element), and Lean likewise \
    places the simulator on the left of Simulates / PSimulates; under the reversed order \
    A ≤ B := B.Simulates A (or B.PSimulates A), P.join Q is a binary join and optimal systems \
    are greatest elements; (2) IsOptimal.polyBounded_on_NP_subset, \
    exists_isOptimal_iff_of_paddable, and exists_isOptimal_UNSAT_iff formalize the full (2) ↔ (3) \
    equivalence of Theorem 2.1(i) for paddable decodable languages and in particular UNSAT \
    (encCNF): an optimal refutation system exists iff some refutation system has polynomially \
    bounded proofs on every NP subset X ⊆ UNSAT (proved in the paper for TAUT via first-order \
    arithmetic consistency statements (3) → (5) → (4) → (1) → (2), and proved directly here from \
    Cslib.Complexity.Paddable / UNSAT_paddable); (3) \
    IsOptimal.polynomiallyBounded_UNSAT_iff_NP_eq_coNP and \
    exists_isOptimal_UNSAT_of_NP_eq_coNP state the UNSAT (encCNF) refutation analogue of the §0 \
    TAUT / NP = coNP observation, proved via the existing library equivalence \
    ProofSystem.NP_eq_coNP_iff_exists_polynomiallyBounded without transporting a specific proof \
    system between TAUT and UNSAT. Derived library facts (not cited from the paper as theorems): \
    pSimulates_join_iff, simulates_join_iff (binary-join universal properties), \
    IsPOptimal.isOptimal (fixed-system consequence of definitions and PSimulates.simulates, \
    underlying the existential (7) → (2) implication of Theorem 2.1(i); Theorem 2.1(ii) instead \
    treats equivalences among (6)–(9)), PolynomiallyBounded.isOptimal, closure lemmas, and \
    NP / P existence results. Unconditional existence for UNSAT is open and not claimed."
