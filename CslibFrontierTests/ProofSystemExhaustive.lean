/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.ProofSystem.Exhaustive
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Complexity.CookLevin.Completeness

/-! Exhaustive proof systems: one for `UNSAT` from its `coNP` membership, one for all bit words
from the always-rejecting verifier of the empty complement, and Goldreich's Theorem B.13 with the
one-system dichotomy for `UNSAT`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.ProofSystemExhaustive

open Cslib.Complexity Turing.MultiTapeTM

/-- `UNSAT` has a proof system, without any assumption on `NP` and `coNP`. -/
example : Nonempty (ProofSystem encCNF UNSAT) :=
  ProofSystem.nonempty_of_mem_coNP cnfDecoder UNSAT_mem_coNP ⟨[[]], fun ⟨_, h⟩ => by simp at h⟩

/-- The always-rejecting verifier has the empty set as its language, so its exhaustive system
proves every bit word. -/
example : Nonempty (ProofSystem encBits Set.univ) :=
  ⟨ProofSystem.exhaustive (p := 0) (V := fun _ => false) (L := Set.univ) Decoder.bits
    (ComputableInPolyTime.const false) (fun a => by simp) (Set.mem_univ [])⟩

/-- Goldreich's Theorem B.13: one fixed refutation system decides `NP = coNP`. -/
example : ∃ M : ProofSystem encCNF UNSAT,
    (M.PolynomiallyBounded ↔ ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC) :=
  ProofSystem.exists_polynomiallyBounded_iff_NP_eq_coNP

/-- The `coNP ⊆ NP` form for the `coNP`-complete set `UNSAT`. -/
example : ∃ M : ProofSystem encCNF UNSAT,
    (M.PolynomiallyBounded ↔ ∀ {γ : Type} (encC : γ ↪ List Bool), coNP encC ⊆ NP encC) :=
  ProofSystem.exists_polynomiallyBounded_iff_coNP_subset_NP CookLevin.UNSAT_coNPComplete cnfDecoder
    ⟨[[]], fun ⟨_, h⟩ => by simp at h⟩

end CslibFrontierTests.ProofSystemExhaustive
