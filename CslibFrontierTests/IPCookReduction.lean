/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.IP.Shamir

/-! Checked uses of `PolyTimeTuringReducible.mem_IP` (Goldreich, Exercise 9.2, second part): the
source's form with the redundant complement hypothesis, and its conclusion with the perfectly
complete interactive proofs of Goldreich's definition. -/

set_option linter.privateModule false

namespace CslibFrontierTests.IPCookReduction

open Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

variable {α : Type} {encA : α ↪ List Bool} {A : Set α} {B : Set (List Bool)}

/-- The source's statement: `S` Cook-reducible to `S′` with `S′` and its complement in `IP`. -/
example (hAB : PolyTimeTuringReducible encA encBits A B) (hB : B ∈ IP encBits)
    (_hBc : Bᶜ ∈ IP encBits) : A ∈ IP encA :=
  hAB.mem_IP hB

/-- The conclusion with perfect completeness and soundness error `1 / 3`. -/
example (hAB : PolyTimeTuringReducible encA encBits A B) (hB : B ∈ IP encBits) :
    ∃ verifier : α → WordOracleComp Unit Bool,
      IsOraclePPTOn encA encBool verifier ∧ IsInteractiveProof verifier A 1 (1 / 3) := by
  have h := hAB.mem_IP hB
  rw [IP_eq_setOf_isInteractiveProof_one] at h
  exact h

end CslibFrontierTests.IPCookReduction
