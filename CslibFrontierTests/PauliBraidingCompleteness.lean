/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingCompleteness
import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingEPR

/-! # Completeness and EPR certification of the width-one Pauli braiding strategy -/

set_option linter.privateModule false

namespace CslibFrontierTests.PauliBraidingCompleteness

open Cslib.PCP Cslib.Quantum Matrix
open scoped Kronecker Real

/-- The explicit honest strategy supplies the optimal score needed to instantiate
the EPR certificate with zero error on the two-qubit state. -/
example :
    let S := pauliBraidingHonestStrategy 1
    ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J)
      (L : Type) (_ : Fintype L) (_ : DecidableEq L)
      (V : Matrix ((Fin 1 → Bool) × J) (Fin 1 → Bool) ℂ)
      (W : Matrix ((Fin 1 → Bool) × L) (Fin 1 → Bool) ℂ),
      Vᴴ * V = 1 ∧ Wᴴ * W = 1 ∧
      let E := extractedEprProjection (Q := Fin 1 → Bool) (J := J) (K := L)
      ‖(WithLp.toLp 2 (((E - 1) * (V ⊗ₖ W)) *ᵥ S.state.ofLp) :
        EuclideanSpace ℂ (((Fin 1 → Bool) × J) × (Fin 1 → Bool) × L))‖ ^ 2 ≤ 0 := by
  intro S
  obtain ⟨J, _, _, L, _, _, V, W, hV, hW, h⟩ :=
    exists_local_eprProjection_of_pauliBraidingGame S (ε := 0)
      (by rw [sub_zero, quantumWinProb_pauliBraidingHonestStrategy])
  refine ⟨J, inferInstance, inferInstance, L, inferInstance, inferInstance, V, W, hV, hW, ?_⟩
  simpa only [mul_zero, pauliBraidingTwistedCommutationError_zero,
    pauliBraidingRoundedConsistencyError_zero, add_zero] using h

end CslibFrontierTests.PauliBraidingCompleteness
