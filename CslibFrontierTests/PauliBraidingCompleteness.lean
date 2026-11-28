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

open Cslib.PCP Cslib.Quantum Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator Real

private theorem eq_zero_of_expect_sq_norm_le_zero {L : Type*} [Fintype L]
    (f : (Fin 1 → Bool) → L → ℂ)
    (h : (𝔼 x, ‖(WithLp.toLp 2 (f x) : EuclideanSpace ℂ L)‖ ^ 2) ≤ 0) (x : Fin 1 → Bool) :
    f x = 0 := by
  let g (y : Fin 1 → Bool) := ‖(WithLp.toLp 2 (f y) : EuclideanSpace ℂ L)‖ ^ 2
  have hg : ∀ y, 0 ≤ g y := fun _ => sq_nonneg _
  have hm : (𝔼 y, g y) = 0 := le_antisymm h (expect_nonneg fun y _ => hg y)
  have hz := congrFun ((Fintype.expect_eq_zero_iff_of_nonneg hg).mp hm) x
  have he := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hz)
  simpa only [WithLp.ofLp_toLp, WithLp.ofLp_zero] using congrArg WithLp.ofLp he

/-- One pair of witnesses simultaneously extracts the EPR state and both
players' Pauli actions at the exact honest score. -/
example :
    let S := pauliBraidingHonestStrategy 1
    ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J)
      (L : Type) (_ : Fintype L) (_ : DecidableEq L)
      (V : Matrix ((Fin 1 → Bool) × J) (Fin 1 → Bool) ℂ)
      (W : Matrix ((Fin 1 → Bool) × L) (Fin 1 → Bool) ℂ),
      Vᴴ * V = 1 ∧ Wᴴ * W = 1 ∧
      let T := V ⊗ₖ W
      let ψ := T *ᵥ S.state.ofLp
      let E := extractedEprProjection (Q := Fin 1 → Bool) (J := J) (K := L)
      ‖(WithLp.toLp 2 (((E - 1) * T) *ᵥ S.state.ofLp) :
        EuclideanSpace ℂ (((Fin 1 → Bool) × J) × (Fin 1 → Bool) × L))‖ ^ 2 ≤ 0 ∧
      (∀ (b : Bool) (x : Fin 1 → Bool),
        let A := 𝔼 d, pauliBraidingBasisObservable S.toCommuting.alice b x d
        let C := kroneckerOne ((cond b (pauliZPow x) (pauliXPow x)) ⊗ₖ (1 : Matrix J J ℂ))
        (T * A) *ᵥ S.state.ofLp = C *ᵥ ψ) ∧
      (∀ (b : Bool) (x : Fin 1 → Bool),
        let B := 𝔼 d, pauliBraidingBasisObservable S.toCommuting.bob b x d
        let C := oneKronecker ((cond b (pauliZPow x) (pauliXPow x)) ⊗ₖ (1 : Matrix L L ℂ))
        (T * B) *ᵥ S.state.ofLp = C *ᵥ ψ) := by
  intro S
  obtain ⟨J, _, _, L, _, _, V, W, h⟩ :=
    exists_pauliBraidingExtraction S (ε := 0)
      (by rw [sub_zero, quantumWinProb_pauliBraidingHonestStrategy])
  refine ⟨J, inferInstance, inferInstance, L, inferInstance, inferInstance, V, W,
    h.alice_isometry, h.bob_isometry, ?_, ?_, ?_⟩
  · simpa only [mul_zero, pauliBraidingTwistedCommutationError_zero,
      pauliBraidingRoundedConsistencyError_zero, add_zero] using h.epr
  · intro b x A C
    rw [mulVec_mulVec, ← sub_eq_zero, ← sub_mulVec]
    refine eq_zero_of_expect_sq_norm_le_zero (fun y =>
      let A' := 𝔼 d, pauliBraidingBasisObservable S.toCommuting.alice b y d
      let C' := kroneckerOne ((cond b (pauliZPow y) (pauliXPow y)) ⊗ₖ (1 : Matrix J J ℂ))
      ((V ⊗ₖ W) * A' - C' * (V ⊗ₖ W)) *ᵥ S.state.ofLp) ?_ x
    simpa only [mul_zero, pauliBraidingRoundingError_zero,
      pauliBraidingRoundedConsistencyError_zero, pauliBraidingTwistedCommutationError_zero,
      ite_self, add_zero] using h.alice b
  · intro b x B C
    rw [mulVec_mulVec, ← sub_eq_zero, ← sub_mulVec]
    refine eq_zero_of_expect_sq_norm_le_zero (fun y =>
      let B' := 𝔼 d, pauliBraidingBasisObservable S.toCommuting.bob b y d
      let C' := oneKronecker ((cond b (pauliZPow y) (pauliXPow y)) ⊗ₖ (1 : Matrix L L ℂ))
      ((V ⊗ₖ W) * B' - C' * (V ⊗ₖ W)) *ᵥ S.state.ofLp) ?_ x
    simpa only [mul_zero, pauliBraidingRoundingError_zero,
      pauliBraidingRoundedConsistencyError_zero, pauliBraidingTwistedCommutationError_zero,
      ite_self, add_zero] using h.bob b

end CslibFrontierTests.PauliBraidingCompleteness
