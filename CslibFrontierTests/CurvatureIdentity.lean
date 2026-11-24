/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Identity

/-! Tests of Lemma B.1 and Proposition B.2 of [AnthropicVPVNP2026] under ordinary imports:

* the number of states grows like `exp (κ √E)`;
* the identity for two crossing wires, read at one coefficient. -/

namespace CslibFrontierTests.CurvatureIdentity

open Cslib.Circuits.Arithmetic.Separation.Curvature Filter

/-- Lemma B.1: some `κ > 0` bounds `log P(E)` by `κ √E` from above for all `E`, and almost from
below for large `E`. -/
example : ∃ κ : ℝ, 0 < κ ∧ ∀ E : ℕ, Real.log (stateCount E) ≤ κ * √E :=
  let ⟨κ, hκ, hle, _⟩ := exists_log_stateCount_asymptotic
  ⟨κ, hκ, hle⟩

/-- Proposition B.2 (a) and (b): the tensors sum to the product of the two diagonals, and each one
splits as few products along `(a, d) | (b, c)`. -/
example (μ ν e₁ e₂ : ℕ) :
    ∃ Ψ : Fin (2 * (e₁ + e₂) + 1) → ↥(states μ e₁) → ↥(states ν e₂) → ↥(states μ e₁) →
        ↥(states ν e₂) → ℤ,
      (∀ a b c d, ∑ N, Ψ N a b c d = (if a = c then 1 else 0) * (if b = d then 1 else 0)) ∧
      ∀ N : Fin (2 * (e₁ + e₂) + 1),
        ∃ (g : Fin ((N.1 + 1) * stateCount N) → ↥(states μ e₁) × ↥(states ν e₂) → ℤ)
          (h : Fin ((N.1 + 1) * stateCount N) → ↥(states ν e₂) × ↥(states μ e₁) → ℤ),
          ∀ a b c d, Ψ N a b c d = ∑ k, g k (a, d) * h k (b, c) :=
  let ⟨Ψ, ha, hb, _⟩ := exists_crossing_identity μ ν e₁ e₂
  ⟨Ψ, ha, hb⟩

end CslibFrontierTests.CurvatureIdentity
