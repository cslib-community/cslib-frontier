/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Identity

/-! Tests of Lemma B.1 and Proposition B.2 of [AnthropicVPVNP2026] under ordinary imports:

* the number of states grows like `exp (κ √E)`, and `P(2) = 2`;
* the identity for two crossing wires on concrete classes of states: its sum is the product of the
  diagonals, and each tensor splits in both ways. -/

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
        ∃ (g : Fin ((N.val + 1) * stateCount N) → ↥(states μ e₁) × ↥(states ν e₂) → ℤ)
          (h : Fin ((N.val + 1) * stateCount N) → ↥(states ν e₂) × ↥(states μ e₁) → ℤ),
          ∀ a b c d, Ψ N a b c d = ∑ k, g k (a, d) * h k (b, c) :=
  let ⟨Ψ, ha, hb, _⟩ := exists_crossing_identity μ ν e₁ e₂
  ⟨Ψ, ha, hb⟩

/-- There are two states of energy at most `2`: `(∅, ∅)` and `({0}, {0})`. -/
example : stateCount 2 = 2 := by decide

/-- Lemma B.1, the lower bound at `ε = κ / 2`. -/
example : ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ E : ℕ in atTop, κ / 2 * √E ≤ Real.log (stateCount E) := by
  obtain ⟨κ, hκ, -, hge⟩ := exists_log_stateCount_asymptotic
  refine ⟨κ, hκ, (hge (κ / 2) (by positivity)).mono fun E hE => ?_⟩
  linarith

/-- The states used below exist: `({0}, {1})` and `({1}, {0})` have size `1` and energy `4`, and
`({0}, {0})` has size `1` and energy `2`. -/
example : (({0}, {1}) : Finset ℕ × Finset ℕ) ∈ states 1 4 ∧
    (({1}, {0}) : Finset ℕ × Finset ℕ) ∈ states 1 4 ∧
    (({0}, {0}) : Finset ℕ × Finset ℕ) ∈ states 1 2 := by
  simp [mem_lowStates, energy]

/-- Proposition B.2 on the classes of size `1` and energies `4` and `2`, at the distinct states
`({0}, {1})`, `({1}, {0})` and the state `({0}, {0})`: the tensors sum to `1` on the diagonal and to
`0` off it, and each one splits along `(a, d) | (b, c)` and along `(a, b) | (c, d)`. -/
example (s₀ s₁ : ↥(states 1 4)) (t₀ : ↥(states 1 2)) (h₀ : s₀.val = ({0}, {1}))
    (h₁ : s₁.val = ({1}, {0})) :
    ∃ Ψ : Fin (2 * (4 + 2) + 1) → ↥(states 1 4) → ↥(states 1 2) → ↥(states 1 4) →
        ↥(states 1 2) → ℤ,
      (∑ N, Ψ N s₀ t₀ s₀ t₀ = 1) ∧ (∑ N, Ψ N s₀ t₀ s₁ t₀ = 0) ∧
      (∀ N : Fin (2 * (4 + 2) + 1),
        ∃ (g : Fin ((N.val + 1) * stateCount N) → ↥(states 1 4) × ↥(states 1 2) → ℤ)
          (h : Fin ((N.val + 1) * stateCount N) → ↥(states 1 2) × ↥(states 1 4) → ℤ),
          Ψ N s₀ t₀ s₁ t₀ = ∑ k, g k (s₀, t₀) * h k (t₀, s₁)) ∧
      ∀ N : Fin (2 * (4 + 2) + 1),
        ∃ (g : Fin ((2 * (4 + 2) - N.val + 1) * stateCount (2 * (4 + 2) - N.val)) →
            ↥(states 1 4) × ↥(states 1 2) → ℤ)
          (h : Fin ((2 * (4 + 2) - N.val + 1) * stateCount (2 * (4 + 2) - N.val)) →
            ↥(states 1 4) × ↥(states 1 2) → ℤ),
          Ψ N s₀ t₀ s₁ t₀ = ∑ k, g k (s₀, t₀) * h k (s₁, t₀) := by
  obtain ⟨Ψ, ha, hb, hc⟩ := exists_crossing_identity 1 1 4 2
  have hne : s₀ ≠ s₁ := fun h => by
    have := congrArg Subtype.val h
    rw [h₀, h₁] at this
    simp at this
  refine ⟨Ψ, by simp [ha], by simp [ha, hne], fun N => ?_, fun N => ?_⟩
  · obtain ⟨g, h, hgh⟩ := hb N
    exact ⟨g, h, hgh _ _ _ _⟩
  · obtain ⟨g, h, hgh⟩ := hc N _ rfl
    exact ⟨g, h, hgh _ _ _ _⟩

end CslibFrontierTests.CurvatureIdentity
