/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.LinearityTest
import CslibFrontier.Foundations.Quantum.PauliTwirl

/-! # Linearity from the linearity and consistency tests

Checked clients: the pointwise estimate and the averaged bound in any state of any star-ordered
algebra, and the tensor-product corollary with rounding. A concrete instance: the commuting phase
flips `Z^a`, used both as the single-query observables and as the pair observables, pass the tests
with `ε = η₁ = η₂ = 0` in every state, so the bound certifies their exact linearity in that state.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LinearityTest

open Matrix Cslib Cslib.Quantum Finset
open scoped Kronecker MatrixOrder ComplexOrder BigOperators Matrix.Norms.L2Operator

/-- **Linearity from consistency**, in any state of any star-ordered algebra. -/
example {n R : Type} [Fintype n] [DecidableEq n] [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] [Algebra ℂ R] [StarModule ℂ R] [SelfAdjointDecompose R]
    (φ : AlgState R) (A : (n → Bool) → R) (N₁ N₂ : (n → Bool) → (n → Bool) → R)
    (hA : ∀ a, star (A a) * A a ≤ 1) (hN₁ : ∀ a b, star (N₁ a b) * N₁ a b ≤ 1)
    (hc₁ : ∀ a b c, Commute (N₁ a b) (A c)) (hc₂ : ∀ a b c, Commute (N₂ a b) (A c))
    {ε η₁ η₂ : ℝ} (hL : 1 - ε ≤ 𝔼 a, 𝔼 b, (φ (N₁ a b * N₂ a b * A (a + b))).re)
    (hC₁ : 𝔼 a, 𝔼 b, φ.norm (A a - N₁ a b) ^ 2 ≤ η₁)
    (hC₂ : 𝔼 a, 𝔼 b, φ.norm (A b - N₂ a b) ^ 2 ≤ η₂) :
    1 - ε - √η₁ - √η₂ ≤ 𝔼 a, 𝔼 b, (φ (A a * A b * A (a + b))).re :=
  one_sub_le_expect_re_apply_mul_mul φ A N₁ N₂ hA hN₁ hc₁ hc₂ hL hC₁ hC₂

/-- **Exactly linear observables from the tests**, on the first player's factor. -/
example {ι κ n : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype n]
    [DecidableEq n] (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ)) (A : (n → Bool) → Matrix ι ι ℂ)
    (hA : ∀ a, IsSelfAdjoint (A a)) (hA2 : ∀ a, A a * A a = 1)
    (N₁ N₂ : (n → Bool) → (n → Bool) → Matrix κ κ ℂ) (hN₁ : ∀ a b, N₁ a b ∈ unitary (Matrix κ κ ℂ))
    {ε η₁ η₂ : ℝ}
    (hL : 1 - ε ≤ 𝔼 a, 𝔼 b, (φ ((1 ⊗ₖ N₁ a b) * (1 ⊗ₖ N₂ a b) * (A (a + b) ⊗ₖ 1))).re)
    (hC₁ : 𝔼 a, 𝔼 b, φ.norm (A a ⊗ₖ 1 - 1 ⊗ₖ N₁ a b) ^ 2 ≤ η₁)
    (hC₂ : 𝔼 a, 𝔼 b, φ.norm (A b ⊗ₖ 1 - 1 ⊗ₖ N₂ a b) ^ 2 ≤ η₂) :
    ∃ P : Measurement (n → Bool) (Matrix ι ι ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix ι ι ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm ((A a - P.charObs a) ⊗ₖ 1) ^ 2 ≤ 40 * (ε + √η₁ + √η₂) :=
  exists_isProjective_charObs_of_linearityTest φ A hA hA2 N₁ N₂ hN₁ hL hC₁ hC₂

/-- **Concrete instance.** The phase flips `Z^a`, as single-query and as pair observables, pass the
tests with no error in every state, so the bound gives exact average linearity. -/
example {n : Type} [Fintype n] [DecidableEq n] (φ : AlgState (Matrix (n → Bool) (n → Bool) ℂ)) :
    1 ≤ 𝔼 a, 𝔼 b, (φ (pauliZPow a * pauliZPow b * pauliZPow (a + b))).re := by
  have hZ : ∀ a, pauliZPow a ∈ unitary (Matrix (n → Bool) (n → Bool) ℂ) :=
    pauliZPow_mem_unitaryGroup
  have hcomm : ∀ a b, Commute (pauliZPow (ι := n) a) (pauliZPow b) := fun a b => by
    rw [Commute, SemiconjBy, pauliZPow_mul, pauliZPow_mul, add_comm]
  have hcontract (a : n → Bool) : star (pauliZPow a) * pauliZPow a ≤ 1 :=
    (Unitary.star_mul_self_of_mem (hZ a)).le
  have h := one_sub_le_expect_re_apply_mul_mul (ε := 0) (η₁ := 0) (η₂ := 0) φ pauliZPow
    (fun a _ => pauliZPow a) (fun _ b => pauliZPow b) hcontract (fun a _ => hcontract a)
    (fun a _ c => hcomm a c) (fun _ b c => hcomm b c)
    (by simp only [pauliZPow_mul, BitString.add_self, pauliZPow_zero, φ.map_one, Complex.one_re,
      Fintype.expect_const, sub_zero, le_refl])
    (by simp [AlgState.norm_zero])
    (by simp [AlgState.norm_zero])
  simpa using h

end CslibFrontierTests.LinearityTest
