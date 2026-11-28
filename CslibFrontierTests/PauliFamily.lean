/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.Algebra.PauliFamily
import CslibFrontier.Foundations.Quantum.PauliCompression

/-! # The Pauli family and its defect

Checked clients: averages over the Pauli group are averages over bit strings, the defect of the
Pauli family is bounded by consistency, anticommutation and linearity, and the bound applies to
Alice's Pauli strings on her register with Bob's phase flips on his, where the compression
corollary gives an isometry for every state.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PauliFamily

open Matrix Cslib Cslib.Quantum Cslib.BitString Finset
open scoped Kronecker MatrixOrder BigOperators

/-- Averages over the Pauli group are averages over the two bit strings. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → Bool) → (ι → Bool) → ℝ) :
    𝔼 p : PauliGroup ι, F p.x p.z = 𝔼 a, 𝔼 b, F a b :=
  expect_pauliGroup F

/-- The defect from consistency, anticommutation and linearity, in any star-ordered algebra. -/
example {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Algebra ℂ A] [StarModule ℂ A] [SelfAdjointDecompose A]
    (φ : AlgState A) (X Z ZB : (ι → Bool) → A) (hX : ∀ a, X a ∈ unitary A)
    (hZ : ∀ b, Z b ∈ unitary A) (hZB : ∀ b, ZB b ∈ unitary A)
    (hXB : ∀ a b, Commute (X a) (ZB b)) (hZZB : ∀ b b', Commute (Z b) (ZB b')) :
    𝔼 p, 𝔼 q, φ.norm (pauliFamily X Z p * pauliFamily X Z q - pauliFamily X Z (p * q)) ^ 2 ≤
      5 * (8 * 𝔼 b, φ.norm (Z b - ZB b) ^ 2 +
        𝔼 a, 𝔼 b, φ.norm (Z b * X a - (signVal (a ⬝ᵥ b) : ℂ) • (X a * Z b)) ^ 2 +
        𝔼 a, 𝔼 a', φ.norm (X a * X a' - X (a + a')) ^ 2 +
        𝔼 b, 𝔼 b', φ.norm (Z b * Z b' - Z (b + b')) ^ 2) :=
  expect_norm_pauliFamily_sub_sq_le φ X Z ZB hX hZ hZB hXB hZZB

/-- A Hermitian involution, tensored with the identity on either side, is unitary. -/
theorem mem_unitary_kronecker {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] {P : Matrix n n ℂ} (hP : P.IsHermitian) (hPP : P * P = 1) :
    P ⊗ₖ (1 : Matrix m m ℂ) ∈ unitary (Matrix (n × m) (n × m) ℂ) ∧
      (1 : Matrix m m ℂ) ⊗ₖ P ∈ unitary (Matrix (m × n) (m × n) ℂ) := by
  have h1 : star P * P = 1 := by rw [star_eq_conjTranspose, hP.eq, hPP]
  refine ⟨Unitary.mem_iff.mpr ⟨?_, ?_⟩, Unitary.mem_iff.mpr ⟨?_, ?_⟩⟩ <;>
    simp only [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one, hP.eq,
      ← mul_kronecker_mul, hPP, Matrix.one_mul, one_kronecker_one]

/-- **Concrete client.** Alice holds the Pauli strings on her register and Bob holds the phase
flips on his; the compression corollary applies, with one isometry for every state. -/
example : ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J)
    (W : Matrix ((Fin 2 → Bool) × J) ((Fin 2 → Bool) × (Fin 2 → Bool)) ℂ), Wᴴ * W = 1 ∧
    ∀ φ : AlgState (Matrix ((Fin 2 → Bool) × (Fin 2 → Bool)) ((Fin 2 → Bool) × (Fin 2 → Bool)) ℂ),
      𝔼 a, 𝔼 b, φ.norm (pauliXPow a ⊗ₖ (1 : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℂ) *
          (pauliZPow b ⊗ₖ 1) - Wᴴ * ((pauliXPow a * pauliZPow b) ⊗ₖ (1 : Matrix J J ℂ)) * W) ^ 2 ≤
        5 * (8 * 𝔼 b, φ.norm (pauliZPow b ⊗ₖ 1 - 1 ⊗ₖ pauliZPow b) ^ 2 +
          𝔼 a, 𝔼 b, φ.norm (pauliZPow b ⊗ₖ 1 * (pauliXPow a ⊗ₖ 1) -
            (signVal (a ⬝ᵥ b) : ℂ) • (pauliXPow a ⊗ₖ 1 * (pauliZPow b ⊗ₖ 1))) ^ 2 +
          𝔼 a, 𝔼 a', φ.norm (pauliXPow a ⊗ₖ 1 * (pauliXPow a' ⊗ₖ 1) -
            pauliXPow (a + a') ⊗ₖ 1) ^ 2 +
          𝔼 b, 𝔼 b', φ.norm (pauliZPow b ⊗ₖ 1 * (pauliZPow b' ⊗ₖ 1) -
            pauliZPow (b + b') ⊗ₖ 1) ^ 2) :=
  exists_isometry_compress_of_consistent
    (fun a => pauliXPow a ⊗ₖ (1 : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℂ))
    (fun b => pauliZPow b ⊗ₖ (1 : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℂ))
    (fun b => (1 : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℂ) ⊗ₖ pauliZPow b)
    (fun a => (mem_unitary_kronecker (pauliXPow_isHermitian a) (pauliXPow_mul_self a)).1)
    (fun b => (mem_unitary_kronecker (pauliZPow_isHermitian b) (pauliZPow_mul_self b)).1)
    (fun b => (mem_unitary_kronecker (pauliZPow_isHermitian b) (pauliZPow_mul_self b)).2)
    (fun a b => by simp only [Commute, SemiconjBy, ← mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul])
    (fun b b' => by simp only [Commute, SemiconjBy, ← mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul])

end CslibFrontierTests.PauliFamily
