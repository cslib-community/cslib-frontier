/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.PauliStoneVonNeumann

/-! # The Stone–von Neumann theorem for qubits

Checked clients: the Pauli strings satisfy the Pauli relations, `Π X(c) Π = δ_{c,0} Π`, and every
representation of the Pauli relations, for instance the Pauli strings themselves, is unitarily
equivalent to the Pauli strings tensored with the identity.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PauliStoneVonNeumann

open Matrix Cslib Cslib.Quantum Cslib.BitString
open scoped Kronecker

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The Pauli strings anticommute according to the inner product. -/
example (a b : ι → Bool) :
    pauliZPow b * pauliXPow a = (signVal (a ⬝ᵥ b) : ℂ) • (pauliXPow a * pauliZPow b) :=
  pauliZPow_mul_pauliXPow a b

/-- The code projection kills every nonzero bit flip. -/
example (R : PauliRep ι κ) (c : ι → Bool) (hc : c ≠ 0) :
    R.codeProj * R.X c * R.codeProj = 0 := by
  rw [R.codeProj_mul_X_mul_codeProj, ite_eq_right hc]

/-- **Stone–von Neumann.** Every representation of the Pauli relations is unitarily equivalent to
the Pauli strings tensored with the identity. -/
example (R : PauliRep ι κ) : ∃ (L : Finset κ) (Φ : Matrix κ ((ι → Bool) × L) ℂ),
    Φᴴ * Φ = 1 ∧ Φ * Φᴴ = 1 ∧ (∀ a, R.X a = Φ * (pauliXPow a ⊗ₖ (1 : Matrix L L ℂ)) * Φᴴ) ∧
      ∀ b, R.Z b = Φ * (pauliZPow b ⊗ₖ (1 : Matrix L L ℂ)) * Φᴴ :=
  R.exists_unitary_eq_pauli

/-- The concrete client: the Pauli strings on two qubits, as a representation of the Pauli
relations, are unitarily equivalent to themselves tensored with the identity on a code space. -/
example : ∃ (L : Finset (Fin 2 → Bool)) (Φ : Matrix (Fin 2 → Bool) ((Fin 2 → Bool) × L) ℂ),
    Φᴴ * Φ = 1 ∧ Φ * Φᴴ = 1 ∧
      ∀ a, pauliXPow a = Φ * (pauliXPow a ⊗ₖ (1 : Matrix L L ℂ)) * Φᴴ :=
  let ⟨L, Φ, h1, h2, hX, _⟩ := (PauliRep.standard (ι := Fin 2)).exists_unitary_eq_pauli
  ⟨L, Φ, h1, h2, hX⟩

end CslibFrontierTests.PauliStoneVonNeumann
