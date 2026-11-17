/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.PauliGroup
import CslibFrontier.Foundations.Quantum.PauliCompression

/-! # Compression of the Pauli family

Checked clients: the Pauli group relations, the Pauli strings as an exact representation of the
Pauli group, the compression bound for arbitrary unitaries in every state, and its concrete
instance on the Pauli strings, where the defect vanishes and the isometry recovers the products
exactly in every state.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PauliCompression

open Matrix Cslib Cslib.Quantum Cslib.Quantum.PauliGroup Cslib.BitString
open scoped Kronecker MatrixOrder BigOperators

/-- `Z^b X^a = (-1)^{a·b} X^a Z^b` in the Pauli group. -/
example {ι : Type} [Fintype ι] (a b : ι → Bool) :
    ofZ b * ofX a = (if a ⬝ᵥ b then negOne else 1) * (ofX a * ofZ b) :=
  ofZ_mul_ofX a b

/-- **Compression of the Pauli family** for arbitrary unitaries: one isometry for every state. -/
example {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X Z : (ι → Bool) → Matrix κ κ ℂ) (hX : ∀ a, (X a)ᴴ * X a = 1)
    (hZ : ∀ b, (Z b)ᴴ * Z b = 1) :
    ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (W : Matrix ((ι → Bool) × J) κ ℂ),
      Wᴴ * W = 1 ∧ ∀ φ : AlgState (Matrix κ κ ℂ),
      𝔼 a, 𝔼 b, φ.norm (X a * Z b -
          Wᴴ * ((pauliXPow a * pauliZPow b) ⊗ₖ (1 : Matrix J J ℂ)) * W) ^ 2 ≤
        𝔼 p, 𝔼 q, φ.norm (pauliFamily X Z p * pauliFamily X Z q - pauliFamily X Z (p * q)) ^ 2 :=
  exists_isometry_compress_pauliFamily X Z hX hZ

/-- **Concrete client.** For the Pauli strings on two qubits the defect vanishes, so in every state
the isometry recovers every product `X^a Z^b` exactly. -/
example : ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J)
      (W : Matrix ((Fin 2 → Bool) × J) (Fin 2 → Bool) ℂ), Wᴴ * W = 1 ∧
      ∀ φ : AlgState (Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℂ), ∀ a b,
        φ.norm (pauliXPow a * pauliZPow b -
          Wᴴ * ((pauliXPow a * pauliZPow b) ⊗ₖ (1 : Matrix J J ℂ)) * W) = 0 := by
  have hX : ∀ a : Fin 2 → Bool, (pauliXPow a)ᴴ * pauliXPow a = 1 := fun a => by
    rw [(pauliXPow_isHermitian a).eq, pauliXPow_mul_self]
  have hZ : ∀ b : Fin 2 → Bool, (pauliZPow b)ᴴ * pauliZPow b = 1 := fun b => by
    rw [(pauliZPow_isHermitian b).eq, pauliZPow_mul_self]
  obtain ⟨J, _, _, W, hW, h⟩ := exists_isometry_compress_pauliFamily pauliXPow pauliZPow hX hZ
  refine ⟨J, inferInstance, inferInstance, W, hW, fun φ a b => ?_⟩
  have h := h φ
  simp only [pauliFamily_pauliXPow_mul, sub_self, AlgState.norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.expect_const_zero] at h
  have h0 := (Fintype.expect_eq_zero_iff_of_nonneg
    (fun a => Finset.expect_nonneg fun b _ => sq_nonneg _)).mp
    (le_antisymm h (Finset.expect_nonneg fun _ _ => Finset.expect_nonneg fun _ _ => sq_nonneg _))
  have h1 := (Fintype.expect_eq_zero_iff_of_nonneg (fun b => sq_nonneg _)).mp (congrFun h0 a)
  exact pow_eq_zero_iff two_ne_zero |>.mp (congrFun h1 b)

end CslibFrontierTests.PauliCompression
