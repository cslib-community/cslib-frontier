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
Pauli group, the compression bound for arbitrary unitaries, and its concrete instance on the
Pauli strings, where the defect vanishes and the isometry recovers the products exactly on the
vector.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PauliCompression

open Matrix Cslib Cslib.Quantum Cslib.Quantum.PauliGroup Cslib.BitString
open scoped Kronecker

/-- `Z^b X^a = (-1)^{a·b} X^a Z^b` in the Pauli group. -/
example {ι : Type} [Fintype ι] (a b : ι → Bool) :
    ofZ b * ofX a = (if a ⬝ᵥ b then negOne else 1) * (ofX a * ofZ b) :=
  ofZ_mul_ofX a b

/-- **Compression of the Pauli family** for arbitrary unitaries. -/
example {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X Z : (ι → Bool) → Matrix κ κ ℂ) (hX : ∀ a, (X a)ᴴ * X a = 1)
    (hZ : ∀ b, (Z b)ᴴ * Z b = 1) (ψ : EuclideanSpace ℂ κ) :
    ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (W : Matrix ((ι → Bool) × J) κ ℂ),
      Wᴴ * W = 1 ∧
      2 * (∑ a, ∑ b, ‖(WithLp.toLp 2 ((X a * Z b -
          Wᴴ * ((pauliXPow a * pauliZPow b) ⊗ₖ (1 : Matrix J J ℂ)) * W) *ᵥ ψ.ofLp) :
          EuclideanSpace ℂ κ)‖ ^ 2) / Fintype.card (PauliGroup ι) ≤
        (∑ p, ∑ q, ‖(WithLp.toLp 2 ((pauliFamily X Z p * pauliFamily X Z q -
          pauliFamily X Z (p * q)) *ᵥ ψ.ofLp) : EuclideanSpace ℂ κ)‖ ^ 2) /
          (Fintype.card (PauliGroup ι)) ^ 2 :=
  exists_isometry_compress_pauliFamily X Z hX hZ ψ

/-- **Concrete client.** For the Pauli strings on two qubits the defect vanishes, so on any vector
the isometry recovers every product `X^a Z^b` exactly. -/
example (ψ : EuclideanSpace ℂ (Fin 2 → Bool)) :
    ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J)
      (W : Matrix ((Fin 2 → Bool) × J) (Fin 2 → Bool) ℂ), Wᴴ * W = 1 ∧
      ∀ a b, (pauliXPow a * pauliZPow b) *ᵥ ψ.ofLp =
        (Wᴴ * ((pauliXPow a * pauliZPow b) ⊗ₖ (1 : Matrix J J ℂ)) * W) *ᵥ ψ.ofLp := by
  have hX : ∀ a : Fin 2 → Bool, (pauliXPow a)ᴴ * pauliXPow a = 1 := fun a => by
    rw [(pauliXPow_isHermitian a).eq, pauliXPow_mul_self]
  have hZ : ∀ b : Fin 2 → Bool, (pauliZPow b)ᴴ * pauliZPow b = 1 := fun b => by
    rw [(pauliZPow_isHermitian b).eq, pauliZPow_mul_self]
  obtain ⟨J, _, _, W, hW, h⟩ := exists_isometry_compress_pauliFamily pauliXPow pauliZPow hX hZ ψ
  refine ⟨J, inferInstance, inferInstance, W, hW, fun a b => ?_⟩
  simp only [pauliFamily_pauliXPow_mul, sub_self, zero_mulVec, WithLp.toLp_zero, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
    zero_div] at h
  have hc : (0 : ℝ) < Fintype.card (PauliGroup (Fin 2)) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hc, zero_mul] at h
  have h0 : ∑ a, ∑ b, ‖(WithLp.toLp 2 ((pauliXPow a * pauliZPow b -
      Wᴴ * ((pauliXPow a * pauliZPow b) ⊗ₖ (1 : Matrix J J ℂ)) * W) *ᵥ ψ.ofLp) :
      EuclideanSpace ℂ (Fin 2 → Bool))‖ ^ 2 = 0 :=
    le_antisymm (by linarith) (by positivity)
  have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity).mp h0 a (Finset.mem_univ a)
  have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity).mp this b
    (Finset.mem_univ b)
  rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, WithLp.toLp_eq_zero, sub_mulVec,
    sub_eq_zero] at this
  exact this

end CslibFrontierTests.PauliCompression
