/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.RegularCompression
import CslibFrontier.Foundations.Quantum.Pauli

/-! # Compression of the regular representation

Checked clients of the compression step toward the Gowers–Hatami theorem: the regular
representation is a unitary representation, the averaging isometry is an isometry and intertwines
up to the multiplicative defect, the averaged compression bound holds in the vector state, and the
Pauli representation of `ℤ/2` is recovered exactly.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.RegularCompression

open Matrix Cslib Cslib.Quantum
open scoped MatrixOrder

variable {G ι : Type} [Group G] [Fintype G] [DecidableEq G] [Fintype ι] [DecidableEq ι]

/-- The regular representation is a unitary representation. -/
example (y y' : G) :
    regularRep (ι := ι) y * regularRep y' = regularRep (y * y') ∧
      (regularRep (ι := ι) y)ᴴ * regularRep y = 1 :=
  ⟨regularRep_mul y y', conjTranspose_regularRep_mul y⟩

/-- The averaging isometry of a family of unitaries is an isometry. -/
example (f : G → Matrix ι ι ℂ) (hf : ∀ x, (f x)ᴴ * f x = 1) :
    (regularIsometry f)ᴴ * regularIsometry f = 1 :=
  conjTranspose_regularIsometry_mul f hf

/-- The averaging isometry intertwines `f` and the regular representation up to the
multiplicative defect, for any matrices. -/
example (f : G → Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    (∑ y, ‖(WithLp.toLp 2 ((regularIsometry f * f y - regularRep y * regularIsometry f) *ᵥ
      ψ.ofLp) : EuclideanSpace ℂ (ι × G))‖ ^ 2) / Fintype.card G =
    (∑ x, ∑ y, ‖(WithLp.toLp 2 ((f x * f y - f (x * y)) *ᵥ ψ.ofLp) :
      EuclideanSpace ℂ ι)‖ ^ 2) / (Fintype.card G) ^ 2 :=
  sum_norm_regularIsometry_mul_sub_eq f ψ

/-- The averaged compression bound in the state-dependent norm of a vector state. -/
example (f : G → Matrix ι ι ℂ) (hf : ∀ x, (f x)ᴴ * f x = 1) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) :
    (∑ y, (AlgState.vector ψ hψ).norm
        (f y - (regularIsometry f)ᴴ * regularRep y * regularIsometry f) ^ 2) / Fintype.card G ≤
      (∑ x, ∑ y, (AlgState.vector ψ hψ).norm (f x * f y - f (x * y)) ^ 2) /
        (Fintype.card G) ^ 2 :=
  sum_vector_norm_sub_compress_le f hf ψ hψ

/-- The representation of `ℤ/2` by the Pauli `X`. -/
noncomputable def pauliRep : Multiplicative (ZMod 2) → Matrix Bool Bool ℂ :=
  fun g => if g.toAdd = 0 then 1 else pauliX

theorem pauliRep_unitary (x : Multiplicative (ZMod 2)) : (pauliRep x)ᴴ * pauliRep x = 1 := by
  unfold pauliRep
  split_ifs
  · simp
  · rw [pauliX_isHermitian.eq, pauliX_mul_self]

theorem pauliRep_mul (x y : Multiplicative (ZMod 2)) :
    pauliRep x * pauliRep y = pauliRep (x * y) := by
  have hcases : ∀ g : Multiplicative (ZMod 2), g = 1 ∨ g = Multiplicative.ofAdd 1 := by decide
  have h₁ : pauliRep 1 = 1 := ite_eq_left rfl
  have hX : pauliRep (Multiplicative.ofAdd 1) = pauliX := ite_eq_right (by decide)
  have hsq : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
  rcases hcases x with rfl | rfl <;> rcases hcases y with rfl | rfl <;>
    simp [h₁, hX, hsq, pauliX_mul_self]

/-- The Pauli representation of `ℤ/2` is recovered exactly by the compression, in every
vector. -/
example (ψ : EuclideanSpace ℂ Bool) (y : Multiplicative (ZMod 2)) :
    pauliRep y *ᵥ ψ.ofLp =
      ((regularIsometry pauliRep)ᴴ * regularRep y * regularIsometry pauliRep) *ᵥ ψ.ofLp :=
  mulVec_eq_compress_of_mul pauliRep pauliRep_unitary ψ
    (fun x y => by rw [pauliRep_mul]) y

end CslibFrontierTests.RegularCompression
