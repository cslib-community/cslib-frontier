/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.PauliTwirl
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Polar
import CslibFrontier.Foundations.BooleanAnalysis.HadamardRectangles

/-!
# Exact Pauli relations: the Stone–von Neumann theorem for qubits

Hermitian matrices `X(a)`, `Z(b)` on `ℂ^κ`, indexed by bit strings `a, b : ι → Bool`, satisfy the
**Pauli relations** (`Cslib.Quantum.PauliRep`) when `X` and `Z` are representations of `(ℤ/2)^ι`
and `Z(b) X(a) = (-1)^{a·b} X(a) Z(b)`. The Pauli strings `X^a`, `Z^b` on `n = |ι|` qubits are the
basic example, and every other is a multiple of it: there is a unitary
`Φ : ℂ^{2ⁿ} ⊗ ℂ^L → ℂ^κ` with

`X(a) = Φ (X^a ⊗ 1) Φᴴ`,  `Z(b) = Φ (Z^b ⊗ 1) Φᴴ`

(`Cslib.Quantum.PauliRep.exists_unitary_eq_pauli`). This is the uniqueness of the representation
of the Pauli group in which `-1` acts as `-1` (the Stone–von Neumann theorem for the finite
Heisenberg group). In rigidity it is the last step of the analysis of the Pauli braiding test,
which [Natarajan and Vidick, §4.2, the remark after Theorem 14][NatarajanVidick2017]
(arXiv:1610.03574v1) use without proof, as well known.

The proof is explicit. The `Z(b)` commute, and `Π = 2^{-n} ∑_b Z(b)` projects onto their joint
`+1` eigenspace, the *code space* (`Cslib.Quantum.PauliRep.codeProj`). Character orthogonality
gives `Π X(c) Π = δ_{c,0} Π` (`Cslib.Quantum.PauliRep.codeProj_mul_X_mul_codeProj`) and
`∑_z X(z) Π X(z) = 1` (`Cslib.Quantum.PauliRep.sum_X_mul_codeProj_mul_X`). For an isometry `E` onto
the code space, `Φ(|z⟩ ⊗ ℓ) = X(z) E ℓ` is then unitary, and it intertwines: `X(a)` shifts `z` by
`a`, and `Z(b)` acts on `X(z) E ℓ` by the sign `(-1)^{b·z}`.

## Main definitions

* `Cslib.Quantum.PauliRep`: matrices satisfying the Pauli relations.
* `Cslib.Quantum.PauliRep.codeProj`: the projection onto the joint `+1` eigenspace of the `Z(b)`.
* `Cslib.Quantum.PauliRep.standard`: the Pauli strings `X^a`, `Z^b`.

## Main results

* `Cslib.Quantum.PauliRep.exists_isometry_codeProj`: an isometry onto the code space.
* `Cslib.Quantum.PauliRep.exists_unitary_eq_pauli`: the Stone–von Neumann theorem for qubits.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

@[expose] public section

open Matrix Finset Cslib.BitString
open scoped Kronecker

namespace Cslib.Quantum

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Hermitian matrices `X(a)`, `Z(b)` on `ℂ^κ`, indexed by bit strings, satisfying the **Pauli
relations**: `X` and `Z` are representations of `(ℤ/2)^ι`, and
`Z(b) X(a) = (-1)^{a·b} X(a) Z(b)`. -/
structure PauliRep (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq κ] where
  /-- The bit-flip observables. -/
  X : (ι → Bool) → Matrix κ κ ℂ
  /-- The phase-flip observables. -/
  Z : (ι → Bool) → Matrix κ κ ℂ
  isHermitian_X : ∀ a, (X a).IsHermitian
  isHermitian_Z : ∀ b, (Z b).IsHermitian
  X_mul : ∀ a a', X a * X a' = X (a + a')
  Z_mul : ∀ b b', Z b * Z b' = Z (b + b')
  X_zero : X 0 = 1
  Z_zero : Z 0 = 1
  Z_mul_X : ∀ a b, Z b * X a = (signVal (a ⬝ᵥ b) : ℂ) • (X a * Z b)

/-- Character orthogonality: `∑_b (-1)^{c·b} = 2ⁿ δ_{c,0}`. -/
private theorem sum_signVal_dotProduct (c : ι → Bool) :
    ∑ b : ι → Bool, (signVal (c ⬝ᵥ b) : ℂ) = if c = 0 then (2 : ℂ) ^ Fintype.card ι else 0 := by
  have h := sum_signVal_dotProduct_mul_signVal_dotProduct c 0
  have h0 : signVal (0 : Bool) = 1 := signVal_false
  simp only [zero_dotProduct, h0, mul_one] at h
  rw [← Complex.ofReal_sum, h]
  split_ifs <;> push_cast <;> rfl

namespace PauliRep

variable (R : PauliRep ι κ)

omit [DecidableEq ι] in
theorem X_mul_self (a : ι → Bool) : R.X a * R.X a = 1 := by
  rw [R.X_mul, BitString.add_self, R.X_zero]

omit [DecidableEq ι] in
theorem X_mul_Z (a b : ι → Bool) : R.X a * R.Z b = (signVal (a ⬝ᵥ b) : ℂ) • (R.Z b * R.X a) := by
  have h := congrArg (fun M => R.X a * M * R.X a) (R.Z_mul_X a b)
  simp only [Matrix.mul_assoc, R.X_mul_self, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul] at h
  rwa [← Matrix.mul_assoc, R.X_mul_self, Matrix.one_mul] at h

/-- The projection `Π = 2^{-n} ∑_b Z(b)` onto the joint `+1` eigenspace of the `Z(b)`. -/
noncomputable def codeProj : Matrix κ κ ℂ :=
  ((2 : ℂ) ^ Fintype.card ι)⁻¹ • ∑ b, R.Z b

theorem Z_mul_codeProj (b : ι → Bool) : R.Z b * R.codeProj = R.codeProj := by
  rw [codeProj, Matrix.mul_smul, Matrix.mul_sum]
  congr 1
  simp only [R.Z_mul]
  exact Fintype.sum_equiv (Equiv.addLeft b) _ _ fun _ => rfl

theorem codeProj_mul_Z (b : ι → Bool) : R.codeProj * R.Z b = R.codeProj := by
  rw [codeProj, Matrix.smul_mul, Matrix.sum_mul]
  congr 1
  simp only [R.Z_mul]
  exact Fintype.sum_equiv (Equiv.addRight b) _ _ fun _ => rfl

theorem isHermitian_codeProj : R.codeProj.IsHermitian := by
  rw [codeProj, IsHermitian, conjTranspose_smul, conjTranspose_sum]
  simp [fun b => (R.isHermitian_Z b).eq]

theorem codeProj_mul_self : R.codeProj * R.codeProj = R.codeProj := by
  nth_rewrite 1 [codeProj]
  rw [Matrix.smul_mul, Matrix.sum_mul]
  simp only [R.Z_mul_codeProj, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]

/-- `Π X(c) Π = δ_{c,0} Π`. -/
theorem codeProj_mul_X_mul_codeProj (c : ι → Bool) :
    R.codeProj * R.X c * R.codeProj = if c = 0 then R.codeProj else 0 := by
  have h1 : R.codeProj * R.X c =
      R.X c * (((2 : ℂ) ^ Fintype.card ι)⁻¹ • ∑ b, (signVal (c ⬝ᵥ b) : ℂ) • R.Z b) := by
    rw [codeProj, Matrix.smul_mul, Matrix.sum_mul, Matrix.mul_smul, Matrix.mul_sum]
    simp only [R.Z_mul_X, Matrix.mul_smul]
  rw [h1, Matrix.mul_assoc, Matrix.smul_mul, Matrix.sum_mul]
  simp only [Matrix.smul_mul, R.Z_mul_codeProj, ← Finset.sum_smul, sum_signVal_dotProduct]
  split_ifs with hc
  · subst hc
    rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul, R.X_zero,
      Matrix.one_mul]
  · simp

/-- `∑_z X(z) Π X(z) = 1`. -/
theorem sum_X_mul_codeProj_mul_X : ∑ z, R.X z * R.codeProj * R.X z = 1 := by
  have h1 (z b : ι → Bool) : R.X z * R.Z b * R.X z = (signVal (z ⬝ᵥ b) : ℂ) • R.Z b := by
    rw [R.X_mul_Z, Matrix.smul_mul, Matrix.mul_assoc, R.X_mul_self, Matrix.mul_one]
  have h2 (z : ι → Bool) : R.X z * R.codeProj * R.X z =
      ((2 : ℂ) ^ Fintype.card ι)⁻¹ • ∑ b, (signVal (b ⬝ᵥ z) : ℂ) • R.Z b := by
    rw [codeProj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
    simp only [h1, dotProduct_comm]
  simp only [h2, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, sum_signVal_dotProduct, ite_smul, zero_smul, sum_ite_eq',
    mem_univ, ite_true, R.Z_zero, smul_smul]
  rw [inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]

omit [Fintype ι] [DecidableEq ι] in
private theorem boolVec_add_eq_zero_iff {z z' : ι → Bool} : z + z' = 0 ↔ z = z' :=
  ⟨fun h => by simpa [add_assoc, BitString.add_self] using congrArg (· + z') h,
    fun h => h ▸ BitString.add_self z⟩

/-- `Eᴴ X(z) X(z') E = δ_{z,z'}` for an isometry `E` onto the code space. -/
private theorem isometry_X_mul_X {L : Type*} [DecidableEq L] {E : Matrix κ L ℂ}
    (hEE : Eᴴ * E = 1) (hPE : R.codeProj * E = E) (z z' : ι → Bool) :
    Eᴴ * (R.X z * R.X z') * E = if z = z' then 1 else 0 := by
  have hEPh : Eᴴ * R.codeProj = Eᴴ := by
    rw [← R.isHermitian_codeProj.eq, ← conjTranspose_mul, hPE]
  calc Eᴴ * (R.X z * R.X z') * E
      = (Eᴴ * R.codeProj) * R.X (z + z') * (R.codeProj * E) := by rw [R.X_mul, hEPh, hPE]
    _ = Eᴴ * (R.codeProj * R.X (z + z') * R.codeProj) * E := by simp only [Matrix.mul_assoc]
    _ = if z = z' then 1 else 0 := by
      rw [codeProj_mul_X_mul_codeProj]
      by_cases h : z = z'
      · simp [h, Matrix.mul_assoc, hPE, hEE]
      · simp [h, boolVec_add_eq_zero_iff]
/-- The code space has an isometry: `E` with `Eᴴ E = 1` and `E Eᴴ = Π`. -/
theorem exists_isometry_codeProj : ∃ L : Finset κ, ∃ E : Matrix κ L ℂ,
    Eᴴ * E = 1 ∧ E * Eᴴ = R.codeProj :=
  R.isHermitian_codeProj.exists_isometry_of_mul_self R.codeProj_mul_self

/-- **Stone–von Neumann for the Pauli relations**: Hermitian matrices satisfying the Pauli
relations are unitarily equivalent to the Pauli strings on `n` qubits tensored with the identity:
there is a unitary `Φ : ℂ^{2ⁿ} ⊗ ℂ^L → ℂ^κ` with `X(a) = Φ (X^a ⊗ 1) Φᴴ` and
`Z(b) = Φ (Z^b ⊗ 1) Φᴴ`. -/
theorem exists_unitary_eq_pauli : ∃ (L : Finset κ) (Φ : Matrix κ ((ι → Bool) × L) ℂ),
    Φᴴ * Φ = 1 ∧ Φ * Φᴴ = 1 ∧ (∀ a, R.X a = Φ * (pauliXPow a ⊗ₖ (1 : Matrix L L ℂ)) * Φᴴ) ∧
      ∀ b, R.Z b = Φ * (pauliZPow b ⊗ₖ (1 : Matrix L L ℂ)) * Φᴴ := by
  obtain ⟨L, E, hEE, hEP⟩ := R.exists_isometry_codeProj
  have hPE : R.codeProj * E = E := by rw [← hEP, Matrix.mul_assoc, hEE, Matrix.mul_one]
  have hZE : ∀ b, R.Z b * E = E := fun b => by rw [← hPE, ← Matrix.mul_assoc, R.Z_mul_codeProj]
  let Φ : Matrix κ ((ι → Bool) × L) ℂ := Matrix.of fun i p => (R.X p.1 * E) i p.2
  have hΦΦ : Φᴴ * Φ = 1 := by
    ext ⟨z, l⟩ ⟨z', l'⟩
    have h := congrFun (congrFun (R.isometry_X_mul_X hEE hPE z z') l) l'
    change ((R.X z * E)ᴴ * (R.X z' * E)) l l' = _
    rw [conjTranspose_mul, (R.isHermitian_X z).eq, ← Matrix.mul_assoc, Matrix.mul_assoc Eᴴ, h]
    by_cases hz : z = z'
    · subst hz; simp [Matrix.one_apply]
    · simp [hz]
  have hΦΦ' : Φ * Φᴴ = 1 := by
    rw [← R.sum_X_mul_codeProj_mul_X]
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]
    refine sum_congr rfl fun z _ => ?_
    have hz : R.X z * R.codeProj * R.X z = (R.X z * E) * (R.X z * E)ᴴ := by
      rw [← hEP, conjTranspose_mul, (R.isHermitian_X z).eq, Matrix.mul_assoc, Matrix.mul_assoc,
        ← Matrix.mul_assoc (R.X z)]
    rw [hz]; rfl
  have hΦ_kron (A : Matrix (ι → Bool) (ι → Bool) ℂ) (i : κ) (z : ι → Bool) (l : L) :
      (Φ * (A ⊗ₖ (1 : Matrix L L ℂ))) i (z, l) = ∑ z', (R.X z' * E) i l * A z' z := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    exact sum_congr rfl fun z' _ => by simp [Φ, Matrix.one_apply]
  have hX (a : ι → Bool) : R.X a * Φ = Φ * (pauliXPow a ⊗ₖ (1 : Matrix L L ℂ)) := by
    ext i ⟨z, l⟩
    rw [hΦ_kron]
    have hiff (z' : ι → Bool) : (z = z' + a) ↔ (z' = z + a) := by
      constructor <;> rintro rfl <;> simp
    simp only [pauliXPow_apply, hiff, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
    change (R.X a * (R.X z * E)) i l = _
    rw [← Matrix.mul_assoc, R.X_mul, add_comm]
  have hZ (b : ι → Bool) : R.Z b * Φ = Φ * (pauliZPow b ⊗ₖ (1 : Matrix L L ℂ)) := by
    ext i ⟨z, l⟩
    rw [hΦ_kron]
    simp only [pauliZPow_apply, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
    change (R.Z b * (R.X z * E)) i l = _
    rw [← Matrix.mul_assoc, R.Z_mul_X, Matrix.smul_mul, Matrix.mul_assoc, hZE,
      Matrix.smul_apply, smul_eq_mul, dotProduct_comm, mul_comm]
  exact ⟨L, Φ, hΦΦ, hΦΦ', fun a => by rw [← hX, Matrix.mul_assoc, hΦΦ', Matrix.mul_one],
    fun b => by rw [← hZ, Matrix.mul_assoc, hΦΦ', Matrix.mul_one]⟩

end PauliRep

/-- The Pauli strings on `ι → Bool` satisfy the Pauli relations. -/
noncomputable def PauliRep.standard : PauliRep ι (ι → Bool) where
  X := pauliXPow
  Z := pauliZPow
  isHermitian_X := pauliXPow_isHermitian
  isHermitian_Z := pauliZPow_isHermitian
  X_mul := pauliXPow_mul
  Z_mul := pauliZPow_mul
  X_zero := pauliXPow_zero
  Z_zero := pauliZPow_zero
  Z_mul_X := pauliZPow_mul_pauliXPow

end Cslib.Quantum
