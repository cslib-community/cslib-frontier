/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Involution
public import CslibFrontier.Foundations.Quantum.PauliGroup
public import CslibFrontier.Foundations.Quantum.PauliStoneVonNeumann
public import CslibFrontier.Foundations.Quantum.RegularCompression
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Polar

/-!
# Compression of the Pauli family

A step toward robust Pauli rigidity, the analysis of the Pauli braiding test
[Natarajan and Vidick, §4.2, Theorem 14][NatarajanVidick2017] (arXiv:1610.03574v1, p. 19). That
theorem starts from consistency, linearity and anticommutation conditions of a strategy and
produces exact Pauli operators close to each generator `X(a)`, `Z(b)` on an enlarged state. This
file proves the compression bound behind it, for the products `X(a) Z(b)`. For unitaries `X(a)`,
`Z(b)` on `ℂ^κ` there is one isometry `W : ℂ^κ → ℂ^{2ⁿ} ⊗ ℂ^J` with, in every state `φ`,

`E_{a,b} ‖X(a) Z(b) - Wᴴ (X^a Z^b ⊗ 1) W‖²_φ ≤ E_{p,q} ‖f(p) f(q) - f(pq)‖²_φ`,

where `f(s, a, b) = (-1)^s X(a) Z(b)` is the **Pauli family** on the Pauli group
(`Cslib.Quantum.pauliFamily`), and the right side is its multiplicative defect
(`Cslib.Quantum.exists_isometry_compress_pauliFamily`). The bound does not depend on `n`.

Two steps toward Theorem 14 are not formalized here: bounding the defect of the Pauli family by
the consistency, linearity and anticommutation conditions, and passing from the products to the
individual generators. Both are tracked in
[#6149](https://github.com/cslib-community/cslib-frontier/issues/6149) (milestone M3). The bound
alone does not certify the generators: `X(a) = -X^a`, `Z(b) = -Z^b` give the Pauli strings as
products, with defect `0`, but `X(0) = Z(0) = -1`.

The proof composes three steps:

* compress the regular representation `g` of the Pauli group through the averaging isometry `V`
  of `f` (`Cslib.Quantum.expect_norm_sub_compress_sq_le`), which bounds
  `E_p ‖f(p) - Vᴴ g(p) V‖²_φ` in every state;
* since `f(-p) = -f(p)` exactly, `g(-1) V = -V` exactly
  (`Cslib.Quantum.regularRep_negOne_mul_regularIsometry`), so `V` maps into the `-1` eigenspace of
  the central element, the range of the eigenspace projection `signProj (g(-1)) true` of
  `Cslib.Quantum.signProj`, on which `g` compresses to an exact representation of the Pauli
  relations (`Cslib.Quantum.codeRep`);
* by the Stone–von Neumann theorem for qubits
  (`Cslib.Quantum.PauliRep.exists_unitary_eq_pauli`) that representation is the Pauli strings
  tensored with the identity.

## Main definitions

* `Cslib.Quantum.pauliFamily`: `(s, a, b) ↦ (-1)^s X(a) Z(b)`.
* `Cslib.Quantum.codeRep`: the compressed regular representation, satisfying the Pauli relations.

## Main results

* `Cslib.Quantum.pauliFamily_pauliXPow_mul`: the Pauli strings are an exact representation.
* `Cslib.Quantum.regularRep_negOne_mul_regularIsometry`: `g(-1) V = -V`.
* `Cslib.Quantum.exists_isometry_compress_pauliFamily`: the compression bound for the Pauli family.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

@[expose] public section

open Matrix Finset Cslib.BitString
open scoped BigOperators

namespace Cslib.Quantum

open PauliGroup

section Rep

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The regular representation of the Pauli group on `ℂ^κ ⊗ ℂ^{P_ι}`. -/
local notation "reg" => regularRep (ι := κ) (G := PauliGroup ι)

theorem regularRep_negOne_mul_self : reg negOne * reg negOne = 1 := by
  rw [regularRep_mul, negOne_mul_negOne, regularRep_one]

omit [Fintype κ] [DecidableEq ι] in
theorem isHermitian_regularRep_of_inv {y : PauliGroup ι} (hy : y⁻¹ = y) : (reg y).IsHermitian := by
  rw [IsHermitian, conjTranspose_regularRep, hy]

theorem commute_regularRep_negOne (y : PauliGroup ι) : reg negOne * reg y = reg y * reg negOne := by
  rw [regularRep_mul, regularRep_mul, commute_negOne]

private theorem isHermitian_signProj_regularRep_negOne :
    (signProj (reg negOne) true).IsHermitian :=
  isSelfAdjoint_signProj (isHermitian_regularRep_of_inv negOne_inv).isSelfAdjoint true

private theorem regularRep_negOne_mul_signProj :
    reg negOne * signProj (reg negOne) true = -signProj (reg negOne) true := by
  rw [mul_signProj regularRep_negOne_mul_self, signVal_true]
  push_cast
  rw [neg_one_smul]

private theorem commute_regularRep_signProj (y : PauliGroup ι) :
    reg y * signProj (reg negOne) true = signProj (reg negOne) true * reg y :=
  ((show Commute (reg negOne) (reg y) from commute_regularRep_negOne y).signProj_left true).eq.symm

variable {L : Type*} [Fintype L] [DecidableEq L] {E : Matrix (κ × PauliGroup ι) L ℂ}

private theorem compress_mul (hEE : Eᴴ * E = 1) (hEP : E * Eᴴ = signProj (reg negOne) true)
    (y y' : PauliGroup ι) :
    Eᴴ * reg y * E * (Eᴴ * reg y' * E) = Eᴴ * reg (y * y') * E := by
  have hPE : signProj (reg negOne) true * E = E := by
    rw [← hEP, Matrix.mul_assoc, hEE, Matrix.mul_one]
  rw [show Eᴴ * reg y * E * (Eᴴ * reg y' * E) = Eᴴ * reg y * (E * Eᴴ) * reg y' * E by
    simp only [Matrix.mul_assoc], hEP, Matrix.mul_assoc (Eᴴ * reg y),
    ← commute_regularRep_signProj,
    ← Matrix.mul_assoc, Matrix.mul_assoc _ _ E, hPE, ← regularRep_mul]
  simp only [Matrix.mul_assoc]

private theorem compress_negOne_mul (hEE : Eᴴ * E = 1) (hEP : E * Eᴴ = signProj (reg negOne) true)
    (y : PauliGroup ι) : Eᴴ * reg (negOne * y) * E = -(Eᴴ * reg y * E) := by
  have hPE : signProj (reg negOne) true * E = E := by
    rw [← hEP, Matrix.mul_assoc, hEE, Matrix.mul_one]
  have hJE : reg negOne * E = -E := by
    rw [← hPE, ← Matrix.mul_assoc, regularRep_negOne_mul_signProj, Matrix.neg_mul]
  rw [← regularRep_mul, commute_regularRep_negOne]
  simp only [Matrix.mul_assoc]
  rw [hJE]
  simp

/-- The regular representation compressed to the `-1` eigenspace of the central element satisfies
the Pauli relations. -/
noncomputable def codeRep (hEE : Eᴴ * E = 1) (hEP : E * Eᴴ = signProj (reg negOne) true) :
    PauliRep ι L where
  X a := Eᴴ * reg (ofX a) * E
  Z b := Eᴴ * reg (ofZ b) * E
  isHermitian_X a := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      (isHermitian_regularRep_of_inv (ofX_inv a)).eq, Matrix.mul_assoc]
  isHermitian_Z b := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      (isHermitian_regularRep_of_inv (ofZ_inv b)).eq, Matrix.mul_assoc]
  X_mul a a' := by rw [compress_mul hEE hEP, ofX_mul_ofX]
  Z_mul b b' := by rw [compress_mul hEE hEP, ofZ_mul_ofZ]
  X_zero := by rw [ofX_zero, regularRep_one, Matrix.mul_one, hEE]
  Z_zero := by rw [ofZ_zero, regularRep_one, Matrix.mul_one, hEE]
  Z_mul_X a b := by
    rw [compress_mul hEE hEP, compress_mul hEE hEP, ofZ_mul_ofX]
    cases h : a ⬝ᵥ b
    · simp
    · simp [compress_negOne_mul hEE hEP]

/-- The **Pauli family** `(s, a, b) ↦ (-1)^s X(a) Z(b)` of observables `X`, `Z`. -/
noncomputable def pauliFamily (X Z : (ι → Bool) → Matrix κ κ ℂ) (p : PauliGroup ι) :
    Matrix κ κ ℂ :=
  (signVal p.sign : ℂ) • (X p.x * Z p.z)

variable (X Z : (ι → Bool) → Matrix κ κ ℂ)

omit [DecidableEq ι] [DecidableEq κ] in
theorem pauliFamily_negOne_mul (p : PauliGroup ι) :
    pauliFamily X Z (negOne * p) = -pauliFamily X Z p := by
  rw [negOne_mul, pauliFamily, pauliFamily, signVal_not]
  push_cast
  rw [neg_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem conjTranspose_pauliFamily_mul (hX : ∀ a, (X a)ᴴ * X a = 1) (hZ : ∀ b, (Z b)ᴴ * Z b = 1)
    (p : PauliGroup ι) : (pauliFamily X Z p)ᴴ * pauliFamily X Z p = 1 := by
  have h1 : (Z p.z)ᴴ * (X p.x)ᴴ * (X p.x * Z p.z) = 1 := by
    rw [show (Z p.z)ᴴ * (X p.x)ᴴ * (X p.x * Z p.z) = (Z p.z)ᴴ * ((X p.x)ᴴ * X p.x) * Z p.z by
      simp only [Matrix.mul_assoc], hX, Matrix.mul_one, hZ]
  rw [pauliFamily, conjTranspose_smul, smul_mul_smul_comm, conjTranspose_mul, h1,
    Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, signVal_mul_self,
    Complex.ofReal_one, one_smul]

omit [DecidableEq κ] in
/-- The Pauli strings form an exact representation of the Pauli group. -/
theorem pauliFamily_pauliXPow_mul (p q : PauliGroup ι) :
    pauliFamily pauliXPow pauliZPow p * pauliFamily pauliXPow pauliZPow q =
      pauliFamily pauliXPow pauliZPow (p * q) := by
  simp only [pauliFamily, smul_mul_smul_comm, PauliGroup.mul_sign, PauliGroup.mul_x,
    PauliGroup.mul_z]
  rw [show pauliXPow p.x * pauliZPow p.z * (pauliXPow q.x * pauliZPow q.z) =
      pauliXPow p.x * (pauliZPow p.z * pauliXPow q.x) * pauliZPow q.z by
    simp only [Matrix.mul_assoc], pauliZPow_mul_pauliXPow, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, show pauliXPow p.x * (pauliXPow q.x * pauliZPow p.z) * pauliZPow q.z =
      pauliXPow p.x * pauliXPow q.x * (pauliZPow p.z * pauliZPow q.z) by
    simp only [Matrix.mul_assoc], pauliXPow_mul, pauliZPow_mul, dotProduct_comm q.x p.z]
  congr 1
  have : signVal (p.sign + q.sign + p.z ⬝ᵥ q.x) =
      signVal p.sign * signVal q.sign * signVal (p.z ⬝ᵥ q.x) := by
    rw [show p.sign + q.sign + p.z ⬝ᵥ q.x = ((p.sign ^^ q.sign) ^^ p.z ⬝ᵥ q.x) from rfl,
      signVal_xor, signVal_xor]
  rw [this]
  push_cast
  ring

/-- The averaging isometry of the Pauli family lies in the `-1` eigenspace of the central element:
`g(-1) V = -V`, exactly. -/
theorem regularRep_negOne_mul_regularIsometry :
    reg negOne * regularIsometry (pauliFamily X Z) = -regularIsometry (pauliFamily X Z) := by
  ext ⟨i, z⟩ j
  rw [Matrix.mul_apply, sum_eq_single (i, z * negOne) (fun q _ hq => by
    rw [regularRep_apply, ite_eq_right hq, zero_mul]) (by simp)]
  rw [regularRep_apply, ite_eq_left rfl, one_mul, Matrix.neg_apply, regularIsometry_apply,
    regularIsometry_apply, ← commute_negOne, pauliFamily_negOne_mul, Matrix.neg_apply, mul_neg]

theorem signProj_regularRep_negOne_mul_regularIsometry :
    signProj (reg negOne) true * regularIsometry (pauliFamily X Z) =
      regularIsometry (pauliFamily X Z) := by
  rw [signProj, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
    regularRep_negOne_mul_regularIsometry, signVal_true, smul_neg]
  push_cast
  rw [neg_one_smul, neg_neg, ← two_smul ℂ, smul_smul]
  norm_num

end Rep

section Robust

open scoped Kronecker MatrixOrder

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {κ : Type v} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
/-- Averaging over the Pauli group averages over the two bit strings; the sign does not matter. -/
private theorem expect_pauliGroup (F : (ι → Bool) → (ι → Bool) → ℝ) :
    𝔼 p : PauliGroup ι, F p.x p.z = 𝔼 a, 𝔼 b, F a b := by
  rw [Fintype.expect_equiv equivProd (fun p => F p.x p.z) (fun t => F t.2.1 t.2.2) (fun _ => rfl),
    ← Finset.univ_product_univ, Finset.expect_product]
  dsimp only
  rw [Finset.expect_const Finset.univ_nonempty, ← Finset.univ_product_univ, Finset.expect_product]

/-- **Compression of the Pauli family**, a step toward robust Pauli rigidity
[Natarajan and Vidick, §4.2, Theorem 14][NatarajanVidick2017]: for unitaries `X(a)`, `Z(b)` on
`ℂ^κ` there is one isometry `W : ℂ^κ → ℂ^{2ⁿ} ⊗ ℂ^J` under which, in **every** state `φ`, the
products `X(a) Z(b)` are close on average to the Pauli strings `X^a Z^b ⊗ 1`, with error the
multiplicative defect of the Pauli family `(s, a, b) ↦ (-1)^s X(a) Z(b)` and no dependence on
`n`. -/
theorem exists_isometry_compress_pauliFamily (X Z : (ι → Bool) → Matrix κ κ ℂ)
    (hX : ∀ a, (X a)ᴴ * X a = 1) (hZ : ∀ b, (Z b)ᴴ * Z b = 1) :
    ∃ (J : Type (max u v)) (_ : Fintype J) (_ : DecidableEq J)
      (W : Matrix ((ι → Bool) × J) κ ℂ), Wᴴ * W = 1 ∧ ∀ φ : AlgState (Matrix κ κ ℂ),
      𝔼 a, 𝔼 b, φ.norm (X a * Z b -
          Wᴴ * ((pauliXPow a * pauliZPow b) ⊗ₖ (1 : Matrix J J ℂ)) * W) ^ 2 ≤
        𝔼 p, 𝔼 q, φ.norm (pauliFamily X Z p * pauliFamily X Z q - pauliFamily X Z (p * q)) ^ 2 := by
  set f := pauliFamily X Z
  set V := regularIsometry f
  have hf := conjTranspose_pauliFamily_mul X Z hX hZ
  obtain ⟨L₁, E, hEE, hEP⟩ :=
    (isHermitian_signProj_regularRep_negOne :
      (signProj (regularRep (ι := κ) (negOne : PauliGroup ι)) true).IsHermitian
      ).exists_isometry_of_mul_self (signProj_mul_self regularRep_negOne_mul_self true)
  let R := codeRep hEE hEP
  obtain ⟨L₂, Φ, hΦ1, hΦ2, hXΦ, hZΦ⟩ := R.exists_unitary_eq_pauli
  set W : Matrix ((ι → Bool) × L₂) κ ℂ := Φᴴ * (Eᴴ * V)
  have hEV : E * (Eᴴ * V) = V := by
    rw [← Matrix.mul_assoc, hEP, signProj_regularRep_negOne_mul_regularIsometry]
  have hWW : Wᴴ * W = 1 := by
    simp only [W, conjTranspose_mul, conjTranspose_conjTranspose]
    rw [show Vᴴ * E * Φ * (Φᴴ * (Eᴴ * V)) = Vᴴ * (E * (Φ * Φᴴ) * (Eᴴ * V)) by
      simp only [Matrix.mul_assoc], hΦ2, Matrix.mul_one, hEV]
    exact conjTranspose_regularIsometry_mul f hf
  have hRXZ : ∀ a b, R.X a * R.Z b = Φ * ((pauliXPow a * pauliZPow b) ⊗ₖ
      (1 : Matrix L₂ L₂ ℂ)) * Φᴴ := fun a b => by
    rw [hXΦ, hZΦ, show Φ * (pauliXPow a ⊗ₖ (1 : Matrix L₂ L₂ ℂ)) * Φᴴ *
        (Φ * (pauliZPow b ⊗ₖ (1 : Matrix L₂ L₂ ℂ)) * Φᴴ) =
        Φ * (pauliXPow a ⊗ₖ (1 : Matrix L₂ L₂ ℂ)) * (Φᴴ * Φ) *
          (pauliZPow b ⊗ₖ (1 : Matrix L₂ L₂ ℂ)) * Φᴴ by simp only [Matrix.mul_assoc], hΦ1,
      Matrix.mul_one, Matrix.mul_assoc Φ, ← mul_kronecker_mul, Matrix.mul_one]
  have key : ∀ p : PauliGroup ι, Vᴴ * regularRep p * V = (signVal p.sign : ℂ) •
      (Wᴴ * ((pauliXPow p.x * pauliZPow p.z) ⊗ₖ (1 : Matrix L₂ L₂ ℂ)) * W) := fun p => by
    have hc : Eᴴ * regularRep (ofX p.x * ofZ p.z) * E = R.X p.x * R.Z p.z :=
      (compress_mul hEE hEP _ _).symm
    have hp : Eᴴ * regularRep p * E = (signVal p.sign : ℂ) • (R.X p.x * R.Z p.z) := by
      conv_lhs => rw [p.eq_sign_mul]
      cases h : p.sign
      · simp [hc]
      · simp [compress_negOne_mul hEE hEP, hc]
    calc Vᴴ * regularRep p * V = (E * (Eᴴ * V))ᴴ * regularRep p * (E * (Eᴴ * V)) := by rw [hEV]
      _ = (Eᴴ * V)ᴴ * (Eᴴ * regularRep p * E) * (Eᴴ * V) := by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hp, hRXZ]
          simp only [W, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.smul_mul,
            Matrix.mul_smul, Matrix.mul_assoc]
  refine ⟨L₂, inferInstance, inferInstance, W, hWW, fun φ => ?_⟩
  refine le_of_eq_of_le ?_ (expect_norm_sub_compress_sq_le f φ hf)
  rw [← expect_pauliGroup (fun a b => φ.norm (X a * Z b -
    Wᴴ * ((pauliXPow a * pauliZPow b) ⊗ₖ (1 : Matrix L₂ L₂ ℂ)) * W) ^ 2)]
  refine Finset.expect_congr rfl fun p _ => ?_
  rw [key, show f p = (signVal p.sign : ℂ) • (X p.x * Z p.z) from rfl, ← smul_sub,
    AlgState.norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_signVal, one_mul]

end Robust

end Cslib.Quantum
