/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Expect
import CslibFrontier.Tactic.CommuteLeft
public import CslibFrontier.Foundations.Quantum.PauliGroup
public import CslibFrontier.Foundations.Data.BitString.Sign

/-!
# The Pauli family and its defect

Observables `X(a)`, `Z(b)`, indexed by bit strings, define the **Pauli family**
`f(s, a, b) = (-1)^s X(a) Z(b)` on the Pauli group (`Cslib.Quantum.pauliFamily`). Its
multiplicative defect `E_{p,q} ‖f(p) f(q) - f(pq)‖²_φ` measures how far `X` and `Z` are from the
Pauli relations in the state `φ`. It is the hypothesis of the compression bound for the Pauli
family (`Cslib.Quantum.exists_isometry_compress_pauliFamily`).

This file bounds the defect by the conditions a nonlocal game can test, in the commuting model,
where Bob's observables `Zᴮ(b)` commute with Alice's `X`, `Z`
(`Cslib.Quantum.expect_norm_pauliFamily_sub_sq_le`):

`E_{p,q} ‖f(p) f(q) - f(pq)‖²_φ ≤ 5 (8 ε_c + ε_a + ε_X + ε_Z)`.

Here:
* `ε_c = E_b ‖Z(b) - Zᴮ(b)‖²_φ` is the consistency of Alice's `Z` with Bob's;
* `ε_a = E_{a,b} ‖Z(b) X(a) - (-1)^{a·b} X(a) Z(b)‖²_φ` is the anticommutation defect;
* `ε_X`, `ε_Z` are the linearity defects `E ‖X(a) X(a') - X(a+a')‖²_φ` and
  `E ‖Z(b) Z(b') - Z(b+b')‖²_φ`.

This is a bridge for *unitary* families. It relates to the conditions of the Pauli braiding
analysis [Natarajan and Vidick, §4.2, Theorem 13][NatarajanVidick2017] (arXiv:1610.03574v1,
p. 19; that version is titled *Robust self-testing of many-qubit states*) as follows:

* the source's operators, eq. (11) on p. 18, are averaged marginals of the provers' measurements,
  not unitaries; deriving unitary families `X`, `Z`, `Zᴮ` from a strategy is a further input;
* the source separates anticommutation on the pairs with `a·b = 1` from commutation on the pairs
  with `a·b = 0`; the defect `ε_a` here combines both over all pairs, as the signed relation
  `Z(b) X(a) = (-1)^{a·b} X(a) Z(b)`;
* only the consistency of `Z` is needed here.

The connection from the game to these unitary families and the all-pairs error is tracked in
[#6149](https://github.com/cslib-community/cslib-frontier/issues/6149) (milestone M3).

The proof is a `calc` chain in the state calculus (`Cslib.Quantum.norm_mul_mul_mul_sub_le`).
Multiplication on the right does not preserve closeness in a state. So each operator that must be
replaced at the right end of a product is first exchanged with Bob's consistent copy, commuted to
the left, and absorbed by a unitary there (left multiplication by a unitary preserves closeness).

## Main definitions

* `Cslib.Quantum.pauliFamily`: `(s, a, b) ↦ (-1)^s X(a) Z(b)`.

## Main results

* `Cslib.Quantum.expect_pauliGroup`, `Cslib.Quantum.expect_pauliGroup₂`: averages over the Pauli
  group are averages over bit strings.
* `Cslib.Quantum.norm_mul_mul_mul_sub_le`: the pointwise defect bound.
* `Cslib.Quantum.expect_norm_pauliFamily_sub_sq_le`: the defect from consistency, anticommutation
  and linearity.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

@[expose] public section

open Finset Cslib.BitString
open scoped BigOperators

namespace Cslib.Quantum

variable {A : Type*} [Ring A] [Algebra ℂ A] {ι : Type*} [Fintype ι]

open PauliGroup

/-- The **Pauli family** `(s, a, b) ↦ (-1)^s X(a) Z(b)` of observables `X`, `Z`. -/
noncomputable def pauliFamily (X Z : (ι → Bool) → A) (p : PauliGroup ι) : A :=
  (signVal p.sign : ℂ) • (X p.x * Z p.z)

/-- Averaging over the Pauli group averages over the two bit strings; the sign does not matter. -/
theorem expect_pauliGroup [DecidableEq ι] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (ι → Bool) → (ι → Bool) → M) :
    𝔼 p : PauliGroup ι, F p.x p.z = 𝔼 a, 𝔼 b, F a b := by
  rw [Fintype.expect_equiv equivProd (fun p => F p.x p.z) (fun t => F t.2.1 t.2.2) (fun _ => rfl),
    ← Finset.univ_product_univ, Finset.expect_product]
  dsimp only
  rw [Finset.expect_const Finset.univ_nonempty, ← Finset.univ_product_univ, Finset.expect_product]

/-- Averaging over pairs of Pauli group elements averages over four bit strings. -/
theorem expect_pauliGroup₂ [DecidableEq ι] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (G : (ι → Bool) → (ι → Bool) → (ι → Bool) → (ι → Bool) → M) :
    𝔼 p : PauliGroup ι, 𝔼 q : PauliGroup ι, G p.x p.z q.x q.z =
      𝔼 a, 𝔼 b, 𝔼 a', 𝔼 b', G a b a' b' := by
  rw [expect_pauliGroup (fun a b => 𝔼 q : PauliGroup ι, G a b q.x q.z)]
  exact Finset.expect_congr rfl fun a _ => Finset.expect_congr rfl fun b _ =>
    expect_pauliGroup (G a b)

/-- The defect of the Pauli family at `(p, q)`, up to a sign. -/
theorem pauliFamily_mul_sub (X Z : (ι → Bool) → A) (p q : PauliGroup ι) :
    pauliFamily X Z p * pauliFamily X Z q - pauliFamily X Z (p * q) =
      (signVal (p.sign + q.sign) : ℂ) • (X p.x * Z p.z * X q.x * Z q.z -
        (signVal (q.x ⬝ᵥ p.z) : ℂ) • (X (p.x + q.x) * Z (p.z + q.z))) := by
  have hs₁ : (signVal (p.sign + q.sign) : ℂ) = signVal p.sign * signVal q.sign := by
    rw [show p.sign + q.sign = (p.sign ^^ q.sign) from rfl, signVal_xor]; push_cast; rfl
  have hs₂ : (signVal (p * q).sign : ℂ) =
      signVal p.sign * signVal q.sign * signVal (q.x ⬝ᵥ p.z) := by
    rw [PauliGroup.mul_sign, dotProduct_comm p.z q.x,
      show p.sign + q.sign + q.x ⬝ᵥ p.z = ((p.sign ^^ q.sign) ^^ q.x ⬝ᵥ p.z) from rfl,
      signVal_xor, signVal_xor]
    push_cast; rfl
  simp only [pauliFamily, smul_mul_smul_comm, hs₁, hs₂, PauliGroup.mul_x, PauliGroup.mul_z,
    smul_sub, smul_smul, mul_assoc]

theorem pauliFamily_negOne_mul (X Z : (ι → Bool) → A) (p : PauliGroup ι) :
    pauliFamily X Z (negOne * p) = -pauliFamily X Z p := by
  rw [negOne_mul, pauliFamily, pauliFamily, signVal_not]
  push_cast
  rw [neg_smul]

section State

variable [StarRing A] [PartialOrder A] [StarOrderedRing A] [StarModule ℂ A]
  [SelfAdjointDecompose A]

open AlgState

/-- **Pointwise Pauli defect** (Bob trick): with Bob's observables `Zᴮ(b)` commuting with Alice's
`X`, `Z`, `‖X(a)Z(b)X(a')Z(b') - (-1)^{a'·b} X(a+a')Z(b+b')‖_φ` is at most
`2c(b) + 2c(b') + α(a', b) + ℓ_X(a, a') + ℓ_Z(b, b')`. -/
theorem norm_mul_mul_mul_sub_le (φ : AlgState A) (X Z ZB : (ι → Bool) → A)
    (hX : ∀ a, X a ∈ unitary A) (hZ : ∀ b, Z b ∈ unitary A) (hZB : ∀ b, ZB b ∈ unitary A)
    (hXB : ∀ a b, Commute (X a) (ZB b)) (hZZB : ∀ b b', Commute (Z b) (ZB b'))
    (a b a' b' : ι → Bool) :
    φ.norm (X a * Z b * X a' * Z b' - (signVal (a' ⬝ᵥ b) : ℂ) • (X (a + a') * Z (b + b'))) ≤
      2 * φ.norm (Z b - ZB b) + 2 * φ.norm (Z b' - ZB b') +
        φ.norm (Z b * X a' - (signVal (a' ⬝ᵥ b) : ℂ) • (X a' * Z b)) +
        φ.norm (X a * X a' - X (a + a')) + φ.norm (Z b * Z b' - Z (b + b')) := by
  set s : ℂ := (signVal (a' ⬝ᵥ b) : ℂ)
  have hs : ‖s‖ = 1 := by simp [s]
  have c1 : ∀ c, Z c ≈[φ; φ.norm (Z c - ZB c)] ZB c := fun c => φ.approx_norm_sub _ _
  have c2 : ∀ c, ZB c ≈[φ; φ.norm (Z c - ZB c)] Z c := fun c => (c1 c).symm
  have chain := calc
      X a * Z b * X a' * Z b' ≈[φ; φ.norm (Z b' - ZB b')] X a * Z b * X a' * ZB b' :=
        (c1 b').mul_left_unitary (by unitary_mem)
    _ = ZB b' * X a * (Z b * X a') := by commute_left [hXB, hZZB]
    _ ≈[φ; φ.norm (Z b * X a' - s • (X a' * Z b))] ZB b' * X a * (s • (X a' * Z b)) :=
        (φ.approx_norm_sub _ _).mul_left_unitary (by unitary_mem)
    _ = s • (ZB b' * (X a * X a') * Z b) := by
        rw [mul_smul_comm]; simp only [mul_assoc]
    _ ≈[φ; ‖s‖ * φ.norm (Z b - ZB b)] s • (ZB b' * (X a * X a') * ZB b) :=
        ((c1 b).mul_left_unitary (by unitary_mem)).smul s
    _ = s • (ZB b' * ZB b * (X a * X a')) := by commute_left [hXB]
    _ ≈[φ; ‖s‖ * φ.norm (X a * X a' - X (a + a'))] s • (ZB b' * ZB b * X (a + a')) :=
        ((φ.approx_norm_sub _ _).mul_left_unitary (by unitary_mem)).smul s
    _ = s • (X (a + a') * ZB b' * ZB b) := by commute_left [hXB]
    _ ≈[φ; ‖s‖ * φ.norm (Z b - ZB b)] s • (X (a + a') * ZB b' * Z b) :=
        ((c2 b).mul_left_unitary (by unitary_mem)).smul s
    _ = s • (X (a + a') * Z b * ZB b') := by commute_left [hXB, hZZB]
    _ ≈[φ; ‖s‖ * φ.norm (Z b' - ZB b')] s • (X (a + a') * Z b * Z b') :=
        ((c2 b').mul_left_unitary (by unitary_mem)).smul s
    _ ≈[φ; ‖s‖ * φ.norm (Z b * Z b' - Z (b + b'))] s • (X (a + a') * Z (b + b')) := by
        rw [mul_assoc]; exact ((φ.approx_norm_sub _ _).mul_left_unitary (hX _)).smul s
  rw [approx_iff] at chain
  simp only [hs, one_mul] at chain
  linarith

/-- `(x₁ + ⋯ + x₅)² ≤ 5 (x₁² + ⋯ + x₅²)`, Cauchy–Schwarz against the constant `1`. -/
private theorem sq_add₅_le (x₁ x₂ x₃ x₄ x₅ : ℝ) :
    (x₁ + x₂ + x₃ + x₄ + x₅) ^ 2 ≤ 5 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 + x₅ ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ ![x₁, x₂, x₃, x₄, x₅] fun _ => (1 : ℝ)
  simp only [Fin.sum_univ_five, Matrix.cons_val, mul_one, one_pow] at h
  linarith

/-- **The Pauli-family defect from game-level conditions**: with Bob's observables `Zᴮ(b)`
commuting with Alice's `X`, `Z`,
`E_{p,q} ‖f(p) f(q) - f(pq)‖²_φ ≤ 5 (8 ε_c + ε_a + ε_X + ε_Z)`, where `ε_c` is the consistency
`E_b ‖Z(b) - Zᴮ(b)‖²_φ`, `ε_a` the anticommutation `E_{a,b} ‖Z(b)X(a) - (-1)^{a·b} X(a)Z(b)‖²_φ`,
and `ε_X`, `ε_Z` the linearity defects `E ‖X(a)X(a') - X(a+a')‖²_φ` and
`E ‖Z(b)Z(b') - Z(b+b')‖²_φ`. -/
theorem expect_norm_pauliFamily_sub_sq_le [DecidableEq ι] (φ : AlgState A)
    (X Z ZB : (ι → Bool) → A)
    (hX : ∀ a, X a ∈ unitary A) (hZ : ∀ b, Z b ∈ unitary A) (hZB : ∀ b, ZB b ∈ unitary A)
    (hXB : ∀ a b, Commute (X a) (ZB b)) (hZZB : ∀ b b', Commute (Z b) (ZB b')) :
    𝔼 p, 𝔼 q, φ.norm (pauliFamily X Z p * pauliFamily X Z q - pauliFamily X Z (p * q)) ^ 2 ≤
      5 * (8 * 𝔼 b, φ.norm (Z b - ZB b) ^ 2 +
        𝔼 a, 𝔼 b, φ.norm (Z b * X a - (signVal (a ⬝ᵥ b) : ℂ) • (X a * Z b)) ^ 2 +
        𝔼 a, 𝔼 a', φ.norm (X a * X a' - X (a + a')) ^ 2 +
        𝔼 b, 𝔼 b', φ.norm (Z b * Z b' - Z (b + b')) ^ 2) := by
  set c := fun b => φ.norm (Z b - ZB b)
  set α := fun a b => φ.norm (Z b * X a - (signVal (a ⬝ᵥ b) : ℂ) • (X a * Z b))
  set ℓX := fun a a' => φ.norm (X a * X a' - X (a + a'))
  set ℓZ := fun b b' => φ.norm (Z b * Z b' - Z (b + b'))
  have hpt : ∀ p q : PauliGroup ι,
      φ.norm (pauliFamily X Z p * pauliFamily X Z q - pauliFamily X Z (p * q)) ^ 2 ≤
      5 * (4 * c p.z ^ 2 + 4 * c q.z ^ 2 + α q.x p.z ^ 2 + ℓX p.x q.x ^ 2 +
        ℓZ p.z q.z ^ 2) := fun p q => by
    rw [pauliFamily_mul_sub, AlgState.norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_signVal, one_mul]
    have h := norm_mul_mul_mul_sub_le φ X Z ZB hX hZ hZB hXB hZZB p.x p.z q.x q.z
    have h0 := φ.norm_nonneg (X p.x * Z p.z * X q.x * Z q.z -
      (signVal (q.x ⬝ᵥ p.z) : ℂ) • (X (p.x + q.x) * Z (p.z + q.z)))
    refine (pow_le_pow_left₀ h0 h 2).trans ?_
    refine (sq_add₅_le _ _ _ _ _).trans (le_of_eq ?_)
    simp only [c, α, ℓX, ℓZ]
    ring
  refine (Finset.expect_le_expect fun p _ => Finset.expect_le_expect fun q _ => hpt p q).trans
    (le_of_eq ?_)
  rw [expect_pauliGroup₂ (fun a b a' b' => 5 * (4 * c b ^ 2 + 4 * c b' ^ 2 + α a' b ^ 2 +
    ℓX a a' ^ 2 + ℓZ b b' ^ 2))]
  simp only [← Finset.mul_expect, Finset.expect_add_distrib, Fintype.expect_const]
  rw [Finset.expect_comm Finset.univ Finset.univ (fun a b => α b a ^ 2)]
  ring

end State

end Cslib.Quantum
