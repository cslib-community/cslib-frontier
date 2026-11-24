/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Walk
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Data.Matrix.Mul
import Batteries.Data.Nat.Bitwise.Lemmas
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.PieceFacts

/-!
# The Walsh–Hadamard shape of Lemma 5.1

This file formalizes the remark after Lemma 5.1 (`separating-ntime-from-space.tex`, §5.1, "The lemma
has a familiar shape"). Throughout, types are restricted to `i, j < 2^b`, a matrix is a function of
two types,
and the Walsh–Hadamard matrix is `𝓗(i, j) = chi i j = (-1)^{⟨i,j⟩}`.

* "The matrix `(C_{i,j})` is the tensor product over the bit positions `e < b` of the matrices
  `[[1, z^{2^e}], [z^{2^e}, -1]]`": `C_eq_prod`, `C i j = ∏_{e<b} cBit e (bit e of i) (bit e of j)`,
  where `cBit e` is that matrix with rows and columns indexed by a bit (`false` first). The block
  form of the same statement is `C_kron`: adding bit `b` multiplies by `cBit b`.
* "Each of which squares to `1 + z^{2^{e+1}}` times the identity": `cMat_mul_self`, for the
  matrix `cMat e` of `cBit e`. `sum_C_mul_C_eq_prod` is the tensor square,
  `∑_{n<2^b} C_{i,n} C_{n,j} = [i = j] ∏_{e<b} (1 + z^{2^{e+1}})`, which is Lemma 5.1 in the
  form `sum_C_mul_C` after cancelling `1 - z²`.
* "At `z = 1` it is the Walsh–Hadamard matrix `𝓗` of order `2^b`, so Lemma 5.1 is a form of the
  identity `𝓗² = 2^b I`": `eval_C_one` and `hadamard_mul_self`.
* "In general `C` is the entrywise product of the Walsh–Hadamard matrix with the dyadic
  convolution matrix `(z^{i⊕j})`, which `𝓗` diagonalizes": `C_eq_hadamard_mul`,
  `dyadic_eigen` (column `j` of `𝓗` is an eigenvector of `(z^{k⊕l})` with eigenvalue the Walsh
  transform `∑_n 𝓗(n, j) z^n`) and `hadamard_diagonalizes`,
  `∑_{k,l} 𝓗(i,k) z^{k⊕l} 𝓗(l,j) = [i = j] 2^b ∑_n 𝓗(i,n) z^n`.

## Differences from the paper

* `⟨i, j⟩` is the parity of the number of common one-bits; `chi` uses the count `ip i j` in the
  exponent of `-1`, which gives the same sign.
* `𝓗 (𝓓) 𝓗 = 2^b · diag` is the diagonalization with the unnormalized `𝓗`, whose inverse is
  `2^{-b} 𝓗`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset LaurentPolynomial

/-! ### Bits -/

/-- The sign as a product over the bit positions below `b`. -/
theorem chi_eq_prod {i j b : ℕ} (hi : i < 2 ^ b) :
    chi i j = ∏ e ∈ range b, if i.testBit e && j.testBit e then -1 else 1 := by
  rw [chi, ip_eq_card _ _ _ hi, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
    mul_one]

/-- A number below `2^b` is the sum of the powers `2^e` over its one-bits. -/
theorem natCast_eq_sum_testBit (b : ℕ) :
    ∀ n : ℕ, n < 2 ^ b → (n : ℤ) = ∑ e ∈ range b, if n.testBit e then (2 : ℤ) ^ e else 0 := by
  induction b with
  | zero => intro n hn; simp at hn; simp [hn]
  | succ b ih =>
    intro n hn
    rw [Finset.sum_range_succ']
    have h2 : n / 2 < 2 ^ b := by rw [pow_succ] at hn; omega
    have e1 : ∀ e ∈ range b, (if n.testBit (e + 1) then (2 : ℤ) ^ (e + 1) else 0) =
        2 * (if (n / 2).testBit e then (2 : ℤ) ^ e else 0) := by
      intro e _
      rw [Nat.testBit_succ]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, ← ih (n / 2) h2, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

/-- A product of monomials is the monomial of the sum. -/
theorem prod_T {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ e ∈ s, (T (f e) : Lp) = T (∑ e ∈ s, f e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, ← T_add]

/-! ### (a) The tensor product -/

/-- The `2 × 2` factor of bit position `e`, `[[1, z^{2^e}], [z^{2^e}, -1]]`, with rows and columns
indexed by the bit (`false`, then `true`). -/
noncomputable def cBit (e : ℕ) : Bool → Bool → Lp
  | false, false => 1
  | true, true => -1
  | _, _ => T ((2 : ℤ) ^ e)

/-- The factor of bit position `e` as a matrix. -/
noncomputable def cMat (e : ℕ) : Matrix Bool Bool Lp := Matrix.of (cBit e)

theorem cBit_eq (e : ℕ) (p q : Bool) :
    cBit e p q = LaurentPolynomial.C (if p && q then -1 else 1) *
      T (if (p ^^ q) then (2 : ℤ) ^ e else 0) := by
  cases p <;> cases q <;> simp [cBit]

/-- **The tensor product (a).** Restricted to types below `2^b`, `C` is the tensor product over
the bit positions `e < b` of the factors `cBit e`. -/
theorem C_eq_prod {b i j : ℕ} (hi : i < 2 ^ b) (hj : j < 2 ^ b) :
    C i j = ∏ e ∈ range b, cBit e (i.testBit e) (j.testBit e) := by
  simp only [cBit_eq, Finset.prod_mul_distrib, ← map_prod, prod_T]
  rw [C, chi_eq_prod hi, d, natCast_eq_sum_testBit b _ (Nat.xor_lt_two_pow hi hj)]
  simp only [Nat.testBit_xor]

/-- **The tensor product, block form.** For types below `2^b`, setting bit `b` of the two types
to `p` and `q` multiplies `C` by the entry `(p, q)` of the factor of bit `b`:
`C` on `2^(b+1)` types is `cMat b ⊗ C` on `2^b` types. -/
theorem C_kron {b i j : ℕ} (hi : i < 2 ^ b) (hj : j < 2 ^ b) (p q : Bool) :
    C (2 ^ b * p.toNat + i) (2 ^ b * q.toNat + j) = cBit b p q * C i j := by
  have hp : 2 ^ b * p.toNat + i < 2 ^ (b + 1) := by
    cases p <;> simp [pow_succ] <;> omega
  have hq : 2 ^ b * q.toNat + j < 2 ^ (b + 1) := by
    cases q <;> simp [pow_succ] <;> omega
  rw [C_eq_prod hp hq, C_eq_prod hi hj, Finset.prod_range_succ, mul_comm]
  congr 1
  · simp only [Nat.testBit_two_pow_mul_add _ hi, Nat.testBit_two_pow_mul_add _ hj, lt_irrefl,
      ↓reduceIte, Nat.sub_self]
    cases p <;> cases q <;> rfl
  · refine Finset.prod_congr rfl fun e he => ?_
    rw [mem_range] at he
    simp only [Nat.testBit_two_pow_mul_add _ hi, Nat.testBit_two_pow_mul_add _ hj, he,
      ↓reduceIte]

/-! ### (b) Each factor squares to a multiple of the identity -/

theorem T_two_pow_mul_self (e : ℕ) :
    (T ((2 : ℤ) ^ e) : Lp) * T ((2 : ℤ) ^ e) = T ((2 : ℤ) ^ (e + 1)) := by
  rw [← T_add, pow_succ]; ring_nf

/-- **(b)** `[[1, z^{2^e}], [z^{2^e}, -1]]² = (1 + z^{2^{e+1}}) I`. -/
theorem cMat_mul_self (e : ℕ) : cMat e * cMat e = (1 + T ((2 : ℤ) ^ (e + 1)) : Lp) •
    (1 : Matrix Bool Bool Lp) := by
  refine Matrix.ext fun p r => ?_
  have h := T_two_pow_mul_self e
  cases p <;> cases r <;> simp [cMat, cBit, Matrix.mul_apply, h, add_comm]

/-- The telescoping product `(1 - z²) ∏_{e<b} (1 + z^{2^{e+1}}) = 1 - z^{2^{b+1}}`. -/
theorem oneSubZ2_mul_prod (b : ℕ) :
    oneSubZ2 * ∏ e ∈ range b, (1 + T ((2 : ℤ) ^ (e + 1))) = 1 - T ((2 : ℤ) ^ (b + 1)) := by
  induction b with
  | zero => simp [oneSubZ2]
  | succ b ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih, ← T_two_pow_mul_self (b + 1)]
    ring

theorem oneSubZ2_ne_zero : oneSubZ2 ≠ 0 := by
  intro h
  have := congrArg (fun f : Lp => f.coeff 0) h
  simp only [oneSubZ2, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply] at this
  rw [← T_zero, T_apply, T_apply] at this
  simp at this

/-- **The tensor square.** `∑_{n<2^b} C_{i,n} C_{n,j} = [i = j] ∏_{e<b} (1 + z^{2^{e+1}})`: by
(a) and (b), the square of a tensor product of factors that square to `(1 + z^{2^{e+1}}) I`.
It is `sum_C_mul_C` (Lemma 5.1 restricted to types below `2^b`) after cancelling `1 - z²`. -/
theorem sum_C_mul_C_eq_prod {b i j : ℕ} (hi : i < 2 ^ b) (hj : j < 2 ^ b) :
    ∑ n ∈ range (2 ^ b), C i n * C n j = eqL i j * ∏ e ∈ range b, (1 + T ((2 : ℤ) ^ (e + 1))) := by
  apply mul_left_cancel₀ oneSubZ2_ne_zero
  rw [sum_C_mul_C b i j hi hj, mul_left_comm, oneSubZ2_mul_prod]

/-! ### (c) At `z = 1`: the Walsh–Hadamard matrix -/

/-- Evaluation at `z = 1`. -/
noncomputable abbrev evalOne : Lp →+* ℤ := eval₂ (RingHom.id ℤ) (1 : ℤˣ)

/-- **(c)** At `z = 1`, `C` is the Walsh–Hadamard matrix `𝓗(i, j) = (-1)^{⟨i,j⟩}`. -/
theorem eval_C_one (i j : ℕ) : evalOne (C i j) = chi i j := by
  simp [C, eval₂_T]

/-- **(c)** `𝓗² = 2^b I` for the Walsh–Hadamard matrix of order `2^b`: Lemma 5.1, in the form
`sum_C_mul_C_eq_prod`, at `z = 1`. -/
theorem hadamard_mul_self {b i j : ℕ} (hi : i < 2 ^ b) (hj : j < 2 ^ b) :
    ∑ n ∈ range (2 ^ b), chi i n * chi n j = if i = j then 2 ^ b else 0 := by
  have h := congrArg evalOne (sum_C_mul_C_eq_prod hi hj)
  simp only [map_sum, map_mul, map_prod, eval_C_one] at h
  rw [h]
  have h1 : ∀ e ∈ range b, evalOne (1 + T ((2 : ℤ) ^ (e + 1))) = 2 := by
    intro e _; simp [eval₂_T]
  rw [Finset.prod_congr rfl h1, Finset.prod_const, card_range]
  by_cases hij : i = j <;> simp [eqL, hij]

/-! ### (d) The dyadic convolution matrix -/

/-- **(d)** `C` is the entrywise product of the Walsh–Hadamard matrix with the dyadic convolution
matrix `(z^{i⊕j})`. -/
theorem C_eq_hadamard_mul (i j : ℕ) : C i j = (chi i j : Lp) * T ((i ^^^ j : ℕ) : ℤ) := by
  rw [C, eq_intCast, d]

/-- The sign is multiplicative in its first argument for `⊕`. -/
theorem chi_xor_left (k n j : ℕ) : chi (k ^^^ n) j = chi k j * chi n j := by
  have h := chi_mul_chi k j n
  rw [chi_comm j n] at h
  rw [h, chi, ip_comm]

/-- **(d), the eigenvectors.** Column `j` of the Walsh–Hadamard matrix is an eigenvector of the
dyadic convolution matrix `(z^{k⊕l})_{k,l<2^b}`, with eigenvalue the Walsh transform
`∑_{n<2^b} 𝓗(n, j) z^n`. -/
theorem dyadic_eigen {b k j : ℕ} (hk : k < 2 ^ b) :
    ∑ l ∈ range (2 ^ b), T ((k ^^^ l : ℕ) : ℤ) * (chi l j : Lp) =
      (∑ n ∈ range (2 ^ b), T (n : ℤ) * (chi n j : Lp)) * (chi k j : Lp) := by
  rw [Finset.sum_mul]
  refine Finset.sum_nbij' (fun l => k ^^^ l) (fun n => k ^^^ n) ?_ ?_ ?_ ?_ ?_
  · intro l hl; simp only [mem_range] at hl ⊢; exact Nat.xor_lt_two_pow hk hl
  · intro n hn; simp only [mem_range] at hn ⊢; exact Nat.xor_lt_two_pow hk hn
  · intro l _; simp
  · intro n _; simp
  · intro l _
    have : chi l j = chi k j * chi (k ^^^ l) j := by
      rw [chi_xor_left, ← mul_assoc, ← chi_xor_left, Nat.xor_self]
      simp [chi, ip]
    rw [this]; push_cast; ring

/-- **(d), the diagonalization.** `𝓗` diagonalizes the dyadic convolution matrix:
`∑_{k,l<2^b} 𝓗(i,k) z^{k⊕l} 𝓗(l,j) = [i = j] 2^b ∑_{n<2^b} 𝓗(i,n) z^n`. -/
theorem hadamard_diagonalizes {b i j : ℕ} (hi : i < 2 ^ b) (hj : j < 2 ^ b) :
    ∑ k ∈ range (2 ^ b), ∑ l ∈ range (2 ^ b),
        (chi i k : Lp) * T ((k ^^^ l : ℕ) : ℤ) * (chi l j : Lp) =
      if i = j then 2 ^ b * ∑ n ∈ range (2 ^ b), (chi i n : Lp) * T (n : ℤ) else 0 := by
  have e1 : ∀ k ∈ range (2 ^ b), ∑ l ∈ range (2 ^ b),
      (chi i k : Lp) * T ((k ^^^ l : ℕ) : ℤ) * (chi l j : Lp) =
      (∑ n ∈ range (2 ^ b), T (n : ℤ) * (chi n j : Lp)) * ((chi i k * chi k j : ℤ) : Lp) := by
    intro k hk
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [dyadic_eigen (mem_range.mp hk)]
    push_cast; ring
  rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, ← Int.cast_sum, hadamard_mul_self hi hj]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    rw [mul_comm]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [chi_comm]; ring
  · simp [hij]

end Cslib.Complexity.NtimeDspace.Cube
