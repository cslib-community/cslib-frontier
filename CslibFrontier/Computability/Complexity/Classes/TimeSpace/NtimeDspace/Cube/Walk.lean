/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Pieces
public import Mathlib.Algebra.Ring.GeomSum
import Batteries.Data.Nat.Bitwise.Lemmas

/-!
# Walks on the cube (Lemma 5.1)

`walk_coeff` is Lemma 5.1 of the paper, `(1 - z²) ∑_n C_{i,n} C_{n,j} = [i = j]` in `ℤ((z))`,
stated coefficientwise: the coefficient of `z^e` of the series is that of any partial sum over
`n < N` with `e + i < N`, because the terms with `n ≥ N` have exponent at least `n - i`
(eq:metric). `sum_C_mul_C` is the finite form used by the row cut: restricted to types below
`2^b`, `(1 - z²) ∑_{n < 2^b} C_{i,n} C_{n,j} = [i = j] (1 - z^{2^{b+1}})`, the graded form of
`𝓗² = 2^b I` for the Walsh–Hadamard matrix.

## Main results

* `ip_comm`, `chi_comm`, `C_comm`: the sign and the step are symmetric.
* `chi_mul_chi`: `χ(i,n) χ(n,j) = (-1)^{⟨i ⊕ j, n⟩}`.
* `walk_coeff`: Lemma 5.1.
* `sum_C_mul_C`: the finite Walsh–Hadamard form.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset LaurentPolynomial

/-! ### Bit helpers -/

private theorem lt_two_pow_of_le {i M : ℕ} (h : i ≤ M) : i < 2 ^ M :=
  lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) h)

/-- `ip i j` may be counted over any range `range M` with `i < 2^M`. -/
theorem ip_eq_card (i j M : ℕ) (h : i < 2 ^ M) :
    ip i j = ((range M).filter fun e => i.testBit e && j.testBit e).card := by
  unfold ip
  congr 1
  ext e
  simp only [mem_filter, mem_range, Bool.and_eq_true]
  constructor
  · rintro ⟨-, hi, hp⟩
    refine ⟨?_, hi, hp⟩
    by_contra hM
    have : i < 2 ^ e := lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow this] at hi
    exact absurd hi (by simp)
  · rintro ⟨-, hi, hp⟩
    refine ⟨?_, hi, hp⟩
    have := Nat.ge_two_pow_of_testBit hi
    have : e < 2 ^ e := Nat.lt_two_pow_self
    omega

/-- A sign `(-1)^{#filter}` as a product of signs. -/
private theorem neg_one_pow_card_filter (s : Finset ℕ) (p : ℕ → Bool) :
    ((-1 : ℤ) ^ (s.filter fun e => p e).card) = ∏ e ∈ s, if p e then -1 else 1 := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

theorem ip_comm (i j : ℕ) : ip i j = ip j i := by
  rw [ip_eq_card i j (i + j) (lt_two_pow_of_le (by omega)),
    ip_eq_card j i (i + j) (lt_two_pow_of_le (by omega))]
  congr 1
  ext e
  simp [Bool.and_comm]

theorem chi_comm (i j : ℕ) : chi i j = chi j i := by
  unfold chi; rw [ip_comm]

theorem C_comm (i j : ℕ) : C i j = C j i := by
  unfold C; rw [chi_comm, d_comm]

theorem chi_mul_chi (i n j : ℕ) : chi i n * chi n j = (-1) ^ ip (i ^^^ j) n := by
  have hM : ∀ x, x ≤ i + n + j → x < 2 ^ (i + n + j) := fun x hx => lt_two_pow_of_le hx
  have hx : i ^^^ j < 2 ^ (i + n + j) := Nat.xor_lt_two_pow (hM i (by omega)) (hM j (by omega))
  unfold chi
  rw [ip_eq_card i n _ (hM i (by omega)), ip_eq_card n j _ (hM n (by omega)),
    ip_eq_card _ n _ hx, neg_one_pow_card_filter, neg_one_pow_card_filter,
    neg_one_pow_card_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [Nat.testBit_xor]
  cases i.testBit e <;> cases n.testBit e <;> cases j.testBit e <;> simp

/-! ### The involution and the step product -/

private theorem ip_zero_left (n : ℕ) : ip 0 n = 0 := by
  unfold ip; simp

private theorem ip_two_pow {x k : ℕ} (hx : x.testBit k = true) : ip x (2 ^ k) = 1 := by
  unfold ip
  rw [Finset.card_eq_one]
  refine ⟨k, ?_⟩
  ext e
  simp only [mem_filter, mem_range, Nat.testBit_two_pow, mem_singleton, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨-, -, h⟩; exact h.symm
  · rintro rfl
    refine ⟨?_, hx, rfl⟩
    have := Nat.ge_two_pow_of_testBit hx
    have : e < 2 ^ e := Nat.lt_two_pow_self
    omega

/-- The sign is multiplicative in the second argument for `⊕`. -/
private theorem sign_xor (x a b : ℕ) :
    (-1 : ℤ) ^ ip x (a ^^^ b) = (-1) ^ ip x a * (-1) ^ ip x b := by
  have := chi_mul_chi a x b
  unfold chi at this
  rw [ip_comm x (a ^^^ b), ← this, ip_comm a x]

/-- Setting a clear bit is adding its power of two. -/
private theorem xor_two_pow_eq_add {x k : ℕ} (h : x.testBit k = false) :
    x ^^^ 2 ^ k = x + 2 ^ k := by
  have hr : x % 2 ^ (k + 1) < 2 ^ k := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [Nat.testBit_mod_two_pow]
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · simp [h]
    · simp only [Bool.and_eq_false_imp, decide_eq_true_eq]; omega
  have hx : x = 2 ^ (k + 1) * (x / 2 ^ (k + 1)) + x % 2 ^ (k + 1) := (Nat.div_add_mod x _).symm
  have hx' : x + 2 ^ k = 2 ^ (k + 1) * (x / 2 ^ (k + 1)) + (x % 2 ^ (k + 1) + 2 ^ k) := by
    rw [← Nat.add_assoc, Nat.div_add_mod]
  have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hr' : x % 2 ^ (k + 1) + 2 ^ k < 2 ^ (k + 1) := lt_of_lt_of_eq (by omega) h2.symm
  have hr'' : x % 2 ^ (k + 1) + 2 ^ k = 2 ^ k * 1 + x % 2 ^ (k + 1) := by omega
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, hx', Nat.testBit_two_pow]
  conv_lhs => rw [hx]
  rw [Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by positivity)),
    Nat.testBit_two_pow_mul_add _ hr']
  by_cases hj : j < k + 1
  · rw [ite_eq_left hj, ite_eq_left hj, hr'', Nat.testBit_two_pow_mul_add _ hr]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · rw [ite_eq_left hjk, show decide (k = j) = false from decide_eq_false (by omega),
        Bool.xor_false]
    · have hjk : j = k := by omega
      subst hjk
      simp [Nat.testBit_lt_two_pow hr]
  · rw [ite_eq_right hj, ite_eq_right hj,
      show decide (k = j) = false from decide_eq_false (by omega), Bool.xor_false]

/-- Flipping a bit where `i` and `j` differ preserves the exponent `d(i,n) + d(n,j)`. -/
private theorem d_add_d_flip {i j n k : ℕ} (hk : (i ^^^ j).testBit k = true) :
    d i (n ^^^ 2 ^ k) + d (n ^^^ 2 ^ k) j = d i n + d n j := by
  unfold d
  have e1 : i ^^^ (n ^^^ 2 ^ k) = (i ^^^ n) ^^^ 2 ^ k := (Nat.xor_assoc _ _ _).symm
  have e2 : (n ^^^ 2 ^ k) ^^^ j = (n ^^^ j) ^^^ 2 ^ k := by
    rw [Nat.xor_assoc, Nat.xor_comm (2 ^ k) j, ← Nat.xor_assoc]
  rw [e1, e2]
  have hb : (i ^^^ n).testBit k = !(n ^^^ j).testBit k := by
    simp only [Nat.testBit_xor] at hk ⊢
    cases hi : i.testBit k <;> cases hn : n.testBit k <;> cases hj : j.testBit k <;>
      simp_all
  generalize i ^^^ n = a at hb ⊢
  generalize n ^^^ j = c at hb ⊢
  have flip : ∀ y : ℕ, y.testBit k = true → y = (y ^^^ 2 ^ k) + 2 ^ k := by
    intro y hy
    have hy' : (y ^^^ 2 ^ k).testBit k = false := by
      simp [Nat.testBit_xor, Nat.testBit_two_pow_self, hy]
    have := xor_two_pow_eq_add hy'
    rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
  cases hc : c.testBit k
  · rw [hc] at hb
    have h1 := xor_two_pow_eq_add hc
    have h2 := flip a (by simpa using hb)
    generalize 2 ^ k = p at h1 h2 ⊢
    omega
  · rw [hc] at hb
    have h1 := xor_two_pow_eq_add (x := a) (by simpa using hb)
    have h2 := flip c hc
    generalize 2 ^ k = p at h1 h2 ⊢
    omega

/-- The product of two steps. -/
private theorem C_mul_C (i n j : ℕ) :
    C i n * C n j = LaurentPolynomial.C ((-1) ^ ip (i ^^^ j) n) * T ((d i n + d n j : ℕ) : ℤ) := by
  unfold C
  rw [← chi_mul_chi, map_mul, Nat.cast_add, T_add]
  ring

/-- The coefficient of `(1 - z²) c z^m`. -/
private theorem coeff_oneSubZ2_mul (s m e : ℤ) :
    (oneSubZ2 * (LaurentPolynomial.C s * T m)).coeff e =
      (if m = e then s else 0) - (if m + 2 = e then s else 0) := by
  have : oneSubZ2 * (LaurentPolynomial.C s * T m) =
      LaurentPolynomial.C s * T m - LaurentPolynomial.C s * T (m + 2) := by
    unfold oneSubZ2; rw [T_add]; ring
  rw [this, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, ← single_eq_C_mul_T,
    ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, Finsupp.single_apply]

/-! ### Lemma 5.1 -/

/-- **The finite Walsh–Hadamard form of Lemma 5.1.** -/
theorem sum_C_mul_C (b i j : ℕ) (hi : i < 2 ^ b) (hj : j < 2 ^ b) :
    oneSubZ2 * ∑ n ∈ range (2 ^ b), C i n * C n j = eqL i j * (1 - T (2 ^ (b + 1))) := by
  by_cases hij : i = j
  · subst hij
    have hs : ∑ n ∈ range (2 ^ b), C i n * C n i = ∑ m ∈ range (2 ^ b), (T 2 : Lp) ^ m := by
      refine Finset.sum_nbij' (fun n => i ^^^ n) (fun m => i ^^^ m) ?_ ?_ ?_ ?_ ?_
      · intro n hn; simp only [mem_range] at hn ⊢; exact Nat.xor_lt_two_pow hi hn
      · intro n hn; simp only [mem_range] at hn ⊢; exact Nat.xor_lt_two_pow hi hn
      · intro n _; simp
      · intro n _; simp
      · intro n _
        rw [C_mul_C, Nat.xor_self, ip_zero_left, pow_zero, map_one, one_mul, T_pow, d_comm n i]
        unfold d
        congr 1
        push_cast
        ring
    rw [hs, oneSubZ2, mul_neg_geom_sum, T_pow, eqL, ite_eq_left rfl, one_mul]
    congr 2
  · rw [eqL, ite_eq_right hij, zero_mul]
    obtain ⟨k, hk'⟩ := Nat.exists_testBit_ne_of_ne hij
    have hk : (i ^^^ j).testBit k = true := by
      rw [Nat.testBit_xor]
      cases hi' : i.testBit k <;> cases hj' : j.testBit k <;> simp_all
    have hkb : 2 ^ k < 2 ^ b :=
      lt_of_le_of_lt (Nat.ge_two_pow_of_testBit hk) (Nat.xor_lt_two_pow hi hj)
    have hsum : ∑ n ∈ range (2 ^ b), C i n * C n j = 0 := by
      refine Finset.sum_involution (fun n _ => n ^^^ 2 ^ k) ?_ ?_ ?_ ?_
      · intro n _
        rw [C_mul_C, C_mul_C, d_add_d_flip hk, sign_xor, ip_two_pow hk, pow_one, ← add_mul,
          ← map_add]
        simp
      · intro n _ _ h
        have := congrArg (fun m => m.testBit k) h
        simp [Nat.testBit_xor, Nat.testBit_two_pow_self] at this
      · intro n hn; simp only [mem_range] at hn ⊢; exact Nat.xor_lt_two_pow hn hkb
      · intro n _; simp
    rw [hsum, mul_zero]

/-- **Lemma 5.1**, coefficientwise: for `e + i < N`, the coefficient of `z^e` in
`(1 - z²) ∑_{n < N} C_{i,n} C_{n,j}` is `[i = j][e = 0]`. -/
theorem walk_coeff (i j N : ℕ) (e : ℤ) (he : e + i < N) :
    (oneSubZ2 * ∑ n ∈ range N, C i n * C n j).coeff e = if i = j ∧ e = 0 then 1 else 0 := by
  obtain ⟨b, hb⟩ : ∃ b, b = i + j + N := ⟨_, rfl⟩
  have hN : N ≤ 2 ^ b := (lt_two_pow_of_le (by omega)).le
  have key := congrArg (fun p : Lp => p.coeff e)
    (sum_C_mul_C b i j (lt_two_pow_of_le (by omega)) (lt_two_pow_of_le (by omega)))
  rw [← Finset.sum_range_add_sum_Ico _ hN, mul_add, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply] at key
  have hz : (oneSubZ2 * ∑ n ∈ Ico N (2 ^ b), C i n * C n j).coeff e = 0 := by
    rw [Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [mem_Ico] at hn
    rw [C_mul_C, coeff_oneSubZ2_mul]
    have h1 := le_add_d i n
    have : e < ((d i n + d n j : ℕ) : ℤ) := by push_cast; omega
    rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero]
  rw [hz, add_zero] at key
  rw [key]
  by_cases hij : i = j
  · subst hij
    rw [eqL, ite_eq_left rfl, one_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, ← T_zero,
      T_apply, T_apply]
    have hN2 : (N : ℤ) < 2 ^ (b + 1) := by
      exact_mod_cast (show N < 2 ^ (b + 1) from lt_two_pow_of_le (by omega))
    have hne : ¬ ((2 : ℤ) ^ (b + 1) = e) := by
      generalize (2 : ℤ) ^ (b + 1) = q at hN2 ⊢
      omega
    rw [ite_eq_right hne, sub_zero]
    rcases eq_or_ne e 0 with h0 | h0
    · subst h0; simp
    · simp [h0, h0.symm]
  · simp [eqL, hij]

end Cslib.Complexity.NtimeDspace.Cube
