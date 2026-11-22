/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field

/-!
# Elementary prime product lower bound

This module proves the prime product bound used by the residue route to the 3-SAT count
(`ThreeSat.prime_window`); it is not a statement of the current paper. For every even `X ≥ 2` and
every `H ≥ 2`,
`log ∏_{H < p ≤ X} p ≥ X - log(X+1) - √X log X - H log H`, the product running over primes.

The proof avoids the prime number theorem, using only the factorization and exponential
bounds of the central binomial coefficient `(2n).choose n = centralBinom n`.

## Main results

* `prime_prod_lower_bound_nat`: the exact integer multiplicative lower bound
  `2^X ≤ (X + 1) * X^(Nat.sqrt X) * H^H * ∏_{H < p ≤ X, p prime} p`.
* `prime_prod_lower_bound_real`: the exact logarithmic lower bound over `ℝ` with base-2 logarithm
  `Real.logb 2 (∏ p) ≥ X - Real.logb 2 (X + 1) - Real.sqrt X * Real.logb 2 X - H * Real.logb 2 H`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open Nat Finset

/-- The set of primes up to `X`. -/
def primesUpTo (X : ℕ) : Finset ℕ :=
  (range (X + 1)).filter Nat.Prime

/-- The set of primes in `(H, X]`. -/
def primesWindow (H X : ℕ) : Finset ℕ :=
  (Ioc H X).filter Nat.Prime

theorem primesUpTo_subset (X : ℕ) : primesUpTo X ⊆ range (X + 1) := by
  simp [primesUpTo]

theorem mem_primesUpTo_iff {X p : ℕ} : p ∈ primesUpTo X ↔ p ≤ X ∧ p.Prime := by
  rw [primesUpTo, mem_filter, mem_range, Nat.lt_succ_iff]

theorem mem_primesWindow_iff {H X p : ℕ} : p ∈ primesWindow H X ↔ H < p ∧ p ≤ X ∧ p.Prime := by
  simp [primesWindow, and_assoc]

theorem card_filter_prime_le_self {R : ℕ} :
    #((range (R + 1)).filter Nat.Prime) ≤ R := by
  rcases R with rfl | R
  · simp [Nat.not_prime_zero]
  · have hsub : (range (R + 2)).filter Nat.Prime ⊆ Ico 2 (R + 2) := by
      intro x hx
      simp only [mem_filter, mem_range] at hx
      simp only [mem_Ico]
      exact ⟨hx.2.two_le, hx.1⟩
    refine (card_le_card hsub).trans ?_
    rw [Nat.card_Ico]
    omega

/-- Prime factorization of the central binomial coefficient restricted to primes. -/
theorem prod_primesUpTo_pow_factorization (n : ℕ) :
    ∏ p ∈ primesUpTo (2 * n), p ^ (centralBinom n).factorization p = centralBinom n := by
  conv_rhs => rw [← prod_pow_factorization_centralBinom n]
  refine Finset.prod_subset (primesUpTo_subset (2 * n)) fun p hp hp' => ?_
  have hnot : ¬
      p.Prime := fun hprime => hp' (by rw [mem_primesUpTo_iff]; exact ⟨by simpa using hp, hprime⟩)
  rw [factorization_eq_zero_of_not_prime (centralBinom n) hnot, _root_.pow_zero]

/-- Primes at most `√X` contribute at most `X^(√X)` to `centralBinom (X/2)`. -/
theorem prod_le_sqrt_factorization_le (n : ℕ) (hn : 0 < n) :
    ∏ p ∈ (primesUpTo (2 * n)).filter (· ≤ Nat.sqrt (2 * n)),
      p ^ (centralBinom n).factorization p ≤ (2 * n) ^ Nat.sqrt (2 * n) := by
  set R := Nat.sqrt (2 * n)
  have hXpos : 0 < 2 * n := by omega
  refine (prod_le_prod fun p _ => pow_factorization_choose_le hXpos).trans ?_
  rw [prod_const]
  have hsub : (primesUpTo (2 * n)).filter (· ≤ R) ⊆ (range (R + 1)).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_primesUpTo_iff] at hp ⊢
    exact ⟨mem_range.mpr (Nat.lt_succ_of_le hp.2), hp.1.2⟩
  refine Nat.pow_le_pow_right hXpos ((card_le_card hsub).trans card_filter_prime_le_self)

/-- Primes between `√X` and `X` contribute at most their product to `centralBinom (X/2)`. -/
theorem prod_gt_sqrt_factorization_le (n : ℕ) :
    ∏ p ∈ (primesUpTo (2 * n)).filter (fun p => Nat.sqrt (2 * n) < p),
      p ^ (centralBinom n).factorization p ≤
    ∏ p ∈ (primesUpTo (2 * n)).filter (fun p => Nat.sqrt (2 * n) < p), p := by
  refine prod_le_prod fun p hp => ?_
  simp only [mem_filter, mem_primesUpTo_iff] at hp
  have hp2 : 2 * n < p ^ 2 := Nat.sqrt_lt'.mp hp.2
  have hle1 : (centralBinom n).factorization p ≤ 1 :=
    factorization_choose_le_one (k := n) hp2
  rcases le_iff_lt_or_eq.mp hle1 with h0 | h1
  · have hz : (centralBinom n).factorization p = 0 := by omega
    rw [hz, _root_.pow_zero]
    exact hp.1.2.pos
  · rw [h1, _root_.pow_one]

/-- The primes between `√X` and `X` are bounded by the full product of primes up to `X`. -/
theorem prod_gt_sqrt_le_prod_all (X : ℕ) :
    ∏ p ∈ (primesUpTo X).filter (fun p => Nat.sqrt X < p), p ≤
    ∏ p ∈ primesUpTo X, p := by
  refine prod_le_prod_of_subset_of_one_le (filter_subset _ _) fun p hp _ => ?_
  simp only [mem_primesUpTo_iff] at hp
  exact hp.2.pos

/-- The product of primes up to `X` factors as primes `≤ H` and primes in `(H, X]`. -/
theorem prod_primesUpTo_eq_mul (H X : ℕ) :
    ∏ p ∈ primesUpTo X, p =
      (∏ p ∈ (primesUpTo X).filter (· ≤ H), p) *
      ∏ p ∈ primesWindow H X, p := by
  have hd : Disjoint ((primesUpTo X).filter (· ≤ H)) (primesWindow H X) := by
    rw [disjoint_iff_ne]
    rintro a ha b hb rfl
    simp only [mem_filter, mem_primesWindow_iff] at ha hb
    omega
  have hu : (primesUpTo X).filter (· ≤ H) ∪ primesWindow H X = primesUpTo X := by
    ext x
    simp only [mem_union, mem_filter, mem_primesUpTo_iff, mem_primesWindow_iff]
    constructor
    · rintro (⟨⟨hx, hp⟩, hle⟩ | ⟨hgt, hx, hp⟩) <;> exact ⟨hx, hp⟩
    · rintro ⟨hx, hp⟩
      by_cases h : x ≤ H
      · left; exact ⟨⟨hx, hp⟩, h⟩
      · right; exact ⟨by omega, hx, hp⟩
  rw [← prod_union hd, hu]

/-- The product of primes `≤ H` is at most `H^H`. -/
theorem prod_primes_le_H_le (H X : ℕ) (hH : 1 ≤ H) :
    ∏ p ∈ (primesUpTo X).filter (· ≤ H), p ≤ H ^ H := by
  have hsub : (primesUpTo X).filter (· ≤ H) ⊆ (range (H + 1)).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_primesUpTo_iff] at hp ⊢
    exact ⟨mem_range.mpr (Nat.lt_succ_of_le hp.2), hp.1.2⟩
  refine (prod_le_prod (g := fun _ => H) fun p hp => ?_).trans ?_
  · simp only [mem_filter] at hp
    exact hp.2
  · rw [prod_const]
    exact Nat.pow_le_pow_right (by omega) ((card_le_card hsub).trans card_filter_prime_le_self)

/-- Upper bound on the central binomial coefficient by `X^(√X) * H^H * ∏_{H < p ≤ X} p`. -/
theorem centralBinom_le_prod_primes (n H : ℕ) (hn : 0 < n) (hH : 1 ≤ H) :
    centralBinom n ≤ (2 * n) ^ Nat.sqrt (2 * n) * H ^ H * ∏ p ∈ primesWindow H (2 * n), p := by
  have hdec : primesUpTo (2 * n) =
      ((primesUpTo (2 * n)).filter (· ≤ Nat.sqrt (2 * n))) ∪
      ((primesUpTo (2 * n)).filter (fun p => Nat.sqrt (2 * n) < p)) := by
    ext p
    simp only [mem_union, mem_filter]
    constructor
    · intro h
      rcases le_or_gt p (Nat.sqrt (2 * n)) with hle | hgt
      · left; exact ⟨h, hle⟩
      · right; exact ⟨h, hgt⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  have hd : Disjoint ((primesUpTo (2 * n)).filter (· ≤ Nat.sqrt (2 * n)))
      ((primesUpTo (2 * n)).filter (fun p => Nat.sqrt (2 * n) < p)) := by
    rw [disjoint_iff_ne]
    rintro a ha b hb rfl
    simp only [mem_filter] at ha hb
    omega
  have hdecomp : ∏ p ∈ primesUpTo (2 * n), p ^ (centralBinom n).factorization p =
      (∏ p ∈ (primesUpTo (2 * n)).filter (· ≤ Nat.sqrt (2 * n)), p ^
          (centralBinom n).factorization p) *
      ∏ p ∈ (primesUpTo (2 * n)).filter (fun p => Nat.sqrt (2 * n) < p), p ^
          (centralBinom n).factorization p := by
    conv_lhs => rw [hdec, prod_union hd]
  rw [← prod_primesUpTo_pow_factorization n, hdecomp]
  have h1 := prod_le_sqrt_factorization_le n hn
  have h2 := prod_gt_sqrt_factorization_le n
  have h3 := prod_gt_sqrt_le_prod_all (2 * n)
  have h4 := prod_primes_le_H_le H (2 * n) hH
  rw [prod_primesUpTo_eq_mul H (2 * n)] at h3
  have hprod : (∏ p ∈ (primesUpTo (2 * n)).filter (fun p => Nat.sqrt (2 * n) < p), p ^
      (centralBinom n).factorization p) ≤
      H ^ H * ∏ p ∈ primesWindow H (2 * n), p := by
    calc _ ≤ ∏ p ∈ (primesUpTo (2 * n)).filter (fun p => Nat.sqrt (2 * n) < p), p := h2
      _ ≤ (∏ p ∈ (primesUpTo (2 * n)).filter (· ≤ H), p) * ∏ p ∈ primesWindow H (2 * n), p := h3
      _ ≤ H ^ H * ∏ p ∈ primesWindow H (2 * n), p := Nat.mul_le_mul_right _ h4
  calc _ ≤ (2 * n) ^ Nat.sqrt (2 * n) * (H ^ H * ∏ p ∈ primesWindow H (2 * n), p) :=
        Nat.mul_le_mul h1 hprod
    _ = (2 * n) ^ Nat.sqrt (2 * n) * H ^ H * ∏ p ∈ primesWindow H (2 * n), p := by ring

/-- **The prime product bound (integer multiplicative form)**:
For every even `X ≥ 2` and every `H ≥ 2`,
`2^X ≤ (X + 1) * X^(Nat.sqrt X) * H^H * ∏_{H < p ≤ X, p prime} p`. -/
theorem prime_prod_lower_bound_nat (X H : ℕ) (hXeven : Even X) (hX : 2 ≤ X) (_hH : 2 ≤ H) :
    2 ^ X ≤ (X + 1) * X ^ Nat.sqrt X * H ^ H * ∏ p ∈ primesWindow H X, p := by
  obtain ⟨n, rfl⟩ := hXeven
  have hX_eq : n + n = 2 * n := by ring
  have hn : 0 < n := by omega
  have h4 : 4 ^ n ≤ (2 * n + 1) * centralBinom n :=
    four_pow_le_two_mul_add_one_mul_centralBinom n
  have h2X : 2 ^ (2 * n) = 4 ^ n := by
    rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul, mul_comm]
  have hbinom := centralBinom_le_prod_primes n H hn (by omega)
  rw [hX_eq, h2X]
  calc 4 ^ n ≤ (2 * n + 1) * centralBinom n := h4
    _ ≤ (2 * n + 1) * ((2 * n) ^ Nat.sqrt (2 * n) * H ^ H * ∏ p ∈ primesWindow H (2 * n), p) :=
        Nat.mul_le_mul_left _ hbinom
    _ = (2 * n + 1) * (2 * n) ^ Nat.sqrt (2 * n) * H ^ H * ∏ p ∈ primesWindow H
        (2 * n), p := by ring

/-- **The prime product bound (real logarithmic form)**:
For every even `X ≥ 2` and every `H ≥ 2`,
`Real.logb 2 (∏_{H < p ≤ X} p) ≥ X - Real.logb 2 (X + 1) - Real.sqrt X * Real.logb 2 X - H *
Real.logb 2 H`. -/
theorem prime_prod_lower_bound_real (X H : ℕ) (hXeven : Even X) (hX : 2 ≤ X) (hH : 2 ≤ H) :
    (X : ℝ) - Real.logb 2 (X + 1) - Real.sqrt X * Real.logb 2 X - (H : ℝ) * Real.logb 2 H ≤
      Real.logb 2 (∏ p ∈ primesWindow H X, (p : ℝ)) := by
  have hnat := prime_prod_lower_bound_nat X H hXeven hX hH
  have hPpos : 0 < (∏ p ∈ primesWindow H X, p : ℝ) := by
    norm_cast
    refine prod_pos fun p hp => ?_
    simp only [mem_primesWindow_iff] at hp
    exact_mod_cast hp.2.2.pos
  have hX1pos : 0 < (X + 1 : ℝ) := by positivity
  have hXpos : 0 < (X : ℝ) := by positivity
  have hHpos : 0 < (H : ℝ) := by positivity
  have h2Xpos : 0 < (2 ^ X : ℝ) := by positivity
  have hR_le : (2 ^ X : ℝ) ≤ ((X + 1) * X ^ Nat.sqrt X * H ^ H * ∏ p ∈ primesWindow H X, p :
      ℝ) := by
    exact_mod_cast hnat
  have hR_prod : ((X + 1) * X ^ Nat.sqrt X * H ^ H * ∏ p ∈ primesWindow H X, p : ℝ) =
      (X + 1 : ℝ) * (X : ℝ) ^ Nat.sqrt X * (H : ℝ) ^ H * (∏ p ∈ primesWindow H X, (p : ℝ)) := by
    push_cast
    rfl
  rw [hR_prod] at hR_le
  have hlog := Real.log_le_log h2Xpos hR_le
  have hX1_ne : (X + 1 : ℝ) ≠ 0 := ne_of_gt hX1pos
  have hXR_ne : (X : ℝ) ^ Nat.sqrt X ≠ 0 := ne_of_gt (by positivity)
  have hHH_ne : (H : ℝ) ^ H ≠ 0 := ne_of_gt (by positivity)
  have hP_ne : (∏ p ∈ primesWindow H X, (p : ℝ)) ≠ 0 := ne_of_gt hPpos
  rw [Real.log_pow,
      Real.log_mul (mul_ne_zero (mul_ne_zero hX1_ne hXR_ne) hHH_ne) hP_ne,
      Real.log_mul (mul_ne_zero hX1_ne hXR_ne) hHH_ne,
      Real.log_mul hX1_ne hXR_ne,
      Real.log_pow, Real.log_pow] at hlog
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv := div_le_div_of_nonneg_right hlog hlog2pos.le
  simp only [add_div, mul_div_cancel_right₀ _ hlog2pos.ne', mul_div_assoc] at hdiv
  simp only [Real.logb]
  have hsq_le : (Nat.sqrt X : ℝ) ≤ Real.sqrt X := Real.nat_sqrt_le_real_sqrt
  have hlogXnonneg : 0 ≤ Real.log X / Real.log 2 := by
    rw [div_nonneg_iff]
    left
    refine ⟨Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X)), hlog2pos.le⟩
  have hsq_mul : (Nat.sqrt X : ℝ) * (Real.log X / Real.log 2) ≤ Real.sqrt X *
      (Real.log X / Real.log 2) :=
    mul_le_mul_of_nonneg_right hsq_le hlogXnonneg
  linarith

end Cslib.Complexity.NtimeDspace.Cross
