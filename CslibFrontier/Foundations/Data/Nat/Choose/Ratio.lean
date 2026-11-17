/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
import CslibFrontier.Foundations.Data.Nat.Choose
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Ratios of binomial coefficients above half the ground set

Raising `t` by `k` above half of an `n`-set lowers the binomial coefficient by at least the factor
`((n - t) / t) ^ k`, hence by `(2 (n - t) / n) ^ k`
(`Nat.choose_add_le_choose_mul_div_pow`). This is the corrected form of Exercise 13.3(a) of the
Arora–Barak web draft, which the draft's counting for Håstad's switching lemma (Lemma 13.2)
needs. It is the real-valued reading of `Nat.choose_sub_mul_pow_le`, which bounds the same ratio
by the slightly stronger `((n - t) / (t + 1)) ^ k`.

## Main results

* `Nat.choose_add_le_choose_mul_div_pow`: Arora–Barak, Exercise 13.3(a), corrected.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft 2007-01-08,
  Exercise 13.3][AroraBarak07]
-/

public section

/-- **Arora–Barak, Exercise 13.3(a), corrected** (web draft 2007-01-08, p. 252/268). The draft
prints `C(n, t + k) ≤ C(n, t) (n / (n - t)) ^ k` for `t > n / 2`, which is true but too weak for
the proof of Lemma 13.2. The bound that proof needs is, for `t > n / 2`,
`C(n, t + k) ≤ C(n, t) ((n - t) / t) ^ k ≤ C(n, t) (2 (n - t) / n) ^ k`. -/
theorem Nat.choose_add_le_choose_mul_div_pow {n t k : ℕ} (ht : n < 2 * t) :
    (n.choose (t + k) : ℝ) ≤ n.choose t * (((n - t : ℕ) : ℝ) / t) ^ k ∧
      (n.choose t : ℝ) * (((n - t : ℕ) : ℝ) / t) ^ k ≤
        n.choose t * (2 * ((n - t : ℕ) : ℝ) / n) ^ k := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  refine ⟨?_, ?_⟩
  · rcases le_or_gt (t + k) n with htk | htk
    · -- `C(n, n - t - k) (t + 1) ^ k ≤ C(n, n - t) (n - t) ^ k`
      have h := Nat.choose_sub_mul_pow_le (m := n) (ℓ := n - t) (s := k) (by omega) (by omega)
      rw [show n - t - k = n - (t + k) by omega, Nat.choose_symm htk,
        Nat.choose_symm (by omega : t ≤ n), show n - (n - t) + 1 = t + 1 by omega] at h
      have h' : (n.choose (t + k) : ℝ) * (t : ℝ) ^ k ≤ n.choose t * ((n - t : ℕ) : ℝ) ^ k := by
        have : (n.choose (t + k) : ℝ) * ((t + 1 : ℕ) : ℝ) ^ k ≤
            n.choose t * ((n - t : ℕ) : ℝ) ^ k := by exact_mod_cast h
        refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le ?_ k)
          (by positivity)) this
        push_cast; linarith
      rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
      exact h'
    · rw [Nat.choose_eq_zero_of_lt htk, Nat.cast_zero]
      positivity
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Nat.choose_eq_zero_of_lt (show 0 < t by omega)]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k) (by positivity)
    rw [div_le_div_iff₀ htpos hnpos]
    have : (n : ℝ) ≤ 2 * t := by exact_mod_cast ht.le
    nlinarith [show (0 : ℝ) ≤ ((n - t : ℕ) : ℝ) by positivity]
