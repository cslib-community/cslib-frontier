/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Square-root averaging and scaling lemmas

Cauchy–Schwarz bounds the mean square root by the square root of an upper bound on the mean
(`Finset.sum_sqrt_le_card_mul_sqrt`), and `Real.sqrt_mul_div_self` rescales square-root regret
bounds to time averages. `Real.natCeil_sqrt_eq` writes `⌈√m⌉₊` with the integer square root, the
ceiling counterpart of Mathlib's `Real.nat_floor_real_sqrt_eq_nat_sqrt`.

`Real.log_add_one_le_sqrt` is the bound `log (x + 1) ≤ √x` for `x ≥ 0`, which turns a product of
`deg v + 1` choices into a sum of square roots of degrees. [KhannaPuttermanSong2026] uses it in
the count of successful admissibility tests in batch processing (§3.2, p. 16) and in the proof of
Lemma 3.10 (§3.4, p. 20); the paper's `log` is the natural logarithm (§2, p. 11). Mathlib's
Cauchy–Schwarz inequality `Real.sum_sqrt_mul_sqrt_le` with one factor constant then gives
`∑ v ∈ s, √(d v) ≤ √#s * √(∑ v ∈ s, d v)`.

## References

* [S. Khanna, A. Putterman, J. Song, *A Deterministic Linear Time Algorithm for Minimum Spanning
  Tree*][KhannaPuttermanSong2026]
-/

public section

namespace Finset

/-- Cauchy–Schwarz averaging: if `∑ i ∈ s, F i ≤ #s * B`, then `∑ i ∈ s, √(F i) ≤ #s * √B`. -/
theorem sum_sqrt_le_card_mul_sqrt {ι : Type*} (s : Finset ι) {F : ι → ℝ}
    (hF : ∀ i ∈ s, 0 ≤ F i) {B : ℝ} (hB : 0 ≤ B) (hsum : ∑ i ∈ s, F i ≤ #s * B) :
    ∑ i ∈ s, Real.sqrt (F i) ≤ #s * Real.sqrt B := by
  have hcs := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => Real.sqrt (F i))
  have hsq : ∑ i ∈ s, Real.sqrt (F i) ^ 2 = ∑ i ∈ s, F i :=
    sum_congr rfl fun i hi => Real.sq_sqrt (hF i hi)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, hsq] at hcs
  refine (pow_le_pow_iff_left₀ (sum_nonneg fun i _ => Real.sqrt_nonneg _) (by positivity)
    two_ne_zero).mp ?_
  rw [mul_pow, Real.sq_sqrt hB]
  nlinarith [(by positivity : (0 : ℝ) ≤ #s)]

end Finset

/-- Dividing the square root of `T * L` by `T > 0` yields `√(L / T)`. -/
theorem Real.sqrt_mul_div_self {T L : ℝ} (hT : 0 < T) : √(T * L) / T = √(L / T) := by
  have hs : √T * √T = T := Real.mul_self_sqrt hT.le
  have hs0 : 0 < √T := Real.sqrt_pos.mpr hT
  rw [Real.sqrt_mul hT.le, Real.sqrt_div' L hT.le, div_eq_div_iff hT.ne' hs0.ne']
  linear_combination √L * hs

/-- `log (x + 1) ≤ √x` for `x ≥ 0`, the bound used in [KhannaPuttermanSong2026] for the count of
successful admissibility tests in batch processing (§3.2, p. 16) and in the proof of Lemma 3.10
(§3.4, p. 20). With `s = √x`, the cubic Taylor polynomial
`1 + s + s² / 2 + s³ / 6 ≤ exp s` already dominates `1 + s²`. -/
theorem Real.log_add_one_le_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log (x + 1) ≤ √x := by
  have hs : 0 ≤ √x := Real.sqrt_nonneg x
  have hxs : x = √x ^ 2 := (Real.sq_sqrt hx).symm
  rw [Real.log_le_iff_le_exp (by positivity)]
  have h := Real.sum_le_exp_of_nonneg hs 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  nlinarith [mul_nonneg hs (sq_nonneg (√x - 3 / 2))]

/-- The ceiling of `√m` as an integer square root: `⌈√m⌉₊ = Nat.sqrt (m - 1) + 1` for `m ≠ 0`. -/
theorem Real.natCeil_sqrt_eq (m : ℕ) :
    ⌈Real.sqrt (m : ℝ)⌉₊ = if m = 0 then 0 else Nat.sqrt (m - 1) + 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  simp only [hm.ne', ↓reduceIte]
  rw [Nat.ceil_eq_iff (Nat.succ_ne_zero _), Nat.succ_sub_one,
    Real.lt_sqrt (Nat.cast_nonneg _), Real.sqrt_le_iff]
  have hlt : m - 1 < ((m - 1).sqrt + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt (m - 1)
    rwa [← sq] at h
  exact ⟨by exact_mod_cast (Nat.sqrt_le' (m - 1)).trans_lt (Nat.sub_lt hm one_pos),
    ⟨by positivity, by exact_mod_cast (by omega : m ≤ ((m - 1).sqrt + 1) ^ 2)⟩⟩
