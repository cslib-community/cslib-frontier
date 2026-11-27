/-
Copyright (c) 2026 Vincent Liew, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/SpecialFunctions/Trigonometric/Series.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import CslibFrontier.Foundations.Analysis.SpecialFunctions.BinomialSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The Maclaurin series of `arcsin`

For `|z| < 1`, `(1 - z²)^(-1/2) = ∑_n C(2n, n) / 4ⁿ · z^(2n)`
(`Real.hasSum_centralBinom_div_four_pow_mul_pow_two_mul`), by the binomial series
`Real.hasSum_choose_mul_pow` with exponent `-1/2`, whose coefficients are
`C(-1/2, n) = (-1)ⁿ C(2n, n) / 4ⁿ`. Integrating termwise,
`arcsin z = ∑_n C(2n, n) / (4ⁿ (2n + 1)) · z^(2n + 1)` (`Real.hasSum_arcsin`)
[O'Donnell, equation (5.9) and Exercise 5.18(a), (b)][ODonnell2014]. The series of `arcsin` is
differentiated termwise on `(-r, r)` for `|z| < r < 1` and compared with `arcsin`, which has the
same derivative and value `0` at `0`.

The endpoints `z = ±1` of Exercise 5.18(c) are not covered.

## Main results

* `Real.hasSum_centralBinom_div_four_pow_mul_pow_two_mul`: the series of `(1 - z²)^(-1/2)`.
* `Real.hasSum_arcsin`: the Maclaurin series of `arcsin` on `(-1, 1)`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 5.3 and Exercise 5.18.
-/

public section

namespace Real

open Finset

/-- `∏_{i < n} (i + 1/2) / n! = C(2n, n) / 4ⁿ`. -/
private theorem prod_add_half_div_factorial (n : ℕ) :
    (∏ i ∈ range n, ((i : ℝ) + 1 / 2)) / n.factorial = (Nat.centralBinom n : ℝ) / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h' : ((n : ℝ) + 1) * Nat.centralBinom (n + 1) =
        2 * (2 * n + 1) * Nat.centralBinom n := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hc : (Nat.centralBinom (n + 1) : ℝ) = 2 * (2 * n + 1) * Nat.centralBinom n / (n + 1) := by
      rw [← h']; field_simp
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have ih' : (∏ i ∈ range n, ((i : ℝ) + 1 / 2)) =
        n.factorial * (Nat.centralBinom n / 4 ^ n) := by
      rw [← ih, mul_div_cancel₀ _ hf]
    rw [prod_range_succ, Nat.factorial_succ, hc, ih', pow_succ]
    push_cast
    field_simp
    ring

/-- The binomial coefficients of the exponent `-1/2` are `C(-1/2, n) = (-1)ⁿ C(2n, n) / 4ⁿ`. -/
private theorem choose_neg_half_mul_neg_one_pow (n : ℕ) :
    Ring.choose (-1 / 2 : ℝ) n * (-1) ^ n = (Nat.centralBinom n : ℝ) / 4 ^ n := by
  rw [Ring.choose_eq_smul, smul_eq_mul, ← Polynomial.aeval_eq_smeval, Polynomial.aeval_def,
    ← Polynomial.eval_map, descPochhammer_map, descPochhammer_eval_eq_prod_range,
    ← prod_add_half_div_factorial, inv_mul_eq_div, div_mul_eq_mul_div,
    show ((-1 : ℝ)) ^ n = ∏ _j ∈ range n, (-1 : ℝ) by simp, ← prod_mul_distrib]
  congr 1
  exact prod_congr rfl fun i _ => by ring

/-- **The series of `(1 - z²)^(-1/2)`** [O'Donnell, Exercise 5.18(a)][ODonnell2014]: for
`|z| < 1`, `1 / √(1 - z²) = ∑_n C(2n, n) / 4ⁿ · z^(2n)`. -/
theorem hasSum_centralBinom_div_four_pow_mul_pow_two_mul {z : ℝ} (hz : |z| < 1) :
    HasSum (fun n => (Nat.centralBinom n : ℝ) / 4 ^ n * z ^ (2 * n)) (1 / √(1 - z ^ 2)) := by
  have hz2 : |-z ^ 2| < 1 := by
    rw [abs_neg, abs_pow]; exact pow_lt_one₀ (abs_nonneg z) hz two_ne_zero
  have h := hasSum_choose_mul_pow (a := -1 / 2) hz2
  have hpos : 0 < 1 - z ^ 2 := by nlinarith [abs_nonneg z, sq_abs z]
  convert h using 1
  · funext n
    rw [← choose_neg_half_mul_neg_one_pow, pow_mul, neg_pow]
    ring
  · rw [← sub_eq_add_neg, sqrt_eq_rpow, one_div, ← rpow_neg hpos.le]
    norm_num

/-- **The Maclaurin series of `arcsin`** [O'Donnell, equation (5.9) and Exercise 5.18(b)]
[ODonnell2014]: for `|x| < 1`, `arcsin x = ∑_n C(2n, n) / (4ⁿ (2n + 1)) · x^(2n + 1)`. -/
theorem hasSum_arcsin {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n => (Nat.centralBinom n : ℝ) / 4 ^ n / (2 * n + 1) * x ^ (2 * n + 1))
      (arcsin x) := by
  set a : ℕ → ℝ := fun n => (Nat.centralBinom n : ℝ) / 4 ^ n with ha
  have ha0 (n : ℕ) : 0 ≤ a n := by positivity
  have ha1 (n : ℕ) : a n ≤ 1 :=
    (div_le_one (by positivity)).2 (by exact_mod_cast Nat.centralBinom_le_four_pow n)
  set r : ℝ := (|x| + 1) / 2 with hr
  have hxr : |x| < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 ≤ r := (abs_nonneg x).trans hxr.le
  set g : ℕ → ℝ → ℝ := fun n z => a n / (2 * n + 1) * z ^ (2 * n + 1) with hg
  set u : ℕ → ℝ := fun n => a n * r ^ (2 * n) with hu
  have hu_sum : Summable u := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (summable_geometric_of_lt_one (sq_nonneg r) (by nlinarith))
    rw [hu, ← pow_mul]
    exact mul_le_of_le_one_left (by positivity) (ha1 n)
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith [abs_nonneg x], by linarith [abs_nonneg x]⟩
  have habs {y : ℝ} (hy : y ∈ Set.Ioo (-r) r) : |y| ≤ r := abs_le.2 ⟨hy.1.le, hy.2.le⟩
  have hderiv (n : ℕ) (y : ℝ) : HasDerivAt (g n) (a n * y ^ (2 * n)) y := by
    have h := (hasDerivAt_pow (2 * n + 1) y).const_mul (a n / (2 * n + 1))
    convert h using 1
    push_cast
    field_simp
  have hbound (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) : ‖a n * y ^ (2 * n)‖ ≤ u n := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 n), abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg y) (habs hy) _) (ha0 n)
  -- the series has derivative `1 / √(1 - y²)` on `(-r, r)`
  have hS (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) :
      HasDerivAt (fun z => ∑' n, g n z) (1 / √(1 - y ^ 2)) y := by
    have h := hasDerivAt_tsum_of_isPreconnected hu_sum isOpen_Ioo isPreconnected_Ioo
      (fun n y _ => hderiv n y) (fun n y hy => hbound n y hy) h0mem (by simp [hg]) hy
    convert h using 1
    exact (hasSum_centralBinom_div_four_pow_mul_pow_two_mul
      (by linarith [habs hy] : |y| < 1)).tsum_eq.symm
  -- so it agrees with `arcsin` there
  have harcsin (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) : HasDerivAt arcsin (1 / √(1 - y ^ 2)) y :=
    hasDerivAt_arcsin (by linarith [hy.1]) (by linarith [hy.2])
  have heq : Set.EqOn (fun z => ∑' n, g n z) arcsin (Set.Ioo (-r) r) :=
    isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
      (fun y hy => (hS y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (harcsin y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => by rw [(hS y hy).deriv, (harcsin y hy).deriv]) h0mem (by simp [hg])
  have hxmem : x ∈ Set.Ioo (-r) r := ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hsum : Summable fun n => g n x := by
    refine Summable.of_norm_bounded hu_sum fun n => ?_
    rw [hg, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_nonneg (by positivity : 0 ≤ a n / (2 * n + 1))]
    have h1 : a n / (2 * n + 1) ≤ a n :=
      div_le_self (ha0 n) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    have h2 : |x| ^ (2 * n + 1) ≤ |x| ^ (2 * n) :=
      pow_le_pow_of_le_one (abs_nonneg x) (by linarith) (by omega)
    have h3 : |x| ^ (2 * n) ≤ r ^ (2 * n) := pow_le_pow_left₀ (abs_nonneg x) hxr.le _
    exact mul_le_mul h1 (h2.trans h3) (by positivity) (ha0 n)
  exact heq hxmem ▸ hsum.hasSum

end Real
