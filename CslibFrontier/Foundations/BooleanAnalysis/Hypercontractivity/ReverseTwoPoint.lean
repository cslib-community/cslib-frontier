/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.LpNorm
public import CslibFrontier.Foundations.BooleanAnalysis.Noise
import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity.TwoPoint
import CslibFrontier.Foundations.Analysis.SpecialFunctions.BinomialSeries
import CslibFrontier.Foundations.Analysis.SpecialFunctions.OneAddRpow
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Reverse hypercontractivity of a single bit

For `0 < p ≤ 1` the `L^p` "norm" of a nonnegative function of one uniformly random bit `x = ±1`,
`a + b x` with `|b| ≤ a`, is at most the geometric mean of `a + ρ b x` when `ρ ^ 2 ≤ 1 - p`. This
is the **reverse two-point inequality** for the exponents `p` and `0`
(`BitString.rpow_add_rpow_le_sq_sub_sq_mul_sq_rpow`): raised to the power `p`, it reads
`((a + b) ^ p + (a - b) ^ p) / 2 ≤ (a ^ 2 - ρ ^ 2 b ^ 2) ^ (p / 2)`
[O'Donnell, Exercise 10.7(f)][ODonnell2014].

For nonnegative `f = a + b x` and `g = c + d x` and `-1 < r, s ≤ 0`, the inequality bounds
`‖f‖_{1 + r} ^ 2` by `a ^ 2 + r b ^ 2` and `‖g‖_{1 + s} ^ 2` by `c ^ 2 + s d ^ 2`, the squared
geometric means of `T_{√(-r)} f` and `T_{√(-s)} g`. With `σ = √(-r) |b|` and `τ = √(-s) |d|`, the
inequality `(a ^ 2 - σ ^ 2) (c ^ 2 - τ ^ 2) ≤ (a c - σ τ) ^ 2` and `σ τ = √(r s) |b d|` then give
the **Reverse Two-Function Hypercontractivity Theorem** on one bit for `0 ≤ ρ ≤ √(r s)`:
`‖f‖_{1 + r} ‖g‖_{1 + s} ≤ a c + ρ b d = 𝔼_x f x · T_ρ g x`
(`BitString.lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_unit`)
[O'Donnell, Exercise 10.6][ODonnell2014]. This is the analogue of the forward proof, with
geometric means in place of `L^2` norms and the arithmetic–geometric mean inequality in place of
the Cauchy–Schwarz inequality.

The reverse two-point inequality for `q = 0` is proved by two monotonicity arguments for
derivatives: with `t = |b| / a`, the ratio of `(1 + t) ^ p + (1 - t) ^ p` to
`(1 - (1 - p) t ^ 2) ^ (p / 2)` decreases on `[0, 1]`, because
`(1 - (1 - p) t) (1 - t) ^ (p - 1)` stays above `(1 + (1 - p) t) (1 + t) ^ (p - 1)`.

For **positive exponents** `0 < q ≤ p ≤ 1` and `ρ ^ 2 (1 - q) ≤ 1 - p`, the reverse two-point
inequality `‖a + b x‖_p ≤ ‖a + ρ b x‖_q`
(`BitString.rpow_add_rpow_le_rpow_add_rpow_rpow`, in norm form
`BitString.lpNorm_le_lpNorm_noiseOp_of_unit`) [O'Donnell, Exercise 10.7(a), (b)][ODonnell2014]
follows the binomial-series proof of the forward two-point inequality. With `a = 1` and
`|t| < 1`, `((1 + t) ^ p + (1 - t) ^ p) / 2 = ∑_k C(p, 2k) t ^ (2k)`, and for `0 < q < 1` every
`C(q, 2k)` with `k ≥ 1` is at most `0`. Bernoulli's inequality `(1 + s) ^ θ ≥ 1 + θ s` for
`θ = p / q ≥ 1` bounds the `p / q`-th power of `1 + ∑_k C(q, 2k) (ρ t) ^ (2k)` below by
`1 + ∑_k (p / q) C(q, 2k) ρ ^ (2k) t ^ (2k)`, and the coefficients compare term by term:
`C(p, 2k) ≤ (p / q) C(q, 2k) ρ ^ (2k)`. For `ρ ^ 2 = (1 - p) / (1 - q)` this is an equality at
`k = 1`, and passing from `k` to `k + 1` multiplies the two sides by
`(2k - q) (2k + 1 - q) ρ ^ 2` and `(2k - p) (2k + 1 - p)` (over a common denominator), the first
at most the second: this is O'Donnell's hint that `(j - r) / √(1 - r)` increases in `r`. A smaller
`ρ ^ 2` only raises the right side, since `C(q, 2k) ≤ 0`, so no monotonicity of norms in the
exponent is needed. Continuity in `t` gives `t = ±1`.

## Main results

* `Cslib.BitString.rpow_add_rpow_le_sq_sub_sq_mul_sq_rpow`: the reverse two-point inequality
  for the exponents `p` and `0`.
* `Cslib.BitString.rpow_add_rpow_le_rpow_add_rpow_rpow`,
  `Cslib.BitString.lpNorm_le_lpNorm_noiseOp_of_unit`: the reverse two-point inequality for
  exponents `0 < q ≤ p ≤ 1`.
* `Cslib.BitString.lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_unit`: the Reverse Two-Function
  Hypercontractivity Theorem on one bit, for `-1 < r, s ≤ 0`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Set
open scoped BigOperators

/-! ### The reverse two-point inequality -/

/-- For `0 ≤ p ≤ 1` and `0 ≤ t < 1`, `(1 + (1 - p) t) (1 + t) ^ (p - 1)` is at most
`(1 - (1 - p) t) (1 - t) ^ (p - 1)`: their difference increases from `0`, with derivative
`p (1 - p) t ((1 - t) ^ (p - 2) - (1 + t) ^ (p - 2))`. -/
private theorem one_add_mul_mul_rpow_le {p t : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1) (ht : 0 ≤ t)
    (ht' : t < 1) :
    (1 + (1 - p) * t) * (1 + t) ^ (p - 1) ≤ (1 - (1 - p) * t) * (1 - t) ^ (p - 1) := by
  have hW : MonotoneOn (fun t : ℝ => (1 - (1 - p) * t) * (1 - t) ^ (p - 1) -
      (1 + (1 - p) * t) * (1 + t) ^ (p - 1)) (Ico 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (f' := fun t => (1 - p) * p * t * ((1 - t) ^ (p - 2) - (1 + t) ^ (p - 2)))
      (fun t ht => ?_) (fun t ht => ?_) fun t ht => ?_
    · have h1 : 1 + t ≠ 0 := by linarith [ht.1]
      have h2 : 1 - t ≠ 0 := by linarith [ht.2]
      exact (((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).mul
        ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl h2))).sub
        ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).mul
        ((continuousAt_const.add continuousAt_id).rpow_const (Or.inl h1)))).continuousWithinAt
    · rw [interior_Ico] at ht
      have h1 : 1 + t ≠ 0 := by linarith [ht.1]
      have h2 : 1 - t ≠ 0 := by linarith [ht.2]
      have d1 := Real.hasDerivAt_one_add_rpow (p - 1) (by linarith [ht.1] : -1 < t)
      have d2 := Real.hasDerivAt_one_sub_rpow (p - 1) ht.2
      have h := ((((hasDerivAt_id t).const_mul (1 - p)).const_sub 1).mul d2).sub
        ((((hasDerivAt_id t).const_mul (1 - p)).const_add 1).mul d1)
      convert h.hasDerivWithinAt using 1
      · rfl
      have e1 : (1 + t) ^ (p - 1) = (1 + t) ^ (p - 2) * (1 + t) := by
        rw [← Real.rpow_add_one h1]; ring_nf
      have e2 : (1 - t) ^ (p - 1) = (1 - t) ^ (p - 2) * (1 - t) := by
        rw [← Real.rpow_add_one h2]; ring_nf
      simp only [id_eq, show p - 1 - 1 = p - 2 by ring, e1, e2]
      ring
    · rw [interior_Ico] at ht
      have h := Real.rpow_le_rpow_of_nonpos (by linarith [ht.2] : 0 < 1 - t)
        (by linarith [ht.1] : 1 - t ≤ 1 + t) (by linarith : p - 2 ≤ 0)
      exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hp0) ht.1.le) (sub_nonneg.2 h)
  have h := hW ⟨le_rfl, zero_lt_one⟩ ⟨ht, ht'⟩ ht
  simp only [mul_zero, sub_zero, add_zero, Real.one_rpow, sub_self] at h
  linarith

/-- For `0 < p ≤ 1` and `0 ≤ t ≤ 1`, `(1 + t) ^ p + (1 - t) ^ p ≤ 2 (1 - (1 - p) t ^ 2) ^ (p / 2)`:
the ratio of the two sides decreases from `1`. -/
private theorem one_add_rpow_add_one_sub_rpow_le {p t : ℝ} (hp : 0 < p) (hp' : p ≤ 1)
    (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (1 + t) ^ p + (1 - t) ^ p ≤ 2 * (1 - (1 - p) * t ^ 2) ^ (p / 2) := by
  have hB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < 1 - (1 - p) * t ^ 2 := by
    nlinarith [ht.1, ht.2, mul_le_mul ht.2 ht.2 ht.1 zero_le_one]
  -- the ratio `Q t` of the two sides, up to the factor `2`
  have hQ : AntitoneOn (fun t : ℝ => ((1 + t) ^ p + (1 - t) ^ p) *
      (1 - (1 - p) * t ^ 2) ^ (-(p / 2))) (Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (f' := fun t => p * (1 - (1 - p) * t ^ 2) ^ (-(p / 2) - 1) *
        ((1 + (1 - p) * t) * (1 + t) ^ (p - 1) - (1 - (1 - p) * t) * (1 - t) ^ (p - 1)))
      (fun t ht => ?_) (fun t ht => ?_) fun t ht => ?_
    · exact ((((continuousAt_const.add continuousAt_id).rpow_const (Or.inr hp.le)).add
        ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inr hp.le))).mul
        ((continuousAt_const.sub (continuousAt_const.mul (continuousAt_id.pow 2))).rpow_const
          (Or.inl (hB t ht).ne'))).continuousWithinAt
    · rw [interior_Icc] at ht
      have h1 : 1 + t ≠ 0 := by linarith [ht.1]
      have h2 : 1 - t ≠ 0 := by linarith [ht.2]
      have h3 := (hB t ⟨ht.1.le, ht.2.le⟩).ne'
      have d1 := Real.hasDerivAt_one_add_rpow p (by linarith [ht.1] : -1 < t)
      have d2 := Real.hasDerivAt_one_sub_rpow p ht.2
      have d3 := (((hasDerivAt_pow 2 t).const_mul (1 - p)).const_sub 1).rpow_const
        (p := -(p / 2)) (Or.inl h3)
      convert ((d1.add d2).mul d3).hasDerivWithinAt using 1
      have e1 : (1 + t) ^ p = (1 + t) ^ (p - 1) * (1 + t) := by
        rw [← Real.rpow_add_one h1, sub_add_cancel]
      have e2 : (1 - t) ^ p = (1 - t) ^ (p - 1) * (1 - t) := by
        rw [← Real.rpow_add_one h2, sub_add_cancel]
      have e3 : (1 - (1 - p) * t ^ 2) ^ (-(p / 2)) =
          (1 - (1 - p) * t ^ 2) ^ (-(p / 2) - 1) * (1 - (1 - p) * t ^ 2) := by
        rw [← Real.rpow_add_one h3, sub_add_cancel]
      simp only [Pi.add_apply, e1, e2, e3, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      ring
    · rw [interior_Icc] at ht
      refine mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hp.le (Real.rpow_nonneg
        (hB t ⟨ht.1.le, ht.2.le⟩).le _)) (sub_nonpos.2 ?_)
      exact one_add_mul_mul_rpow_le hp.le hp' ht.1.le ht.2
  have h := hQ ⟨le_rfl, zero_le_one⟩ ⟨ht, ht'⟩ ht
  have hM := Real.rpow_pos_of_pos (hB t ⟨ht, ht'⟩) (p / 2)
  simp only [add_zero, sub_zero, Real.one_rpow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, mul_one, Real.rpow_neg (hB t ⟨ht, ht'⟩).le] at h
  rw [← div_eq_mul_inv, div_le_iff₀ hM] at h
  linarith

/-- **The reverse two-point inequality for the exponents `p` and `0`**: for `0 < p`,
`ρ ^ 2 ≤ 1 - p` (so `p ≤ 1`) and `|b| ≤ a`,
`((a + b) ^ p + (a - b) ^ p) / 2 ≤ (a ^ 2 - ρ ^ 2 b ^ 2) ^ (p / 2)`.
For a uniformly random bit `x = ±1` it says that `‖a + b x‖_p ^ p` is at most the `p`-th power
of the geometric mean `√((a + ρ b) (a - ρ b))` of `a + ρ b x`
[O'Donnell, Exercise 10.7(f)][ODonnell2014]. -/
theorem rpow_add_rpow_le_sq_sub_sq_mul_sq_rpow {p ρ a b : ℝ} (hp : 0 < p) (hρ : ρ ^ 2 ≤ 1 - p)
    (hb : |b| ≤ a) :
    ((a + b) ^ p + (a - b) ^ p) / 2 ≤ (a ^ 2 - ρ ^ 2 * b ^ 2) ^ (p / 2) := by
  have hp' : p ≤ 1 := by nlinarith [sq_nonneg ρ]
  have ha0 : 0 ≤ a := (abs_nonneg b).trans hb
  have hab := Real.abs_add_rpow_add_abs_sub_rpow (a := a) (b := b) (by rwa [abs_of_nonneg ha0]) p
  rw [abs_of_nonneg (by linarith [neg_abs_le b] : 0 ≤ a + b),
    abs_of_nonneg (by linarith [le_abs_self b] : 0 ≤ a - b), abs_of_nonneg ha0] at hab
  rcases ha0.eq_or_lt with ha | ha
  · obtain rfl : b = 0 := abs_eq_zero.1 (le_antisymm (ha ▸ hb) (abs_nonneg b))
    subst ha
    simp [Real.zero_rpow hp.ne', Real.zero_rpow (half_pos hp).ne']
  set t := |b| / a
  have ht0 : 0 ≤ t := div_nonneg (abs_nonneg b) ha.le
  have ht1 : t ≤ 1 := (div_le_one ha).2 hb
  have hbt : |b| = a * t := by rw [mul_div_cancel₀ _ ha.ne']
  have hB : 0 ≤ 1 - (1 - p) * t ^ 2 := by nlinarith [mul_le_mul ht1 ht1 ht0 zero_le_one]
  have key := one_add_rpow_add_one_sub_rpow_le hp hp' ht0 ht1
  calc ((a + b) ^ p + (a - b) ^ p) / 2
      = a ^ p * ((1 + t) ^ p + (1 - t) ^ p) / 2 := by
        rw [hab, hbt, show a + a * t = a * (1 + t) by ring, show a - a * t = a * (1 - t) by ring,
          Real.mul_rpow ha.le (by linarith), Real.mul_rpow ha.le (by linarith), mul_add]
    _ ≤ a ^ p * (1 - (1 - p) * t ^ 2) ^ (p / 2) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg ha.le p)
    _ = (a ^ 2 - (1 - p) * b ^ 2) ^ (p / 2) := by
        rw [← sq_abs b, hbt, show a ^ 2 - (1 - p) * (a * t) ^ 2 = a ^ 2 * (1 - (1 - p) * t ^ 2) by
          ring, Real.mul_rpow (sq_nonneg a) hB, ← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le,
          Nat.cast_ofNat, mul_div_cancel₀ p two_ne_zero]
    _ ≤ (a ^ 2 - ρ ^ 2 * b ^ 2) ^ (p / 2) := by
        refine Real.rpow_le_rpow ?_ ?_ (by positivity)
        · rw [← sq_abs b, hbt]
          nlinarith [mul_nonneg (sq_nonneg a) hB]
        · nlinarith [sq_nonneg b]

/-! ### The reverse two-point inequality for positive exponents -/

/-- The even part of the binomial series: `((1 + x) ^ a + (1 - x) ^ a) / 2` is the sum of
`(C(a, n) x ^ n + C(a, n) (-x) ^ n) / 2`, whose odd terms vanish. -/
private theorem hasSum_choose_mul_pow_add_neg_pow {a x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => (Ring.choose a n * x ^ n + Ring.choose a n * (-x) ^ n) / 2)
      (((1 + x) ^ a + (1 - x) ^ a) / 2) := by
  have h := ((Real.hasSum_choose_mul_pow (a := a) hx).add
    (Real.hasSum_choose_mul_pow (a := a) (x := -x) (by rwa [abs_neg]))).div_const 2
  rwa [← sub_eq_add_neg] at h

/-- Two steps of the recursion for binomial coefficients:
`C(a, n + 2) (n + 1) (n + 2) = C(a, n) (a - n) (a - n - 1)`. -/
private theorem choose_add_two_mul (a : ℝ) (n : ℕ) :
    Ring.choose a (n + 2) * ((n + 1) * (n + 2)) =
      Ring.choose a n * ((a - n) * (a - n - 1)) := by
  have h1 (m : ℕ) : Ring.choose a (m + 1) * (m + 1) = Ring.choose a m * (a - m) := by
    have h := Ring.choose_smul_choose a (Nat.le_add_right m 1)
    rw [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right,
      nsmul_eq_mul] at h
    push_cast at h
    linarith
  have h2 := h1 (n + 1)
  push_cast at h2
  linear_combination (n + 1 : ℝ) * h2 + (a - n - 1) * h1 n

/-- The factor-by-factor comparison: for `0 < q ≤ p ≤ 1` and `j ≥ 2`,
`(j - q) (j + 1 - q) (1 - p) ≤ (j - p) (j + 1 - p) (1 - q)`. The difference of the two sides is
`(p - q) (j (j - 1) - (1 - p) (1 - q))`. This is O'Donnell's hint that `(j - r) / √(1 - r)`
increases in `r`, for two consecutive factors at once. -/
private theorem sub_mul_sub_mul_le {p q j : ℝ} (hq : 0 < q) (hqp : q ≤ p) (hp : p ≤ 1)
    (hj : 2 ≤ j) :
    (j - q) * (j + 1 - q) * (1 - p) ≤ (j - p) * (j + 1 - p) * (1 - q) := by
  have h : (j - p) * (j + 1 - p) * (1 - q) - (j - q) * (j + 1 - q) * (1 - p) =
      (p - q) * (j * (j - 1) - (1 - p) * (1 - q)) := by ring
  have h2 : (1 - p) * (1 - q) ≤ 1 := by nlinarith
  have h3 : 2 ≤ j * (j - 1) := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hqp) (by linarith : 0 ≤ j * (j - 1) - (1 - p) * (1 - q))]

/-- The coefficient comparison: for `0 < q ≤ p ≤ 1` and `k ≥ 1`, `C(q, 2k) ≤ 0` and
`q C(p, 2k) (1 - q) ^ k ≤ p C(q, 2k) (1 - p) ^ k`. Both sides are equal for `k = 1`; passing
from `k` to `k + 1` multiplies `C(a, 2k)` by `(2k - a) (2k + 1 - a) / ((2k + 1) (2k + 2))`. -/
private theorem choose_two_mul_nonpos_and_le {p q : ℝ} (hq : 0 < q) (hqp : q ≤ p) (hp : p ≤ 1)
    {k : ℕ} (hk : 1 ≤ k) :
    Ring.choose q (2 * k) ≤ 0 ∧
      q * Ring.choose p (2 * k) * (1 - q) ^ k ≤ p * Ring.choose q (2 * k) * (1 - p) ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
    have e (a : ℝ) : Ring.choose a 2 = a * (a - 1) / 2 := by
      have h := choose_add_two_mul a 0
      simp only [Nat.cast_zero, Ring.choose_zero_right] at h
      linarith
    simp only [mul_one, pow_one, e]
    constructor <;> nlinarith
  | succ k hk ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hk' : (2 : ℝ) ≤ 2 * k := by exact_mod_cast Nat.mul_le_mul_left 2 hk
    have hD : (0 : ℝ) < (2 * k + 1) * (2 * k + 2) := by positivity
    have e (a : ℝ) : Ring.choose a (2 * (k + 1)) =
        Ring.choose a (2 * k) * ((a - 2 * k) * (a - 2 * k - 1)) /
          ((2 * k + 1) * (2 * k + 2)) := by
      have h := choose_add_two_mul a (2 * k)
      rw [show 2 * (k + 1) = 2 * k + 2 by ring]
      push_cast at h
      rw [eq_div_iff hD.ne']
      exact h
    have hXq : 0 ≤ (q - 2 * k) * (q - 2 * k - 1) := by nlinarith
    have hXp : 0 ≤ (p - 2 * k) * (p - 2 * k - 1) := by nlinarith
    rw [e, e]
    refine ⟨div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg ih1 hXq) hD.le, ?_⟩
    rw [pow_succ, pow_succ]
    have hR : p * Ring.choose q (2 * k) * (1 - p) ^ k ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) ih1)
        (pow_nonneg (by linarith) _)
    have hA : 0 ≤ (p - 2 * k) * (p - 2 * k - 1) * (1 - q) := mul_nonneg hXp (by linarith)
    have hB : (q - 2 * k) * (q - 2 * k - 1) * (1 - p) ≤
        (p - 2 * k) * (p - 2 * k - 1) * (1 - q) := by
      nlinarith [sub_mul_sub_mul_le hq hqp hp hk']
    have h1 := mul_le_mul_of_nonneg_right ih2 hA
    have h2 := mul_le_mul_of_nonpos_left hB hR
    field_simp
    nlinarith

/-- The coefficient comparison with a correlation: for `0 < q ≤ p ≤ 1`, `q < 1`, `k ≥ 1` and
`0 ≤ σ` with `σ (1 - q) ≤ 1 - p`, `C(p, 2k) ≤ (p / q) C(q, 2k) σ ^ k`. -/
private theorem choose_two_mul_le {p q σ : ℝ} (hq : 0 < q) (hqp : q ≤ p) (hp : p ≤ 1)
    (hq1 : q < 1) (hσ : 0 ≤ σ) (hσ' : σ * (1 - q) ≤ 1 - p) {k : ℕ} (hk : 1 ≤ k) :
    Ring.choose p (2 * k) ≤ p / q * Ring.choose q (2 * k) * σ ^ k := by
  obtain ⟨h1, h2⟩ := choose_two_mul_nonpos_and_le hq hqp hp hk
  have hq1' : 0 < 1 - q := by linarith
  have hσk : σ ^ k * (1 - q) ^ k ≤ (1 - p) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hσ hq1'.le) hσ' k
  have h3 : p * Ring.choose q (2 * k) * (1 - p) ^ k ≤
      p * Ring.choose q (2 * k) * (σ ^ k * (1 - q) ^ k) :=
    mul_le_mul_of_nonpos_left hσk (mul_nonpos_of_nonneg_of_nonpos (by linarith) h1)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hq]
  refine le_of_mul_le_mul_right ?_ (pow_pos hq1' k)
  nlinarith

/-- The normalized reverse two-point inequality for `|t| < 1`, by comparing binomial series. The
right side is at least `1 + (p / q) (E - 1)` by Bernoulli's inequality, where `E` is the even
part of the binomial series of `(1 + ρ t) ^ q`, and the comparison of coefficients bounds the
series of this lower bound below by the series of the left side. -/
private theorem one_add_rpow_add_one_sub_rpow_le_rpow_of_lt {p q ρ t : ℝ} (hq : 0 < q)
    (hqp : q ≤ p) (hp : p ≤ 1) (hq1 : q < 1) (hρ : ρ ^ 2 * (1 - q) ≤ 1 - p) (ht : |t| < 1) :
    ((1 + t) ^ p + (1 - t) ^ p) / 2 ≤ (((1 + ρ * t) ^ q + (1 - ρ * t) ^ q) / 2) ^ (p / q) := by
  have hρ1 : |ρ| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    nlinarith
  have hρt : |ρ * t| < 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg ρ, abs_nonneg t]
  set E := ((1 + ρ * t) ^ q + (1 - ρ * t) ^ q) / 2
  have hE : 0 ≤ E := by
    have := abs_lt.1 hρt
    have h1 : 0 ≤ (1 + ρ * t) ^ q := Real.rpow_nonneg (by linarith) _
    have h2 : 0 ≤ (1 - ρ * t) ^ q := Real.rpow_nonneg (by linarith) _
    positivity
  -- Bernoulli's inequality `(1 + s) ^ θ ≥ 1 + θ s` for `θ = p / q ≥ 1`
  have hB := one_add_mul_self_le_rpow_one_add (s := E - 1) (by linarith)
    ((one_le_div hq).2 hqp)
  rw [add_sub_cancel] at hB
  refine le_trans ?_ hB
  have hS := ((hasSum_choose_mul_pow_add_neg_pow (a := q) hρt).mul_left (p / q)).add
    (hasSum_ite_eq 0 (1 - p / q))
  rw [show p / q * E + (1 - p / q) = 1 + p / q * (E - 1) by ring] at hS
  refine hasSum_le (fun n => ?_) (hasSum_choose_mul_pow_add_neg_pow (a := p) ht) hS
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · rw [← two_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [ite_eq_right (by omega), Even.neg_pow ⟨k, by ring⟩, Even.neg_pow ⟨k, by ring⟩,
        pow_mul, pow_mul, mul_pow, mul_pow]
      have h := choose_two_mul_le hq hqp hp hq1 (sq_nonneg ρ) hρ hk
      nlinarith [mul_le_mul_of_nonneg_right h (pow_nonneg (sq_nonneg t) k)]
  · rw [ite_eq_right (by rintro rfl; exact Nat.not_odd_zero hn), hn.neg_pow, hn.neg_pow]
    simp

/-- The normalized reverse two-point inequality for `|t| ≤ 1`: both sides are continuous in `t`,
so the case `|t| < 1` extends to `t = ±1`. -/
private theorem one_add_rpow_add_one_sub_rpow_le_rpow {p q ρ t : ℝ} (hq : 0 < q) (hqp : q ≤ p)
    (hp : p ≤ 1) (hq1 : q < 1) (hρ : ρ ^ 2 * (1 - q) ≤ 1 - p) (ht : |t| ≤ 1) :
    ((1 + t) ^ p + (1 - t) ^ p) / 2 ≤ (((1 + ρ * t) ^ q + (1 - ρ * t) ^ q) / 2) ^ (p / q) := by
  have hp0 : 0 < p := hq.trans_le hqp
  have hc (a c : ℝ) (ha : 0 < a) :
      Continuous fun t : ℝ => ((1 + c * t) ^ a + (1 - c * t) ^ a) / 2 := by
    fun_prop (disch := positivity)
  have hcl : IsClosed {t : ℝ | ((1 + t) ^ p + (1 - t) ^ p) / 2 ≤
      (((1 + ρ * t) ^ q + (1 - ρ * t) ^ q) / 2) ^ (p / q)} := by
    refine isClosed_le ?_ ((Real.continuous_rpow_const (by positivity)).comp (hc q ρ hq))
    simpa using hc p 1 hp0
  have h := hcl.closure_subset_iff.2 fun t (ht : t ∈ Ioo (-1 : ℝ) 1) =>
    one_add_rpow_add_one_sub_rpow_le_rpow_of_lt hq hqp hp hq1 hρ (abs_lt.2 ht)
  rw [closure_Ioo (by norm_num)] at h
  exact h (abs_le.1 ht)

/-- **The reverse two-point inequality for positive exponents**: for `0 < q ≤ p ≤ 1`,
`ρ ^ 2 (1 - q) ≤ 1 - p` (so `ρ ^ 2 ≤ (1 - p) / (1 - q)` when `q < 1`) and `|b| ≤ a`,
`((a + b) ^ p + (a - b) ^ p) / 2 ≤ (((a + ρ b) ^ q + (a - ρ b) ^ q) / 2) ^ (p / q)`.
For a uniformly random bit `x = ±1` it says that `‖a + b x‖_p ^ p` is at most `‖a + ρ b x‖_q ^ p`
[O'Donnell, Exercise 10.7(a)][ODonnell2014]. As in the proof of the forward two-point
inequality, the two sides are compared through their binomial series; the bound on `ρ` is
O'Donnell's `0 ≤ ρ ≤ √((1 - p) / (1 - q))` of Exercise 10.7(b), which the coefficient
comparison reaches directly. -/
theorem rpow_add_rpow_le_rpow_add_rpow_rpow {p q ρ a b : ℝ} (hq : 0 < q) (hqp : q ≤ p)
    (hp : p ≤ 1) (hρ : ρ ^ 2 * (1 - q) ≤ 1 - p) (hb : |b| ≤ a) :
    ((a + b) ^ p + (a - b) ^ p) / 2 ≤ (((a + ρ * b) ^ q + (a - ρ * b) ^ q) / 2) ^ (p / q) := by
  rcases (hqp.trans hp).lt_or_eq with hq1 | rfl
  swap
  · obtain rfl : p = 1 := le_antisymm hp hqp
    simp only [Real.rpow_one, div_one]
    linarith
  have hp0 : 0 < p := hq.trans_le hqp
  have ha0 : 0 ≤ a := (abs_nonneg b).trans hb
  have hρ1 : |ρ| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    nlinarith
  rcases ha0.eq_or_lt with ha | ha
  · obtain rfl : b = 0 := abs_eq_zero.1 (le_antisymm (ha ▸ hb) (abs_nonneg b))
    subst ha
    simp only [add_zero, sub_zero, mul_zero, Real.zero_rpow hp0.ne', Real.zero_rpow hq.ne',
      zero_div]
    exact Real.rpow_nonneg le_rfl _
  set t := b / a
  have hbt : b = a * t := by rw [mul_div_cancel₀ _ ha.ne']
  have ht : |t| ≤ 1 := by rw [abs_div, abs_of_pos ha]; exact (div_le_one ha).2 hb
  have ht' := abs_le.1 ht
  have hρt := abs_le.1 (show |ρ * t| ≤ 1 by
    rw [abs_mul]; nlinarith [abs_nonneg ρ, abs_nonneg t])
  have key := one_add_rpow_add_one_sub_rpow_le_rpow hq hqp hp hq1 hρ ht
  have hE : 0 ≤ ((1 + ρ * t) ^ q + (1 - ρ * t) ^ q) / 2 := by
    have h1 : 0 ≤ (1 + ρ * t) ^ q := Real.rpow_nonneg (by linarith) _
    have h2 : 0 ≤ (1 - ρ * t) ^ q := Real.rpow_nonneg (by linarith) _
    positivity
  calc ((a + b) ^ p + (a - b) ^ p) / 2
      = a ^ p * (((1 + t) ^ p + (1 - t) ^ p) / 2) := by
        rw [hbt, show a + a * t = a * (1 + t) by ring, show a - a * t = a * (1 - t) by ring,
          Real.mul_rpow ha.le (by linarith), Real.mul_rpow ha.le (by linarith)]
        ring
    _ ≤ a ^ p * (((1 + ρ * t) ^ q + (1 - ρ * t) ^ q) / 2) ^ (p / q) :=
        mul_le_mul_of_nonneg_left key (Real.rpow_nonneg ha.le p)
    _ = (((a + ρ * b) ^ q + (a - ρ * b) ^ q) / 2) ^ (p / q) := by
        rw [hbt, show a + ρ * (a * t) = a * (1 + ρ * t) by ring,
          show a - ρ * (a * t) = a * (1 - ρ * t) by ring, Real.mul_rpow ha.le (by linarith),
          Real.mul_rpow ha.le (by linarith), ← mul_add, mul_div_assoc,
          Real.mul_rpow (Real.rpow_nonneg ha.le q) hE, ← Real.rpow_mul ha.le,
          mul_div_cancel₀ p hq.ne']

/-- **The reverse two-point inequality in norm form**: for `0 < q ≤ p ≤ 1`,
`0 ≤ ρ ≤ √((1 - p) / (1 - q))` and a nonnegative function `f` of one bit,
`‖f‖_p ≤ ‖T_ρ f‖_q` [O'Donnell, Exercise 10.7(a), (b)][ODonnell2014]. -/
theorem lpNorm_le_lpNorm_noiseOp_of_unit {p q ρ : ℝ} (hq : 0 < q) (hqp : q ≤ p) (hp : p ≤ 1)
    (hρ : 0 ≤ ρ) (hρ' : ρ ≤ √((1 - p) / (1 - q))) {f : (Unit → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) : lpNorm p f ≤ lpNorm q (noiseOp ρ f) := by
  have hp0 : 0 < p := hq.trans_le hqp
  have hσ : 0 ≤ (1 - p) / (1 - q) := div_nonneg (by linarith) (by linarith)
  have hρ2 : ρ ^ 2 ≤ (1 - p) / (1 - q) :=
    (pow_le_pow_left₀ hρ hρ' 2).trans (Real.sq_sqrt hσ).le
  have hρ2' : ρ ^ 2 * (1 - q) ≤ 1 - p := by
    rcases (show q ≤ 1 by linarith).lt_or_eq with hq1 | rfl
    · exact (le_div_iff₀ (by linarith)).1 hρ2
    · simp only [sub_self, mul_zero]
      linarith
  have hρ1 : ρ ≤ 1 :=
    hρ'.trans (Real.sqrt_le_one.2 (div_le_one_of_le₀ (by linarith) (by linarith)))
  set A := f fun _ => false
  set B := f fun _ => true
  have hA : 0 ≤ A := hf _
  have hB : 0 ≤ B := hf _
  have key := rpow_add_rpow_le_rpow_add_rpow_rpow (a := (A + B) / 2) (b := (A - B) / 2) hq hqp
    hp hρ2' (abs_le.2 ⟨by linarith, by linarith⟩)
  have hT0 : (noiseOp ρ f fun _ => false) = (A + B) / 2 + ρ * ((A - B) / 2) := by
    rw [noiseOp_unit, Bool.not_false]
    ring
  have hT1 : (noiseOp ρ f fun _ => true) = (A + B) / 2 - ρ * ((A - B) / 2) := by
    rw [noiseOp_unit, Bool.not_true]
    ring
  rw [show (A + B) / 2 + (A - B) / 2 = A by ring, show (A + B) / 2 - (A - B) / 2 = B by ring,
    ← hT0, ← hT1] at key
  have hT0' : 0 ≤ noiseOp ρ f fun _ => false := by rw [hT0]; nlinarith
  have hT1' : 0 ≤ noiseOp ρ f fun _ => true := by rw [hT1]; nlinarith
  have hX : 0 ≤ (A ^ p + B ^ p) / 2 := by positivity
  have hY : 0 ≤ ((noiseOp ρ f fun _ => false) ^ q + (noiseOp ρ f fun _ => true) ^ q) / 2 := by
    positivity
  rw [lpNorm, lpNorm, Fintype.expect_unique_bool, Fintype.expect_unique_bool, abs_of_nonneg hA,
    abs_of_nonneg hB, abs_of_nonneg hT0', abs_of_nonneg hT1']
  calc ((A ^ p + B ^ p) / 2) ^ p⁻¹
      ≤ ((((noiseOp ρ f fun _ => false) ^ q + (noiseOp ρ f fun _ => true) ^ q) / 2) ^ (p / q)) ^
          p⁻¹ := Real.rpow_le_rpow hX key (inv_nonneg.2 hp0.le)
    _ = (((noiseOp ρ f fun _ => false) ^ q + (noiseOp ρ f fun _ => true) ^ q) / 2) ^ q⁻¹ := by
        rw [← Real.rpow_mul hY, div_mul_eq_mul_div, mul_inv_cancel₀ hp0.ne', one_div]

/-! ### Two functions of a single bit -/

/-- For `-1 < r ≤ 0` and a nonnegative function `f` of one bit, with values `A` and `B`, the
square of `‖f‖_{1 + r}` is at most `((A + B) / 2) ^ 2 + r ((A - B) / 2) ^ 2`, the square of the
geometric mean of `T_{√(-r)} f`. -/
private theorem lpNorm_sq_le_of_unit {r : ℝ} (hr : -1 < r) (hr' : r ≤ 0)
    {f : (Unit → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    lpNorm (1 + r) f ^ 2 ≤ (((f fun _ => false) + f fun _ => true) / 2) ^ 2 +
      r * (((f fun _ => false) - f fun _ => true) / 2) ^ 2 := by
  set A := f fun _ => false
  set B := f fun _ => true
  have hA : 0 ≤ A := hf _
  have hB : 0 ≤ B := hf _
  have hp : 0 < 1 + r := by linarith
  have hX : 0 ≤ ((A + B) / 2) ^ 2 + r * ((A - B) / 2) ^ 2 := by
    nlinarith [mul_nonneg hA hB, mul_nonneg (by linarith : 0 ≤ r + 1) (sq_nonneg (A - B))]
  set X := ((A + B) / 2) ^ 2 + r * ((A - B) / 2) ^ 2
  have key := rpow_add_rpow_le_sq_sub_sq_mul_sq_rpow (ρ := √(-r)) (a := (A + B) / 2)
    (b := (A - B) / 2) hp (by rw [Real.sq_sqrt (by linarith)]; linarith)
    (abs_le.2 ⟨by linarith, by linarith⟩)
  rw [show (A + B) / 2 + (A - B) / 2 = A by ring, show (A + B) / 2 - (A - B) / 2 = B by ring,
    Real.sq_sqrt (by linarith), neg_mul, sub_neg_eq_add] at key
  have hS : 0 ≤ (A ^ (1 + r) + B ^ (1 + r)) / 2 := by positivity
  rw [lpNorm, Fintype.expect_unique_bool, abs_of_nonneg hA, abs_of_nonneg hB,
    ← Real.rpow_natCast, ← Real.rpow_mul hS]
  calc ((A ^ (1 + r) + B ^ (1 + r)) / 2) ^ ((1 + r)⁻¹ * ((2 : ℕ) : ℝ))
      ≤ (X ^ ((1 + r) / 2)) ^ ((1 + r)⁻¹ * ((2 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow hS key (by positivity)
    _ = X := by
        rw [← Real.rpow_mul hX, Nat.cast_ofNat,
          show (1 + r) / 2 * ((1 + r)⁻¹ * 2) = 1 by field_simp, Real.rpow_one]

/-- **The Reverse Two-Function Hypercontractivity Theorem on one bit**: for `-1 < r, s ≤ 0`,
`0 ≤ ρ ≤ √(r s)` and nonnegative functions `f` and `g` of one bit,
`‖f‖_{1 + r} ‖g‖_{1 + s} ≤ 𝔼_x f x · T_ρ g x` [O'Donnell, Exercise 10.6][ODonnell2014]. -/
theorem lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_unit {r s ρ : ℝ} (hr : -1 < r) (hr' : r ≤ 0)
    (hs : -1 < s) (hs' : s ≤ 0) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ √(r * s)) {f g : (Unit → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    lpNorm (1 + r) f * lpNorm (1 + s) g ≤ 𝔼 x, f x * noiseOp ρ g x := by
  have hf2 := lpNorm_sq_le_of_unit hr hr' hf
  have hg2 := lpNorm_sq_le_of_unit hs hs' hg
  have hE : 𝔼 x, f x * noiseOp ρ g x =
      ((f fun _ => false) + f fun _ => true) / 2 * (((g fun _ => false) + g fun _ => true) / 2) +
        ρ * (((f fun _ => false) - f fun _ => true) / 2) *
          (((g fun _ => false) - g fun _ => true) / 2) := by
    rw [Fintype.expect_unique_bool, noiseOp_unit, noiseOp_unit, Bool.not_false, Bool.not_true]
    ring
  rw [hE]
  have hA : 0 ≤ f fun _ => false := hf _
  have hB : 0 ≤ f fun _ => true := hf _
  have hC : 0 ≤ g fun _ => false := hg _
  have hD : 0 ≤ g fun _ => true := hg _
  have ham : |((f fun _ => false) - f fun _ => true) / 2| ≤
      ((f fun _ => false) + f fun _ => true) / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have hbn : |((g fun _ => false) - g fun _ => true) / 2| ≤
      ((g fun _ => false) + g fun _ => true) / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  set m := ((f fun _ => false) + f fun _ => true) / 2
  set a := ((f fun _ => false) - f fun _ => true) / 2
  set n := ((g fun _ => false) + g fun _ => true) / 2
  set b := ((g fun _ => false) - g fun _ => true) / 2
  -- `σ = √(-r) |a|` and `τ = √(-s) |b|`, so that `σ τ = √(r s) |a b|`
  set σ := √(-r) * |a|
  set τ := √(-s) * |b|
  have hσ2 : σ ^ 2 = -r * a ^ 2 := by rw [mul_pow, Real.sq_sqrt (by linarith), sq_abs]
  have hτ2 : τ ^ 2 = -s * b ^ 2 := by rw [mul_pow, Real.sq_sqrt (by linarith), sq_abs]
  have hστ : σ * τ = √(r * s) * (|a| * |b|) := by
    rw [show r * s = -r * -s by ring, Real.sqrt_mul (by linarith)]
    ring
  have hσ : 0 ≤ σ := by positivity
  have hτ : 0 ≤ τ := by positivity
  have hm : 0 ≤ m := (abs_nonneg a).trans ham
  have hn : 0 ≤ n := (abs_nonneg b).trans hbn
  have hσm : σ ≤ m := (abs_le_of_sq_le_sq' (by
    nlinarith [sq_abs a, abs_nonneg a, mul_le_mul ham ham (abs_nonneg a) hm]) hm).2
  have hτn : τ ≤ n := (abs_le_of_sq_le_sq' (by
    nlinarith [sq_abs b, abs_nonneg b, mul_le_mul hbn hbn (abs_nonneg b) hn]) hn).2
  have hlow : m * n - σ * τ ≤ m * n + ρ * a * b := by
    have h1 : -(ρ * a * b) ≤ ρ * (|a| * |b|) := by
      rw [mul_assoc, ← abs_mul, ← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) hρ
    have h2 : ρ * (|a| * |b|) ≤ σ * τ := by
      rw [hστ]
      exact mul_le_mul_of_nonneg_right hρ' (by positivity)
    linarith
  have hP : 0 ≤ lpNorm (1 + r) f * lpNorm (1 + s) g :=
    mul_nonneg (lpNorm_nonneg _ _) (lpNorm_nonneg _ _)
  have hmn : 0 ≤ m * n - σ * τ := by nlinarith
  refine le_trans ?_ hlow
  refine (pow_le_pow_iff_left₀ hP hmn two_ne_zero).1 ?_
  rw [mul_pow]
  calc lpNorm (1 + r) f ^ 2 * lpNorm (1 + s) g ^ 2 ≤ (m ^ 2 - σ ^ 2) * (n ^ 2 - τ ^ 2) := by
        refine mul_le_mul (by linarith) (by linarith) (sq_nonneg _) (by nlinarith)
    _ ≤ (m * n - σ * τ) ^ 2 := by nlinarith [sq_nonneg (m * τ - n * σ)]

end Cslib.BitString
