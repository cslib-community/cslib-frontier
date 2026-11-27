/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.ReverseHolder
public import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity.ReverseTwoPoint
public import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity.Tensorization
public import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity.TwoPoint
public import CslibFrontier.Foundations.BooleanAnalysis.ReverseHypercontractivity
import CslibFrontier.Foundations.Data.Finset.Expect

/-! # Reverse hypercontractivity on small cubes

Instances of the reverse two-point inequalities, the Reverse Two-Function Hypercontractivity
Theorem, the reverse Hölder inequality, the equivalence of the two-function and one-function
forms, the one-function Reverse Hypercontractivity Theorem for `q < 0 < p`, `0 < q < p` and
`q < p < 0`, and the Reverse Small-Set Expansion Theorem. A negative-exponent norm is computed (a
harmonic mean), and the two-function theorem is applied beyond `-1 < r` at `r = -2` with
`s = -1 / 4`, `ρ = 1 / 2` and with `s = -1 / 2`, `ρ = 1`, and in the mirror case `s = -2`. On one
bit, the subcubes `{x | x () = true}` and `{x | x () = false}` have volume `1 / 2`, and at
`ρ = 1 / 2` a correlated pair lands in them with probability `1 / 8`; the Reverse Small-Set
Expansion Theorem bounds this by `1 / 16`, and by `1 / 4`, the product of the volumes, at
`ρ = 0`. The examples show that the hypotheses are
satisfiable, also for functions with zeros and for exponents strictly inside `(0, 1)`.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisReverseHypercontractivity

open Cslib Cslib.BitString Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- The reverse two-point inequality at `p = 1 / 2` and `ρ = 1 / 2`, for `|b| ≤ a`.
example {a b : ℝ} (hb : |b| ≤ a) :
    ((a + b) ^ (1 / 2 : ℝ) + (a - b) ^ (1 / 2 : ℝ)) / 2 ≤
      (a ^ 2 - (1 / 2) ^ 2 * b ^ 2) ^ ((1 / 2 : ℝ) / 2) :=
  rpow_add_rpow_le_sq_sub_sq_mul_sq_rpow (by norm_num) (by norm_num) hb

-- The one-bit theorem at `r = -1 / 3`, `s = -3 / 4` and the largest correlation `ρ = 1 / 2`, for
-- a function with a zero.
example (g : (Unit → Bool) → ℝ) (hg : ∀ x, 0 ≤ g x) :
    lpNorm (1 + -1 / 3) (fun x : Unit → Bool => if x () then 3 else 0) * lpNorm (1 + -3 / 4) g ≤
      𝔼 x, (if x () then 3 else 0) * noiseOp (1 / 2) g x :=
  lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_unit (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by rw [show (-1 / 3 : ℝ) * (-3 / 4) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
    (fun x => by split_ifs <;> norm_num) hg

-- Tensorization applied directly: the one-bit theorem at `r = s = -1 / 2` and `ρ = 1 / 2` gives
-- the inequality on every cube.
example {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    lpNorm (1 / 2) f * lpNorm (1 / 2) g ≤ 𝔼 x, f x * noiseOp (1 / 2) g x := by
  refine le_expect_mul_noiseOp_of_unit (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun f g hf hg => ?_) hf hg
  have h := lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_unit (r := -1 / 2) (s := -1 / 2)
    (ρ := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show (-1 / 2 : ℝ) * (-1 / 2) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
    hf hg
  norm_num at h
  exact h

-- The theorem on every cube, at `r = -1 / 3`, `s = -3 / 4` and `ρ = 1 / 2`.
example {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    lpNorm (2 / 3) f * lpNorm (1 / 4) g ≤ 𝔼 x, f x * noiseOp (1 / 2) g x := by
  have h := lpNorm_mul_lpNorm_le_expect_mul_noiseOp (r := -1 / 3) (s := -3 / 4) (ρ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show (-1 / 3 : ℝ) * (-3 / 4) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
    hf hg
  norm_num at h
  exact h

-- At `r = s = 0` and `ρ = 0` the theorem gives `𝔼 f · 𝔼 g ≤ 𝔼_x f x · T_0 g x` (the two sides are
-- in fact equal).
example {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    lpNorm 1 f * lpNorm 1 g ≤ 𝔼 x, f x * noiseOp 0 g x := by
  simpa using lpNorm_mul_lpNorm_le_expect_mul_noiseOp (r := 0) (s := 0) (ρ := 0) (by norm_num)
    le_rfl (by norm_num) le_rfl le_rfl (by simp) hf hg

-- Exercise 10.8: `r = s = -1 / 2` for arbitrary real functions, at `ρ = 1 / 2`.
example (f g : (ι → Bool) → ℝ) :
    (𝔼 x, |f x|) ^ 2 * (𝔼 x, |g x|) ^ 2 ≤ 𝔼 x, f x ^ 2 * noiseOp (1 / 2) (fun y => g y ^ 2) x :=
  sq_expect_abs_mul_sq_expect_abs_le (by norm_num) le_rfl f g

/-! ### Negative exponents, reverse Hölder and the one-function form -/

-- For a positive function, `lpNorm (-1)` is the harmonic mean: here of `1` and `1 / 3`.
example : lpNorm (-1) (fun x : Unit → Bool => if x () then 1 else 1 / 3 : (Unit → Bool) → ℝ) =
    1 / 2 := by
  rw [lpNorm_of_nonneg _ fun x => by split_ifs <;> norm_num, Fintype.expect_unique_bool]
  simp only [Real.rpow_neg_one]
  norm_num

-- The reverse Hölder inequality at `p = 1 / 2`, whose conjugate exponent is `-1`.
example {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 < f x) (hg : ∀ x, 0 < g x) :
    lpNorm (1 / 2) f * lpNorm (-1) g ≤ 𝔼 x, f x * g x := by
  have h := lpNorm_mul_lpNorm_le_expect_mul (p := 1 / 2) (by norm_num) (by norm_num) hf hg
  norm_num at h
  exact h

-- `‖f‖_{1/2}` is the least value of `𝔼 f g` over positive `g` with `‖g‖_{-1} = 1`.
example {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 < f x) :
    IsLeast {c | ∃ g : (ι → Bool) → ℝ, (∀ x, 0 < g x) ∧ lpNorm (-1) g = 1 ∧
      c = 𝔼 x, f x * g x} (lpNorm (1 / 2) f) := by
  have h := isLeast_expect_mul (p := 1 / 2) (by norm_num) (by norm_num) hf
  norm_num at h
  exact h

-- Through the equivalence of the two forms, the two-function theorem at `r = -2`, `s = -1 / 2`
-- and `ρ = 1`, beyond `-1 < r`, gives `‖g‖_{1/2} ≤ ‖T_1 g‖_{1/2}`.
example {g : (ι → Bool) → ℝ} (hg : ∀ x, 0 < g x) :
    lpNorm (1 + -1 / 2) g ≤ lpNorm (1 + (-2)⁻¹) (noiseOp 1 g) :=
  (le_expect_mul_noiseOp_iff_lpNorm_le_lpNorm_noiseOp (s := -1 / 2) (by norm_num) (by norm_num)
    (by norm_num) le_rfl).1
    (fun f g hf hg => by
      have h := lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_lt_neg_one (r := -2) (s := -1 / 2)
        (ρ := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hf fun x => (hg x).le
      norm_num at h ⊢
      exact h) g hg

-- The one-function theorem at `p = 1 / 2`, `q = -1` and the largest correlation `ρ = 1 / 2`, for
-- a nonnegative function.
theorem lpNorm_half_le_lpNorm_neg_one_noiseOp_half {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    lpNorm (1 / 2) f ≤ lpNorm (-1) (noiseOp (1 / 2) f) :=
  lpNorm_le_lpNorm_noiseOp (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show (1 - 1 / 2 : ℝ) / (1 - -1) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]) hf

-- It applies to a function with a zero: the indicator of a one-bit subcube.
example : lpNorm (1 / 2) (fun x : Unit → Bool => if x () then (1 : ℝ) else 0) ≤
    lpNorm (-1) (noiseOp (1 / 2) fun x : Unit → Bool => if x () then (1 : ℝ) else 0) :=
  lpNorm_half_le_lpNorm_neg_one_noiseOp_half fun x => by split_ifs <;> norm_num

-- The equivalence of the two forms, backwards: the one-function theorem at `p = 1 / 2`, `q = -1`
-- and `ρ = 1 / 2` gives the two-function inequality at `r = s = -1 / 2`.
example {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 < f x) (hg : ∀ x, 0 < g x) :
    lpNorm (1 + -1 / 2) f * lpNorm (1 + -1 / 2) g ≤ 𝔼 x, f x * noiseOp (1 / 2) g x :=
  (le_expect_mul_noiseOp_iff_lpNorm_le_lpNorm_noiseOp (r := -1 / 2) (s := -1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).2
    (fun g hg => by
      have h := lpNorm_half_le_lpNorm_neg_one_noiseOp_half fun x => (hg x).le
      norm_num
      exact h) f g hf hg

/-! ### Positive exponents: `0 < q < p ≤ 1`, and `r < -1` -/

-- The reverse two-point inequality at `p = 1 / 2`, `q = 1 / 4` and the largest correlation
-- `ρ = √(2 / 3)`, for which `ρ ^ 2 (1 - q) = 1 - p`.
example {a b : ℝ} (hb : |b| ≤ a) :
    ((a + b) ^ (1 / 2 : ℝ) + (a - b) ^ (1 / 2 : ℝ)) / 2 ≤
      (((a + √(2 / 3) * b) ^ (1 / 4 : ℝ) + (a - √(2 / 3) * b) ^ (1 / 4 : ℝ)) / 2) ^
        ((1 / 2 : ℝ) / (1 / 4)) :=
  rpow_add_rpow_le_rpow_add_rpow_rpow (by norm_num) (by norm_num) (by norm_num)
    (by rw [Real.sq_sqrt (by norm_num)]; norm_num) hb

-- Its norm form on one bit, for a function with a zero.
example : lpNorm (1 / 2) (fun x : Unit → Bool => if x () then (1 : ℝ) else 0) ≤
    lpNorm (1 / 4) (noiseOp (√(2 / 3)) fun x : Unit → Bool => if x () then (1 : ℝ) else 0) :=
  lpNorm_le_lpNorm_noiseOp_of_unit (by norm_num) (by norm_num) (by norm_num)
    (Real.sqrt_nonneg _) (le_of_eq (by norm_num)) fun x => by split_ifs <;> norm_num

/-- The one-function theorem at `p = 1 / 2`, `q = 1 / 4` and the largest correlation
`ρ = √(2 / 3)`, for a nonnegative function on any cube. -/
theorem lpNorm_half_le_lpNorm_quarter_noiseOp {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    lpNorm (1 / 2) f ≤ lpNorm (1 / 4) (noiseOp (√(2 / 3)) f) :=
  lpNorm_le_lpNorm_noiseOp (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Real.sqrt_nonneg _) (le_of_eq (by norm_num)) hf

-- It applies to the indicator of a one-bit subcube, which has a zero.
example : lpNorm (1 / 2) (fun x : Unit → Bool => if x () then (1 : ℝ) else 0) ≤
    lpNorm (1 / 4) (noiseOp (√(2 / 3)) fun x : Unit → Bool => if x () then (1 : ℝ) else 0) :=
  lpNorm_half_le_lpNorm_quarter_noiseOp fun x => by split_ifs <;> norm_num

-- The two-function theorem at `r = -2`, `s = -1 / 4` and `ρ = 1 / 2 ≤ √(1 / 2)`: the exponents are
-- `1 + r = -1` and `1 + s = 3 / 4`.
example {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 < f x) (hg : ∀ x, 0 ≤ g x) :
    lpNorm (-1) f * lpNorm (3 / 4) g ≤ 𝔼 x, f x * noiseOp (1 / 2) g x := by
  have h := lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_lt_neg_one (r := -2) (s := -1 / 4)
    (ρ := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Real.le_sqrt_of_sq_le (by norm_num)) hf hg
  norm_num at h
  exact h

-- At `r = -2`, `s = -1 / 2` it reaches `ρ = √(r s) = 1` for nonnegative `g`.
example {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 < f x) (hg : ∀ x, 0 ≤ g x) :
    lpNorm (-1) f * lpNorm (1 / 2) g ≤ 𝔼 x, f x * noiseOp 1 g x := by
  have h := lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_lt_neg_one (r := -2) (s := -1 / 2)
    (ρ := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hf hg
  norm_num at h ⊢
  exact h

-- The mirror case `s < -1 < r` at `r = -1 / 4`, `s = -2` and `ρ = 1 / 2`, for a nonnegative `f`
-- and a positive `g`.
example {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 < g x) :
    lpNorm (3 / 4) f * lpNorm (-1) g ≤ 𝔼 x, f x * noiseOp (1 / 2) g x := by
  have h := lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_neg_one_lt_of_lt_neg_one (r := -1 / 4)
    (s := -2) (ρ := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Real.le_sqrt_of_sq_le (by norm_num)) hf hg
  norm_num at h
  exact h

-- The reverse Hölder inequality at `p = 1 / 2`, whose conjugate exponent is `-1`, for a
-- nonnegative first function.
example {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 < g x) :
    lpNorm (1 / 2) f * lpNorm (-1) g ≤ 𝔼 x, f x * g x := by
  have h := lpNorm_mul_lpNorm_le_expect_mul_of_pos (p := 1 / 2) (by norm_num) (by norm_num) hf hg
  norm_num at h
  exact h

-- The reverse Hölder inequality at `p = -1`, whose conjugate exponent is `1 / 2`, for a
-- nonnegative second function.
example {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 < f x) (hg : ∀ x, 0 ≤ g x) :
    lpNorm (-1) f * lpNorm (1 / 2) g ≤ 𝔼 x, f x * g x := by
  have h := lpNorm_mul_lpNorm_le_expect_mul_of_neg (p := -1) (by norm_num) hf hg
  norm_num at h
  exact h

/-! ### Negative exponents: `q < p < 0` -/

-- The one-function theorem at `p = -1`, `q = -2` and the largest correlation `ρ = √(2 / 3)`, for a
-- positive function.
example {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 < f x) :
    lpNorm (-1) f ≤ lpNorm (-2) (noiseOp (√(2 / 3)) f) :=
  lpNorm_le_lpNorm_noiseOp_of_neg (by norm_num) (by norm_num) (Real.sqrt_nonneg _)
    (le_of_eq (by norm_num)) hf

/-! ### Reverse small-set expansion for one-bit subcubes -/

/-- The subcube of the one-bit cube where the bit is `c`. -/
def subcube (c : Bool) : Set (Unit → Bool) := {x | x () = c}

/-- Each one-bit subcube has volume `1 / 2`. -/
theorem expect_indicator_subcube (c : Bool) :
    𝔼 x, (subcube c).indicator (1 : (Unit → Bool) → ℝ) x = 1 / 2 := by
  rw [Fintype.expect_unique_bool]
  cases c <;> simp [subcube, Set.indicator]

-- The `L^2` norm of a subcube indicator is the square root of its volume.
example :
    lpNorm 2 ((subcube true).indicator (1 : (Unit → Bool) → ℝ)) = (1 / 2 : ℝ) ^ (2⁻¹ : ℝ) := by
  rw [lpNorm_indicator_one two_ne_zero, expect_indicator_subcube]

/-- The volume `1 / 2` is `exp (-a ^ 2 / 2)` for `a = √(2 log 2)`. -/
theorem half_eq_exp : (1 / 2 : ℝ) = Real.exp (-(√(2 * Real.log 2) ^ 2 / 2)) := by
  rw [Real.sq_sqrt (by positivity), mul_div_cancel_left₀ _ two_ne_zero, Real.exp_neg,
    Real.exp_log two_pos, one_div]

/-- A `1 / 2`-correlated pair lands in opposite subcubes with probability `1 / 8`. -/
theorem expect_indicator_mul_noiseOp_subcube :
    𝔼 x, (subcube true).indicator 1 x * noiseOp (1 / 2) ((subcube false).indicator 1) x =
      (1 / 8 : ℝ) := by
  rw [Fintype.expect_unique_bool, noiseOp_unit, noiseOp_unit]
  simp [subcube, Set.indicator]
  norm_num

-- The Reverse Small-Set Expansion Theorem bounds it by `1 / 16`.
example :
    (1 / 16 : ℝ) ≤
      𝔼 x, (subcube true).indicator 1 x * noiseOp (1 / 2) ((subcube false).indicator 1) x := by
  set a := √(2 * Real.log 2)
  have h := exp_le_expect_indicator_mul_noiseOp_indicator (ρ := 1 / 2) (by norm_num) (by norm_num)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    ((expect_indicator_subcube true).trans half_eq_exp)
    ((expect_indicator_subcube false).trans half_eq_exp)
  convert h using 1
  have ha : a ^ 2 = 2 * Real.log 2 := Real.sq_sqrt (by positivity)
  rw [show (a ^ 2 + 2 * (1 / 2) * a * a + a ^ 2) / (2 * (1 - (1 / 2) ^ 2)) = 4 * Real.log 2 by
    rw [show a ^ 2 + 2 * (1 / 2) * a * a + a ^ 2 = 3 * a ^ 2 by ring, ha]
    ring, Real.exp_neg, show 4 * Real.log 2 = Real.log 16 by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num, Real.exp_log (by norm_num), one_div]

-- At `ρ = 0` the bound is the product `1 / 4` of the volumes.
example :
    (1 / 4 : ℝ) ≤
      𝔼 x, (subcube true).indicator 1 x * noiseOp 0 ((subcube false).indicator 1) x := by
  set a := √(2 * Real.log 2)
  have h := exp_le_expect_indicator_mul_noiseOp_indicator le_rfl zero_lt_one
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    ((expect_indicator_subcube true).trans half_eq_exp)
    ((expect_indicator_subcube false).trans half_eq_exp)
  convert h using 1
  have ha : a ^ 2 = 2 * Real.log 2 := Real.sq_sqrt (by positivity)
  rw [show (a ^ 2 + 2 * 0 * a * a + a ^ 2) / (2 * (1 - 0 ^ 2)) = Real.log 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, ha]
    ring, Real.exp_neg, Real.exp_log (by norm_num), one_div]

-- The degenerate volume `1`: `a = 0` for the whole cube.
example (B : Set (ι → Bool)) {b : ℝ} (hb : 0 ≤ b)
    (hB : 𝔼 x, B.indicator (1 : (ι → Bool) → ℝ) x = Real.exp (-(b ^ 2 / 2))) :
    Real.exp (-(b ^ 2 / (2 * (1 - (1 / 2) ^ 2)))) ≤
      𝔼 x, (Set.univ : Set (ι → Bool)).indicator 1 x * noiseOp (1 / 2) (B.indicator 1) x := by
  have h := exp_le_expect_indicator_mul_noiseOp_indicator (ρ := 1 / 2) (a := 0) (by norm_num)
    (by norm_num) le_rfl hb (A := Set.univ) (by simp) hB
  simpa using h

-- The mirror case `b = 0` for the whole cube as `B`.
example (A : Set (ι → Bool)) {a : ℝ} (ha : 0 ≤ a)
    (hA : 𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x = Real.exp (-(a ^ 2 / 2))) :
    Real.exp (-(a ^ 2 / (2 * (1 - (1 / 2) ^ 2)))) ≤
      𝔼 x, A.indicator 1 x * noiseOp (1 / 2) ((Set.univ : Set (ι → Bool)).indicator 1) x := by
  have h := exp_le_expect_indicator_mul_noiseOp_indicator (ρ := 1 / 2) (b := 0) (by norm_num)
    (by norm_num) ha le_rfl (B := Set.univ) hA (by simp)
  simpa using h

end CslibFrontierTests.BooleanAnalysisReverseHypercontractivity
