/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.LpNorm
public import CslibFrontier.Foundations.BooleanAnalysis.Noise
import CslibFrontier.Foundations.Analysis.ReverseHolder
import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity.ReverseTwoPoint
import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity.Tensorization

/-!
# Reverse hypercontractivity on the Boolean cube

For nonnegative functions, the expectation of `f x g y` over a `ρ`-correlated pair `(x, y)`,
which is `𝔼_x f x · T_ρ g x`, is bounded *below* by a product of `L^p` "norms" with exponents
at most `1` [O'Donnell, Remark 10.3 and Exercises 10.6–10.9][ODonnell2014]. Writing `‖f‖_p` for
`Cslib.lpNorm`, which for a positive `f` and `p < 0` is the book's `𝔼[f ^ p] ^ (1 / p)`
(`Cslib.lpNorm_of_nonneg`), this file proves:

* the **Reverse Two-Function Hypercontractivity Theorem** `‖f‖_{1 + r} ‖g‖_{1 + s} ≤
  𝔼_x f x · T_ρ g x` for `0 ≤ ρ ≤ √(r s) ≤ 1`: for `-1 < r, s ≤ 0` and nonnegative `f` and `g`
  (`BitString.lpNorm_mul_lpNorm_le_expect_mul_noiseOp`); for `r < -1 < s ≤ 0`, positive `f` and
  nonnegative `g` (`BitString.lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_lt_neg_one`); for
  `s < -1 < r`, nonnegative `f` and positive `g`, by exchanging `f` and `g`
  (`BitString.lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_neg_one_lt_of_lt_neg_one`);
* its case `r = s = -1/2` on every cube, derived from the general theorem (O'Donnell's
  Exercise 10.8 asks for a direct proof of the one-bit case), which needs no sign condition after
  replacing `f` and `g` by their squares: `(𝔼 |f|) ^ 2 (𝔼 |g|) ^ 2 ≤ 𝔼_x f x ^ 2 · T_ρ g ^ 2 x`
  for `0 ≤ ρ ≤ 1 / 2` (`BitString.sq_expect_abs_mul_sq_expect_abs_le`);
* the **equivalence of the two-function and one-function forms** (Exercise 10.6(b)): for `r < 0`
  with `r ≠ -1`, the two-function inequality for all positive `f` and `g` holds if and only if
  `‖g‖_{1 + s} ≤ ‖T_ρ g‖_{1 + 1 / r}` for all positive `g`
  (`BitString.le_expect_mul_noiseOp_iff_lpNorm_le_lpNorm_noiseOp`);
* the **Reverse Hypercontractivity Theorem** `‖f‖_p ≤ ‖T_ρ f‖_q` for
  `0 ≤ ρ ≤ √((1 - p) / (1 - q))`: for `q < p` with `q ≠ 0`, `0 < p ≤ 1` and nonnegative `f`
  (`BitString.lpNorm_le_lpNorm_noiseOp`), and for `q < p < 0` and positive `f`
  (`BitString.lpNorm_le_lpNorm_noiseOp_of_neg`);
* the **Reverse Small-Set Expansion Theorem**: if `A` and `B` have volumes `exp (-a ^ 2 / 2)` and
  `exp (-b ^ 2 / 2)` with `a, b ≥ 0`, and `0 ≤ ρ < 1`, then a `ρ`-correlated pair `(x, y)` has
  `x ∈ A` and `y ∈ B` with probability at least `exp (-(a ^ 2 + 2 ρ a b + b ^ 2) / (2 (1 - ρ ^ 2)))`
  (`BitString.exp_le_expect_indicator_mul_noiseOp_indicator`).

The two-function theorem for `-1 < r, s ≤ 0` is the one-bit case
(`BitString.lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_unit`) tensorized by
`BitString.le_expect_mul_noiseOp_of_unit`. For `r < -1` the one-bit case is the reverse two-point
inequality `‖g‖_{1 + s} ≤ ‖T_ρ g‖_{1 + 1 / r}` for the positive exponents `1 + 1 / r ≤ 1 + s`
(`BitString.lpNorm_le_lpNorm_noiseOp_of_unit`, Exercise 10.7(a)) followed by the reverse Hölder
inequality, tensorized by `BitString.le_expect_mul_noiseOp_of_unit_of_pos`. The equivalence of the
two forms is the reverse Hölder inequality and its equality case
(`Cslib.lpNorm_mul_lpNorm_le_expect_mul`, `Cslib.expect_mul_rpow_sub_one`): `1 + r` and
`1 + 1 / r` are Hölder conjugates. The same argument with `r = 1 / (q - 1)` and `s = p - 1` turns
the two-function theorem into the one-function theorem for `0 < p`, with `r ∈ (-1, 0)` when
`q < 0` and `r < -1` when `0 < q`; for nonnegative `f` that is not identically `0`, `T_ρ f` is
positive (`BitString.noiseOp_pos_of_nonneg`), which is all the argument needs. For `q < p < 0`
the equivalence turns the one-function theorem into the two-function theorem with
`1 + s = p < 0`, which is the case `r < -1` with `f` and `g` exchanged (the duality of
Exercise 10.7(d)). The Small-Set Expansion Theorem applies the two-function theorem to the
indicators of `A` and `B` with `1 + r = a (1 - ρ ^ 2) / (a + ρ b)` and
`1 + s = b (1 - ρ ^ 2) / (ρ a + b)`, which lie in `(0, 1]` and have `r s = ρ ^ 2`
(Exercise 10.9); when `a = 0` or `b = 0` one of the sets is the whole cube.

## Scope

O'Donnell states the two-function theorem for all `r, s ≤ 0` with `√(r s) ≤ 1`, with `‖f‖_p` for
`p ≤ 0` defined for positive `f` (as `𝔼[f ^ p] ^ (1 / p)` for `p < 0` and the geometric mean for
`p = 0`) and extended to nonnegative `f` by limits, and the one-function theorem for all
`-∞ ≤ q < p ≤ 1`. Covered here are the two-function theorem for all `r, s ≤ 0` other than `-1`
with `0 ≤ ρ ≤ √(r s) ≤ 1`, and the one-function theorem for all `q < p ≤ 1` other than `0`. A
function whose exponent is negative is assumed positive; a function whose exponent lies in
`(0, 1]` may be nonnegative, where `Cslib.lpNorm` is the book's norm and no limit is needed.

Not covered:

* the exponents `p = 0`, `q = 0` and `q = -∞` (Exercise 10.7(c), (f)), beyond the one-bit
  inequality for `q = 0` (`BitString.rpow_add_rpow_le_sq_sub_sq_mul_sq_rpow`). `Cslib.lpNorm 0` is
  `1`, not the geometric mean, so `r = -1` and `s = -1` are excluded throughout;
* nonnegative functions with a negative exponent: a function with a negative exponent is assumed
  positive (Exercise 10.6(a) is not formalized).

The case `ρ = 1` of the Small-Set Expansion Theorem is excluded: its bound is then `0` unless
`a = b = 0`, while Lean's division by `0` would make the stated bound `1`.

## Main results

* `Cslib.BitString.lpNorm_mul_lpNorm_le_expect_mul_noiseOp`: the Reverse Two-Function
  Hypercontractivity Theorem for `-1 < r, s ≤ 0`.
* `Cslib.BitString.lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_lt_neg_one`,
  `Cslib.BitString.lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_neg_one_lt_of_lt_neg_one`: the same
  theorem for `r < -1 < s ≤ 0` and for `s < -1 < r ≤ 0`.
* `Cslib.BitString.sq_expect_abs_mul_sq_expect_abs_le`: its case `r = s = -1/2`.
* `Cslib.BitString.le_expect_mul_noiseOp_iff_lpNorm_le_lpNorm_noiseOp`: the equivalence of the
  two-function and one-function forms.
* `Cslib.BitString.lpNorm_le_lpNorm_noiseOp`: the Reverse Hypercontractivity Theorem for
  `q < p`, `q ≠ 0` and `0 < p ≤ 1`.
* `Cslib.BitString.lpNorm_le_lpNorm_noiseOp_of_neg`: the same theorem for `q < p < 0`.
* `Cslib.BitString.exp_le_expect_indicator_mul_noiseOp_indicator`: the Reverse Small-Set
  Expansion Theorem.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Two-function reverse hypercontractivity -/

/-- **The Reverse Two-Function Hypercontractivity Theorem**: for `-1 < r, s ≤ 0`,
`0 ≤ ρ ≤ √(r s)` and nonnegative `f` and `g`, the expectation `𝔼_x f x · T_ρ g x` of `f x g y`
over a `ρ`-correlated pair `(x, y)` is at least `‖f‖_{1 + r} ‖g‖_{1 + s}`
[O'Donnell, Exercise 10.6][ODonnell2014]. -/
theorem lpNorm_mul_lpNorm_le_expect_mul_noiseOp {r s ρ : ℝ} (hr : -1 < r) (hr' : r ≤ 0)
    (hs : -1 < s) (hs' : s ≤ 0) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ √(r * s)) {f g : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    lpNorm (1 + r) f * lpNorm (1 + s) g ≤ 𝔼 x, f x * noiseOp ρ g x :=
  le_expect_mul_noiseOp_of_unit (by linarith : 0 < 1 + r).ne' (by linarith : 0 < 1 + s).ne' hρ
    (hρ'.trans (Real.sqrt_le_one.2 (by nlinarith)))
    (fun _ _ hf hg => lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_unit hr hr' hs hs' hρ hρ' hf hg)
    hf hg

/-- **The Reverse Two-Function Hypercontractivity Theorem for `r = s = -1/2`**: for
`0 ≤ ρ ≤ 1 / 2` and any real `f` and `g`, the expectation of `f x ^ 2 g y ^ 2` over a
`ρ`-correlated pair `(x, y)` is at least `(𝔼 |f|) ^ 2 (𝔼 |g|) ^ 2`. This is the statement of
[O'Donnell, Exercise 10.8][ODonnell2014] on every cube, derived from the general theorem rather
than proved directly. -/
theorem sq_expect_abs_mul_sq_expect_abs_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1 / 2)
    (f g : (ι → Bool) → ℝ) :
    (𝔼 x, |f x|) ^ 2 * (𝔼 x, |g x|) ^ 2 ≤ 𝔼 x, f x ^ 2 * noiseOp ρ (fun y => g y ^ 2) x := by
  have h := lpNorm_mul_lpNorm_le_expect_mul_noiseOp (r := -1 / 2) (s := -1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hρ
    (by rwa [show (-1 / 2 : ℝ) * (-1 / 2) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
    (f := fun x => f x ^ 2) (g := fun y => g y ^ 2) (fun _ => sq_nonneg _) fun _ => sq_nonneg _
  rwa [show (1 : ℝ) + -1 / 2 = 1 / 2 by norm_num, lpNorm_half_sq, lpNorm_half_sq] at h

/-! ### One-function reverse hypercontractivity -/

/-- **The two forms of reverse hypercontractivity are equivalent**: for `r < 0` with `r ≠ -1`
and `|ρ| ≤ 1`, the two-function inequality `‖f‖_{1 + r} ‖g‖_{1 + s} ≤ 𝔼_x f x · T_ρ g x` holds
for all positive `f` and `g` if and only if `‖g‖_{1 + s} ≤ ‖T_ρ g‖_{1 + 1 / r}` holds for all
positive `g`. The exponents `1 + r` and `1 + 1 / r` are Hölder conjugates, and the proof is the
reverse Hölder inequality with its equality case [O'Donnell, Exercise 10.6(b)][ODonnell2014]. -/
theorem le_expect_mul_noiseOp_iff_lpNorm_le_lpNorm_noiseOp {r s ρ : ℝ} (hr : r < 0)
    (hr1 : r ≠ -1) (hρ : -1 ≤ ρ) (hρ' : ρ ≤ 1) :
    (∀ f g : (ι → Bool) → ℝ, (∀ x, 0 < f x) → (∀ x, 0 < g x) →
      lpNorm (1 + r) f * lpNorm (1 + s) g ≤ 𝔼 x, f x * noiseOp ρ g x) ↔
    ∀ g : (ι → Bool) → ℝ, (∀ x, 0 < g x) →
      lpNorm (1 + s) g ≤ lpNorm (1 + r⁻¹) (noiseOp ρ g) := by
  have hr0 : r ≠ 0 := hr.ne
  have hq0 : 1 + r⁻¹ ≠ 0 := by
    intro h
    apply hr1
    field_simp at h
    linarith
  have hq1 : 1 + r⁻¹ ≠ 1 := by simpa using hr.ne
  have hconj : (1 + r⁻¹) / (1 + r⁻¹ - 1) = 1 + r := by
    rw [add_sub_cancel_left]
    field_simp
    ring
  have hconj' : (1 + r) / (1 + r - 1) = 1 + r⁻¹ := by
    rw [add_sub_cancel_left]
    field_simp
    ring
  constructor
  · intro h g hg
    -- test against `h = (T_ρ g) ^ (1 / r)`, the equality case of the reverse Hölder inequality
    have hT := noiseOp_pos hρ hρ' hg
    have heq := expect_mul_rpow_sub_one hq0 hq1 hT
    rw [hconj, add_sub_cancel_left] at heq
    have key := h (fun x => noiseOp ρ g x ^ r⁻¹) g (fun x => Real.rpow_pos_of_pos (hT x) _) hg
    simp only [mul_comm (_ ^ r⁻¹), heq] at key
    rw [mul_comm (lpNorm (1 + r⁻¹) _)] at key
    exact le_of_mul_le_mul_left key (lpNorm_pos _ fun x => Real.rpow_pos_of_pos (hT x) _)
  · intro h f g hf hg
    have hT := noiseOp_pos hρ hρ' hg
    have hH := lpNorm_mul_lpNorm_le_expect_mul (p := 1 + r)
      (by intro h; apply hr1; linarith)
      (by linarith) hf hT
    rw [hconj'] at hH
    exact (mul_le_mul_of_nonneg_left (h g hg) (lpNorm_nonneg _ _)).trans hH

/-- **The Reverse Two-Function Hypercontractivity Theorem for `r < -1`**: for `r < -1` and
`-1 < s ≤ 0` with `r s ≤ 1`, `0 ≤ ρ ≤ √(r s)`, positive `f` and nonnegative `g`,
`‖f‖_{1 + r} ‖g‖_{1 + s} ≤ 𝔼_x f x · T_ρ g x` [O'Donnell, Exercise 10.6][ODonnell2014]. On one
bit it is the reverse two-point inequality `‖g‖_{1 + s} ≤ ‖T_ρ g‖_{1 + 1 / r}` for the exponents
`0 < 1 + 1 / r ≤ 1 + s ≤ 1` (`BitString.lpNorm_le_lpNorm_noiseOp_of_unit`) followed by the reverse
Hölder inequality, and it tensorizes by `BitString.le_expect_mul_noiseOp_of_unit_of_pos`. The case
`s < -1 < r` is `BitString.lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_neg_one_lt_of_lt_neg_one`.
-/
theorem lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_lt_neg_one {r s ρ : ℝ} (hr : r < -1)
    (hs : -1 < s) (hs' : s ≤ 0) (hrs : r * s ≤ 1) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ √(r * s))
    {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 < f x) (hg : ∀ x, 0 ≤ g x) :
    lpNorm (1 + r) f * lpNorm (1 + s) g ≤ 𝔼 x, f x * noiseOp ρ g x := by
  have hr0 : r ≠ 0 := by intro h; linarith
  have hρ1 : ρ ≤ 1 := hρ'.trans (Real.sqrt_le_one.2 hrs)
  -- the exponents `q = 1 + 1 / r ≤ p = 1 + s` of the one-function form
  have hq0 : 0 < 1 + r⁻¹ := by
    rw [show 1 + r⁻¹ = (1 + r) / r by field_simp; ring]
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  have hqp : 1 + r⁻¹ ≤ 1 + s := by
    have h : r⁻¹ - s = (1 - r * s) / r := by field_simp
    linarith [div_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hrs) (by linarith : r ≤ 0)]
  have hρs : ρ ≤ √((1 - (1 + s)) / (1 - (1 + r⁻¹))) := by
    rwa [show (1 - (1 + s)) / (1 - (1 + r⁻¹)) = r * s by field_simp; ring]
  have hconj : (1 + r) / (1 + r - 1) = 1 + r⁻¹ := by
    rw [add_sub_cancel_left]
    field_simp
    ring
  refine le_expect_mul_noiseOp_of_unit_of_pos (by linarith) (by linarith) hρ hρ1
    (fun f g hf hg => ?_) hf hg
  have h1 := lpNorm_le_lpNorm_noiseOp_of_unit hq0 hqp (by linarith) hρ hρs hg
  have h2 := lpNorm_mul_lpNorm_le_expect_mul_of_neg (p := 1 + r) (by linarith) hf
    (noiseOp_nonneg (by linarith) hρ1 hg)
  rw [hconj] at h2
  exact (mul_le_mul_of_nonneg_left h1 (lpNorm_nonneg _ _)).trans h2

/-- **The Reverse Two-Function Hypercontractivity Theorem for `s < -1`**: for `-1 < r ≤ 0` and
`s < -1` with `r s ≤ 1`, `0 ≤ ρ ≤ √(r s)`, nonnegative `f` and positive `g`,
`‖f‖_{1 + r} ‖g‖_{1 + s} ≤ 𝔼_x f x · T_ρ g x` [O'Donnell, Exercise 10.6][ODonnell2014]. This is
`BitString.lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_lt_neg_one` with `f` and `g` exchanged,
since `T_ρ` is self-adjoint (`BitString.expect_mul_noiseOp_comm`). -/
theorem lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_neg_one_lt_of_lt_neg_one {r s ρ : ℝ}
    (hr : -1 < r) (hr' : r ≤ 0) (hs : s < -1) (hrs : r * s ≤ 1) (hρ : 0 ≤ ρ)
    (hρ' : ρ ≤ √(r * s)) {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 < g x) :
    lpNorm (1 + r) f * lpNorm (1 + s) g ≤ 𝔼 x, f x * noiseOp ρ g x := by
  rw [expect_mul_noiseOp_comm, mul_comm (lpNorm _ f)]
  simp only [mul_comm (noiseOp ρ f _)]
  rw [mul_comm r s] at hrs hρ'
  exact lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_lt_neg_one hs hr hr' hrs hρ hρ' hg hf

/-- **The Reverse Hypercontractivity Theorem for positive `p`**: for `q < p` with `q ≠ 0` and
`0 < p ≤ 1`, `0 ≤ ρ ≤ √((1 - p) / (1 - q))` and nonnegative `f`, `‖f‖_p ≤ ‖T_ρ f‖_q`. This is the
theorem of [O'Donnell, Exercise 10.6][ODonnell2014] in the cases of Exercise 10.7(a), (b), (e),
proved via Exercise 10.6(b):
the two-function theorem with `r = 1 / (q - 1)` and `s = p - 1` is tested against
`(T_ρ f) ^ (q - 1)`. Here `r` lies in `(-1, 0)` when `q < 0` and below `-1` when `0 < q`. -/
theorem lpNorm_le_lpNorm_noiseOp {p q ρ : ℝ} (hq : q ≠ 0) (hqp : q < p) (hp : 0 < p)
    (hp' : p ≤ 1) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ √((1 - p) / (1 - q))) {f : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    lpNorm p f ≤ lpNorm q (noiseOp ρ f) := by
  by_cases h0 : ∀ x, f x = 0
  · have hf0 : lpNorm p f = 0 := by
      simp [lpNorm, h0, Real.zero_rpow hp.ne', Real.zero_rpow (inv_ne_zero hp.ne')]
    exact hf0 ▸ lpNorm_nonneg _ _
  push Not at h0
  obtain ⟨y, hy⟩ := h0
  have hq1 : q - 1 < 0 := by linarith
  have hq1' : q - 1 ≠ 0 := hq1.ne
  have hq1'' : 1 - q ≠ 0 := by intro h; linarith
  have hr : (q - 1)⁻¹ < 0 := inv_lt_zero.2 hq1
  have hσ1 : (1 - p) / (1 - q) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hρ1 : ρ < 1 := hρ'.trans_lt ((Real.sqrt_lt' one_pos).2 (by rwa [one_pow]))
  -- `T_ρ f` is positive, and `h = (T_ρ f) ^ (q - 1)` is the extremal function for it
  have hT := noiseOp_pos_of_nonneg (by linarith) hρ1 hf ((hf y).lt_of_ne' hy)
  have hh := lpNorm_pos (1 + (q - 1)⁻¹) fun x => Real.rpow_pos_of_pos (hT x) (q - 1)
  have heq := expect_mul_rpow_sub_one hq (by linarith : q ≠ 1) hT
  rw [show q / (q - 1) = 1 + (q - 1)⁻¹ by field_simp; ring] at heq
  have hrs : (q - 1)⁻¹ * (p - 1) = (1 - p) / (1 - q) := by field_simp; ring
  have key : lpNorm (1 + (q - 1)⁻¹) (fun x => noiseOp ρ f x ^ (q - 1)) * lpNorm (1 + (p - 1)) f ≤
      𝔼 x, noiseOp ρ f x ^ (q - 1) * noiseOp ρ f x := by
    rcases hq.lt_or_gt with hq0 | hq0
    · exact lpNorm_mul_lpNorm_le_expect_mul_noiseOp (r := (q - 1)⁻¹) (s := p - 1)
        (by rw [lt_inv_of_neg (by norm_num) hq1]; linarith) hr.le (by linarith) (by linarith) hρ
        (by rwa [hrs]) (fun x => (Real.rpow_pos_of_pos (hT x) (q - 1)).le) hf
    · refine lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_lt_neg_one (r := (q - 1)⁻¹) (s := p - 1)
        ?_ (by linarith) (by linarith) (by rw [hrs]; exact hσ1.le) hρ (by rwa [hrs])
        (fun x => Real.rpow_pos_of_pos (hT x) (q - 1)) hf
      rw [inv_lt_of_neg hq1 (by norm_num)]
      linarith
  simp only [mul_comm (_ ^ (q - 1)), heq, add_sub_cancel] at key
  rw [mul_comm (lpNorm q _)] at key
  exact le_of_mul_le_mul_left key hh

/-- **The Reverse Hypercontractivity Theorem for negative `p`**: for `q < p < 0`,
`0 ≤ ρ ≤ √((1 - p) / (1 - q))` and positive `f`, `‖f‖_p ≤ ‖T_ρ f‖_q`: the theorem of
[O'Donnell, Exercise 10.6][ODonnell2014] in the cases of Exercise 10.7(d). By the equivalence of
the two forms (Exercise 10.6(b)) it is the two-function theorem for
`1 + r = q / (q - 1) ∈ (0, 1)` and `1 + s = p < 0`, which is
`BitString.lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_neg_one_lt_of_lt_neg_one`: the duality of the
exercise, through the reverse Hölder inequality. -/
theorem lpNorm_le_lpNorm_noiseOp_of_neg {p q ρ : ℝ} (hqp : q < p) (hp : p < 0) (hρ : 0 ≤ ρ)
    (hρ' : ρ ≤ √((1 - p) / (1 - q))) {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 < f x) :
    lpNorm p f ≤ lpNorm q (noiseOp ρ f) := by
  have hq1 : q - 1 < 0 := by linarith
  have hq1' : q - 1 ≠ 0 := hq1.ne
  have hq1'' : 1 - q ≠ 0 := by intro h; linarith
  have hr : (q - 1)⁻¹ < 0 := inv_lt_zero.2 hq1
  have hr' : -1 < (q - 1)⁻¹ := by
    rw [lt_inv_of_neg (by norm_num) hq1]
    linarith
  have hσ1 : (1 - p) / (1 - q) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  have hρ1 : ρ ≤ 1 := hρ'.trans (Real.sqrt_le_one.2 hσ1)
  have hrs : (p - 1) * (q - 1)⁻¹ = (1 - p) / (1 - q) := by field_simp; ring
  have h := (le_expect_mul_noiseOp_iff_lpNorm_le_lpNorm_noiseOp (ι := ι) (s := p - 1) hr
    hr'.ne' (by linarith) hρ1).1 (fun f g hf hg => ?_) f hf
  · rwa [add_sub_cancel, inv_inv, add_sub_cancel] at h
  have hsr : (q - 1)⁻¹ * (p - 1) = (1 - p) / (1 - q) := by rw [mul_comm, hrs]
  exact lpNorm_mul_lpNorm_le_expect_mul_noiseOp_of_neg_one_lt_of_lt_neg_one hr' hr.le
    (by linarith) (by rw [hsr]; exact hσ1) hρ (by rwa [hsr]) (fun x => (hf x).le) hg

/-! ### Reverse small-set expansion -/

/-- If `A` has volume `1`, the probability that `x ∈ A` and `y ∈ B` for a `ρ`-correlated pair
`(x, y)` is the volume of `B`. -/
private theorem expect_indicator_mul_noiseOp_of_expect_eq_one {A : Set (ι → Bool)}
    (hA : 𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x = 1) (ρ : ℝ) (B : Set (ι → Bool)) :
    𝔼 x, A.indicator 1 x * noiseOp ρ (B.indicator 1) x =
      𝔼 x, B.indicator (1 : (ι → Bool) → ℝ) x := by
  have h0 : 𝔼 x, (1 - A.indicator (1 : (ι → Bool) → ℝ) x) = 0 := by
    rw [expect_sub_distrib, Fintype.expect_const, hA, sub_self]
  have h1 : (fun x => 1 - A.indicator (1 : (ι → Bool) → ℝ) x) = 0 :=
    (Fintype.expect_eq_zero_iff_of_nonneg fun x =>
      sub_nonneg.2 (Set.indicator_le_self' (fun _ _ => zero_le_one) x)).1 h0
  have hA1 (x : ι → Bool) : A.indicator (1 : (ι → Bool) → ℝ) x = 1 := by
    linarith [congrFun h1 x, Pi.zero_apply (M := fun _ : ι → Bool => ℝ) x]
  simp only [hA1, one_mul]
  have h := expect_mul_noiseOp_comm ρ (fun _ => (1 : ℝ)) (B.indicator 1)
  simpa only [one_mul, noiseOp_const] using h

/-- **The Reverse Small-Set Expansion Theorem**: let `0 ≤ ρ < 1`, and let `A` and `B` have volumes
`exp (-a ^ 2 / 2)` and `exp (-b ^ 2 / 2)` with `a, b ≥ 0`. Then the probability that `x ∈ A` and
`y ∈ B` for a `ρ`-correlated pair `(x, y)`, which is `𝔼_x 1_A x · T_ρ 1_B x`, is at least
`exp (-(a ^ 2 + 2 ρ a b + b ^ 2) / (2 (1 - ρ ^ 2)))`
[O'Donnell, Remark 10.3 and Exercise 10.9][ODonnell2014]. -/
theorem exp_le_expect_indicator_mul_noiseOp_indicator {ρ a b : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) {A B : Set (ι → Bool)}
    (hA : 𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x = Real.exp (-(a ^ 2 / 2)))
    (hB : 𝔼 x, B.indicator (1 : (ι → Bool) → ℝ) x = Real.exp (-(b ^ 2 / 2))) :
    Real.exp (-((a ^ 2 + 2 * ρ * a * b + b ^ 2) / (2 * (1 - ρ ^ 2)))) ≤
      𝔼 x, A.indicator 1 x * noiseOp ρ (B.indicator 1) x := by
  have hd : 0 < 1 - ρ ^ 2 := by nlinarith
  -- when one volume is `1`, the probability is the other volume
  have hle (c : ℝ) : Real.exp (-(c ^ 2 / (2 * (1 - ρ ^ 2)))) ≤ Real.exp (-(c ^ 2 / 2)) :=
    Real.exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg c) (by positivity)
      (by nlinarith)))
  rcases ha.eq_or_lt with rfl | ha0
  · rw [expect_indicator_mul_noiseOp_of_expect_eq_one (by rw [hA]; simp) ρ B, hB]
    simpa using hle b
  rcases hb.eq_or_lt with rfl | hb0
  · rw [expect_mul_noiseOp_comm]
    simp only [mul_comm (noiseOp ρ _ _)]
    rw [expect_indicator_mul_noiseOp_of_expect_eq_one (by rw [hB]; simp) ρ A, hA]
    simpa using hle a
  -- the exponents `p = 1 + r` and `q = 1 + s` of Exercise 10.9
  set p := a * (1 - ρ ^ 2) / (a + ρ * b) with hp
  set q := b * (1 - ρ ^ 2) / (ρ * a + b) with hq
  have hab : 0 < a + ρ * b := by positivity
  have hba : 0 < ρ * a + b := by positivity
  have hp0 : 0 < p := by positivity
  have hq0 : 0 < q := by positivity
  have hp1 : p ≤ 1 := (div_le_one hab).2 (by nlinarith [mul_nonneg hρ hb])
  have hq1 : q ≤ 1 := (div_le_one hba).2 (by nlinarith [mul_nonneg hρ ha])
  have hpq : (p - 1) * (q - 1) = ρ ^ 2 := by
    rw [hp, hq]
    field_simp
    ring
  have h := lpNorm_mul_lpNorm_le_expect_mul_noiseOp (r := p - 1) (s := q - 1) (by linarith)
    (by linarith) (by linarith) (by linarith) hρ (by rw [hpq, Real.sqrt_sq hρ])
    (f := A.indicator 1) (g := B.indicator 1) (Set.indicator_nonneg fun _ _ => zero_le_one)
    (Set.indicator_nonneg fun _ _ => zero_le_one)
  rw [add_sub_cancel, add_sub_cancel, lpNorm_indicator_one hp0.ne', lpNorm_indicator_one hq0.ne',
    hA, hB, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add] at h
  convert h using 2
  rw [hp, hq]
  field_simp
  ring

end Cslib.BitString
