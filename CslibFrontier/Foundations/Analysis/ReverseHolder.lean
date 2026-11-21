/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.LpNorm
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.MeanInequalities

/-!
# The reverse Hölder inequality on finite types

For an exponent `p < 1` with `p ≠ 0` (the exponent `0` is excluded because `Cslib.lpNorm 0` is
`1`, not the geometric mean), write `p' = p / (p - 1)` for its Hölder conjugate, which
is again below `1`: it lies in `(0, 1)` when `p < 0` and below `0` when `0 < p < 1`. For positive
functions `f` and `g` on a finite type with the uniform distribution, the **reverse Hölder
inequality** `‖f‖_p ‖g‖_{p'} ≤ 𝔼_x f x g x` holds (`Cslib.lpNorm_mul_lpNorm_le_expect_mul`),
where `‖f‖_p = (𝔼_x f x ^ p) ^ (1 / p)` is `Cslib.lpNorm` also for negative `p`. Equality holds
for `g = f ^ (p - 1)` (`Cslib.expect_mul_rpow_sub_one`), so `‖f‖_p` is the least value of
`𝔼_x f x g x` over positive `g` with `‖g‖_{p'} = 1` (`Cslib.isLeast_expect_mul`)
[O'Donnell, Exercise 10.6][ODonnell2014].

For `0 < p < 1` the inequality is the weighted Hölder inequality
(`Real.compact_inner_le_weight_mul_Lp_of_nonneg`) with exponent `1 / p`, weights `g ^ p'` and
values `f ^ p g ^ (-p')`; the case `p < 0` follows by exchanging `f` and `g`. Only the function
with the exponent in `(0, 1)` enters through nonnegative powers, so it may vanish somewhere:
nonnegative `f` and positive `g` suffice for `0 < p < 1`
(`Cslib.lpNorm_mul_lpNorm_le_expect_mul_of_pos`), and positive `f` and nonnegative `g` for
`p < 0` (`Cslib.lpNorm_mul_lpNorm_le_expect_mul_of_neg`).

## Main results

* `Cslib.lpNorm_mul_lpNorm_le_expect_mul`: the reverse Hölder inequality.
* `Cslib.lpNorm_mul_lpNorm_le_expect_mul_of_pos`, `Cslib.lpNorm_mul_lpNorm_le_expect_mul_of_neg`:
  the same for `0 < p < 1` and for `p < 0`, where the function whose exponent lies in `(0, 1)`
  need only be nonnegative.
* `Cslib.expect_mul_rpow_sub_one`: its equality case.
* `Cslib.isLeast_expect_mul`: `‖f‖_p` as a minimum of `𝔼_x f x g x`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib

open Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] [Nonempty α]

/-- **The reverse Hölder inequality for `0 < p < 1`**: for nonnegative `f` and positive `g` on a
finite type, `‖f‖_p ‖g‖_{p / (p - 1)} ≤ 𝔼_x f x g x`; here `p / (p - 1) < 0`, and `f`, whose
exponent is `p`, may vanish somewhere [O'Donnell, Exercise 10.6][ODonnell2014]. -/
theorem lpNorm_mul_lpNorm_le_expect_mul_of_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f g : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 < g x) :
    lpNorm p f * lpNorm (p / (p - 1)) g ≤ 𝔼 x, f x * g x := by
  have hp1' : p - 1 ≠ 0 := (by linarith : p - 1 < 0).ne
  set p' := p / (p - 1) with hp'
  have hexp : p' + -p' * p⁻¹ = 1 := by rw [hp']; field_simp; ring
  have e1 (x : α) : g x ^ p' * (f x ^ p * g x ^ (-p')) = f x ^ p := by
    rw [mul_left_comm, ← Real.rpow_add (hg x), add_neg_cancel, Real.rpow_zero, mul_one]
  have e2 (x : α) : g x ^ p' * (f x ^ p * g x ^ (-p')) ^ p⁻¹ = f x * g x := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hf x) _) (Real.rpow_nonneg (hg x).le _),
      ← Real.rpow_mul (hf x), ← Real.rpow_mul (hg x).le, mul_inv_cancel₀ hp.ne',
      Real.rpow_one, mul_left_comm, ← Real.rpow_add (hg x), hexp, Real.rpow_one]
  have key := Real.compact_inner_le_weight_mul_Lp_of_nonneg univ (p := p⁻¹)
    (one_le_inv₀ hp |>.2 hp1.le) (w := fun x => g x ^ p') (f := fun x => f x ^ p * g x ^ (-p'))
    (fun x => (Real.rpow_pos_of_pos (hg x) _).le)
    (fun x => mul_nonneg (Real.rpow_nonneg (hf x) _) (Real.rpow_nonneg (hg x).le _))
  simp only [e1, e2, inv_inv] at key
  set A := 𝔼 x, f x ^ p
  set B := 𝔼 x, g x ^ p'
  set C := 𝔼 x, f x * g x
  have hB : 0 < B := expect_pos (fun x _ => Real.rpow_pos_of_pos (hg x) _) univ_nonempty
  have hC : 0 ≤ C := expect_nonneg fun x _ => mul_nonneg (hf x) (hg x).le
  have hA : 0 ≤ A := expect_nonneg fun x _ => Real.rpow_nonneg (hf x) _
  rw [lpNorm_of_nonneg p hf, lpNorm_of_nonneg p' fun x => (hg x).le]
  calc A ^ p⁻¹ * B ^ p'⁻¹ ≤ (B ^ (1 - p) * C ^ p) ^ p⁻¹ * B ^ p'⁻¹ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hA key (inv_nonneg.2 hp.le))
          (Real.rpow_nonneg hB.le _)
    _ = C * B ^ ((1 - p) * p⁻¹ + p'⁻¹) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hB.le _) (Real.rpow_nonneg hC _),
          ← Real.rpow_mul hB.le, ← Real.rpow_mul hC, mul_inv_cancel₀ hp.ne', Real.rpow_one,
          Real.rpow_add hB]
        ring
    _ = C := by
        rw [show (1 - p) * p⁻¹ + p'⁻¹ = 0 by rw [hp']; field_simp; ring, Real.rpow_zero,
          mul_one]

/-- **The reverse Hölder inequality for `p < 0`**: for positive `f` and nonnegative `g` on a
finite type, `‖f‖_p ‖g‖_{p / (p - 1)} ≤ 𝔼_x f x g x`; here `p / (p - 1)` lies in `(0, 1)`, so `g`
may vanish somewhere [O'Donnell, Exercise 10.6][ODonnell2014]. -/
theorem lpNorm_mul_lpNorm_le_expect_mul_of_neg {p : ℝ} (hp : p < 0) {f g : α → ℝ}
    (hf : ∀ x, 0 < f x) (hg : ∀ x, 0 ≤ g x) :
    lpNorm p f * lpNorm (p / (p - 1)) g ≤ 𝔼 x, f x * g x := by
  -- exchange the roles: `p / (p - 1)` lies in `(0, 1)` and its conjugate is `p`
  have h0 : 0 < p / (p - 1) := div_pos_of_neg_of_neg hp (by linarith)
  have h1 : p / (p - 1) < 1 := (div_lt_one_of_neg (by linarith)).2 (by linarith)
  have hp1' : p - 1 ≠ 0 := (by linarith : p - 1 < 0).ne
  have h := lpNorm_mul_lpNorm_le_expect_mul_of_pos h0 h1 hg hf
  rw [show p / (p - 1) / (p / (p - 1) - 1) = p by
    rw [div_sub_one hp1']; field_simp; ring] at h
  simpa only [mul_comm] using h

/-- **The reverse Hölder inequality**: for `p < 1` with `p ≠ 0` and positive functions `f` and `g`
on a finite type, `‖f‖_p ‖g‖_{p / (p - 1)} ≤ 𝔼_x f x g x`
[O'Donnell, Exercise 10.6][ODonnell2014]. -/
theorem lpNorm_mul_lpNorm_le_expect_mul {p : ℝ} (hp : p ≠ 0) (hp1 : p < 1) {f g : α → ℝ}
    (hf : ∀ x, 0 < f x) (hg : ∀ x, 0 < g x) :
    lpNorm p f * lpNorm (p / (p - 1)) g ≤ 𝔼 x, f x * g x := by
  rcases hp.lt_or_gt with hp | hp
  · exact lpNorm_mul_lpNorm_le_expect_mul_of_neg hp hf fun x => (hg x).le
  · exact lpNorm_mul_lpNorm_le_expect_mul_of_pos hp hp1 (fun x => (hf x).le) hg

/-- **Equality in the reverse Hölder inequality**: for `p ≠ 0, 1` and positive `f`,
`𝔼_x f x · f x ^ (p - 1) = ‖f‖_p ‖f ^ (p - 1)‖_{p / (p - 1)}`. -/
theorem expect_mul_rpow_sub_one {p : ℝ} (hp : p ≠ 0) (hp1 : p ≠ 1) {f : α → ℝ}
    (hf : ∀ x, 0 < f x) :
    𝔼 x, f x * f x ^ (p - 1) = lpNorm p f * lpNorm (p / (p - 1)) fun x => f x ^ (p - 1) := by
  have hp1' : p - 1 ≠ 0 := sub_ne_zero.2 hp1
  have e1 (x : α) : f x * f x ^ (p - 1) = f x ^ p := by
    rw [mul_comm, ← Real.rpow_add_one (hf x).ne', sub_add_cancel]
  have e2 (x : α) : (f x ^ (p - 1)) ^ (p / (p - 1)) = f x ^ p := by
    rw [← Real.rpow_mul (hf x).le, mul_div_cancel₀ _ hp1']
  have hA : 0 < 𝔼 x, f x ^ p :=
    expect_pos (fun x _ => Real.rpow_pos_of_pos (hf x) _) univ_nonempty
  rw [lpNorm_of_nonneg p fun x => (hf x).le,
    lpNorm_of_nonneg _ fun x => (Real.rpow_pos_of_pos (hf x) _).le]
  simp only [e1, e2]
  rw [← Real.rpow_add hA, show p⁻¹ + (p / (p - 1))⁻¹ = 1 by field_simp; ring, Real.rpow_one]

/-- **`‖f‖_p` as a minimum**: for `p < 1` with `p ≠ 0` and positive `f`, `‖f‖_p` is the least
value of `𝔼_x f x g x` over positive `g` with `‖g‖_{p / (p - 1)} = 1`
[O'Donnell, Exercise 10.6][ODonnell2014]. -/
theorem isLeast_expect_mul {p : ℝ} (hp : p ≠ 0) (hp1 : p < 1) {f : α → ℝ} (hf : ∀ x, 0 < f x) :
    IsLeast {c | ∃ g : α → ℝ, (∀ x, 0 < g x) ∧ lpNorm (p / (p - 1)) g = 1 ∧
      c = 𝔼 x, f x * g x} (lpNorm p f) := by
  have hq : p / (p - 1) ≠ 0 := div_ne_zero hp (sub_ne_zero.2 hp1.ne)
  set h : α → ℝ := fun x => f x ^ (p - 1)
  have hh (x : α) : 0 < h x := Real.rpow_pos_of_pos (hf x) _
  have hN := lpNorm_pos (p / (p - 1)) hh
  refine ⟨⟨fun x => (lpNorm (p / (p - 1)) h)⁻¹ * h x, fun x => mul_pos (inv_pos.2 hN) (hh x),
    ?_, ?_⟩, ?_⟩
  · rw [lpNorm_const_mul hq, abs_of_nonneg (inv_nonneg.2 hN.le), inv_mul_cancel₀ hN.ne']
  · simp only [mul_left_comm (f _), ← mul_expect, expect_mul_rpow_sub_one hp hp1.ne hf, h]
    exact (inv_mul_cancel_right₀ hN.ne' _).symm.trans (by ring)
  · rintro c ⟨g, hg, hg1, rfl⟩
    simpa only [hg1, mul_one] using lpNorm_mul_lpNorm_le_expect_mul hp hp1 hf hg

end Cslib
