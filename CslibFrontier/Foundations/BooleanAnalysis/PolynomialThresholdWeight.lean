/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import CslibFrontier.Foundations.BooleanAnalysis.PolynomialThreshold
public import Mathlib.Analysis.Complex.Exponential
import CslibFrontier.Foundations.BooleanAnalysis.KhintchineKahane
import CslibFrontier.Foundations.BooleanAnalysis.LowDegreeMoments
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# The low-degree Fourier weight of polynomial threshold functions

A polynomial threshold function `f` of degree at most `k` (`BitString.IsPTF k f`) has Fourier
weight `W^{≤k}[f] = ∑_{|S| ≤ k} f̂(S) ^ 2 ≥ e ^ (-2 k)` on the levels up to `k`
(`BitString.IsPTF.exp_neg_two_mul_le_sum_fourierCoeff_sq`): this is the **Gotsman–Linial
Theorem** [GotsmanLinial1994] [O'Donnell, Theorem 5.9][ODonnell2014].

Following O'Donnell, write `f = sgn p` with `p` of degree at most `k`. Then
`‖p‖_1 = 𝔼 f p = ∑_{|S| ≤ k} f̂(S) p̂(S) ≤ √(W^{≤k}[f]) ‖p‖_2` by Plancherel's identity and
Cauchy–Schwarz (`BitString.sq_expect_abs_le_sum_fourierCoeff_sq_mul`), and `‖p‖_2 ≤ e ^ k ‖p‖_1`
by the `L^1`–`L^2` comparison for low-degree functions
(`BitString.lpNorm_two_le_exp_mul_lpNorm_one`, [O'Donnell, Theorem 9.22][ODonnell2014]). The bound
`e ^ (-2 k)` cannot be improved beyond `2 ^ (1 - k)` [O'Donnell, Exercise 5.11][ODonnell2014].

For linear threshold functions, `k = 1`, the Khintchine–Kahane inequality `‖p‖_2 ≤ √2 ‖p‖_1`
(`BitString.expect_sq_le_two_mul_expect_abs_sq_of_mem_lowDegree_one`, in
`CslibFrontier.Foundations.BooleanAnalysis.KhintchineKahane`) replaces `e` by `√2`: every linear
threshold function has `W^{≤1}[f] ≥ 1/2` [O'Donnell, Theorem 5.2][ODonnell2014]. The theorem
(`BitString.one_half_le_sum_fourierCoeff_sq_of_nonneg_mul`) takes `f = sgn ℓ` in the form
`0 ≤ f(x) ℓ(x)` for a nonzero `ℓ` of degree at most one, so `ℓ` may vanish on the cube and `f`
may take either value there; `BitString.IsPTF.one_half_le_sum_fourierCoeff_sq` is the case
`IsPTF 1 f`.

## Main results

* `Cslib.BitString.sq_expect_abs_le_sum_fourierCoeff_sq_mul`: the Cauchy–Schwarz step,
  `(𝔼 |p|) ^ 2 ≤ W^T[f] 𝔼 p ^ 2` when `f = sgn p` and `p` is supported on `T`.
* `Cslib.BitString.IsPTF.exp_neg_two_mul_le_sum_fourierCoeff_sq`: the Gotsman–Linial Theorem.
* `Cslib.BitString.one_half_le_sum_fourierCoeff_sq_of_nonneg_mul`,
  `Cslib.BitString.IsPTF.one_half_le_sum_fourierCoeff_sq`: Theorem 5.2, `W^{≤1}[f] ≥ 1/2` for a
  linear threshold function `f`.

## References

* [C. Gotsman, N. Linial, *Spectral properties of threshold functions*][GotsmanLinial1994]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Cauchy–Schwarz step for threshold functions**: if `f`, read as signs, agrees in sign
with `p` and the Fourier coefficients of `p` vanish outside `T`, then
`(𝔼 |p|) ^ 2 ≤ (∑_{S ∈ T} f̂(S) ^ 2) 𝔼 p ^ 2`, since `𝔼 |p| = 𝔼 f p = ∑_{S ∈ T} f̂(S) p̂(S)` by
Plancherel's identity [O'Donnell, proofs of Theorems 5.2 and 5.9][ODonnell2014]. -/
theorem sq_expect_abs_le_sum_fourierCoeff_sq_mul {T : Finset (Finset ι)} {f : (ι → Bool) → Bool}
    {p : (ι → Bool) → ℝ} (hpT : ∀ S ∉ T, fourierCoeff p S = 0)
    (hp : ∀ x, 0 ≤ signVal (f x) * p x) :
    (𝔼 x, |p x|) ^ 2 ≤ (∑ S ∈ T, fourierCoeff (fun x => signVal (f x)) S ^ 2) * 𝔼 x, p x ^ 2 := by
  have hinner : 𝔼 x, |p x| = ∑ S ∈ T, fourierCoeff (fun x => signVal (f x)) S * fourierCoeff p S :=
    (expect_congr rfl fun x _ => (signVal_mul_eq_abs hp x).symm).trans
      (expect_mul_eq_sum_of_fourierCoeff_eq_zero hpT _)
  have hpm : 𝔼 x, p x ^ 2 = ∑ S ∈ T, fourierCoeff p S ^ 2 := by
    simpa only [sq] using expect_mul_eq_sum_of_fourierCoeff_eq_zero hpT p
  rw [hinner, hpm]
  exact sum_mul_sq_le_sq_mul_sq T _ _

/-- **The Gotsman–Linial Theorem**: a polynomial threshold function `f` of degree at most `k`,
read as signs, has Fourier weight at least `e ^ (-2 k)` on the sets of at most `k` coordinates
[GotsmanLinial1994] [O'Donnell, Theorem 5.9][ODonnell2014]. -/
theorem IsPTF.exp_neg_two_mul_le_sum_fourierCoeff_sq {k : ℕ} {f : (ι → Bool) → Bool}
    (hf : IsPTF k f) :
    Real.exp (-(2 * k)) ≤ ∑ S with #S ≤ k, fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
  obtain ⟨p, hpT, hpos⟩ := hf
  have hpdeg (S : Finset ι) (hS : k < #S) : fourierCoeff p S = 0 :=
    hpT S fun h => (mem_filter.1 h).2.not_gt hS
  -- Theorem 9.22 with `p = 1` turns `(𝔼 |p|) ^ 2 ≤ W m` into `e ^ (-2 k) ≤ W`
  exact exp_neg_two_mul_le_of_sq_expect_abs_le (mem_lowDegree_iff_fourierCoeff_eq_zero.2 hpdeg)
    (Fintype.expect_sq_pos fun h => (hpos 0).ne' (by rw [h, Pi.zero_apply, mul_zero]))
    (sq_expect_abs_le_sum_fourierCoeff_sq_mul hpT fun x => (hpos x).le)

/-- **Linear threshold functions have Fourier weight at least `1/2` up to level one**
[O'Donnell, Theorem 5.2][ODonnell2014]: if `f`, read as signs, agrees in sign with a nonzero real
function `ℓ` of degree at most one (`0 ≤ f(x) ℓ(x)` for every `x`, so `f = sgn ℓ` wherever
`ℓ ≠ 0`), then its Fourier weight on the sets of at most one coordinate is at least `1/2`.
By Cauchy–Schwarz `(𝔼 |ℓ|) ^ 2 ≤ W^{≤1}[f] 𝔼 ℓ ^ 2`, and `𝔼 ℓ ^ 2 ≤ 2 (𝔼 |ℓ|) ^ 2` by the
Khintchine–Kahane inequality (`expect_sq_le_two_mul_expect_abs_sq_of_mem_lowDegree_one`). The
assumption `ℓ ≠ 0` is needed: every `f` agrees in sign with `ℓ = 0`. -/
theorem one_half_le_sum_fourierCoeff_sq_of_nonneg_mul {f : (ι → Bool) → Bool}
    {ℓ : (ι → Bool) → ℝ} (hℓ : ℓ ∈ lowDegree ℝ ι 1) (hℓ0 : ℓ ≠ 0)
    (hf : ∀ x, 0 ≤ signVal (f x) * ℓ x) :
    1 / 2 ≤ ∑ S with #S ≤ 1, fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
  have hℓT (S : Finset ι) (hS : S ∉ ({S | #S ≤ 1} : Finset (Finset ι))) :
      fourierCoeff ℓ S = 0 :=
    mem_lowDegree_iff_fourierCoeff_eq_zero.1 hℓ S (by simpa using hS)
  have hcs := sq_expect_abs_le_sum_fourierCoeff_sq_mul hℓT hf
  have hKK := expect_sq_le_two_mul_expect_abs_sq_of_mem_lowDegree_one hℓ
  refine le_of_mul_le_mul_right (a := 𝔼 x, ℓ x ^ 2) ?_ (Fintype.expect_sq_pos hℓ0)
  linarith

/-- **Theorem 5.2 for `IsPTF 1`** [O'Donnell, Theorem 5.2][ODonnell2014]: the sign of a function of
degree at most one that vanishes nowhere has Fourier weight at least `1/2` up to level one. -/
theorem IsPTF.one_half_le_sum_fourierCoeff_sq {f : (ι → Bool) → Bool}
    (hf : IsPTF 1 f) :
    1 / 2 ≤ ∑ S with #S ≤ 1, fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
  obtain ⟨ℓ, hℓT, hpos⟩ := hf
  exact one_half_le_sum_fourierCoeff_sq_of_nonneg_mul
    (mem_lowDegree_iff_fourierCoeff_eq_zero.2 fun S hS => hℓT S fun h =>
      (mem_filter.1 h).2.not_gt hS)
    (fun h => (hpos 0).ne' (by rw [h, Pi.zero_apply, mul_zero])) fun x => (hpos x).le

end Cslib.BitString
