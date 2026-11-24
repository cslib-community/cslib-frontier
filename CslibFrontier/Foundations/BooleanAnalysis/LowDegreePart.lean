/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.LpNorm
public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
public import CslibFrontier.Foundations.BooleanAnalysis.Noise
import CslibFrontier.Foundations.BooleanAnalysis.Bonami

/-!
# The low-degree part and its `L^q` norms

The *low-degree part* of a real function `f` on the cube up to degree `k` is
`f^{≤k} = ∑_{|S| ≤ k} f̂(S) χ_S` (`BitString.lowDegreePart`), in the notation introduced after
[O'Donnell, Definition 1.19][ODonnell2014]. It keeps the Fourier coefficients on the sets of at
most `k` coordinates (`BitString.fourierCoeff_lowDegreePart`), has degree at most `k`
(`BitString.lowDegreePart_mem_lowDegree`), is the sum of the degree-`j` parts `f^{=j}` for
`j ≤ k` (`BitString.sum_range_levelPart`), is `f` itself once `k` is the number of coordinates
(`BitString.lowDegreePart_of_card_le`), and does not increase the `L²` norm
(`BitString.lpNorm_two_lowDegreePart_le`).

For `q ≥ 2`, the generalized Bonami Lemma `‖g‖_q ≤ √(q - 1) ^ k ‖g‖_2` for `g` of degree at most
`k` (`BitString.lpNorm_le_sqrt_pow_mul_lpNorm_two`, [O'Donnell, Theorem 9.21][ODonnell2014]) gives
`‖f^{≤k}‖_q ≤ √(q - 1) ^ k ‖f^{≤k}‖_2 ≤ √(q - 1) ^ k ‖f‖_2`
(`BitString.lpNorm_lowDegreePart_le_lpNorm_two`), and the monotonicity of `L^p` norms
(`Cslib.lpNorm_le_lpNorm_of_exponent_le`) then gives `‖f^{≤k}‖_q ≤ √(q - 1) ^ k ‖f‖_q`
(`BitString.lpNorm_lowDegreePart_le`): this is the case `q ≥ 2` of
[O'Donnell, Proposition 10.37][ODonnell2014], which is also
[O'Donnell, Exercise 9.8(a)][ODonnell2014].

For `0 < ρ ≤ 1`, the noise operator scales each coefficient of `f^{≤k}` by a factor at least
`ρ ^ k`, so `‖f^{≤k}‖_2 ≤ (1 / ρ) ^ k ‖T_ρ f‖_2` (`BitString.lpNorm_two_lowDegreePart_le_noiseOp`),
and the same chain gives `‖f^{≤k}‖_q ≤ (√(q - 1) / ρ) ^ k ‖T_ρ f‖_q` for every `q ≥ 2`
(`BitString.lpNorm_lowDegreePart_le_noiseOp`). [O'Donnell, Lemma 10.38][ODonnell2014] is its case
`q = 4`, `‖f^{≤k}‖_4 ≤ (√3 / ρ) ^ k ‖T_ρ f‖_4`.

For `1 < q ≤ 2`, the direct proof that [O'Donnell, Exercise 9.8(b)][ODonnell2014] suggests takes
`ρ = √(q - 1)` in the `L²` bound and applies the `(p, 2)`-Hypercontractivity Theorem at `p = q`,
`‖T_ρ f‖_2 ≤ ‖f‖_q` (`BitString.lpNorm_two_noiseOp_le`), giving
`‖f^{≤k}‖_2 ≤ (1 / √(q - 1)) ^ k ‖f‖_q` (`BitString.lpNorm_two_lowDegreePart_le_lpNorm`); as
`‖f^{≤k}‖_q ≤ ‖f^{≤k}‖_2`, this is the case `1 < q ≤ 2` of Proposition 10.37,
`‖f^{≤k}‖_q ≤ (1 / √(q - 1)) ^ k ‖f‖_q` (`BitString.lpNorm_lowDegreePart_le_of_le_two`).

## Main definitions

* `Cslib.BitString.lowDegreePart`: the low-degree part `f^{≤k}`.

## Main results

* `Cslib.BitString.fourierCoeff_lowDegreePart`, `Cslib.BitString.sum_range_levelPart`,
  `Cslib.BitString.lpNorm_two_lowDegreePart_le`: the coefficients of the low-degree part, its
  decomposition into degree-`j` parts, and its `L²` norm.
* `Cslib.BitString.lpNorm_lowDegreePart_le_lpNorm_two`, `Cslib.BitString.lpNorm_lowDegreePart_le`:
  Exercise 9.8(a) and Proposition 10.37 for `q ≥ 2`.
* `Cslib.BitString.lpNorm_two_lowDegreePart_le_lpNorm`,
  `Cslib.BitString.lpNorm_lowDegreePart_le_of_le_two`: Exercise 9.8(b) and Proposition 10.37 for
  `1 < q ≤ 2`.
* `Cslib.BitString.lpNorm_lowDegreePart_le_noiseOp`: Lemma 10.38, for every `q ≥ 2`.

## Usage

For `f : (ι → Bool) → ℝ`, `lowDegreePart k f` is `f^{≤k}`; rewrite its coefficients with the simp
lemma `fourierCoeff_lowDegreePart`, and pass `lowDegreePart_mem_lowDegree k f` to any result about
functions of degree at most `k`. `lpNorm_lowDegreePart_le hq k f` bounds `‖f^{≤k}‖_q` for
`hq : 2 ≤ q`, and `lpNorm_lowDegreePart_le_of_le_two hq hq2 k f` for `1 < q ≤ 2`; at `q = 4` the
factor `√(4 - 1) ^ k` normalizes to `√3 ^ k` by `norm_num`.
`lpNorm_lowDegreePart_le_noiseOp hq hρ hρ1 k f` compares with `T_ρ f` instead. The checked clients
in
[CslibFrontierTests/BooleanAnalysisLowDegreePart.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisLowDegreePart.lean)
compute the low-degree parts of a character and of the two-bit function `χ_{0} + χ_{0, 1}`,
compare `L¹` and `L²` norms, and instantiate Proposition 10.37 at `q = 4` and `q = 3 / 2` and
Lemma 10.38 at `q = 4`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The low-degree part `f^{≤k} = ∑_{|S| ≤ k} f̂(S) χ_S` of a real function on the cube. -/
@[expose] noncomputable def lowDegreePart (k : ℕ) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  ∑ S with #S ≤ k, fourierCoeff f S * chi ℝ S x

/-- The low-degree part as a combination of all the characters, with weight zero above
degree `k`. -/
private theorem lowDegreePart_eq_sum_ite (k : ℕ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    lowDegreePart k f x = ∑ S, (if #S ≤ k then fourierCoeff f S else 0) * chi ℝ S x := by
  simp only [lowDegreePart, sum_filter, ite_mul, zero_mul]

/-- The low-degree part keeps the coefficients on the sets of at most `k` coordinates and drops the
others. -/
@[simp]
theorem fourierCoeff_lowDegreePart (k : ℕ) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (lowDegreePart k f) S = if #S ≤ k then fourierCoeff f S else 0 := by
  rw [funext (lowDegreePart_eq_sum_ite k f), fourierCoeff_sum_mul_chi]

/-- The low-degree part has degree at most `k`. -/
theorem lowDegreePart_mem_lowDegree (k : ℕ) (f : (ι → Bool) → ℝ) :
    lowDegreePart k f ∈ lowDegree ℝ ι k :=
  mem_lowDegree_iff_fourierCoeff_eq_zero.2 fun S hS => by
    rw [fourierCoeff_lowDegreePart, ite_eq_right_iff]
    exact fun h => absurd h (not_le.2 hS)

/-- The low-degree part up to degree `k` is the sum of the degree-`j` parts `f^{=j}` for
`j ≤ k`. -/
theorem sum_range_levelPart (k : ℕ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    ∑ j ∈ range (k + 1), levelPart j f x = lowDegreePart k f x := by
  simp only [levelPart, lowDegreePart]
  rw [← sum_fiberwise_of_maps_to (g := card) (t := range (k + 1))
    fun S hS => mem_range.2 (Nat.lt_succ_of_le (mem_filter.1 hS).2)]
  refine sum_congr rfl fun j hj => ?_
  rw [filter_filter]
  refine sum_congr (filter_congr fun S _ => ⟨fun h => ⟨h ▸ Nat.le_of_lt_succ (mem_range.1 hj), h⟩,
    fun h => h.2⟩) fun _ _ => rfl

/-- Up to the number of coordinates, the low-degree part is the function itself. -/
theorem lowDegreePart_of_card_le {k : ℕ} (hk : Fintype.card ι ≤ k) (f : (ι → Bool) → ℝ) :
    lowDegreePart k f = f :=
  fourierCoeff_injective <| funext fun S => by
    rw [fourierCoeff_lowDegreePart, ite_eq_left_iff]
    exact fun h => absurd ((card_le_univ S).trans hk) h

/-- The squared `L²` norm of the low-degree part is the Fourier weight up to degree `k`. -/
theorem lpNorm_two_lowDegreePart_sq (k : ℕ) (f : (ι → Bool) → ℝ) :
    lpNorm 2 (lowDegreePart k f) ^ 2 = ∑ S with #S ≤ k, fourierCoeff f S ^ 2 := by
  rw [lpNorm_two_sq, expect_sq_eq_sum_fourierCoeff_sq]
  simp only [fourierCoeff_lowDegreePart, ite_pow, zero_pow two_ne_zero, sum_ite, sum_const_zero,
    add_zero]

/-- Taking the low-degree part does not increase the `L²` norm. -/
theorem lpNorm_two_lowDegreePart_le (k : ℕ) (f : (ι → Bool) → ℝ) :
    lpNorm 2 (lowDegreePart k f) ≤ lpNorm 2 f := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (lpNorm_nonneg _ _) ?_
  rw [lpNorm_two_lowDegreePart_sq, lpNorm_two_sq, expect_sq_eq_sum_fourierCoeff_sq]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _

/-- For `q ≥ 2`, `‖f^{≤k}‖_q ≤ √(q - 1) ^ k ‖f‖_2`, by the generalized Bonami Lemma: the stronger
statement in the hint to [O'Donnell, Exercise 9.8(a)][ODonnell2014]. -/
theorem lpNorm_lowDegreePart_le_lpNorm_two {q : ℝ} (hq : 2 ≤ q) (k : ℕ) (f : (ι → Bool) → ℝ) :
    lpNorm q (lowDegreePart k f) ≤ √(q - 1) ^ k * lpNorm 2 f :=
  (lpNorm_le_sqrt_pow_mul_lpNorm_two hq (lowDegreePart_mem_lowDegree k f)).trans
    (by gcongr; exact lpNorm_two_lowDegreePart_le k f)

/-- **The low-degree part in `L^q`**, `q ≥ 2` [O'Donnell, Proposition 10.37][ODonnell2014]
[O'Donnell, Exercise 9.8(a)][ODonnell2014]: `‖f^{≤k}‖_q ≤ √(q - 1) ^ k ‖f‖_q`. -/
theorem lpNorm_lowDegreePart_le {q : ℝ} (hq : 2 ≤ q) (k : ℕ) (f : (ι → Bool) → ℝ) :
    lpNorm q (lowDegreePart k f) ≤ √(q - 1) ^ k * lpNorm q f :=
  (lpNorm_lowDegreePart_le_lpNorm_two hq k f).trans
    (by gcongr; exact lpNorm_le_lpNorm_of_exponent_le two_pos hq f)

/-- For `0 < ρ ≤ 1`, the noise operator `T_ρ` scales every coefficient of the low-degree part by a
factor at least `ρ ^ k`, so `‖f^{≤k}‖_2 ≤ (1 / ρ) ^ k ‖T_ρ f‖_2`. -/
theorem lpNorm_two_lowDegreePart_le_noiseOp {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (k : ℕ)
    (f : (ι → Bool) → ℝ) :
    lpNorm 2 (lowDegreePart k f) ≤ (1 / ρ) ^ k * lpNorm 2 (noiseOp ρ f) := by
  refine le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (pow_nonneg (div_nonneg zero_le_one hρ.le) _) (lpNorm_nonneg _ _)) ?_
  rw [mul_pow, lpNorm_two_lowDegreePart_sq, lpNorm_two_sq, expect_sq_eq_sum_fourierCoeff_sq,
    mul_sum]
  calc ∑ S with #S ≤ k, fourierCoeff f S ^ 2
      ≤ ∑ S with #S ≤ k, ((1 / ρ) ^ k) ^ 2 * fourierCoeff (noiseOp ρ f) S ^ 2 :=
        sum_le_sum fun S hS => by
          rw [fourierCoeff_noiseOp, mul_pow, ← mul_assoc, ← mul_pow]
          refine le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ ?_)
          rw [one_div_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (pow_pos hρ k), one_mul]
          exact pow_le_pow_of_le_one hρ.le hρ1 (mem_filter.1 hS).2
    _ ≤ ∑ S, ((1 / ρ) ^ k) ^ 2 * fourierCoeff (noiseOp ρ f) S ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity

/-- **The low-degree part against the noise operator in `L^q`**: for `q ≥ 2` and `0 < ρ ≤ 1`,
`‖f^{≤k}‖_q ≤ (√(q - 1) / ρ) ^ k ‖T_ρ f‖_q`. [O'Donnell, Lemma 10.38][ODonnell2014] is the case
`q = 4`. -/
theorem lpNorm_lowDegreePart_le_noiseOp {q ρ : ℝ} (hq : 2 ≤ q) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (k : ℕ) (f : (ι → Bool) → ℝ) :
    lpNorm q (lowDegreePart k f) ≤ (√(q - 1) / ρ) ^ k * lpNorm q (noiseOp ρ f) :=
  calc lpNorm q (lowDegreePart k f) ≤ √(q - 1) ^ k * lpNorm 2 (lowDegreePart k f) :=
        lpNorm_le_sqrt_pow_mul_lpNorm_two hq (lowDegreePart_mem_lowDegree k f)
    _ ≤ √(q - 1) ^ k * ((1 / ρ) ^ k * lpNorm 2 (noiseOp ρ f)) := by
        gcongr; exact lpNorm_two_lowDegreePart_le_noiseOp hρ hρ1 k f
    _ ≤ √(q - 1) ^ k * ((1 / ρ) ^ k * lpNorm q (noiseOp ρ f)) := by
        gcongr; exact lpNorm_le_lpNorm_of_exponent_le two_pos hq _
    _ = (√(q - 1) / ρ) ^ k * lpNorm q (noiseOp ρ f) := by simp only [div_pow, one_pow]; ring

/-- For `1 < q ≤ 2`, `‖f^{≤k}‖_2 ≤ (1 / √(q - 1)) ^ k ‖f‖_q`: the `L²` bound against the noise
operator at `ρ = √(q - 1)` and the `(p, 2)`-Hypercontractivity Theorem at `p = q`,
`‖T_ρ f‖_2 ≤ ‖f‖_q` (`BitString.lpNorm_two_noiseOp_le`). -/
theorem lpNorm_two_lowDegreePart_le_lpNorm {q : ℝ} (hq : 1 < q) (hq2 : q ≤ 2) (k : ℕ)
    (f : (ι → Bool) → ℝ) :
    lpNorm 2 (lowDegreePart k f) ≤ (1 / √(q - 1)) ^ k * lpNorm q f := by
  have hρ : 0 < √(q - 1) := Real.sqrt_pos.2 (by linarith)
  have hρ1 : √(q - 1) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  exact (lpNorm_two_lowDegreePart_le_noiseOp hρ hρ1 k f).trans
    (by gcongr; exact lpNorm_two_noiseOp_le hq.le hq2 hρ.le le_rfl f)

/-- **The low-degree part in `L^q`**, `1 < q ≤ 2` [O'Donnell, Proposition 10.37][ODonnell2014]
[O'Donnell, Exercise 9.8(b)][ODonnell2014]: `‖f^{≤k}‖_q ≤ (1 / √(q - 1)) ^ k ‖f‖_q`. -/
theorem lpNorm_lowDegreePart_le_of_le_two {q : ℝ} (hq : 1 < q) (hq2 : q ≤ 2) (k : ℕ)
    (f : (ι → Bool) → ℝ) :
    lpNorm q (lowDegreePart k f) ≤ (1 / √(q - 1)) ^ k * lpNorm q f :=
  (lpNorm_le_lpNorm_of_exponent_le (by linarith) hq2 _).trans
    (lpNorm_two_lowDegreePart_le_lpNorm hq hq2 k f)

end Cslib.BitString
