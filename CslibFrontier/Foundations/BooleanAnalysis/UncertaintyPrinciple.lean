/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import Mathlib.Data.Finset.Density

/-!
# The uncertainty principle

A nonzero real function on the cube and its Fourier transform cannot both be sparse: the fraction
of inputs where `f` is nonzero times the number of sets where `f̂` is nonzero is at least one
[O'Donnell, Exercise 3.15][ODonnell2014]
(`BitString.one_le_dens_mul_card_fourierCoeff_ne_zero`). This is the book's
`sparsity(f) · sparsity(f̂) ≥ 1`, with the fractional sparsity `sparsity(f) = Pr_x[f(x) ≠ 0]` of
the exercise, here `dens {x | f x ≠ 0}`, and the Fourier sparsity `sparsity(f̂) = |supp f̂|` of
its Definition 3.9, a count. (Read with the fractional sparsity for `f̂` too, the claim would fail
for every character once `n ≥ 1`.) Multiplying by `2 ^ n` gives the counting form
`2 ^ n ≤ |supp f| · |supp f̂|` (`BitString.two_pow_card_le_card_mul_card_fourierCoeff_ne_zero`).
The equality cases, part (d) of the exercise, are not formalized. The notes to the book's §3.6
credit the uncertainty principle to Matolcsi and Szűcs (1973) [O'Donnell, §3.6][ODonnell2014].

The proof takes `M = max_x |f(x)|`. Each coefficient has `|f̂(S)| ≤ 𝔼 |f| ≤ dens(G) M`, where `G`
is the support of `f`, and `M ≤ ∑_{S ∈ F} |f̂(S)|` by Fourier inversion, where `F` is the support
of `f̂`; so `M ≤ dens(G) |F| M` with `M > 0`. These are the two halves of Exercise 3.9
(`BitString.abs_fourierCoeff_le_expect_abs`, and `BitString.abs_sum_mul_chi_le` restricted to
`F`); the argument avoids the book's normalization `‖f‖₁ = 1` and its passage through `‖f‖₂`.

## Main results

* `Cslib.BitString.one_le_dens_mul_card_fourierCoeff_ne_zero`: the uncertainty principle.
* `Cslib.BitString.two_pow_card_le_card_mul_card_fourierCoeff_ne_zero`: its counting form.

## Usage

For a real function `f : (ι → Bool) → ℝ` over any finite coordinate type `ι` and `hf : f ≠ 0`,
`one_le_dens_mul_card_fourierCoeff_ne_zero hf` gives
`1 ≤ (dens {x | f x ≠ 0} : ℝ) * #{S | fourierCoeff f S ≠ 0}`, and
`two_pow_card_le_card_mul_card_fourierCoeff_ne_zero hf` gives the same with both factors counts,
`2 ^ Fintype.card ι ≤ #{x | f x ≠ 0} * #{S | fourierCoeff f S ≠ 0}`. The hypothesis is needed,
since for the zero function both supports are empty. The two bounds behind it live in
`CslibFrontier.Foundations.BooleanAnalysis.Fourier` and apply to any `f`:
`BitString.abs_fourierCoeff_le_expect_abs f S : |fourierCoeff f S| ≤ 𝔼 x, |f x|` (the right side
is `Cslib.lpNorm 1 f` by `Cslib.lpNorm_one`, from `CslibFrontier.Foundations.Analysis.LpNorm`) and
`BitString.abs_le_sum_abs_fourierCoeff f x : |f x| ≤ ∑ S, |fourierCoeff f S|`. For a sum over a
subfamily `s` of sets, or with weights `c` that are not Fourier coefficients, use
`BitString.abs_sum_mul_chi_le s c x : |∑ S ∈ s, c S * chi ℝ S x| ≤ ∑ S ∈ s, |c S|`. The checked
clients in
[CslibFrontierTests/BooleanAnalysisUncertaintyPrinciple.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisUncertaintyPrinciple.lean)
show that the character `chi ℝ {0}` on two bits attains the bound (`1 · 1 = 1`, or `4 · 1 = 2 ^ 2`
in counts), that the function `1 - [x = 0]`, nonzero at three of the four points with all four
coefficients nonzero, satisfies it strictly (`3/4 · 4 = 3`), and that the zero function violates
it. They check that `chi ℝ {0}` attains both Exercise 3.9 bounds (with
`lpNorm 1 (chi ℝ {0}) = 1` and `|chi ℝ {0} x| = 1` at every input), and bound
`|2 χ_{0} - 3 χ_{1}|` by `5`, attained where the bits differ.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The uncertainty principle** [O'Donnell, Exercise 3.15][ODonnell2014]: if `f` is not
identically zero, the fraction of inputs where `f` is nonzero times the number of sets where `f̂` is
nonzero is at least one, `sparsity(f) · sparsity(f̂) ≥ 1`. -/
theorem one_le_dens_mul_card_fourierCoeff_ne_zero {f : (ι → Bool) → ℝ} (hf : f ≠ 0) :
    1 ≤ (dens {x | f x ≠ 0} : ℝ) * #{S : Finset ι | fourierCoeff f S ≠ 0} := by
  set G := ({x | f x ≠ 0} : Finset (ι → Bool))
  set F := ({S | fourierCoeff f S ≠ 0} : Finset (Finset ι))
  -- `M = max |f|`, attained at `x₀`
  obtain ⟨x₀, -, hx₀⟩ := univ.exists_max_image (fun x => |f x|) univ_nonempty
  set M := |f x₀|
  have hM : 0 < M := by
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hf
    exact (abs_pos.2 hy).trans_le (hx₀ y (mem_univ y))
  -- `|f̂(S)| ≤ 𝔼 |f| ≤ dens(G) M`
  have hcoeff (S : Finset ι) : |fourierCoeff f S| ≤ dens G * M := by
    calc |fourierCoeff f S| ≤ 𝔼 x, |f x| := abs_fourierCoeff_le_expect_abs f S
      _ = (∑ x ∈ G, |f x|) / Fintype.card (ι → Bool) := by
          rw [Fintype.expect_eq_sum_div_card, sum_filter_of_ne fun x _ h => abs_ne_zero.1 h]
      _ ≤ (∑ _x ∈ G, M) / Fintype.card (ι → Bool) := by
          gcongr with x
          exact hx₀ x (mem_univ x)
      _ = dens G * M := by rw [sum_const, nsmul_eq_mul, nnratCast_dens, div_mul_eq_mul_div]
  -- `M ≤ ∑_{S ∈ F} |f̂(S)|` by Fourier inversion
  have hinv : 1 * M ≤ (dens G * #F) * M := by
    calc 1 * M = |∑ S ∈ F, fourierCoeff f S * chi ℝ S x₀| := by
          rw [one_mul, sum_filter_of_ne fun S _ h => left_ne_zero_of_mul h,
            sum_fourierCoeff_mul_chi]
      _ ≤ ∑ S ∈ F, |fourierCoeff f S| := abs_sum_mul_chi_le F _ x₀
      _ ≤ ∑ _S ∈ F, dens G * M := sum_le_sum fun S _ => hcoeff S
      _ = (dens G * #F) * M := by rw [sum_const, nsmul_eq_mul]; ring
  exact le_of_mul_le_mul_right hinv hM

/-- **The uncertainty principle**, counting form: if `f` is not identically zero, the number of
inputs where `f` is nonzero times the number of sets where `f̂` is nonzero is at least the number
`2 ^ n` of inputs. -/
theorem two_pow_card_le_card_mul_card_fourierCoeff_ne_zero {f : (ι → Bool) → ℝ} (hf : f ≠ 0) :
    2 ^ Fintype.card ι ≤ #{x | f x ≠ 0} * #{S : Finset ι | fourierCoeff f S ≠ 0} := by
  have h := one_le_dens_mul_card_fourierCoeff_ne_zero hf
  rw [nnratCast_dens, Fintype.card_fun, Fintype.card_bool, div_mul_eq_mul_div,
    le_div_iff₀ (by positivity), one_mul] at h
  exact_mod_cast h

end Cslib.BitString
