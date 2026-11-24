/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.UncertaintyPrinciple

/-!
# Collected results: the uncertainty principle
-/

register_result "odonnell-hausdorff-young-special-cases" where
  title := "Fourier coefficients are bounded by the L¹ norm, and values by the spectral 1-norm"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 3.9",
      locator := "arXiv:2105.10386v1, §3.6, printed p. 86" }
  ]
  theorems := [
    Cslib.BitString.abs_fourierCoeff_le_expect_abs,
    Cslib.BitString.abs_le_sum_abs_fourierCoeff
  ]
  scope := "Every real function f on the cube (ι → Bool) over a finite coordinate type: \
    |fourierCoeff f S| ≤ 𝔼 x, |f x| for every S (the book's ‖f̂‖∞ ≤ ‖f‖₁, stated per \
    coefficient) and |f x| ≤ ∑ S, |fourierCoeff f S| for every x (‖f‖∞ ≤ ‖f̂‖₁, stated per \
    input). The book's general Hausdorff–Young Inequality is not formalized."

register_result "odonnell-uncertainty-principle" where
  title := "Uncertainty principle on the Boolean cube"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 3.15",
      locator := "arXiv:2105.10386v1, §3.6, printed pp. 86–87; Definition 3.9 on printed p. 72" }
  ]
  theorems := [Cslib.BitString.one_le_dens_mul_card_fourierCoeff_ne_zero]
  scope := "Every real function f ≠ 0 on the cube (ι → Bool) over a finite coordinate type: \
    1 ≤ (dens {x | f x ≠ 0} : ℝ) * #{S | fourierCoeff f S ≠ 0}, the book's \
    sparsity(f) · sparsity(f̂) ≥ 1 with the fractional sparsity Pr_x[f(x) ≠ 0] of f and the \
    Fourier sparsity |supp f̂| of Definition 3.9 (a count). Proved from the two bounds of \
    Exercise 3.9 (odonnell-hausdorff-young-special-cases) instead of the book's route through \
    ‖f‖₁ = 1 and ‖f‖₂ in parts (a)–(c). Part (d), the equality cases, is not formalized."
