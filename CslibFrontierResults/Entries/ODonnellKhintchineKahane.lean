/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.KhintchineKahane
import CslibFrontier.Foundations.BooleanAnalysis.PolynomialThresholdWeight

/-!
# Collected results: Khintchine–Kahane and the level-one weight of LTFs
-/

register_result "odonnell-khintchine-kahane" where
  title := "Khintchine–Kahane inequality with the optimal constant"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 2.55(b), (c)",
      locator := "arXiv:2105.10386v1, §2.6, printed p. 66" }
  ]
  theorems := [
    Cslib.BitString.expect_norm_sum_sq_le_two_mul_sq,
    Cslib.BitString.two_le_of_forall_expect_norm_sum_sq_le
  ]
  scope := "For vectors w : ι → V over a finite coordinate type ι, in any seminormed real space \
    V (the book asks for a normed vector space), with uniform random signs signVal (x i): \
    𝔼 ‖∑ᵢ xᵢ wᵢ‖² ≤ 2 (𝔼 ‖∑ᵢ xᵢ wᵢ‖)², the squared form of the book's \
    𝔼 ‖∑ᵢ xᵢ wᵢ‖ ≥ (1/√2) (𝔼 ‖∑ᵢ xᵢ wᵢ‖²)^(1/2). Optimality, part (c), is stated for V = ℝ \
    and two coordinates: any c with 𝔼 ‖∑ᵢ xᵢ wᵢ‖² ≤ c (𝔼 ‖∑ᵢ xᵢ wᵢ‖)² for every \
    w : Fin 2 → ℝ has 2 ≤ c. Part (a), L g ≤ g (laplacian_norm_sum_le), and the inequality \
    2 Var[g] ≤ 𝔼 g² of part (b) are steps of the proof and are not covered by this entry."

register_result "odonnell-ltf-level-one-weight" where
  title := "Linear threshold functions have Fourier weight at least 1/2 up to degree one"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Theorem 5.2",
      locator := "arXiv:2105.10386v1, §5.1, printed pp. 114–115" }
  ]
  theorems := [Cslib.BitString.one_half_le_sum_fourierCoeff_sq_of_nonneg_mul]
  scope := "For every f : (ι → Bool) → Bool over a finite coordinate type ι, read as signs \
    through signVal (false ↦ 1), and every nonzero real function ℓ of Fourier degree at most \
    one with 0 ≤ signVal (f x) * ℓ x for all x: 1/2 ≤ ∑_{|S| ≤ 1} f̂(S)², the book's \
    W^{≤1}[f] ≥ 1/2. This covers every LTF f = sgn(ℓ), including forms ℓ that vanish on the \
    cube, with either value of f there, and affine forms with a nonzero constant term, as in \
    the book's Exercise 5.5 (§5.6, printed p. 134). The assumption ℓ ≠ 0 excludes only the \
    degenerate representation by the zero form."
