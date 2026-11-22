/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.LowDegreeGranularity
import CslibFrontier.MachineLearning.UniformLearning.ExactLowDegree

/-!
# Collected results: exact learning of low-degree functions
-/

register_result "odonnell-low-degree-granularity" where
  title := "Boolean functions of degree at most k have coefficients in 2^(1-k) Z"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 1.11(b)",
      locator := "arXiv:2105.10386v1, §1.7, printed p. 36" }
  ]
  theorems := [Cslib.BitString.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_of_mem_lowDegree]
  scope := "For a finite coordinate type ι, k : ℕ and f : (ι → Bool) → Bool whose sign \
    reading fun x => signVal (f x) lies in lowDegree ℝ ι k (degree at most k), every Fourier \
    coefficient on S is z / 2 ^ (k - 1) for some integer z, with natural subtraction: integer \
    multiples of 2^(1-k) for k ≥ 1 and integers for k = 0. The book assumes deg(f) = k ≥ 1; \
    the statement assumes deg(f) ≤ k and also covers k = 0. The proof goes through the \
    integer-valued version, exists_fourierCoeff_eq_intCast_div_two_pow_of_mem_lowDegree \
    (coefficients in 2^(-k) Z), following Exercise 1.9(c),(d) (printed pp. 35–36)."

register_result "odonnell-exact-low-degree-learning" where
  title := "Functions of degree at most k are learnable from random examples with error 0"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Theorem 3.36",
      locator := "arXiv:2105.10386v1, §3.4, printed p. 82" }
  ]
  theorems := [Cslib.MachineLearning.UniformLearning.exactLowDegreeLearner_learns]
  scope := "For a finite coordinate type ι, 1 ≤ k, 0 < δ and m with \
    2 · 4 ^ k · log (2 N / δ) ≤ m, where N = #{S : Finset ι | #S ≤ k}, the deterministic \
    learner exactLowDegreeLearner ι k m (empirical Fourier coefficients on the sets of at \
    most k coordinates, rounded to the nearest multiple of 2^(1-k), then the sign of the \
    truncated expansion) satisfies Learns (exactLowDegreeLearner ι k m) \
    {f | (fun x => signVal (f x)) ∈ lowDegree ℝ ι k} 0 δ from m uniform random examples. \
    The book fixes the failure probability at 1/10 (§3.4, printed p. 79); here δ is a \
    parameter. Only the number of examples is certified; \
    the book's running time n^k · poly(n, 2^k) is not certified by a machine model. The \
    book leaves the proof as Exercise 3.36 (§3.6, printed p. 89)."
