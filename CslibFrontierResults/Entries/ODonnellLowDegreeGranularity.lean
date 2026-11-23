/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.DecisionTree.Granularity
import CslibFrontier.Foundations.BooleanAnalysis.LowDegreeGranularity

/-!
# Collected results: granularity of low-degree functions and decision trees
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

register_result "odonnell-decision-tree-granularity" where
  title := "Integer-valued decision trees of depth k have Fourier coefficients in 2^(-k) Z"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Proposition 3.16, fourth item",
      locator := "arXiv:2105.10386v1, §3.2, printed p. 74" }
  ]
  theorems := [Cslib.DecisionTree.exists_fourierCoeff_eq_intCast_div_two_pow_depth]
  scope := "For a finite coordinate type ι, a decision tree t : DecisionTree ι β with leaves in \
    any type β and g : β → ℤ, every Fourier coefficient of fun x => (g (t.eval x) : ℝ) is \
    z / 2 ^ t.depth for some integer z: the function is 2^(-k)-granular (Definition 3.10, \
    printed p. 72) for the depth k of t. Reading the leaves through g covers the source's \
    integer-labeled trees. The depth is the longest structural root-to-leaf path, so a tree \
    that queries a coordinate twice on a path only weakens the bound. The proof is the \
    degree bound, the first item, with the granularity of functions of degree at most k \
    (Cslib.BitString.exists_fourierCoeff_eq_intCast_div_two_pow_of_mem_lowDegree). For a \
    Boolean output read as ±1, \
    Cslib.DecisionTree.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_depth_sub_one \
    gives the finer granularity 2^(1-k) for k ≥ 1, after Exercise 1.11(b), and integer \
    coefficients for k = 0. The source leaves the proof as Exercise 3.21 (§3.6, printed p. 87)."
