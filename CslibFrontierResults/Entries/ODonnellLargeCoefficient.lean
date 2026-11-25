/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.LargeCoefficient

/-!
# Collected results: a large low-degree Fourier coefficient
-/

register_result "odonnell-large-low-degree-fourier-coefficient" where
  title := "A Boolean function of variance at least 1/2 has a large low-degree Fourier coefficient"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Corollary 9.32",
      locator := "arXiv:2105.10386v1, §9.6, printed p. 270" }
  ]
  theorems := [Cslib.BitString.exists_le_fourierCoeff_sq_of_le_expect_sub_expect_sq]
  scope := "For every f : (ι → Bool) → Bool over a finite coordinate type ι, read as signs \
    through signVal (false ↦ 1), with variance 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y))² at \
    least 1/2 and total influence at most K: some nonempty S with |S| ≤ 8 K has \
    f̂(S)² ≥ 1 / (4 (M + 1)^⌊8 K⌋), where M = (256/9) K³ 81^(8 K). Taking K = I[f] gives the \
    book's statement; the book's O(I[f]) and exp(−O(I[f]²)) are made explicit, and the bound \
    is exp(−O(K²)) because K ≥ 1/2. Remark 9.33 is not a separate theorem."
