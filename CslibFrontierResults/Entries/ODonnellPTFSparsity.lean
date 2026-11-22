/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.InnerProduct

/-!
# Collected results: the PTF sparsity of the inner product
-/

register_result "odonnell-inner-product-fourier-spectrum" where
  title := "Fourier spectrum of the inner product mod 2 function"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 1.1(g)",
      locator := "arXiv:2105.10386v1, §1.7, printed p. 34" }
  ]
  theorems := [
    Cslib.BitString.fourierCoeff_signVal_innerProduct,
    Cslib.BitString.abs_fourierCoeff_signVal_innerProduct
  ]
  scope := "The inner product modulo two of the two halves of a string on ι ⊕ ι, for any finite \
    type ι with n = |ι|, read as signs through signVal (false ↦ 1); this is the book's IP_{2n} \
    with the halves indexed by ι rather than by 1..n and n+1..2n. Its Fourier coefficient on S \
    is (−1)^{|S_L ∩ S_R|} / 2^n, with S_L and S_R the parts of S in the two halves, so every \
    coefficient has absolute value 2^{−n}."

register_result "odonnell-inner-product-ptf-sparsity" where
  title := "PTF representations of the inner product mod 2 function have sparsity at least 2^n"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Corollary 5.11",
      locator := "arXiv:2105.10386v1, §5.1, printed p. 117" }
  ]
  theorems := [
    Cslib.BitString.two_pow_le_card_innerProduct_of_nonneg_mul,
    Cslib.BitString.IsPTFOn.two_pow_le_card_innerProduct
  ]
  scope := "The inner product modulo two on ι ⊕ ι, n = |ι|, read as signs. If a real function p \
    on the cube has Fourier coefficients vanishing outside a family T of sets, p ≠ 0, and \
    signVal (innerProduct z) * p z ≥ 0 for every z, then 2^n ≤ |T|; this covers the book's \
    representations f = sgn(p) with sgn(0) = 1 and also lets the inner product take either sign \
    where p = 0. The hypothesis p ≠ 0, implicit in the book, is needed for every n. The same \
    bound holds for the nowhere-vanishing representations of IsPTFOn T. By Definition 5.7, p \
    has sparsity at most |T| for every family T outside which p̂ vanishes; taking T to be the \
    support of p̂ gives the book's statement."
