/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.InnerProduct
import CslibFrontier.Foundations.BooleanAnalysis.InnerProductPTF

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
    Cslib.BitString.fourierCoeff_signVal_dotProduct_fstBits_sndBits,
    Cslib.BitString.abs_fourierCoeff_signVal_dotProduct_fstBits_sndBits
  ]
  scope := "The inner product modulo two fstBits z ⬝ᵥ sndBits z of the two halves of a string z \
    on Fin (n + n), read as signs through signVal (false ↦ 1, true ↦ −1); this is the book's \
    IP_{2n}(x, y) = (−1)^{x·y} with x the first n coordinates and y the last n. Its Fourier \
    coefficient on a set S of coordinates is (−1)^{S_x · S_y} / 2^n, where S_x and S_y are the \
    indicator vectors of the parts of S in the two halves (i with Fin.castAdd n i ∈ S, \
    respectively Fin.natAdd n i ∈ S), so every coefficient has absolute value 2^{−n}, for \
    every n including n = 0. The book asks for the Fourier expansion; this gives every \
    coefficient."

register_result "odonnell-inner-product-ptf-sparsity" where
  title := "PTF representations of the inner product mod 2 function have sparsity at least 2^n"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Corollary 5.11",
      locator := "arXiv:2105.10386v1, §5.1, printed p. 117" }
  ]
  theorems := [
    Cslib.BitString.two_pow_le_card_dotProduct_fstBits_sndBits_of_nonneg_mul,
    Cslib.BitString.IsPTFOn.two_pow_le_card_dotProduct_fstBits_sndBits
  ]
  scope := "The inner product modulo two fstBits z ⬝ᵥ sndBits z of the two halves of a string z \
    on Fin (n + n), read as signs. If a real function p on the cube has Fourier coefficients \
    vanishing outside a family T of sets, p ≠ 0, and \
    signVal (fstBits z ⬝ᵥ sndBits z) * p z ≥ 0 for every z, then 2^n ≤ |T|; this covers the \
    book's representations f = sgn(p) with sgn(0) = 1 and also lets the inner product take \
    either sign where p = 0. The hypothesis p ≠ 0, implicit in the book, is needed for every n. \
    The same bound holds for the nowhere-vanishing representations of IsPTFOn T. By \
    Definition 5.7, p has sparsity at most |T| for every family T outside which p̂ vanishes; \
    taking T to be the support of p̂ gives the book's statement."
