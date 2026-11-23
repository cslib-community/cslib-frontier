/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.SpectralConcentration

/-!
# Collected results: spectral concentration on collections of sets
-/

register_result "odonnell-spectral-concentration-few-sets-and-approximation" where
  title := "Small spectral 1-norm gives concentration on few sets, and concentration survives \
    approximation"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercises 3.16 and 3.17",
      locator := "arXiv:2105.10386v1, §3.6, printed p. 87" }
  ]
  theorems := [
    Cslib.BitString.exists_card_le_sum_fourierCoeff_sq_le,
    Cslib.BitString.sum_fourierCoeff_sq_le_two_mul_add
  ]
  scope := "Real functions f, g on the uniform cube over a finite coordinate type ι, with the \
    Fourier weight of f on a collection T of sets written ∑ S ∈ T, fourierCoeff f S ^ 2 and \
    ε-concentration on F (Definition 3.28, printed p. 79) meaning weight at most ε on Fᶜ. \
    Exercise 3.16: for every ε > 0, f is ε-concentrated on a collection of at most \
    (∑ S, |fourierCoeff f S|) ^ 2 / ε sets, the book's bound ‖f̂‖₁²/ε. Exercise 3.17 is stated \
    unconditionally for every collection T: the weight of g on T is at most twice the sum of \
    the weight of f on T and 𝔼 x, (f x - g x) ^ 2; the book's form (ε₁-concentration of f on F \
    and ‖f − g‖₂² ≤ ε₂ give 2(ε₁ + ε₂)-concentration of g on F) is the case T = Fᶜ."
