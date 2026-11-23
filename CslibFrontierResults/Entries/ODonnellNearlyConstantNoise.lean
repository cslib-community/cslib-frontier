/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.Noise

/-!
# Collected results: noise sensitivity of nearly constant functions
-/

register_result "odonnell-nearly-constant-noise-sensitivity" where
  title := "Nearly constant Boolean functions have small noise sensitivity"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 2.39",
      locator := "arXiv:2105.10386v1, §2.6, printed p. 64" }
  ]
  theorems := [Cslib.BitString.noiseSensitivity_le_two_mul_min]
  scope := "For every f : (ι → Bool) → Bool over a finite coordinate type ι and every real \
    δ ≤ 1, noiseSensitivity δ f ≤ 2 α, where α is the smaller of the two relative Hamming \
    distances hammingDist f (fun _ => b) / 2 ^ card ι to the constants b = false and \
    b = true; read through signVal (false ↦ 1), these are the book's Pr[f = −1] and \
    Pr[f = 1]. The book assumes δ ∈ [0, 1]; the formal statement drops 0 ≤ δ. For δ < 0, \
    noiseSensitivity δ f is a signed-weight average rather than a probability, and the bound \
    follows from Exercise 2.42 (noiseSensitivity_le_mul_totalInfluence), whose right side is \
    then nonpositive."
