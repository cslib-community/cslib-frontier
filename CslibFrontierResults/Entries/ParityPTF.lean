/-
Copyright (c) 2026 Josh Liebow-Feeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Liebow-Feeser
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.ParityPTF

/-!
# Collected results: the PTF degree of parity
-/

register_result "minsky-papert-parity-ptf-degree" where
  title := "The n-bit parity function has polynomial threshold degree n"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := MinskyPapert1969, theorem := "Theorem 3.1.1",
      locator := "Ch. 3, §3.1" },
    { paper := ODonnell2014, theorem := "Exercise 5.10(a)",
      locator := "arXiv:2105.10386v1, §5.6, printed p. 135" }
  ]
  theorems := [
    Cslib.BitString.isPTF_parity_iff,
    Cslib.BitString.le_of_nonneg_mul_parity
  ]
  scope := "The parity of n bits parity n : BitString n → Bool, read as signs through signVal \
    (false ↦ 1, true ↦ −1), is a polynomial threshold function of degree at most k (IsPTF k) \
    if and only if n ≤ k, including the constant case n = 0. The lower bound also holds for \
    representations p that may vanish, provided p ≠ 0 and signVal (parity n x) * p x ≥ 0 for \
    every x (covering f = sgn(p) with sgn(0) = 1); the hypothesis p ≠ 0 is necessary because \
    p = 0 satisfies the sign condition for every k. The module proves the corresponding \
    monomial-family characterization IsPTFOn T (parityOn S) ↔ S ∈ T for any finite index type."
