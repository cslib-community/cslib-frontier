/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.Sturm

/-!
# Collected results: Sturm root counting for arbitrary nonzero real polynomials
-/

register_result "sturm-reduced-real-root-counting" where
  title := "Sturm's theorem for arbitrary nonzero real polynomials via reduced Sturm sequences"
  topic := "algebraic complexity"
  sources := [
    { paper := BasuPollackRoy2006, theorem := "Theorem 2.50", locator := "printed p. 52" }
  ]
  theorems := [
    Polynomial.sturmReducedVariations_sub_eq_card_roots_Ioc
  ]
  scope := "For any nonzero p : ℝ[X] (without assuming separability) and finite real endpoints \
    a ≤ b, the drop sturmReducedVariations p a - sturmReducedVariations p b in sign variations \
    of the GCD-reduced Sturm sequence sturmSeq (p / gcd p (derivative p)) \
    (derivative p / gcd p (derivative p)) equals the number of distinct real roots of p in the \
    half-open interval (a, b] (counted without multiplicity, with no endpoint nonvanishing \
    hypothesis). Adapted over ℝ with finite endpoints on (a, b] from Theorem 2.50's \
    open-interval statement over a real closed field. Outside-fleet source check: \
    https://github.com/cslib-community/cslib-frontier/pull/7735#pullrequestreview-6016516231"
