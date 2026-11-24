/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.StableInfluenceBound

/-!
# Collected results: stable influences bounded by influences
-/

register_result "odonnell-stable-influence-le-influence-rpow" where
  title := "Stable influences of Boolean functions are bounded by powers of influences"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Corollary 9.25",
      locator := "arXiv:2105.10386v1, §9.5, printed p. 264; Corollary 9.12 in §9.2, printed \
        p. 255" }
  ]
  theorems := [Cslib.BitString.stableInfluence_signVal_le_influence_rpow]
  scope := "For every f : (ι → Bool) → Bool over a finite coordinate type ι, read as signs \
    F through signVal (false ↦ 1), every coordinate i and every real ρ with 0 ≤ ρ ≤ 1, \
    stableInfluence ρ i F ≤ influence i F ^ (2 / (1 + ρ)), a real power (Corollary 9.25). \
    Corollary 9.12 is the case ρ = 1/3, with exponent 3/2; it is not stated separately, and \
    the proof of Cslib.BitString.sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le \
    instantiates it there."
