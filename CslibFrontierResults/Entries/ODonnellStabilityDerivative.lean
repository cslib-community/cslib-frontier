/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.StableInfluence

/-!
# Collected results: the derivative of the noise stability
-/

register_result "odonnell-noise-stability-derivative-endpoints" where
  title := "The derivative of the noise stability at 0 and at 1"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Proposition 2.51",
      locator := "arXiv:2105.10386v1, §2.4, printed p. 56" }
  ]
  theorems := [
    Cslib.BitString.hasDerivAt_noiseStability_zero,
    Cslib.BitString.hasDerivAt_noiseStability_one
  ]
  scope := "For a real function f on the uniform cube over any finite coordinate type, the \
    function ρ ↦ Stab_ρ[f] has derivative W¹[f] (levelWeight 1 f) at ρ = 0 and I[f] \
    (totalInfluence f) at ρ = 1, stated as two-sided HasDerivAt. The source's restatement for \
    Boolean f, d/dδ NS_δ[f] = I[f] at δ = 0, is not stated separately. Its claim that NS_δ[f] \
    increases on [0, 1/2] for Boolean f is Cslib.BitString.noiseSensitivity_mono \
    (Noise.lean)."

register_result "odonnell-stable-influence-derivative" where
  title := "The total stable influence: derivative of the noise stability and Fourier formula"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Fact 2.53",
      locator := "arXiv:2105.10386v1, §2.4, printed p. 57" }
  ]
  theorems := [
    Cslib.BitString.hasDerivAt_noiseStability,
    Cslib.BitString.totalStableInfluence_eq_sum
  ]
  scope := "For a real function f on the uniform cube over any finite coordinate type, the \
    function ρ ↦ Stab_ρ[f] has the two-sided derivative I^(ρ)[f] (totalStableInfluence ρ f) at \
    every real ρ, while Definition 2.52 takes ρ ∈ [0, 1]; and \
    I^(ρ)[f] = Σ_S |S| ρ^(|S| − 1) f̂(S)², the source's Σ_k k ρ^(k − 1) W^k[f] summed over \
    sets rather than grouped by degree. The source's Exercise 2.40 (§2.6, printed p. 64) asks \
    the reader to verify Fact 2.53."
