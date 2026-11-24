/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Means

/-! Tests of Proposition B.3 and Lemma C.2 of [AnthropicVPVNP2026] under ordinary imports:

* the crossing inequality (Q) for wire exponents of a spectral point;
* the parallelogram law for the mean norm of prices on two sheets. -/

namespace CslibFrontierTests.CurvatureCrossing

open Cslib.PartyTensor Cslib.Circuits.Arithmetic.Separation.Curvature

variable {K : Type} [Field K]

/-- The inequality (Q) for the wire exponents of a spectral point, which form a price, with
`p = q = 1` and `τ = 1`. -/
example {V : Type} [Fintype V] [DecidableEq V] (F : SpectralPoint K V) (x v y u o o' w w' : V) :
    2 * (F.wireExponent x v + F.wireExponent y u) ≤
      (F.wireExponent x o + F.wireExponent v o' + F.wireExponent x w + F.wireExponent v w') +
        (F.wireExponent y o + F.wireExponent u o' + F.wireExponent u w + F.wireExponent y w') +
        2 + (F.wireExponent o o' ^ 2 + F.wireExponent w w' ^ 2) / 2 := by
  have h := isPrice_crossing_two_mul_le (isPrice_wireExponent (K := K) F) x v y u o o' w w'
    zero_le_one zero_le_one 1 one_pos
  norm_num at h ⊢
  linarith

/-- Lemma C.2: the mean norm of prices on two sheets satisfies the parallelogram law. -/
example (W : ℕ → Bool × ℤ × ℤ → Bool × ℤ × ℤ → ℝ) (hW : ∀ n, IsPrice K (W n)) (Λ : ℝ)
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|))
    (a b : ℤ × ℤ) :
    meanNorm W (a + b) ^ 2 + meanNorm W (a - b) ^ 2 = 2 * meanNorm W a ^ 2 + 2 * meanNorm W b ^ 2 :=
  meanNorm_parallelogram hW hΛ a b

end CslibFrontierTests.CurvatureCrossing
