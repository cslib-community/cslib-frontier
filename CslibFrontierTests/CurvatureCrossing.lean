/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Crossing
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Means

/-! Tests of Proposition B.3 and Lemma C.2 of [AnthropicVPVNP2026] under ordinary imports:

* the crossing inequality (Q) for wire exponents of a spectral point;
* the mean norm of concrete prices on two sheets (wire exponents pulled back along a parity):
  `N ≤ ν`, the limit of `ν(S g)/S`, and the parallelogram law. -/

set_option linter.privateModule false

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

/-- The parity of the first coordinate of a point of the two sheets. -/
def parity : Bool × ℤ × ℤ → Bool
  | (_, i, _) => decide (i % 2 = 0)

/-- Concrete prices on two sheets: the wire exponents of a spectral point on `Bool`, pulled back
along `parity` (the same price for every `n`). -/
noncomputable def parityPrice (F : SpectralPoint K Bool) : ℕ → Bool × ℤ × ℤ → Bool × ℤ × ℤ → ℝ :=
  fun _ a b => F.wireExponent (parity a) (parity b)

theorem isPrice_parityPrice (F : SpectralPoint K Bool) (n : ℕ) : IsPrice K (parityPrice F n) :=
  (isPrice_wireExponent F).comp parity

/-- The prices `parityPrice F` are `1`-Lipschitz on each sheet: a step that keeps the parity costs
nothing, and one that changes it moves the first coordinate by at least `1`, while wire exponents
are at most `1`. -/
theorem parityPrice_le (F : SpectralPoint K Bool) (n : ℕ) (b : Bool) (P g : ℤ × ℤ) :
    parityPrice F n (b, P) (b, P + g) ≤ 1 * (|(g.1 : ℝ)| + |(g.2 : ℝ)|) := by
  obtain ⟨i, j⟩ := P
  obtain ⟨g₁, g₂⟩ := g
  have h2 : (0 : ℝ) ≤ |(g₂ : ℝ)| := abs_nonneg _
  by_cases hg : g₁ = 0
  · subst hg
    simp [parityPrice, parity, SpectralPoint.wireExponent_self, h2]
  · have h1 : (1 : ℝ) ≤ |(g₁ : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hg
    have := F.wireExponent_le_one (parity (b, i, j)) (parity (b, (i, j) + (g₁, g₂)))
    simp only [parityPrice, one_mul]
    linarith

/-- `N` is at most `ν` (no hypothesis on `W`). -/
example (F : SpectralPoint K Bool) :
    meanNorm (parityPrice F) (1, 0) ≤ meanLength (parityPrice F) (1, 0) :=
  meanNorm_le_meanLength _ _

/-- `ν(S g)/S` converges to `N(g)` for the concrete prices `parityPrice F`. -/
example (F : SpectralPoint K Bool) :
    Filter.Tendsto (fun S : ℕ => meanLength (parityPrice F) (S • ((1, 0) : ℤ × ℤ)) / S)
      Filter.atTop (nhds (meanNorm (parityPrice F) (1, 0))) :=
  tendsto_meanLength_div (isPrice_parityPrice F) (parityPrice_le F) (1, 0)

/-- Lemma C.2 for the concrete prices `parityPrice F` and `a = (1, 0)`, `b = (0, 1)`. -/
example (F : SpectralPoint K Bool) :
    meanNorm (parityPrice F) (1, 1) ^ 2 + meanNorm (parityPrice F) (1, -1) ^ 2 =
      2 * meanNorm (parityPrice F) (1, 0) ^ 2 + 2 * meanNorm (parityPrice F) (0, 1) ^ 2 :=
  meanNorm_parallelogram (isPrice_parityPrice F) (parityPrice_le F) (1, 0) (0, 1)

end CslibFrontierTests.CurvatureCrossing
