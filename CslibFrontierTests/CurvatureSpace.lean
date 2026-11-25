/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Curvature
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Fan

/-! Tests of Theorem C.1 and Proposition C.3 of [AnthropicVPVNP2026] under ordinary imports:

* the CN inequality for the wire exponents of a spectral point;
* every price is the metric of a complete CAT(0) space, which then has midpoints. -/

namespace CslibFrontierTests.CurvatureSpace

open Cslib Cslib.PartyTensor Cslib.Circuits.Arithmetic.Separation.Curvature

variable {K : Type} [Field K]

/-- Theorem C.1 for the wire exponents of a spectral point, which form a price. -/
example {V : Type} [Fintype V] [DecidableEq V] (F : SpectralPoint K V) (x v m z : V) {D : ℝ}
    (h1 : F.wireExponent x m ≤ D) (h2 : F.wireExponent v m ≤ D) (h3 : F.wireExponent x v = 2 * D) :
    F.wireExponent z m ^ 2 ≤
      1 / 2 * F.wireExponent z x ^ 2 + 1 / 2 * F.wireExponent z v ^ 2 - D ^ 2 :=
  isPrice_sq_le_of_mid (isPrice_wireExponent F) x v m z h1 h2 h3

/-- Proposition C.3: the points of a price embed isometrically into a complete CAT(0) space, in
which any two of them have a midpoint at half their distance. -/
example {V : Type} {w : V → V → ℝ} (hw : IsPrice K w) (a b : V) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : CompleteCAT0Space X) (f : V → X),
      dist (f a) (CAT0.mid (f a) (f b)) = w a b / 2 := by
  obtain ⟨X, _, _, f, -, hf⟩ := exists_completeCAT0Space_of_isPrice hw
  exact ⟨X, inferInstance, inferInstance, f, by rw [CAT0.dist_mid_left, hf]⟩

/-- Proposition C.3 for the zero price on `Bool`: the price space exists, its metric is a price,
and the images of `true` and `false` coincide with their midpoint. -/
example : ∃ (X : Type) (_ : MetricSpace X) (_ : CompleteCAT0Space X) (f : Bool → X),
    IsPrice ℚ (fun a b : X => dist a b) ∧ dist (f true) (CAT0.mid (f true) (f false)) = 0 := by
  obtain ⟨X, _, _, f, hX, hf⟩ :=
    exists_completeCAT0Space_of_isPrice (isPrice_zero (K := ℚ) (Y := Bool))
  exact ⟨X, inferInstance, inferInstance, f, hX, by rw [CAT0.dist_mid_left, hf]; simp⟩

/-- Theorem C.1 with all hypotheses proved: in the price space of a price, the metric is a price
and `CAT0.mid x v` is at distance `|xv| / 2` from both ends, so the CN inequality holds at it. -/
example {V : Type} {w : V → V → ℝ} (hw : IsPrice ℚ w) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : CompleteCAT0Space X), ∀ x v z : X,
      dist z (CAT0.mid x v) ^ 2 ≤
        1 / 2 * dist z x ^ 2 + 1 / 2 * dist z v ^ 2 - (dist x v / 2) ^ 2 := by
  obtain ⟨X, _, _, -, hX, -⟩ := exists_completeCAT0Space_of_isPrice hw
  refine ⟨X, inferInstance, inferInstance, fun x v z => ?_⟩
  exact isPrice_sq_le_of_mid hX x v (CAT0.mid x v) z (CAT0.dist_mid_left x v).le
    (by rw [dist_comm, CAT0.dist_mid_right]) (by ring)

end CslibFrontierTests.CurvatureSpace
