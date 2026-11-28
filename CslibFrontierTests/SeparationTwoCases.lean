/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Cube
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Rank

/-! Tests of Definition D.1 and Theorem D.2 of [AnthropicVPVNP2026] as a client: `D(r)` of the zero
price, a matrix of rank one in a frame, Theorem D.2 over `ℚ`, and the two hypotheses at work. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationTwoCases

open Cslib.PartyTensor Cslib.Circuits.Arithmetic.Separation.TwoCases
open Cslib.Circuits.Arithmetic.Separation.Flag

/-- The zero price on `Mat_2(F₂)`. -/
private def zeroPrice : Mt 2 → Mt 2 → ℝ := fun _ _ => 0

/-- `D(r) = 0` for the zero price, at every rank. -/
example (r : ℕ) : distAtRank zeroPrice r = 0 := by
  simp [distAtRank, meanSq, rankMean, zeroPrice]

/-- The zero price satisfies the inequality of the contracting hypothesis with `s = 1`. -/
example : distAtRank zeroPrice 2 ≤ 1 * distAtRank zeroPrice 1 := by
  simp [distAtRank, meanSq, rankMean, zeroPrice]

/-- The diagonal matrix of one index has rank one. -/
example : (X 1 1 {(0 : Fin 3)}).rank = 1 := by
  rw [rank_X, Finset.card_singleton]

/-- Theorem D.2 over `ℚ`. -/
example : FlatCase ℚ ∨ ContractingCase ℚ := flatCase_or_contractingCase ℚ

/-- In the flat case the metric of three points of the plane is a price. -/
example {K : Type} [Field K] (hK : FlatCase K) (E : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    IsPrice K fun a b => dist (E a) (E b) :=
  hK 2 (Fin 3) E

/-- Outside the contracting case the square root of the rank is a price on `Mat_3(F₂)`, with
`|a, a|² = 0`. -/
example {K : Type} [Field K] (hK : ¬ ContractingCase K) :
    ∃ w : Mt 3 → Mt 3 → ℝ, IsPrice K w ∧ ∀ a, w a a ^ 2 = 0 := by
  obtain ⟨w, hw, hr⟩ := exists_sq_eq_rank hK (μ := 3) le_rfl
  exact ⟨w, hw, fun a => by rw [hr, sub_self, Matrix.rank_zero, Nat.cast_zero]⟩

/-- In the contracting case some `μ ≥ 2` has `D(μ) ≤ s D(1)` for the zero price. -/
example {K : Type} [Field K] (hK : ContractingCase K) :
    ∃ μ : ℕ, 2 ≤ μ ∧ ∃ s : ℝ, 1 ≤ s ∧ s ^ 2 < μ := by
  obtain ⟨μ, s, hμ, hs, hsm, -⟩ := hK
  exact ⟨μ, hμ, s, hs, hsm⟩

end CslibFrontierTests.SeparationTwoCases
