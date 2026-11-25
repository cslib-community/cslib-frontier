/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Laws.Existence
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Transfer
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Cube

/-! Tests of the existence of laws (Theorem G.2), as a client that sees only the public
statements.

* Over `ℚ`, by Theorem D.2: the flat case holds, or there are laws at the vertices of a tower of
  `SL_h(F₂)` with `h ≥ 4`, over a finitely generated subring of `ℚ`, whose length bound `2 C₁ a₁²`
  is an integer.
* In the contracting case, the laws of Theorem G.2 at the vertices of every tower
  `SLTower.tower h n` (by `VertexLaws.transfer`), with the same contraction. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationLawExistence

open Cslib Cslib.Circuits.Arithmetic.Separation Cslib.Circuits.Arithmetic.Separation.TowerPlan
  Cslib.Circuits.Arithmetic.Separation.TwoCases

/-- Over `ℚ`: the flat case, or laws at the vertices of a tower of `SL_h(F₂)` with `h ≥ 4` over a
finitely generated subring, whose length bound `2 C₁ a₁²` is an integer. -/
example : FlatCase ℚ ∨ ∃ (h : ℕ) (_ : NeZero h) (h3 : 3 ≤ h) (A : Subring ℚ),
    Algebra.FiniteType ℤ A ∧ 4 ≤ h ∧ ∃ FL : VertexLaws A (SLTower.tower h 0 (by omega)),
      ∃ g : ℕ, 2 * FL.contraction * (FL.scale : ℝ) ^ 2 = g := by
  refine (flatCase_or_contractingCase ℚ).imp_right fun hK => ?_
  obtain ⟨h, hh, h3, A, hA, FL, hC, hG⟩ := Laws.exists_vertexLaws hK
  refine ⟨h, hh, h3, A, hA, ?_, FL, FL.lengthBound, hG.symm⟩
  have := FL.contraction_nonneg
  exact_mod_cast (by linarith : (4 : ℝ) ≤ h)

/-- In the contracting case the laws of Theorem G.2 are at the vertices of every tower
`SLTower.tower h n`, with the same contraction. -/
example {K : Type} [Field K] (hK : ContractingCase K) :
    ∃ (h : ℕ) (_ : NeZero h) (h3 : 3 ≤ h) (A : Subring K), Algebra.FiniteType ℤ A ∧
      ∀ n, ∃ FL : VertexLaws A (SLTower.tower h n (by omega)),
        1 + 8 * FL.contraction ≤ (h : ℝ) / 4 := by
  obtain ⟨h, hh, h3, A, hA, FL, hC, -⟩ := Laws.exists_vertexLaws hK
  exact ⟨h, hh, h3, A, hA, fun n => ⟨FL.transfer _ (Equiv.refl _) (Equiv.refl _) fun _ => rfl, hC⟩⟩

end CslibFrontierTests.SeparationLawExistence
