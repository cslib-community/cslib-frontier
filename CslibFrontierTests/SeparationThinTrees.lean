/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Laws.Existence
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Trees.Existence
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Cube
import CslibFrontier.Foundations.Data.Nat.Power

/-! Tests of the thin trees (Theorem H.2), as a client that sees only the public statements. The
tree of the tower plan on the tower with one edge is tested with the fixtures of the tower plan,
in `CslibFrontierTests/SeparationTowerPlan.lean`.

* A factor absorbed in a power (`Nat.mul_pow_le_pow_of_add_le`).
* Over `ℚ`, by Theorem D.2, Theorem G.2 and Theorem H.2: the flat case holds, or there are thin
  trees for networks on two given nodes with one unit of one bit at a node, over a finitely
  generated subring of `ℚ`, with an integer test `2 C₁ a₁²` of the law moves.
* Theorem H.2(b) at a node for thin trees on at most `4` nodes with `γ = 1 / 2`, good outcomes and
  at most `N` initial units at every base party: the units in the end at a node, other than the
  dead ones, are at most `2 · 3 ^ C (N + 16)`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationThinTrees

open Cslib Cslib.Circuits.Arithmetic.Separation Cslib.Circuits.Arithmetic.Separation.Cut
  Cslib.Circuits.Arithmetic.Separation.Trees
  Cslib.Circuits.Arithmetic.Separation.TwoCases

/-- The factor `3` is absorbed in `2 ^ 3`: `3 · 2 ^ 2 ≤ 2 ^ 5`. -/
example : 3 * 2 ^ 2 ≤ 2 ^ 5 := Nat.mul_pow_le_pow_of_add_le le_rfl le_rfl

/-- **Thin trees over `ℚ`**: the flat case holds, or there are thin trees for networks on two
given nodes, with at most one unit of one bit at a node and at most two nodes, over a finitely
generated subring of `ℚ`, whose test of the law moves is the integer `2 C₁ a₁²`. -/
example : FlatCase ℚ ∨ ∃ (A : Subring ℚ) (laws : List (Cut.Law A)) (b G C : ℕ) (γ : ℝ),
    Algebra.FiniteType ℤ A ∧ Nonempty (ThinTrees laws 2 1 1 2 b G C γ) := by
  refine (flatCase_or_contractingCase ℚ).imp_right fun hK => ?_
  obtain ⟨h, hh, h3, A, hA, FL, hC, -⟩ := Laws.exists_vertexLaws hK
  obtain ⟨C, hT⟩ := exists_thinTrees h3 FL hC
  exact ⟨A, _, _, _, C, _, hA, hT A 2 2 1 1 le_rfl le_rfl le_rfl le_rfl⟩

variable {R : Type*} [CommSemiring R] {laws : List (Cut.Law R)} {A N ℓ M b G C : ℕ} {γ : ℝ}

/-- **Theorem H.2(b)** at a node for thin trees on at most `4` nodes with `γ = 1 / 2`: for good
outcomes and at most `N` initial units at every base party, the units in the end at a node that are
not dead and join two parties are at most `2 · 3 ^ C (N + 16)`, as `lg 4 = 3` and
`4 ^ (1 - 1 / 2) = 2`. -/
example (TT : ThinTrees laws A N ℓ 4 b G C (1 / 2)) {n : Fin A → Fin A → Fin (N + 1)}
    (hn : ∀ a, ∑ c, ((n a c : ℕ) + n c a) ≤ N) {o : TT.moves.Channel → Fin TT.U1}
    (hg : ∀ x, TT.plan.Good n o x) (p : Fin (A + TT.A')) :
    (((Play.cutUnits (UnitId.holder TT.moves.channelParty) id
        (TT.plan.cur n o TT.E \ TT.dead o)).filter
      (Play.Holds (UnitId.holder TT.moves.channelParty) p)).card : ℝ) ≤ 2 * 3 ^ C * (N + 16) := by
  have hlg : Interpreter.lg 4 = 3 := by
    rw [Interpreter.lg, show 4 = 2 ^ 2 by rfl, Nat.log_pow one_lt_two]
  have hpow : (4 : ℝ) ^ (1 - 1 / 2 : ℝ) = 2 := by
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
  refine (TT.card_filter_holds_le hn hg p).trans_eq ?_
  rw [hlg, Nat.cast_ofNat, hpow]
  push_cast
  ring

end CslibFrontierTests.SeparationThinTrees
