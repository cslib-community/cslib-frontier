/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Strategic.Universality.DattaThree
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The three-player game on a quadratic

The system `F₀(x) = 4 x² - 1 = 0` has the single root `x = 1/2` in the open simplex `0 < x < 1`.
With degree bound `d = 2`, Alice, Bob and Critter have `2`, `4` and `5` pure strategies. The
totally mixed Nash equilibria have `x = 1/2`, Bob playing the monomials `1, x, x²` with weights
`1/4, 1/8, 1/16`, and Critter uniform. That profile is a totally mixed Nash equilibrium.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.DattaThree

open MvPolynomial Cslib.GameTheory Cslib.GameTheory.DattaThree

/-- `4 x² - 1`. -/
noncomputable def quad : Fin 1 → MvPolynomial (Fin 1) ℝ :=
  fun _ => monomial (Finsupp.single 0 2) 4 - monomial 0 1

example : Fintype.card (Option (Strat 1 2 1 .alice)) = 2 ∧
    Fintype.card (Option (Strat 1 2 1 .bob)) = 4 ∧
    Fintype.card (Option (Strat 1 2 1 .critter)) = 5 :=
  card_strategies

theorem quad_degree : ∀ j, ∀ s ∈ (quad j).support, ∀ i, s i ≤ 2 := by
  classical
  intro j s hs i
  rcases Finset.mem_union.1 (support_sub (Fin 1) _ _ hs) with h | h <;>
    rw [Finset.mem_singleton.1 (support_monomial_subset h)] <;> fin_cases i <;> simp

/-- The root `x = 1/2`, Bob's monomial weights `(1/2)ᵉ / 4`, and Critter uniform. -/
noncomputable def root : Coord 1 2 1 → ℝ
  | ⟨.alice, _⟩ => 1 / 2
  | ⟨.bob, e⟩ => (1 / 2) ^ (e 0 : ℕ) / 4
  | ⟨.critter, _⟩ => 1 / 5

/-- The root, with its monomials on Bob and Critter uniform, is a totally mixed Nash
equilibrium. -/
example : (game (d := 2) quad).IsTotallyMixedNash (simplexProfile root) := by
  rw [isTotallyMixedNash_game_iff quad_degree]
  refine ⟨⟨fun i => ?_, ?_, fun j => ?_⟩, fun e => ?_, fun e => ?_, fun j _ => ?_, fun j => ?_, ?_⟩
  · norm_num [root]
  · norm_num [root]
  · norm_num [quad, eval_monomial, root]
  · simp [root, expoPow, bobScale]
    norm_num
  · norm_num [root, critterWeight]
  · norm_num [root, critterWeight]
  · norm_num [root]
  · simp [root]
    norm_num

end CslibFrontierTests.GameTheory.DattaThree
