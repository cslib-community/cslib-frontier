/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Strategic.Universality.DattaBinary
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Datta's binary game on a quadratic

The system `F₀(x) = 4 x² - 1 = 0` has the single root `x = 1/2` in `(0, 1)`. Datta's binary game
with degree bound `d = 3` has `1 · 3 + max(1, 1) = 4` players, and its totally mixed Nash
equilibria are the profiles with `x = 1/2`, chain players `1/2, 1/4, 1/8`, and no extra players.
That profile is a totally mixed Nash equilibrium.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.DattaBinary

open MvPolynomial Cslib.GameTheory Cslib.GameTheory.DattaBinary

/-- `4 x² - 1`. -/
noncomputable def quad : Fin 1 → MvPolynomial (Fin 1) ℝ :=
  fun _ => monomial (Finsupp.single 0 2) 4 - monomial 0 1

example : Fintype.card (Player 1 3 1) = 4 := by
  rw [card_player]
  rfl

theorem quad_degree : ∀ j, ∀ e ∈ (quad j).support, ∀ i, e i ≤ 3 := by
  classical
  intro j e he i
  rcases Finset.mem_union.1 (support_sub (Fin 1) _ _ he) with h | h <;>
    rw [Finset.mem_singleton.1 (support_monomial_subset h)] <;> fin_cases i <;> simp

/-- The totally mixed equilibria of Datta's binary game for `4 x² - 1`. -/
example (q : Player 1 3 1 → ℝ) :
    (game (d := 3) quad).IsTotallyMixedNash (binaryProfile q) ↔
      (∀ v, 0 < q v ∧ q v < 1) ∧ (4 * q (var 0) ^ 2 - 1 = 0) ∧
        ∀ c : Fin 1 × Fin 3, q (chain c) = q (var c.1) ^ (c.2.val + 1) := by
  rw [isTotallyMixedNash_game_iff quad_degree (by norm_num)]
  simp [quad, Fin.forall_fin_one, eval_monomial]

/-- The root `x = 1/2` with its powers `1/2, 1/4, 1/8`. -/
noncomputable def root : Player 1 3 1 → ℝ
  | .inl _ => 1 / 2
  | .inr (.inl c) => (1 / 2) ^ (c.2.val + 1)
  | .inr (.inr e) => e.elim0

/-- The root, with its powers on the chain players, is a totally mixed Nash equilibrium. -/
example : (game (d := 3) quad).IsTotallyMixedNash (binaryProfile root) := by
  rw [isTotallyMixedNash_game_iff quad_degree (by norm_num)]
  refine ⟨fun v => ?_, fun j => ?_, fun c => ?_⟩
  · rcases v with i | c | e
    · norm_num [root]
    · fin_cases c <;> norm_num [root]
    · exact e.elim0
  · norm_num [quad, eval_monomial, root]
  · simp [root]

end CslibFrontierTests.GameTheory.DattaBinary
