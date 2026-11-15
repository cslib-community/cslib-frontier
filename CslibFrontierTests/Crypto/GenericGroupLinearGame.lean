/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.GenericGroup.LinearGame
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

/-!
# The generic-group bound for games with linear inputs: an ordinary client

Uses the public API of `CslibFrontier.Crypto.Computational.GenericGroup.LinearGame` through an
ordinary import:

* square Diffie–Hellman, a game that is neither discrete logarithm nor computational
  Diffie–Hellman, as an instance of `linearGame`: from the labels of `1` and `x`, output the label
  of `x²`. An adversary that makes at most `T` queries wins with probability at most
  `C(3T + 3, 2) / q + 2 / q`, because a quadratic equation has at most two roots in `ZMod q`;
* primality is needed for two unknowns as for one: in `ZMod 4` the distinct linear forms
  `2 X + 2 Y` and `0` agree at `8` of the `16` points;
* the hypothesis on `W` cannot be dropped: with `W` constantly true, no unknowns and no output
  labels, the adversary that returns at once without a query wins with probability `1`, where the
  conclusion with `ε = 0` would give `0`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GenericGroupLinearGame

open Cslib Cslib.Crypto Cslib.Crypto.GenericGroup
open scoped NNReal

variable {q : ℕ} {S : Type}

/-! ### Square Diffie–Hellman -/

/-- Square Diffie–Hellman in the generic group model: the adversary gets the labels of `1` and of
a uniform `x`, and wins when it outputs the label of `x²`. -/
private noncomputable def sqdhGame [NeZero q] [Fintype S] [DecidableEq S] [Nonempty (ZMod q ↪ S)]
    (A : S → S → ProbOracleComp (GroupOracleSpec q S) S) : Game :=
  linearGame (ι := Unit) (κ := Unit) (fun x _ v => decide (v () = x () * x ()))
    fun g u => (fun w => ((), fun _ => w)) <$> A g (u ())

/-- Over `ZMod q`, `q` prime, the equation `y² = a y + b` has at most two solutions: with one
solution `r`, every other is `a - r`. -/
private theorem card_filter_sq_eq_le [Fact q.Prime] (a b : ZMod q) :
    (Finset.univ.filter fun y : ZMod q => y * y = a * y + b).card ≤ 2 := by
  by_cases h : ∃ r : ZMod q, r * r = a * r + b
  · obtain ⟨r, hr⟩ := h
    refine (Finset.card_le_card fun y hy => ?_).trans (Finset.card_le_two (a := r) (b := a - r))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hy' : (y - r) * (y - (a - r)) = 0 := by linear_combination hy - hr
    rcases mul_eq_zero.mp hy' with hy' | hy'
    · exact Finset.mem_insert.mpr (Or.inl (sub_eq_zero.mp hy'))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (sub_eq_zero.mp hy')))
  · simp [not_exists.mp h]

/-- **Square Diffie–Hellman in the generic group model.** For prime `q`, an adversary that makes
at most `T` queries outputs the label of `x²` with probability at most
`C(3T + 3, 2) / q + 2 / q`. -/
example [NeZero q] [Fintype S] [DecidableEq S] [Nonempty (ZMod q ↪ S)] (hq : q.Prime) {T : ℕ}
    {A : S → S → ProbOracleComp (GroupOracleSpec q S) S} (hA : ∀ g u, (A g u).IsQueryBounded T) :
    (sqdhGame A).succProbability ≤ ((3 * T + 3).choose 2 : ℕ) / q + 2 / q := by
  have : Fact q.Prime := ⟨hq⟩
  refine (succProbability_linearGame_le hq (fun x _ v => decide (v () = x () * x ()))
    (A := fun g u => (fun w => ((), fun _ => w)) <$> A g (u ()))
    (fun g u => (OracleComp.isCostBounded_map_iff _ _ _).mpr (hA g (u ()))) (2 / q)
    fun _ F => ?_).trans_eq ?_
  · rw [Fintype.card_unit, pow_one, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hq.ne_zero)]
    norm_cast
    refine (Finset.card_le_card_of_injOn (fun x : Unit → ZMod q => x ()) ?_ ?_).trans
      (card_filter_sq_eq_le ((F ()).1 ()) (F ()).2)
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Fintype.sum_unique, decide_eq_true_eq] at hx ⊢
      exact hx.symm
    · intro x _ y _ hxy
      funext u
      exact hxy
  · rw [Fintype.card_unit]

/-! ### Where primality is used -/

/-- Over `ZMod 4`, which is not a field, the distinct linear forms `2 X + 2 Y` and `0` in two
unknowns agree at `8` of the `16` points, where over a field of order `4` they would agree at no
more than `4`. -/
example : (Finset.univ.filter fun p : ZMod 4 × ZMod 4 =>
    2 * p.1 + 2 * p.2 + 0 = 0 * p.1 + 0 * p.2 + 0).card = 8 := by
  decide

/-! ### The hypothesis on `W` cannot be dropped -/

/-- With `W` constantly true, no unknowns and no output labels, the adversary that returns at once
always wins. -/
private theorem succProbability_trivial [NeZero q] [Fintype S] [DecidableEq S]
    [Nonempty (ZMod q ↪ S)] :
    (linearGame (q := q) (S := S) (ι := Empty) (κ := Empty) (γ := Unit) (fun _ _ _ => true)
      fun _ _ => pure ((), Empty.elim)).succProbability = 1 := by
  simp [linearGame, runLabeled, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, Game.succProbability]

/-- That adversary makes no query, and the conclusion of `succProbability_linearGame_le` with
`ε = 0` would bound its success probability by `C(1, 2) / q = 0`. -/
example [NeZero q] [Fintype S] [DecidableEq S] [Nonempty (ZMod q ↪ S)] :
    ¬ (linearGame (q := q) (S := S) (ι := Empty) (κ := Empty) (γ := Unit) (fun _ _ _ => true)
      fun _ _ => pure ((), Empty.elim)).succProbability ≤
      (((3 * 0 + Fintype.card Empty + 1 + Fintype.card Empty).choose 2 : ℕ) : ℝ≥0) / q + 0 := by
  rw [succProbability_trivial]
  simp

end CslibFrontierTests.Crypto.GenericGroupLinearGame
