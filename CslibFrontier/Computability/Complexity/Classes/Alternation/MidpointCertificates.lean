/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.Savitch
public import CslibFrontier.Computability.Complexity.Classes.PH
public import Mathlib.Logic.Function.Iterate
import CslibFrontier.Computability.Complexity.Classes.Alternation.Game
import Mathlib.Data.List.GetD
import Mathlib.Data.Set.Function

/-!
# Exact certificates in deterministic midpoint verification

The midpoint recurrence specializes the alternating reachability subroutine of
[Chandra, Kozen and Stockmeyer, proof of Theorem 3.1][ChandraKozenStockmeyer1981] to runs of
exactly `2 ^ depth` deterministic transitions. The existential player supplies a midpoint of
width `w` at each level and the universal player selects one half with a single bit. The branch
verifier uses `Cslib.Complexity.Alternation` to quantify these moves in `2 * depth` blocks,
with `depth * (w + 1)` bits along a branch.

For width-preserving transitions, an exact run also witnesses a bounded walk in
`Cslib.Reachability.reach`. The counts here describe the certificate for the exact run.
`Cslib.Reachability.midpointGame` uses paired single-bit moves for the bounded-walk game.

## Main definitions

* `midpointCheck`: the midpoint predicate for an exact deterministic run.
* `midpointBlocks`: the widths of the alternating midpoint and half-selection blocks.
* `midpointVerify`: verification of a single branch from a word of certificate bits.

## Main results

* `midpointCheck_iff`: the midpoint predicate holds exactly when the prescribed iterate succeeds.
* `reach_of_midpointCheck`: the exact run implies bounded reachability.
* `midpointCheck_of_alternation_midpointVerify`: a winning certificate game implies an exact run.
* `alternation_midpointVerify_iff`: on fixed-width words, a winning game is equivalent to an exact
  run.
* `midpointBlocks_length`: the number of quantifier blocks in the certificate game.
* `midpointBlocks_sum`: the number of certificate bits along one branch.

## References

* [Chandra, Kozen and Stockmeyer, *Alternation*, Theorem 3.1][ChandraKozenStockmeyer1981]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 5.3][AroraBarak09]
-/

public section

namespace Cslib.Reachability

open Cslib.Complexity

/-- Midpoint predicate for a deterministic run of exactly `2 ^ depth` steps.
After the existential midpoint, a universal bit chooses a half run. -/
@[expose] def midpointCheck {State : Type*} (step : State → State) :
    ℕ → State → State → Prop
  | 0, a, b => step a = b
  | depth + 1, a, b => ∃ m, ∀ right : Bool,
      if right then midpointCheck step depth m b else midpointCheck step depth a m

/-- The midpoint predicate holds exactly when the run reaches `b` after `2 ^ depth` steps. -/
theorem midpointCheck_iff {State : Type*} (step : State → State) (depth : ℕ) (a b : State) :
    midpointCheck step depth a b ↔ step^[2 ^ depth] a = b := by
  induction depth generalizing a b with
  | zero => simp [midpointCheck]
  | succ depth ih =>
    have splitRun : step^[2 ^ (depth + 1)] a =
        step^[2 ^ depth] (step^[2 ^ depth] a) := by
      rw [Nat.pow_succ, Nat.mul_two, Function.iterate_add_apply]
    rw [splitRun]
    constructor
    · rintro ⟨m, h⟩
      rw [(ih a m).mp (h false)]
      exact (ih m b).mp (h true)
    · intro h
      exact ⟨step^[2 ^ depth] a, Bool.forall_bool.mpr ⟨(ih a _).mpr rfl, (ih _ b).mpr h⟩⟩

/-- Every endpoint of an exact run from a word of width `w` has width `w`
when the transition preserves that width. -/
private theorem length_of_midpointCheck {step : List Bool → List Bool} {w depth : ℕ}
    {u v : List Bool} (preserves : ∀ a, a.length = w → (step a).length = w)
    (hu : u.length = w) (check : midpointCheck step depth u v) : v.length = w := by
  have h : Set.MapsTo step {a | a.length = w} {a | a.length = w} := fun a ha => preserves a ha
  exact (midpointCheck_iff step depth u v).mp check ▸ h.iterate (2 ^ depth) hu

/-- An exact deterministic run witnesses bounded reachability by `Cslib.Reachability.reach`
whenever the transition preserves the configured word width. -/
theorem reach_of_midpointCheck (step : List Bool → List Bool) (w depth : ℕ) (u v : List Bool)
    (preserves : ∀ a, a.length = w → (step a).length = w) (hu : u.length = w)
    (check : midpointCheck step depth u v) :
    reach (fun a b => decide (step a = b)) w depth u v = true := by
  induction depth generalizing u v with
  | zero =>
    have h : step u = v := check
    simp [reach, h]
  | succ depth ih =>
    obtain ⟨m, moves⟩ := check
    have left : midpointCheck step depth u m := moves false
    have right : midpointCheck step depth m v := moves true
    have hm := length_of_midpointCheck preserves hu left
    simp only [reach, List.any_eq_true, Bool.and_eq_true, Cslib.BitString.mem_enumList]
    exact ⟨m, hm, ih u m hu left, ih m v hm right⟩

/-- Block widths for `Alternation true` in the exact midpoint game.
Each level has an existential block of width `w` and a universal block of width one. -/
@[expose] def midpointBlocks (w : ℕ) : ℕ → List ℕ
  | 0 => []
  | depth + 1 => w :: 1 :: midpointBlocks w depth

/-- Verify a branch of the exact midpoint game. Read the first `w` bits as the midpoint, then
read the half selector and recur on the remaining bits. The leaf checks one transition. -/
@[expose] def midpointVerify (step : List Bool → List Bool) (w : ℕ) :
    ℕ → List Bool → List Bool → List Bool → Bool
  | 0, u, v, _ => decide (step u = v)
  | depth + 1, u, v, z =>
    let m := z.take w
    let rest := z.drop (w + 1)
    if z.getD w false then midpointVerify step w depth m v rest
    else midpointVerify step w depth u m rest

/-- Split one round of the certificate game into a fixed-width midpoint and both half games. -/
private theorem alternation_midpointVerify_succ (step : List Bool → List Bool) (w depth : ℕ)
    (u v : List Bool) :
    Alternation true (midpointBlocks w (depth + 1))
        (fun z => midpointVerify step w (depth + 1) u v z = true) ↔
      ∃ m : List Bool, m.length = w ∧
        Alternation true (midpointBlocks w depth) (fun z => midpointVerify step w depth u m z) ∧
        Alternation true (midpointBlocks w depth) (fun z => midpointVerify step w depth m v z) := by
  rw [midpointBlocks, alternation_true_cons]
  simp only [alternation_false_one_cons, Bool.forall_bool]
  refine exists_congr fun m => and_congr_right fun hm => ?_
  subst w
  simp only [midpointVerify, List.take_append_length, List.getD_append_right _ _ _ _ le_rfl,
    Nat.sub_self, List.getD_cons_zero, List.drop_length_add_append, List.drop_succ_cons,
    List.drop_zero, Bool.false_eq_true, ite_false, ite_true]

/-- Winning the exact midpoint game implies the exact midpoint predicate. -/
theorem midpointCheck_of_alternation_midpointVerify (step : List Bool → List Bool)
    (w depth : ℕ) (u v : List Bool)
    (h : Alternation true (midpointBlocks w depth) (fun z => midpointVerify step w depth u v z)) :
    midpointCheck step depth u v := by
  induction depth generalizing u v with
  | zero => simpa only [midpointBlocks, alternation_nil, midpointVerify, decide_eq_true_eq,
      midpointCheck] using h
  | succ depth ih =>
    obtain ⟨m, _, left, right⟩ := (alternation_midpointVerify_succ step w depth u v).mp h
    exact ⟨m, Bool.forall_bool.mpr ⟨ih u m left, ih m v right⟩⟩

/-- For width-preserving transitions, the alternating certificate verifies exactly the
deterministic runs of length `2 ^ depth` starting from a word of width `w`. -/
theorem alternation_midpointVerify_iff (step : List Bool → List Bool) (w depth : ℕ)
    (u v : List Bool) (preserves : ∀ a, a.length = w → (step a).length = w) (hu : u.length = w) :
    Alternation true (midpointBlocks w depth) (fun z => midpointVerify step w depth u v z = true) ↔
      midpointCheck step depth u v := by
  refine ⟨midpointCheck_of_alternation_midpointVerify step w depth u v, ?_⟩
  intro check
  induction depth generalizing u v with
  | zero => simpa only [midpointBlocks, alternation_nil, midpointVerify, decide_eq_true_eq,
      midpointCheck] using check
  | succ depth ih =>
    obtain ⟨m, moves⟩ := check
    have left : midpointCheck step depth u m := moves false
    have hm := length_of_midpointCheck preserves hu left
    exact (alternation_midpointVerify_succ step w depth u v).mpr
      ⟨m, hm, ih u m hu left, ih m v hm (moves true)⟩

/-- The exact midpoint game has one pair of quantifier blocks per level. -/
theorem midpointBlocks_length (w depth : ℕ) : (midpointBlocks w depth).length = 2 * depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [midpointBlocks, ih, Nat.mul_succ, Nat.add_assoc]

/-- The certificate along a branch has `w + 1` bits for each level. -/
theorem midpointBlocks_sum (w depth : ℕ) : (midpointBlocks w depth).sum = depth * (w + 1) := by
  induction depth with
  | zero => simp [midpointBlocks]
  | succ depth ih =>
    rw [midpointBlocks, List.sum_cons, List.sum_cons, ih, Nat.succ_mul, ← Nat.add_assoc,
      Nat.add_comm (w + 1)]

end Cslib.Reachability
