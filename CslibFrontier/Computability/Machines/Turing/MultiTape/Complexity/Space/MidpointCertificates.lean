/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.Savitch
public import Mathlib.Data.List.Chain
public import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Basic

/-!
# Exact certificates in deterministic midpoint verification

This is the literal midpoint recurrence for a deterministic transition function. Its
base case checks exactly one transition. Each higher level consumes a midpoint and a bit
selecting a half, giving exact reachability after `2 ^ depth` transitions.
Frontier's Savitch machine formalizes bounded graph reachability with a native resource
bound. The present theorems count only the quantifiers and certificate bits of the
literal deterministic protocol.

## Main definitions

* `midpointCheck`, `midpointSchedule`, `midpointBits`.

## Main results

* `midpointCheck_iff` proves exact-step semantics.
* `reach_of_midpointCheck` relates this specialization to Frontier's native Savitch recursion.
* `midpointBits_exact` and `midpointSchedule_alternates` account for a verification branch.

## References

* [S. Arora, B. Barak, Computational Complexity, Theorem 4.13][AroraBarak09]
  gives the underlying divide-and-conquer reachability strategy.
-/

public section

namespace Cslib.Reachability

/-- Literal midpoint protocol for a deterministic run of exactly 2^depth
steps. After the existential midpoint, a universal bit chooses a half run. -/
def midpointCheck {State : Type} (step : State → State) :
    ℕ → State → State → Prop
  | 0, a, b => step a = b
  | depth + 1, a, b => ∃ m, ∀ right : Bool,
      if right then midpointCheck step depth m b else midpointCheck step depth a m

/-- The literal protocol checks exactly the advertised number of steps. -/
theorem midpointCheck_iff {State : Type} (step : State → State)
    (depth : ℕ) (a b : State) :
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
      refine ⟨step^[2 ^ depth] a, ?_⟩
      intro right
      cases right
      · exact (ih a _).mpr rfl
      · exact (ih _ b).mpr h

/-- Exact deterministic midpoint verification supplies a witness for the native bounded
reachability recursion whenever the transition preserves the configured word width. -/
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
    have widths (n : ℕ) : (step^[n] u).length = w := by
      induction n with
      | zero => exact hu
      | succ n hn => rw [Function.iterate_succ_apply']; exact preserves _ hn
    have hm : m.length = w :=
      (midpointCheck_iff step depth u m).mp left ▸ widths _
    simp only [reach, List.any_eq_true, Bool.and_eq_true, Cslib.BitString.mem_enumList]
    exact ⟨m, hm, ih u m hu left, ih m v hm right⟩

/-- The two quantifier roles on a verification branch. -/
inductive MidpointQuantifier where
  | existsMidpoint
  | forallBranch

/-- Quantifier schedule along any branch of the literal protocol. -/
@[expose] def midpointSchedule : ℕ → List MidpointQuantifier
  | 0 => []
  | depth + 1 => .existsMidpoint :: .forallBranch :: midpointSchedule depth

/-- Each symbol in the schedule is its own block because adjacent symbols differ. -/
theorem midpointSchedule_length (depth : ℕ) :
    (midpointSchedule depth).length = 2 * depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [midpointSchedule, ih, Nat.mul_succ]

/-- Adjacent certificates are supplied at opposite quantifier polarities. -/
theorem midpointSchedule_alternates (depth : ℕ) :
    (midpointSchedule depth).IsChain (· ≠ ·) := by
  induction depth with
  | zero => simp [midpointSchedule]
  | succ depth ih =>
    cases depth with
    | zero => simp [midpointSchedule, reduceCtorEq]
    | succ depth =>
      change List.IsChain (· ≠ ·)
        (.existsMidpoint :: .forallBranch :: .existsMidpoint :: .forallBranch ::
          midpointSchedule depth)
      rw [List.isChain_cons_cons, List.isChain_cons_cons]
      exact ⟨(fun h => nomatch h), (fun h => nomatch h), ih⟩

/-- Charged bits along one verification branch for a fixed configuration width. -/
@[expose] def midpointBits (width : ℕ) : ℕ → ℕ
  | 0 => 0
  | depth + 1 => width + 1 + midpointBits width depth

/-- At each level, charge one midpoint configuration and one branch bit. -/
theorem midpointBits_exact (width depth : ℕ) :
    midpointBits width depth = depth * (width + 1) := by
  induction depth with
  | zero => simp [midpointBits]
  | succ depth ih =>
    rw [midpointBits, ih, Nat.succ_mul, Nat.add_comm]

/-- A schedule of at most two blocks checks at most two steps by this rule. -/
theorem midpoint_two_block_limit (depth : ℕ)
    (h : (midpointSchedule depth).length ≤ 2) : 2 ^ depth ≤ 2 := by
  rw [midpointSchedule_length] at h
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (show depth ≤ 1 by omega)

end Cslib.Reachability
