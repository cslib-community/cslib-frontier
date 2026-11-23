/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Machines.Turing.SingleTape.Copy
import Mathlib.Tactic.NormNum

/-!
# Tests for the communication-to-crossing-sequence transfer

A concrete two-step machine exercises false-colored fooling sets: its two rejecting inputs
halt over different symbols. The crossing-sequence injection must therefore preserve the Boolean
verdict rather than demand one common rejecting symbol. Additional tests cover an empty prefix,
the zero counting threshold, and the unmarked copy language's input and time-bound interfaces.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.SingleTapeFoolingSet

open Cslib Cslib.Turing SingleTapeTM Relation

/-- Binary inputs use symbols `0` and `1`; `2` is reserved for acceptance. -/
private def bit (b : Bool) : Fin 3 := if b then 1 else 0

/-- The first two input bits differ; short words are rejected and later bits are ignored. -/
private def firstTwoDiffer : Language Bool := {w | match w with
  | x :: y :: _ => x ≠ y
  | _ => False}

/-- Remember the first bit, move right, then accept exactly when the second bit differs.
On rejection the scanned symbol is left untouched, so `00` and `11` have different outputs. -/
private def xorMachine : SingleTapeTM (Fin 3) where
  State := Option Bool
  q₀ := none
  tr q s := match q with
    | none => (⟨s, some .right⟩, some (some (s == some 1)))
    | some b => (⟨if s = some (bit (!b)) then some 2 else s, none⟩, none)

private lemma xorMachine_decides :
    xorMachine.DecidesByHeadInTime bit firstTwoDiffer 2 (fun _ => 2) := by
  intro w
  refine ⟨_, RelatesWithinSteps.trans (n₁ := 1) (n₂ := 1)
    (RelatesWithinSteps.single rfl) (RelatesWithinSteps.single rfl), rfl, ?_⟩
  change _ ↔ match w with
    | x :: y :: _ => x ≠ y
    | _ => False
  rcases w with _ | ⟨x, _ | ⟨y, w⟩⟩
  · decide
  · cases x <;> decide
  · cases x <;> cases y
    · change (some (0 : Fin 3) = some 2 ↔ false ≠ false)
      decide
    · change (some (2 : Fin 3) = some 2 ↔ false ≠ true)
      decide
    · change (some (2 : Fin 3) = some 2 ↔ true ≠ false)
      decide
    · change (some (1 : Fin 3) = some 2 ↔ true ≠ true)
      decide

/-- These runs reject over `0` and `1`, respectively, rather than a shared rejecting symbol. -/
example : ((xorMachine.absInit [0, 0]).run 2).scanned = some 0 ∧
    ((xorMachine.absInit [1, 1]).run 2).scanned = some 1 := by decide

private def diagonal : Finset (Bool × Bool) := {(false, false), (true, true)}

private lemma diagonal_fools : Communication.IsFoolingSet Bool.xor false diagonal := by
  simp [Communication.IsFoolingSet, diagonal]

private lemma restriction (x y : Bool) :
    [x] ++ [] ++ [y] ∈ firstTwoDiffer ↔ Bool.xor x y = true := by
  change x ≠ y ↔ Bool.xor x y = true
  cases x <;> cases y <;> decide

/-- Apply the new theorem with color `false`; both mixed inputs are accepting. -/
example : (xorMachine.absInit [0, 0]).crossings 1 2 ≠
    (xorMachine.absInit [1, 1]).crossings 1 2 := by
  have hinj := crossings_injOn_of_isFoolingSet xorMachine_decides diagonal_fools
    (fun x => [x]) [] (fun y => [y]) restriction
    (m := 1) (fun _ _ => rfl) (i := 0) (by simp)
  intro h
  have hp : (false, false) = (true, true) :=
    hinj (by simp [diagonal]) (by simp [diagonal]) h
  exact Bool.false_ne_true (congrArg Prod.fst hp)

/-- A singleton restriction can start at boundary zero: no positive-prefix hypothesis is needed. -/
example : Set.InjOn (fun _ : Unit × Unit => (xorMachine.absInit []).crossings 0 2)
    (({((), ())} : Finset (Unit × Unit)) : Set (Unit × Unit)) := by
  apply crossings_injOn_of_isFoolingSet xorMachine_decides
    (f := fun _ _ : Unit => false) (z := false) (S := {((), ())})
    (by simp [Communication.IsFoolingSet]) (fun _ => []) [] (fun _ => [])
    (by intro x y; change False ↔ false = true; decide)
    (m := 0) (fun _ _ => rfl) (i := 0) (by simp)

/-- The finite counting theorem includes threshold zero even for a nonempty fooling set. -/
example :
    (0 + 1) * (diagonal.card - (Fintype.card (Option xorMachine.State) + 1) ^ 0) * 0 ≤
      diagonal.card * 2 :=
  crossing_foolingSet_bound xorMachine_decides diagonal_fools
    (fun x => [x]) [] (fun y => [y]) restriction
    (m := 1) (n := 2) (fun _ _ => rfl) (fun _ _ => rfl) 0

/-- Copying is unmarked and includes the empty word. -/
example : ([] : List Bool) ∈ Cslib.Language.copy Bool := ⟨[], rfl⟩

example : [false, true, false, true] ∈ Cslib.Language.copy Bool := ⟨[false, true], rfl⟩

/-- An odd-length word cannot be a concatenation of two copies. -/
example : [false] ∉ Cslib.Language.copy Bool := by
  rintro ⟨x, hx⟩
  have hlen := congrArg List.length hx
  simp only [List.length_cons, List.length_nil, List.length_append] at hlen
  omega

/-- Even length alone does not suffice: the two halves must coincide. -/
example : [false, true, true, false] ∉ Cslib.Language.copy Bool := by
  change [false, true] ++ [true, false] ∉ Cslib.Language.copy Bool
  rw [Cslib.Language.append_mem_copy_iff (by decide)]
  decide

/-- Instantiate the quadratic bound on a finite machine to rule out a linear copy decider. -/
example : ¬ xorMachine.DecidesByHeadInTime bit (Cslib.Language.copy Bool) 2
    (fun n => n + 1) := by
  intro hdec
  have hd : Nat.clog 2 (Fintype.card xorMachine.State + 2) = 3 := by decide
  have h := copy_lower_bound hdec (n := 128) (by rw [hd]; decide)
  rw [hd] at h
  norm_num at h

end CslibFrontierTests.SingleTapeFoolingSet
