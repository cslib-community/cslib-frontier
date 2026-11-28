/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.IP.PSPACE

/-!
# Tests for the evaluation of a verifier after a history

A one-message verifier `verifier` sends `[true]`, then accepts exactly when the reply starts with
`false`; it flips no coin. With `3` coins (its three instructions) its `8` coin values all accept
after the history `[([true], [false])]`. The checked facts are the values of the evaluator
`Cslib.Complexity.Interaction.evalFrom` on nonempty histories, through
`Cslib.Complexity.Interaction.evalFrom_eq`:

* the accepting continuation `[([true], [false])]` has value `8`;
* the continuation `[([true], [true])]` follows the verifier but rejects, with value `0`;
* the history `[([false], [false])]` answers a message that the verifier does not send; the shift
  construction `Cslib.Complexity.Interaction.shiftFamily` maps this invalid prefix to rejection,
  so its value is `0` although the same reply is accepted after the right message.

The evaluator itself runs for `2 ^ ((t + 1) * (2 * t + 1))` iterations, so it is not unfolded;
the values are computed on the characterization side, as the values of the coin programs.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Complexity.Classes.IP.PSPACE

open Cslib Cslib.Complexity Cslib.Complexity.Interaction Turing

/-- The verifier: send `[true]`, then output `[true]` exactly when the reply starts with `false`. -/
private def verifier : MultiTapePTM 0 Bool (Fin 3) Unit where
  initial := 0
  tr state _ _ answer _ :=
    if state = 0 then
      .step { inputTape := 0, workTapes := Fin.elim0, output := none, state := some 1 }
        (fun _ => some true) (fun _ => 0)
    else if state = 1 then .query () 2
    else
      let out := if answer () = some false then some true else none
      .step { inputTape := 0, workTapes := Fin.elim0, output := out, state := none }
        (fun _ => none) (fun _ => 0)

/-- The instances: one point, encoded by the empty word. -/
private def enc : Unit ↪ List Bool := ⟨fun _ => [], fun _ _ _ => rfl⟩

/-- The number of coins, rounds and message lengths. -/
private def fuel : Unit → ℕ := fun _ => 3

/-- Once a program has finished after `h`, it follows no longer history. -/
private theorem outcome_append_cons_invalid {F : WordQueryComp Unit Bool} {h : History} {b : Bool}
    (hh : outcome F h = .done b) (x : List Bool × List Bool) (e : History) :
    outcome F (h ++ x :: e) = .invalid := by
  unfold outcome at hh ⊢
  rw [after_append]
  rcases hah : after F h with _ | ⟨c⟩ | ⟨q, next⟩
  · rw [hah] at hh
    cases hh
  · simp only [Option.bind_some]
    rfl
  · rw [hah] at hh
    cases hh

/-- The value of a history after which every program has finished is the number of accepting
programs. -/
private theorem value_succ_of_done {R : Type} [Fintype R] {F : R → WordQueryComp Unit Bool}
    {h : History} (hh : ∀ r, ∃ b, outcome (F r) h = .done b) (L n : ℕ) :
    value F L (n + 1) h = accepted F h := by
  have hz (m : List Bool) (y : List Bool) : value F L n (h ++ [(m, y)]) = 0 := by
    refine Nat.le_zero.mp ((value_le_card n _).trans ?_)
    refine Nat.le_zero.mpr (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_))
    intro r _
    obtain ⟨b, hb⟩ := hh r
    simpa using outcome_append_cons_invalid hb (m, y) []
  simp [value, hz]

/-- The value of a history that no program follows is `0`. -/
private theorem value_eq_zero_of_invalid {R : Type} [Fintype R] {F : R → WordQueryComp Unit Bool}
    {h : History} (hh : ∀ r, outcome (F r) h = .invalid) (L n : ℕ) : value F L n h = 0 := by
  refine Nat.le_zero.mp ((value_le_card n h).trans (Nat.le_zero.mpr ?_))
  exact Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun r _ => by simp [hh r])

/-- The accepting continuation: all `8` coin values accept after the history that answers the
message `[true]` with `[false]`. -/
example : evalFrom enc verifier fuel ((), [([true], [false])]) = 8 := by
  have hdone : ∀ r, outcome (coinFamily verifier 3 [] r) [([true], [false])] = .done true := by
    decide +kernel
  rw [evalFrom_eq]
  change value (coinFamily verifier 3 []) 3 3 _ = 8
  rw [value_succ_of_done fun r => ⟨true, hdone r⟩]
  simp [accepted, hdone]

/-- A history that follows the verifier but replies with `[true]` rejects every coin value. -/
example : evalFrom enc verifier fuel ((), [([true], [true])]) = 0 := by
  have hdone : ∀ r, outcome (coinFamily verifier 3 [] r) [([true], [true])] = .done false := by
    decide +kernel
  rw [evalFrom_eq]
  change value (coinFamily verifier 3 []) 3 3 _ = 0
  rw [value_succ_of_done fun r => ⟨false, hdone r⟩]
  simp [accepted, hdone]

/-- A history recording another message than the one the verifier sends: the shifted programs
reject, although the reply `[false]` would be accepted after the message `[true]`. -/
example : evalFrom enc verifier fuel ((), [([false], [false])]) = 0 := by
  have hinv : ∀ r, outcome (coinFamily verifier 3 [] r) [([false], [false])] = .invalid := by
    decide +kernel
  rw [evalFrom_eq]
  exact value_eq_zero_of_invalid hinv 3 3

end CslibFrontierTests.Computability.Complexity.Classes.IP.PSPACE
