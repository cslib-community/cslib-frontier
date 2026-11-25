/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.AlternatingQueryMachine.Compiler

/-! Tests for the compilation of alternating query machines: the guessing machine rejects a wrong
guess of the player and otherwise makes the move, and the guess register of the alternating native
machine makes a choice universal exactly after the guess `true`. -/

namespace CslibFrontierTests.AlternatingQueryMachineCompiler

open Turing Turing.AlternatingQueryMachine Turing.NondeterministicQueryMachine

/-- From state `0`, the choice `true` leads to the accepting state `1` and the choice `false` to the
rejecting state `2`; the player of state `0` is `u`. -/
private def pick (u : Bool) : AlternatingQueryMachine (Fin 3) where
  init := 0
  query _ := 0
  next p := if p.2.2 then 1 else 2
  halted q := q != 0
  accept q := q == 1
  universal _ := u

/-- A wrong guess of the player (`false` at a universal state) halts the guessing machine in a
rejecting state. -/
example : (pick true).guess.step [] (0, none) false = (0, some false) ∧
    (pick true).guess.halted (0, some false) = true ∧
    (pick true).guess.accept (0, some false) = false := by
  decide

/-- A right guess is followed by a move of the guessed player, here to the rejecting state. -/
example : (pick true).guess.replay [] [true, false] (0, none) = (2, none) := by decide

/-- At an existential state the right guess is `false`, followed by the accepting move. -/
example : (pick false).guess.replay [] [false, true] (0, none) = (1, none) ∧
    (pick false).guess.accept (1, none) = true := by
  decide

/-- The guess register records a guess, and the following move clears it. -/
example : Native.nextGuess none true = some true ∧
    Native.nextGuess (Native.nextGuess none true) false = none := by
  decide

/-- Only the choice state with the recorded guess `true` is universal. -/
example :
    Native.isUniversal (SI := Unit) (SP := fun _ => Unit) (SF := Unit) (.choose, some true) = true ∧
    Native.isUniversal (SI := Unit) (SP := fun _ => Unit) (SF := Unit) (.choose, some false) =
      false ∧
    Native.isUniversal (SI := Unit) (SP := fun _ => Unit) (SF := Unit) (.choose, none) = false ∧
    Native.isUniversal (SI := Unit) (SP := fun _ => Unit) (SF := Unit) (.check, some true) =
      false :=
  ⟨rfl, rfl, rfl, rfl⟩

end CslibFrontierTests.AlternatingQueryMachineCompiler
