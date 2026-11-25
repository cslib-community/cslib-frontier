/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunCount
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunRename
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunValue
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.WordCode

/-! Tests of the clause sums of automaton runs under ordinary imports:

* the sizes of the hidden variables and of the clauses for one tape, one input, one step;
* the code of a one-letter word on three places;
* renaming the two inputs of an automaton by the swap;
* the value of an automaton on the one-letter input `[true]` as a clause sum;
* change of rings from `ℤ` to `ℚ`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.TapeRunSum

open Cslib.Circuits.Arithmetic Cslib.Circuits.Arithmetic.Separation.Tape

/-- One tape, one input, one step, one place: `1 + 2 + 3 · 2 + 1 = 10` hidden variables. -/
example : Fintype.card (RunVar Unit 1 1 1) = 10 := by
  rw [RunVar.card]
  simp

/-- The weighted clauses for the alphabet `Bool` and two states. -/
example : Fintype.card (RunStep Bool Unit (Fin 2) 1 1) = 28 := by
  rw [RunStep.card, Fintype.card_option, Fintype.card_prod, Ch.card]
  simp

/-- The code of the word `[true]` on three places sets `(0, some true)` and `(1, none)` only. -/
example : wordCode 3 [true] (0, some true) = true ∧ wordCode 3 [true] (1, none) = true ∧
    wordCode 3 [true] (2, none) = false := by
  decide

example : IsWordCode (wordCode 3 [true]) := isWordCode_wordCode [true]

/-- Also when the word does not fit into the places. -/
example : IsWordCode (wordCode 1 [true, false]) := isWordCode_wordCode _

example : Finset.card {b | wordCode 3 [true] b = true} = 2 :=
  card_ones_wordCode [true] (by norm_num)

/-- A family with two letters at place `0` is no code. -/
example : ¬ IsWordCode (fun b : Fin 2 × Option Bool => decide (b.1 = 0)) := by
  decide

/-- Swapping the two inputs of an automaton and of its letters keeps the value. -/
example (mu : Letter Unit (Fin 2) Bool → Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → List Bool) :
    runVal (fun a => mu (Letter.congr Unit Bool (Equiv.swap 0 1) a)) 0 1 3
      (fun j => u (Equiv.swap 0 1 j)) = runVal mu 0 1 3 u :=
  runVal_congr _ mu 0 1 3 u

/-- The value of an automaton with one input, one step and two states on the input `[true]` is the
clause sum of its run clauses, with two code places and four places for the heads. -/
example (mu : Letter Unit (Fin 1) Bool → Matrix (Fin 2) (Fin 2) ℤ) :
    domainClauseSum (runLits (Γ := Bool) (S := Unit) (n := 1) (t := 1) (M := 4) (N := 2) 0 1)
      (runWeights mu) (code 2 fun _ : Fin 1 => [true]) = runVal mu 0 1 1 fun _ => [true] :=
  runVal_eq_domainClauseSum mu 0 1 _ (by norm_num) (by decide)

/-- Mapping integer matrices to rational ones maps the value. -/
example (mu : Letter Unit (Fin 1) Bool → Matrix (Fin 2) (Fin 2) ℤ) :
    runVal (fun a => (mu a).map (Int.castRingHom ℚ)) 0 1 3 (fun _ => [true]) =
      (runVal mu 0 1 3 fun _ => [true] : ℤ) :=
  (runVal_map (Int.castRingHom ℚ) mu 0 1 3 _).trans (by simp)

end CslibFrontierTests.TapeRunSum
