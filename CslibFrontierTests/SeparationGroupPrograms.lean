/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Group

/-! Tests of the programs of the group program, as a client:

* the encoding of a script of two instructions and the cost of a role instruction;
* the flags of the cuts, and the units of a string of three bits written at two keys;
* the semantics of a one-instruction script, and the formula GROUP at a script whose
  instructions are valid. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.SeparationGroupPrograms

open Cslib.Circuits.Arithmetic.Separation.Interpreter
  Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree
  Cslib.Circuits.Arithmetic.Separation.GroupProgram

/-! ### Syntax and costs -/

/-- A script of two instructions: the contents at two keys agree, and the contents at a key are
the bit `0`. -/
private def script₂ : List Instruction := [.agree [true] [false], .fixed [true, true] [false]]

/-- The encoding of the script, with `T = 1` and `ub = 2` in binary. -/
example : scriptEnc [true] [true, false] script₂ =
    .cons (.cons (ofBits [true]) (ofBits [true, false]))
      (listT [.cons (num 2) (.cons (ofBits [true]) (ofBits [false])),
        .cons (num 3) (.cons (ofBits [true, true]) (ofBits [false]))]) := rfl

/-- A role for two blocks with one slot (one key) and one channel (two keys), at units of three
bits: `2 * (3 + 1)` for the blocks, `5 + 1` and `10 + 1` for writing at the keys, and `1`. -/
example : (Instruction.role 0 2 [[[true]]] [[[false], [true]]]).cost 5 3 = 26 := by decide

/-! ### Cuts and units -/

/-- The flag `0` allows only nothing, the flag `1` only something, the flag `2` anything. -/
example : (flagAllows 0 false, flagAllows 0 true, flagAllows 1 false, flagAllows 1 true,
    flagAllows 2 false) = (true, false, false, true, true) := rfl

/-- Closing the last segment when no letter is left gives one cut. -/
example (sep cur : List Bool) (out : List (List Bool)) :
    cutsClose sep cur [] [] [] out = [cur :: out] := rfl

/-- Three bits in units of two bits at two keys: the second unit is filled up with a zero. -/
example : (putUnits 2 [[true], [false]] [true, false, true] .nil).map
    (fun t => (tget [true] t, tget [false] t)) =
      [(ofBits [true, false], ofBits [true, false])] := by decide

/-- Three bits do not fit into one unit of two bits: nothing is written. -/
example : putUnits 2 [[true]] [true, false, true] .nil = [] := by decide

/-! ### Scripts and GROUP -/

variable {A : Type} [CommRing A] (θ : List Bool → A) {Γ S Q : Type} [Fintype Γ] [Fintype S]
  [DecidableEq S] [Fintype Q] {c : ℕ} (mu : Cslib.Circuits.Arithmetic.Separation.Tape.Letter
    S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool)

/-- The empty trie has the empty contents at the empty key, so the script that asks for them
keeps the empty trie, with the weight `1`. -/
example (T ub : ℕ) : scriptSem θ mu cb [] T ub [.fixed [] []] .nil = [(1, .nil)] := by
  simp [instructionSem, tget, ofBits, List.weightedBind]

/-- GROUP at the script of two comparisons, for any automaton and no roles. -/
example : ∃ F κ, Does θ F (scriptEnc [true] [true, false] script₂)
    ((scriptSem θ mu cb [] (Cslib.BitString.binaryValue [true])
      (Cslib.BitString.binaryValue [true, false]) script₂ .nil).map
      (Prod.map id (groupState (Cslib.BitString.binaryValue [true])
        (Cslib.BitString.binaryValue [true, false])))) (κ * 40) := by
  obtain ⟨F, κ, h⟩ := exists_formula_scriptSem (θ := θ) mu cb []
  refine ⟨F, κ, (h [true] [true, false] script₂ (by simp [script₂, Instruction.Valid])).mono ?_⟩
  exact Nat.mul_le_mul_left _ (by decide)

end CslibFrontierTests.SeparationGroupPrograms
