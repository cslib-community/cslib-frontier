/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Computability.Circuit.Boolean.DeterministicDecomposable
public import Mathlib.Data.Fin.VecNotation

/-! Concrete `module` clients for deterministic decomposable circuits (d-Ds): the exclusive
disjunction as a d-D, a negation above it, and circuits failing each condition. -/

public section

namespace CslibFrontierTests.DeterministicDecomposableCircuit

open Cslib.Circuits

/-! ### 1. Exclusive disjunction -/

/-- `(x 0 ∧ ¬x 1) ∨ (¬x 0 ∧ x 1)`: gates `0` and `1` negate the inputs, gates `2` and `3` are
decomposable conjunctions, and gate `4` is a deterministic disjunction. -/
def xorProgram : Program Boolean.signature 2 5 :=
  (Program.empty : Program Boolean.signature 2 0)
    |>.gate ⟨Boolean.Op.not, ![Wire.input 0]⟩
    |>.gate ⟨Boolean.Op.not, ![Wire.input 1]⟩
    |>.gate ⟨Boolean.Op.and, ![Wire.input 0, Wire.gate 1]⟩
    |>.gate ⟨Boolean.Op.and, ![Wire.gate 0, Wire.input 1]⟩
    |>.gate ⟨Boolean.Op.or, ![Wire.gate 2, Wire.gate 3]⟩

/-- The exclusive disjunction, read at gate `4`. -/
def xorCircuit : Circuit Boolean.signature 2 1 where
  program := xorProgram
  outputs := fun _ => Wire.gate 4

example : xorCircuit.IsDeterministicDecomposable := by
  decide

example : ∀ x : Fin 2 → Bool, xorCircuit.eval Boolean.interpretation x 0 = (x 0 ^^ x 1) := by
  decide

/-- A NOT gate above the disjunction: d-Ds, unlike d-DNNFs, allow negations anywhere. -/
def xnorCircuit : Circuit Boolean.signature 2 1 where
  program := xorProgram.gate ⟨Boolean.Op.not, ![Wire.gate 4]⟩
  outputs := fun _ => Wire.gate 5

example : xnorCircuit.IsDeterministicDecomposable := by
  decide

example : ∀ x : Fin 2 → Bool, xnorCircuit.eval Boolean.interpretation x 0 = !(x 0 ^^ x 1) := by
  decide

/-! ### 2. Failing the conditions -/

/-- `x 0 ∨ x 1` is decomposable but not deterministic: both arguments are true at `(1, 1)`. -/
def orProgram : Program Boolean.signature 2 1 :=
  (Program.empty : Program Boolean.signature 2 0).gate
    ⟨Boolean.Op.or, ![Wire.input 0, Wire.input 1]⟩

example : orProgram.IsDecomposableAt (· = .and) ∧ ¬ orProgram.IsDeterministic := by
  decide

/-- `x 0 ∧ ¬x 0` is deterministic but not decomposable: both arguments read `x 0`. -/
def contradiction : Program Boolean.signature 1 2 :=
  (Program.empty : Program Boolean.signature 1 0)
    |>.gate ⟨Boolean.Op.not, ![Wire.input 0]⟩
    |>.gate ⟨Boolean.Op.and, ![Wire.input 0, Wire.gate 0]⟩

example : ¬ contradiction.IsDecomposableAt (· = .and) ∧ contradiction.IsDeterministic := by
  decide

end CslibFrontierTests.DeterministicDecomposableCircuit
