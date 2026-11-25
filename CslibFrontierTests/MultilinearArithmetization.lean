/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Computability.BranchingProgram.ReadOnceParityArithmetic
public import CslibFrontier.Computability.Circuit.Boolean.DeterministicDecomposableArithmetic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Field.ZMod

/-! Concrete `module` clients for the arithmetization of deterministic decomposable circuits and of
read-once parity branching programs: sizes, syntactic multilinearity, values at the Boolean points
and the multilinear extensions they compute. -/

public section

namespace CslibFrontierTests.MultilinearArithmetization

open Cslib.Circuits Cslib.BranchingPrograms MvPolynomial Cslib.BitString

/-! ### 1. A deterministic decomposable circuit -/

/-- `(x 0 ∧ ¬x 1) ∨ (¬x 0 ∧ x 1)` as a d-D. -/
def xorCircuit : Circuit Boolean.signature 2 1 where
  program := (Program.empty : Program Boolean.signature 2 0)
    |>.gate ⟨Boolean.Op.not, ![Wire.input 0]⟩
    |>.gate ⟨Boolean.Op.not, ![Wire.input 1]⟩
    |>.gate ⟨Boolean.Op.and, ![Wire.input 0, Wire.gate 1]⟩
    |>.gate ⟨Boolean.Op.and, ![Wire.gate 0, Wire.input 1]⟩
    |>.gate ⟨Boolean.Op.or, ![Wire.gate 2, Wire.gate 3]⟩
  outputs := fun _ => Wire.gate 4

theorem xorCircuit_isDD : xorCircuit.IsDeterministicDecomposable := by
  decide

/-- Two negations of four gates each, two multiplications and one addition. -/
example : (xorCircuit.arithmetize ℤ).size = 11 := by
  decide

example : (xorCircuit.arithmetize ℤ).size ≤ 4 * xorCircuit.size :=
  xorCircuit.size_arithmetize_le ℤ

/-- The arithmetic circuit is syntactically multilinear, so it computes the multilinear extension
of the exclusive disjunction, `X 0 + X 1 - 2 X 0 X 1`. -/
example : (xorCircuit.arithmetize ℤ).eval (arithInterpretationWith ℤ C) X 0 =
    multilinearExtension fun x => bitVal ℤ (x 0 ^^ x 1) := by
  rw [xorCircuit_isDD.eval_arithmetize_X]
  congr 1
  funext x
  congr 1
  revert x
  decide

/-- d-Ds simulate syntactically multilinear circuits: the exclusive disjunction has one with at most
`4 · 5` gates computing its multilinear representative. -/
example : ∃ A : Circuit (arithSignature ℤ) 2 1, A.IsSyntacticallyMultilinear ∧
    (A.ComputesMultilinear fun z => xorCircuit.eval Boolean.interpretation z 0) ∧
    A.size ≤ 4 * xorCircuit.size :=
  xorCircuit_isDD.exists_syntacticallyMultilinear

/-! ### 2. A read-once parity branching program -/

/-- `x 0 * x 1 + x 2 * x 3` over `F₂`: two routes testing disjoint pairs of coordinates. -/
def innerProduct : NBP (Fin 4) Bool 4 :=
  NBP.target
    |>.node [⟨0, some (3, true)⟩]
    |>.node [⟨0, some (1, true)⟩]
    |>.node [⟨2, some (0, true)⟩, ⟨1, some (2, true)⟩]

theorem innerProduct_isReadOnce : innerProduct.IsReadOnce := by
  decide

example : (innerProduct.toArith ℤ).size ≤ 4 + 5 * innerProduct.wireCount :=
  innerProduct.size_toArith_le

example : (innerProduct.toArith ℤ).program.IsDecomposableAt (· = .mul) :=
  innerProduct.isDecomposableAt_toArith

/-- At the Boolean points the circuit counts the switched-on paths. -/
example (x : Fin 4 → Bool) :
    (innerProduct.toArith ℤ).eval (arithInterpretationWith ℤ (algebraMap ℤ ℤ)) (bitPoint x) 0 =
      (innerProduct.pathCount x : ℤ) :=
  innerProduct.eval_toArith_bitPoint innerProduct_isReadOnce ℤ x

/-- It computes the multilinear extension of the path count. -/
example : (innerProduct.toArith ℤ).eval (arithInterpretationWith ℤ C) X 0 =
    multilinearExtension fun x => (innerProduct.pathCount x : ℤ) :=
  innerProduct.eval_toArith_X innerProduct_isReadOnce

/-- Over `F₂` read-once parity programs simulate syntactically multilinear circuits: the inner
product modulo two has one with at most `4 + 5 · 4` gates computing its multilinear
representative. -/
example : ∃ A : Circuit (arithSignature (ZMod 2)) 4 1, A.IsSyntacticallyMultilinear ∧
    (A.ComputesMultilinear fun z => decide (innerProduct.AcceptsParity z)) ∧
    A.size ≤ 4 + 5 * innerProduct.wireCount :=
  innerProduct.exists_syntacticallyMultilinear innerProduct_isReadOnce

end CslibFrontierTests.MultilinearArithmetization
