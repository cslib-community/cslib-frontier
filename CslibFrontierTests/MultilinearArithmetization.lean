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

/-- Syntactically multilinear circuits simulate d-Ds: the exclusive disjunction has one with at
most `4 · 5` gates computing its multilinear representative. -/
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

example : (innerProduct.toArith ℤ).size ≤ 2 + 5 * innerProduct.wireCount :=
  innerProduct.size_toArith_le

example : (innerProduct.toArith ℤ).IsSyntacticallyMultilinear :=
  innerProduct.isSyntacticallyMultilinear_toArith

/-- At the Boolean points the circuit counts the switched-on paths. -/
example (x : Fin 4 → Bool) :
    (innerProduct.toArith ℤ).eval (arithInterpretationWith ℤ (algebraMap ℤ ℤ)) (bitPoint x) 0 =
      (innerProduct.pathCount x : ℤ) :=
  innerProduct.eval_toArith_bitPoint innerProduct_isReadOnce ℤ x

/-- It computes the multilinear extension of the path count. -/
example : (innerProduct.toArith ℤ).eval (arithInterpretationWith ℤ C) X 0 =
    multilinearExtension fun x => (innerProduct.pathCount x : ℤ) :=
  innerProduct.eval_toArith_X innerProduct_isReadOnce

/-- Over `F₂` syntactically multilinear circuits simulate read-once parity programs: the inner
product modulo two has one with at most `2 + 5 · 4` gates computing its multilinear
representative. -/
example : ∃ A : Circuit (arithSignature (ZMod 2)) 4 1, A.IsSyntacticallyMultilinear ∧
    (A.ComputesMultilinear fun z => decide (innerProduct.AcceptsParity z)) ∧
    A.size ≤ 2 + 5 * innerProduct.wireCount :=
  innerProduct.exists_syntacticallyMultilinear innerProduct_isReadOnce

/-! ### 3. Different query orders, negative contacts, rectifiers and a dead node -/

/-- `x 2 ∧ (x 0 ↔ x 1)` over `F₂`. From the source, rectifiers lead to two prefixes testing `x 0`
and `x 1` in opposite orders (`x 0`, then `x 1`; and `¬ x 1`, then `¬ x 0`), which merge at a node
testing `x 2`, and to a dead node with no path to the target. Nodes: `0` the target, `1` dead, `2`
tests `x 2`, `3` tests `x 1`, `4` tests `¬ x 0`, `5` tests `x 0`, `6` tests `¬ x 1`, `7` the
source. -/
def twoOrders : NBP (Fin 3) Bool 8 :=
  NBP.target
    |>.node []
    |>.node [⟨0, some (2, true)⟩]
    |>.node [⟨2, some (1, true)⟩]
    |>.node [⟨2, some (0, false)⟩]
    |>.node [⟨3, some (0, true)⟩]
    |>.node [⟨4, some (1, false)⟩]
    |>.node [⟨5, none⟩, ⟨6, none⟩, ⟨1, none⟩]

/-- Each path tests each variable at most once, although the two prefixes query `x 0` and `x 1` in
different orders. -/
theorem twoOrders_isReadOnce : twoOrders.IsReadOnce := by
  decide

example : twoOrders.wireCount = 8 := by
  decide

/-- The program computes `x 2 ∧ (x 0 ↔ x 1)` by parity. -/
example (z : Fin 3 → Bool) : decide (twoOrders.AcceptsParity z) = (z 2 && (z 0 == z 1)) := by
  revert z
  decide

/-- The dead node costs no gate: two gates for the constants and five for each wire. -/
example : (twoOrders.toArith ℤ).size ≤ 2 + 5 * 8 := by
  have := twoOrders.size_toArith_le (R := ℤ)
  rwa [show twoOrders.wireCount = 8 by decide] at this

example (x : Fin 3 → Bool) :
    (twoOrders.toArith ℤ).eval (arithInterpretationWith ℤ (algebraMap ℤ ℤ)) (bitPoint x) 0 =
      (twoOrders.pathCount x : ℤ) :=
  twoOrders.eval_toArith_bitPoint twoOrders_isReadOnce ℤ x

example : ∃ A : Circuit (arithSignature (ZMod 2)) 3 1, A.IsSyntacticallyMultilinear ∧
    (A.ComputesMultilinear fun z => decide (twoOrders.AcceptsParity z)) ∧
    A.size ≤ 2 + 5 * twoOrders.wireCount :=
  twoOrders.exists_syntacticallyMultilinear twoOrders_isReadOnce

end CslibFrontierTests.MultilinearArithmetization
