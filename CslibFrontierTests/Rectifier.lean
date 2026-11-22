/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Circuit.Boolean.Rectifier
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Rectangular matrix orientation, repeated rows, empty inputs, and a nondivisible block
width for the depth-two rectifier construction. -/

set_option linter.privateModule false

open Cslib.Circuits Cslib.Circuits.Boolean.Rectifier

private def repeatedRows : Matrix (Fin 3) (Fin 2) Bool :=
  ![![true, false], ![true, false], ![false, true]]

private theorem eval_repeatedRows (x : Fin 3 → Bool) :
    (rowPatternCircuit repeatedRows).eval interpretation x = ![x 0 || x 1, x 2] := by
  rw [eval_rowPatternCircuit]
  funext j
  fin_cases j <;>
    simp [matrixAction, repeatedRows, Fin.exists_fin_succ]

example :
    (rowPatternCircuit (Matrix.of fun i : Fin 0 => i.elim0 : Matrix (Fin 0) (Fin 3) Bool)).eval
      interpretation Fin.elim0 = fun _ => false := by
  rw [eval_rowPatternCircuit]
  funext j
  simp [matrixAction]

-- Six blocks of width three include one padded column, whose four outgoing wires are omitted.
-- The resulting budget is below both the uniform block bound of 168 and the dense bound of 272.
example (A : Matrix (Fin 16) (Fin 17) Bool) :
    ∃ c : Circuit signature 16 17,
      IsTwoLayer c ∧ c.Computes interpretation (matrixAction A) ∧ c.depth ≤ 2 ∧
        c.program.cost id = 164 := by
  obtain ⟨c, hl, hc, hd, hw⟩ := exists_depth_two_blocked_exact A (s := 3) (by decide)
  norm_num [Nat.ceilDiv_eq_add_pred_div] at hw
  exact ⟨c, hl, hc, hd, hw⟩

-- The native inclusion into the full unbounded Boolean basis preserves the output map.
example (x : Fin 3 → Bool) :
    ((rowPatternCircuit repeatedRows).mapOp toUnbounded).eval
      Boolean.Unbounded.interpretation x = ![x 0 || x 1, x 2] := by
  rw [Circuit.eval_mapOp (I := interpretation), eval_repeatedRows]
