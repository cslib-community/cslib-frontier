/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.RepeatedSquaring

/-!
# Repeated Boolean matrix squaring

Concrete checks of `Cslib.Circuits.Boolean.closureCircuit` on the reflexive path `0 → 1 → 2` on
three vertices. One squaring adds the edge `0 → 2`; two squarings compute reachability, which
`eval_closureCircuit_iff_reflTransGen` turns into reachability and non-reachability statements.
The exact gate count and depth of the two-squaring circuit are computed as well, and the iterate
with zero squarings is the input matrix.
-/

namespace CslibFrontierTests.RepeatedSquaring

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Relation

/-- The reflexive path `0 → 1 → 2`. -/
private def pathRel (i j : Fin 3) : Prop :=
  i = j ∨ j.val = i.val + 1

private instance : DecidableRel pathRel := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Its adjacency matrix, stored row by row. -/
private def pathMatrix : BitString (3 * 3) :=
  ![true, true, false,
    false, true, true,
    false, false, true]

private theorem pathMatrix_iff (i j : Fin 3) : pathMatrix (matrixIndex i j) = true ↔ pathRel i j := by
  revert i j
  decide +kernel

-- Zero squarings return the matrix; one adds `0 → 2`; two squarings add nothing more. The kernel
-- evaluates the circuits (`#eval` of `Circuit.eval` recomputes shared gates and is far slower).
example : List.ofFn ((closureCircuit 3 0).eval Unbounded.interpretation pathMatrix) =
      [true, true, false, false, true, true, false, false, true] ∧
    List.ofFn ((closureCircuit 3 1).eval Unbounded.interpretation pathMatrix) =
      [true, true, true, false, true, true, false, false, true] ∧
    List.ofFn ((closureCircuit 3 2).eval Unbounded.interpretation pathMatrix) =
      [true, true, true, false, true, true, false, false, true] := by
  decide +kernel

-- One squaring sees exactly the walks of two steps, so it already has `0 → 2`.
example : (closureCircuit 3 1).eval Unbounded.interpretation pathMatrix (matrixIndex 0 2) = true ∧
    (closureCircuit 3 0).eval Unbounded.interpretation pathMatrix (matrixIndex 0 2) = false := by
  decide +kernel

-- Reachability read off the circuit: `2` is reachable from `0`, and `0` is not from `2`.
example : ReflTransGen pathRel 0 2 ∧ ¬ ReflTransGen pathRel 2 0 := by
  have h := eval_closureCircuit_iff_reflTransGen pathMatrix_iff (fun i => Or.inl rfl)
    (t := 2) (by decide)
  refine ⟨(h 0 2).1 (by decide +kernel), fun h₂ => ?_⟩
  have := (h 2 0).2 h₂
  revert this
  decide +kernel

-- Walks of exactly `2 ^ 1 = 2` steps, for a relation that is not reflexive: on the strict path
-- `0 → 1 → 2`, one squaring relates only `0` to `2`.
example : ∀ i j : Fin 3,
    RelatesInSteps (fun a b : Fin 3 => b.val = a.val + 1) i j 2 ↔ (i = 0 ∧ j = 2) := by
  have h := eval_closureCircuit_iff_relatesInSteps (r := fun a b : Fin 3 => b.val = a.val + 1)
    (x := ![false, true, false, false, false, true, false, false, false]) (by decide +kernel) 1
  have hv : ∀ i j : Fin 3, (closureCircuit 3 1).eval Unbounded.interpretation
      ![false, true, false, false, false, true, false, false, false] (matrixIndex i j) = true ↔
      (i = 0 ∧ j = 2) := by
    decide +kernel
  intro i j
  rw [pow_one] at h
  rw [← h, hv]

-- Two squarings of a `3 × 3` matrix: `2 * (9 * 4) = 72` gates at depth exactly `4`.
example : (closureCircuit 3 2).size = 72 := by simp

example : (closureCircuit 3 2).depth = 4 := by decide +kernel

end CslibFrontierTests.RepeatedSquaring
