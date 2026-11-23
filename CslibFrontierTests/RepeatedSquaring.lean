/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Circuit.Boolean.RepeatedSquaring
import CslibFrontier.Computability.Circuit.Simps

/-!
# Repeated Boolean matrix squaring

Concrete checks of `Cslib.Circuits.Boolean.squareCircuit` and its iterates under module
encapsulation: `circuit_bound` and `circuit_simps` automation, the single-vertex base case
(`N = 1, t = 0`), the empty graph (`N = 0`), the reflexive path `0 → 1 → 2` on three vertices, the
non-reflexive strict path `0 → 1 → 2`, a directed three-cycle without self-loops, and the
four-vertex reflexive path `0 → 1 → 2 → 3` where the second squaring is needed to reach `3` from
`0`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.RepeatedSquaring

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Relation

-- Automation checks: `circuit_bound` composes `Circuit.depth_iterate_le` with
-- `depth_squareCircuit_le`, and `circuit_simps` normalizes iterated gate counts.
example (N t : ℕ) : ((squareCircuit N).iterate t).depth ≤ 2 * t := by
  circuit_bound

example (N t : ℕ) : ((squareCircuit N).iterate t).size = t * (N ^ 2 * (N + 1)) := by
  simp only [circuit_simps, size_squareCircuit]

-- Single-vertex reflexive relation (`N = 1, t = 0`): `1 ≤ 2 ^ 0`, zero gates, zero depth, and
-- reachability holds with zero squarings.
example :
    ((squareCircuit 1).iterate 0).size = 0 ∧
    ((squareCircuit 1).iterate 0).depth = 0 ∧
    (((squareCircuit 1).iterate 0).eval Unbounded.interpretation ![true]
      (finProdFinEquiv (0, 0)) = true ↔
      ReflTransGen (fun _ _ : Fin 1 => True) 0 0) :=
  ⟨by simp only [circuit_simps, zero_mul], by decide +kernel,
    eval_iterate_squareCircuit_iff_reflTransGen (fun _ _ => by simp) (fun _ => trivial)
      (t := 0) (by decide) 0 0⟩

-- Empty graph (`N = 0`): zero gates and zero depth.
example : ((squareCircuit 0).iterate 3).size = 0 ∧ ((squareCircuit 0).iterate 3).depth = 0 := by
  decide +kernel

/-- The reflexive path `0 → 1 → 2`. -/
private def pathRel (i j : Fin 3) : Prop :=
  i = j ∨ j.val = i.val + 1

private instance : DecidableRel pathRel := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Its adjacency matrix, stored row by row. -/
private def pathMatrix : BitString (3 * 3) :=
  ![true, true, false,
    false, true, true,
    false, false, true]

private theorem pathMatrix_iff (i j : Fin 3) :
    pathMatrix (finProdFinEquiv (i, j)) = true ↔ pathRel i j := by
  revert i j
  decide +kernel

-- Zero squarings return the matrix; one adds `0 → 2`; two squarings add nothing more. The kernel
-- evaluates the circuits (`#eval` of `Circuit.eval` recomputes shared gates and is far slower).
example : List.ofFn (((squareCircuit 3).iterate 0).eval Unbounded.interpretation pathMatrix) =
      [true, true, false, false, true, true, false, false, true] ∧
    List.ofFn (((squareCircuit 3).iterate 1).eval Unbounded.interpretation pathMatrix) =
      [true, true, true, false, true, true, false, false, true] ∧
    List.ofFn (((squareCircuit 3).iterate 2).eval Unbounded.interpretation pathMatrix) =
      [true, true, true, false, true, true, false, false, true] := by
  decide +kernel

-- One squaring sees exactly the walks of two steps, so it already has `0 → 2`.
example :
    ((squareCircuit 3).iterate 1).eval Unbounded.interpretation pathMatrix
      (finProdFinEquiv (0, 2)) = true ∧
    ((squareCircuit 3).iterate 0).eval Unbounded.interpretation pathMatrix
      (finProdFinEquiv (0, 2)) = false := by
  decide +kernel

-- Reachability read off the circuit: `2` is reachable from `0`, and `0` is not from `2`.
example : ReflTransGen pathRel 0 2 ∧ ¬ ReflTransGen pathRel 2 0 := by
  have h := eval_iterate_squareCircuit_iff_reflTransGen pathMatrix_iff (fun i => Or.inl rfl)
    (t := 2) (by decide)
  refine ⟨(h 0 2).1 (by decide +kernel), fun h₂ => ?_⟩
  have := (h 2 0).2 h₂
  revert this
  decide +kernel

-- Walks of exactly `2 ^ 1 = 2` steps, for a relation that is not reflexive: on the strict path
-- `0 → 1 → 2`, one squaring relates only `0` to `2`.
example : ∀ i j : Fin 3,
    RelatesInSteps (fun a b : Fin 3 => b.val = a.val + 1) i j 2 ↔ (i = 0 ∧ j = 2) := by
  have h := eval_iterate_squareCircuit_iff_relatesInSteps
    (r := fun a b : Fin 3 => b.val = a.val + 1)
    (x := ![false, true, false, false, false, true, false, false, false]) (by decide +kernel) 1
  have hv : ∀ i j : Fin 3, ((squareCircuit 3).iterate 1).eval Unbounded.interpretation
      ![false, true, false, false, false, true, false, false, false]
      (finProdFinEquiv (i, j)) = true ↔ (i = 0 ∧ j = 2) := by
    decide +kernel
  intro i j
  rw [pow_one] at h
  rw [← h, hv]

-- Two squarings of a `3 × 3` matrix: `2 * (9 * 4) = 72` gates at depth exactly `4`.
example : ((squareCircuit 3).iterate 2).size = 72 := by simp

example : ((squareCircuit 3).iterate 2).depth = 4 := by decide +kernel

-- Directed 3-cycle `0 → 1 → 2 → 0` without self-loops: `2 ^ 2 = 4` steps advance by one edge
-- (`0 → 1`) and do not stay at `0`.
private def cycle3Matrix : BitString (3 * 3) :=
  ![false, true, false,
    false, false, true,
    true, false, false]

example :
    ((squareCircuit 3).iterate 2).eval Unbounded.interpretation cycle3Matrix
      (finProdFinEquiv (0, 1)) = true ∧
    ((squareCircuit 3).iterate 2).eval Unbounded.interpretation cycle3Matrix
      (finProdFinEquiv (0, 0)) = false := by
  decide +kernel

-- Four-vertex reflexive path `0 → 1 → 2 → 3`: `0 → 3` needs three edges, so one squaring (`2`
-- steps) leaves `(0, 3)` false while two squarings (`4` steps) reach `3` from `0` without adding
-- the reverse edge `3 → 0`.
private def path4Matrix : BitString (4 * 4) :=
  ![true, true, false, false,
    false, true, true, false,
    false, false, true, true,
    false, false, false, true]

example :
    ((squareCircuit 4).iterate 1).eval Unbounded.interpretation path4Matrix
      (finProdFinEquiv (0, 3)) = false ∧
    ((squareCircuit 4).iterate 2).eval Unbounded.interpretation path4Matrix
      (finProdFinEquiv (0, 3)) = true ∧
    ((squareCircuit 4).iterate 2).eval Unbounded.interpretation path4Matrix
      (finProdFinEquiv (3, 0)) = false := by
  decide +kernel

end CslibFrontierTests.RepeatedSquaring
