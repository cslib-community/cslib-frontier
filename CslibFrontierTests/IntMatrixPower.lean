/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.PlantedClique.IntegerPower
import CslibFrontier.Computability.PolyTime.Int.MatrixPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Uniform stored integer matrix-power clients

The certificate below has no fixed dimension: its table, iteration count and seed are all
inputs. Concrete evaluations check signs, padding, truncated rows, an out-of-bounds seed and
the zero-dimensional case. The final identity connects the list machine realization to the
existing vector implementation for every finite integer matrix.

Run with `scripts/build.sh CslibFrontierTests.IntMatrixPower --wfail --iofail`.
-/

set_option linter.privateModule false

open Cslib Turing.MultiTapeTM

example : IntTable.powerColumn [[1, -1], [-1, 1]] 3 0 = [4, -4] := by
  simp only [IntTable.powerColumn, Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    IntTable.mulVec,
    Mathlib.Tactic.Matrix.ListMatrix.dotProduct_eq_sum_map_range]
  decide +kernel

example : IntTable.mulVec [[2], [3, 5, 99]] [7] = [14, 21] := by
  simp only [IntTable.mulVec, Mathlib.Tactic.Matrix.ListMatrix.dotProduct_eq_sum_map_range]
  decide +kernel

example : IntTable.powerColumn [[1, -1], [-1, 1]] 3 8 = [0, 0] := by
  simp only [IntTable.powerColumn, Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    IntTable.mulVec,
    Mathlib.Tactic.Matrix.ListMatrix.dotProduct_eq_sum_map_range]
  decide +kernel

example : IntTable.powerColumn [] 10 0 = [] := by
  decide +kernel

-- All dimensions, entries, exponents and seed indices vary in this one certificate.
example : ComputableInPolyTime
    (fun p : List (List ℤ) × ℕ × ℕ => IntTable.powerColumn p.1 p.2.1 p.2.2)
    (encPair encIntTable (encPair encUnary encUnary)) (encList encIntBin) := by
  fun_prop

example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (s : ℕ) (i : Fin n) :
    IntTable.powerColumn (List.ofFn fun j => List.ofFn (M j)) s i.val =
      List.ofFn fun j : Fin n => (Algorithms.PlantedClique.powerColumnVector M s i)[j.val] := by
  simp only [IntTable.powerColumn_ofFn, Algorithms.PlantedClique.getElem_powerColumnVector]
