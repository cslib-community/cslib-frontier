/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.LinearSolve
import CslibFrontier.Foundations.LinearAlgebra.LinearSolve
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for elimination linear solving and full-basis circuit bounds

Exercises `CslibFrontier.Foundations.LinearAlgebra.LinearSolve` and
`CslibFrontier.Computability.Circuit.LinearSolve` through ordinary `module` imports over `ZMod 5`:
`kernelVecAt` produces a kernel vector normalized to `1` at the prescribed entry when one exists and
`0` when every kernel vector vanishes there; `vecMulSolve` finds the Lagrange weights solving
`w ᵥ* M = ![1, 0]` and returns `0` on an inconsistent system; and `full_kernelBasis`,
`full_kernelVecAt`, and `full_vecMulSolve` instantiate cleanly on coordinate inputs.
-/

set_option linter.privateModule false

namespace Cslib.LinearAlgebra.LinearSolveTests

open Cslib.Circuits Cslib.Circuits.Synthesis Cslib.LinearAlgebra
open scoped Matrix

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def row123 : Matrix (Fin 1) (Fin 3) (ZMod 5) := !![1, 2, 3]

private def row010 : Matrix (Fin 1) (Fin 3) (ZMod 5) := !![0, 1, 0]

private def vandermonde12 : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![1, 1; 1, 2]

private def singular1122 : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![1, 1; 2, 2]

/-- On `(1, 2, 3)` over `ZMod 5`, `kernelVecAt` produces `![3, 1, 0]`, which lies in the kernel
(`mulVec_kernelVecAt`) and has entry `1` equal to `1` (`kernelVecAt_apply_self_eq_one_iff`). -/
example :
    kernelVecAt row123 1 = ![3, 1, 0] ∧
    row123 *ᵥ kernelVecAt row123 1 = 0 ∧
    kernelVecAt row123 1 1 = 1 :=
  ⟨by decide +kernel,
    mulVec_kernelVecAt row123 1,
    (kernelVecAt_apply_self_eq_one_iff row123 1).2 ⟨![3, 1, 0], by decide +kernel, by decide⟩⟩

/-- On `(0, 1, 0)` over `ZMod 5`, `kernelVecAt` evaluates to `0` at index `1`; on `1 : Fin 2`,
every kernel vector of `(1 : Matrix (Fin 2) (Fin 2) (ZMod 5))` has first entry zero, so
`kernelVecAt_eq_zero` yields `0`. -/
example :
    kernelVecAt row010 1 = 0 ∧
    kernelVecAt (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 = 0 :=
  ⟨by decide +kernel,
    kernelVecAt_eq_zero (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 fun v hv => by
      have h0 := congrFun hv 0
      simpa using h0⟩

/-- On rows `(1, 1)` and `(1, 2)` over `ZMod 5`, `vecMulSolve` produces the Lagrange weights
`![2, 4]` at `0` for points `1, 2`, and `vecMul_vecMulSolve` certifies `w ᵥ* M = ![1, 0]`. -/
example :
    vecMulSolve vandermonde12 ![1, 0] = ![2, 4] ∧
    vecMulSolve vandermonde12 ![1, 0] ᵥ* vandermonde12 = ![1, 0] :=
  ⟨by decide +kernel,
    vecMul_vecMulSolve vandermonde12 ![1, 0] ⟨![2, 4], by decide +kernel⟩⟩

/-- When `![1, 0]` is outside the row span of `!![1, 1; 2, 2]` over `ZMod 5`, `vecMulSolve` returns
`0` (`vecMulSolve_eq_zero`), and no `w` satisfies `w ᵥ* M = ![1, 0]` (exercising
`vecMul_vecMulSolve_iff`). -/
example :
    vecMulSolve singular1122 ![1, 0] = 0 ∧
    (¬ ∃ w : Fin 2 → ZMod 5, w ᵥ* singular1122 = ![1, 0]) ∧
    vecMulSolve singular1122 ![1, 0] ᵥ* singular1122 ≠ ![1, 0] := by
  have hno : ¬ ∃ w : Fin 2 → ZMod 5, w ᵥ* singular1122 = ![1, 0] := by decide +kernel
  exact ⟨vecMulSolve_eq_zero singular1122 ![1, 0] hno, hno,
    (vecMul_vecMulSolve_iff singular1122 ![1, 0]).not.2 hno⟩

private abbrev wireInputs (N : ℕ) : Set ((Fin N → ZMod 5) → ZMod 5) :=
  Set.range fun i x => x i

private def wireMatrix13 : Fin 1 → Fin 3 → (Fin 3 → ZMod 5) → ZMod 5 := fun _ l x => x l

private def wireMatrix22 : Fin 2 → Fin 2 → (Fin 6 → ZMod 5) → ZMod 5 :=
  fun k l x => x ⟨2 * k.val + l.val, by omega⟩

private def wireTarget2 : Fin 2 → (Fin 6 → ZMod 5) → ZMod 5 :=
  fun l x => x ⟨4 + l.val, by omega⟩

/-- `full_kernelBasis` synthesizes the spanning kernel family of a `1 × 3` coordinate matrix over
`ZMod 5` within `(3 + 1) ^ 2 + 1 * (8 * (3 + 1) ^ 2)` gates of the full binary basis. -/
example :
    Synthesis (fullInterpretation (k := 2)) (wireInputs 3)
      (Set.range fun il : Fin 3 × Fin 3 =>
        fun x => kernelBasis (fun k l => wireMatrix13 k l x) il.1 il.2)
      ((3 + 1) ^ 2 + 1 * (8 * (3 + 1) ^ 2)) :=
  full_kernelBasis (s := wireInputs 3) wireMatrix13 fun _ l => ⟨l, rfl⟩

/-- `full_kernelVecAt` synthesizes `kernelVecAt` at coordinate `1` for a `1 × 3` matrix over
`ZMod 5` within `kernelVecCost 1 3` gates. -/
example :
    Synthesis (fullInterpretation (k := 2)) (wireInputs 3)
      (Set.range fun l (x : Fin 3 → ZMod 5) =>
        kernelVecAt (fun k l => wireMatrix13 k l x) 1 l)
      (kernelVecCost 1 3) :=
  full_kernelVecAt (s := wireInputs 3) wireMatrix13 (fun _ l => ⟨l, rfl⟩) 1

/-- `full_vecMulSolve` synthesizes `vecMulSolve` for a `2 × 2` matrix and `2`-vector on six
coordinate wires over `ZMod 5` within `kernelVecCost 2 (2 + 1) + 2` gates. -/
example :
    Synthesis (fullInterpretation (k := 2)) (wireInputs 6)
      (Set.range fun k x => vecMulSolve (fun k l => wireMatrix22 k l x)
        (fun l => wireTarget2 l x) k)
      (kernelVecCost 2 (2 + 1) + 2) :=
  full_vecMulSolve (s := wireInputs 6) wireMatrix22 wireTarget2
    (fun k l => ⟨⟨2 * k.val + l.val, by omega⟩, rfl⟩) (fun l => ⟨⟨4 + l.val, by omega⟩, rfl⟩)

end Cslib.LinearAlgebra.LinearSolveTests
