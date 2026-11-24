/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import Mathlib.Data.Sym.Sym2
import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.Restrict
import CslibFrontier.Algorithms.PointerMachine.SmallMSF
meta import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.Restrict
meta import CslibFrontier.Algorithms.PointerMachine.SmallMSF

/-!
# Small instances of optimal comparison-tree synthesis

A triangle needs two comparisons to find its heaviest edge. A forest needs none.
A pair of parallel edges needs one comparison, even with sparse original labels.
-/

-- This test module executes the synthesized programs and inspects their output records.
set_option linter.hashCommand false

namespace CslibFrontierTests.PettieRamachandran

open Cslib Cslib.Multigraph Cslib.Query
open scoped Sym2

/-- The labeled triangle shared by the query and pointer-machine checks. -/
public def triangle (e : Fin 3) : Sym2 (Fin 3) :=
  if e = 0 then s(0, 1) else if e = 1 then s(0, 2) else s(1, 2)

#guard optimalMSFComparisons triangle == 2
#guard (optimalMSFProgram triangle).eval (LEQuery.keyOracle Fin.val) == {0, 1}

private def path (e : Fin 2) : Sym2 (Fin 3) := if e = 0 then s(0, 1) else s(1, 2)

#guard optimalMSFComparisons path == 0
#guard optimalMSFComparisons (fun _ : Fin 2 => (s(0, 0) : Sym2 (Fin 1))) == 0

private def parallel (_ : ℕ) : Sym2 ℕ := s(100, 900)

#guard (optimalMSFOn parallel {9, 71}).eval (LEQuery.keyOracle (fun n : ℕ => -(n : ℤ))) == {71}
#guard (optimalMSFOn parallel {9, 71}).countQueries (LEQuery.keyOracle id) == 1

open Cslib.PointerMachine Cslib.PointerMachine.ComparisonTree

private def traverse (x : State (model ℕ) layout) : ℕ → Option (State (model ℕ) layout)
  | 0 => some x
  | n + 1 => (traverse x n).bind (step (code ℕ))

private def triangleResult (n : ℕ) : Option (ℕ × ℕ × ℕ × Pointer) := do
  let x ← traverse (smallMSFInput triangle Fin.val) n
  let first ← x.deref 0
  let a ← first.ptr 0
  let tail ← first.ptr 1
  let second ← x.heap[tail]?
  let b ← second.ptr 0
  return (x.pc, a, b, second.ptr 1)

-- Nineteen transitions reach the halt. The two links return the original labels 0 and 1.
#guard triangleResult 19 == some (11, 0, 1, none)
#guard (triangleResult 20).isNone

end CslibFrontierTests.PettieRamachandran
