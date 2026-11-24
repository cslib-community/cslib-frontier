/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import Mathlib.Data.Sym.Sym2
import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.Restrict
import CslibFrontier.Algorithms.PointerMachine.BoundSmallMSF
import CslibFrontier.Algorithms.Lean.SoftHeap.Forest
meta import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.Restrict
meta import CslibFrontier.Algorithms.PointerMachine.BoundSmallMSF
meta import CslibFrontier.Algorithms.Lean.SoftHeap.Forest

/-!
# Small instances of optimal comparison-tree synthesis

A triangle needs two comparisons to find its heaviest edge. A forest needs none.
A pair of parallel edges needs one comparison, even with sparse original labels.
The soft-heap test reaches its first key-raising rank at the threshold used by the algorithm.
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

-- Sixty-four insertions make a rank-three tree. Its first refill at threshold two
-- pools labels 1 and 2. The next extraction returns 1 with the raised key 2.
private def firstRaisedExtraction : Option ((ℕ × ℕ) × ℕ × ℕ × (ℕ × ℕ)) := do
  let heap := (List.range 64).foldl (fun h x => SoftHeap.Forest.insert id 2 x h) []
  let (first, after) ← SoftHeap.Forest.extract id 2 heap
  let (second, _) ← SoftHeap.Forest.extract id 2 after
  return (first, after.corruptions, after.insertions, second)

#guard firstRaisedExtraction == some ((0, 0), 1, 64, (1, 2))

-- Bind two differently weighted copies of the triangle to one compiled tree.
-- The second run starts on the first run's final heap and rewrites only the three generic slots.
private def bindingRecord (next : Pointer) (key : ℕ) :
    Record (model ℕ)
      layout :=
  ⟨fun f => if f = 0 then next else none, fun _ => key⟩

private def runBinding (x : State (model ℕ)
    layout) :
    Option (State (model ℕ)
      layout) :=
  (List.range 57).foldlM
    (fun s _ => step (Binding.program ℕ) s) x

private def reboundTriangle : Option (ℕ × List ℕ × ℕ × List ℕ × Bool) := do
  let input := [bindingRecord (some 1) 0, bindingRecord (some 2) 0, bindingRecord none 0,
    bindingRecord (some 4) 0, bindingRecord (some 5) 1, bindingRecord none 2,
    bindingRecord (some 7) 3, bindingRecord (some 8) 0, bindingRecord none 2]
  let table := Binding.compile triangle input
  let regs (source : ℕ) (r : Fin 4) : Pointer :=
    if r = 0 then some table.2.1 else if r = 1 then some 0 else if r = 2 then some source else none
  let first ← runBinding ⟨12, regs 3, fun _ => 0, table.1⟩
  let second ← runBinding { first with pc := 12, ptr := regs 6 }
  let flags (s : State (model ℕ)
      layout) (indices : List ℕ) := indices.filter fun i =>
    ((s.heap[i]?).bind (fun r => r.ptr 4)) == some i
  return (first.pc, flags first [3, 4, 5], second.pc, flags second [6, 7, 8],
    second.heap.length == table.1.length)

#guard reboundTriangle == some (27, [3, 4], 27, [7, 8], true)

end CslibFrontierTests.PettieRamachandran
