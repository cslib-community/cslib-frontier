/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.DFS.TopologicalSort
public import CslibFrontier.Algorithms.WordRAM.DFS
public meta import CslibFrontier.Algorithms.WordRAM.DFS
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval

/-!
# Depth-first search and topological sort: worked examples

Kernel-checked examples (no `native_decide`) of depth-first search and topological sort: a DAG
with its topological order, a cyclic graph and a self-loop, on which topological sort is not a
topological order, reachability from a single root, and the standard-basis word-RAM topological
sort `Cslib.Algorithms.WordRAM.DFS.topoProgram` on the CSR encoding, including the edgeless graph,
the empty graph, a self-loop and parallel arcs.
-/

public section

namespace CslibFrontierTests.DFS

open Cslib.Algorithms.Lean.DFS
open Cslib.WordRAM

/-! ### A DAG -/

/-- The diamond `0 → 1, 0 → 2, 1 → 3, 2 → 3`. -/
def diamond : Fin 4 → List (Fin 4)
  | 0 => [1, 2]
  | 1 => [3]
  | 2 => [3]
  | 3 => []

example : topologicalSort diamond (List.finRange 4) = [0, 2, 1, 3] := by decide +kernel

example : IsTopologicalOrder diamond [0, 2, 1, 3] := ⟨by decide, by decide, by decide⟩

/-- `[0, 1, 3, 2]` is not a topological order: the edge `2 → 3` goes backwards. -/
example : ¬ IsTopologicalOrder diamond [0, 1, 3, 2] := fun h => by
  have := h.sublist 2 3 (by decide)
  revert this
  decide

/-- The diamond is acyclic, witnessed by an explicit topological order. -/
example : Relation.Acyclic (Edge diamond) :=
  acyclic_iff_exists_isTopologicalOrder.2 ⟨[0, 1, 2, 3], by decide, by decide, by decide⟩

/-! ### Cyclic graphs -/

/-- The triangle `0 → 1 → 2 → 0`. -/
def triangle : Fin 3 → List (Fin 3)
  | 0 => [1]
  | 1 => [2]
  | 2 => [0]

theorem not_acyclic_triangle : ¬ Relation.Acyclic (Edge triangle) := fun h =>
  h.irrefl 0
    (.tail (.tail (.single (by decide : Edge triangle 0 1)) (by decide : Edge triangle 1 2))
      (by decide : Edge triangle 2 0))

/-- On the triangle, topological sort still lists every vertex once, but it is not a topological
order. -/
example : (topologicalSort triangle (List.finRange 3)).Nodup ∧
    ¬ IsTopologicalOrder triangle (topologicalSort triangle (List.finRange 3)) :=
  ⟨nodup_topologicalSort List.mem_finRange, fun h =>
    not_acyclic_triangle ((isTopologicalOrder_topologicalSort_iff List.mem_finRange).1 h)⟩

/-- A self-loop is a cycle. -/
def selfLoop : Fin 1 → List (Fin 1) := fun _ => [0]

example : ¬ ∃ l, IsTopologicalOrder selfLoop l := fun h =>
  (acyclic_iff_exists_isTopologicalOrder.2 h).irrefl 0 (.single (by decide))

/-! ### Reachability -/

/-- From the root `1` of the diamond, depth-first search finishes `3` and then `1`. -/
example : (dfs diamond 4 [1]).finished = [1, 3] := by decide +kernel

example : (0 : Fin 4) ∉ (dfs diamond 4 [1]).visited := by
  rw [mem_dfs_visited_iff (by simp)]
  rintro ⟨r, hr, h⟩
  obtain rfl : r = 1 := by simpa using hr
  -- every vertex reachable from `1` lies in `{1, 3}`
  have key : ∀ v, Relation.ReflTransGen (Edge diamond) 1 v → v = 1 ∨ v = 3 := by
    intro v hv
    induction hv with
    | refl => exact .inl rfl
    | tail _ he ih =>
      rcases ih with rfl | rfl
      · exact .inr (by simpa [Edge, diamond] using he)
      · simp [Edge, diamond] at he
  simpa using key 0 h

/-! ### Word-RAM topological sort on the CSR encoding -/

private meta def runTopo (G : Cslib.Algorithms.WordRAM.DFS.Graph) (w : ℕ) :
    Option (List ℕ × Bool) :=
  (Cslib.Algorithms.WordRAM.DFS.topoCode.eval w w (Data.init G.encodeCSR)).map fun (y, t) =>
    (outputList y.mem (y.regs Cslib.Algorithms.WordRAM.DFS.Reg.outReg),
      decide (t < 128 * (G.n + G.m + 1)))

/-- The diamond as a CSR graph: `4` vertices and `4` arcs. -/
abbrev diamondG : Cslib.Algorithms.WordRAM.DFS.Graph := ⟨4, diamond⟩

example : diamondG.encodeCSR = [4, 4, 0, 2, 3, 4, 4, 1, 2, 3, 3] := by decide +kernel

example : ∃ n, ExecutesList 16 Cslib.Algorithms.WordRAM.DFS.topoProgram
    (State.init diamondG.encodeCSR) [0, 2, 1, 3] n ∧ n ≤ 128 * (4 + 4 + 1) := by
  have h := Cslib.Algorithms.WordRAM.DFS.computesListInTime_topoProgram diamondG 16
    (by decide +kernel) (diamondG.inputFits_encodeCSR (by decide +kernel))
  have hw : Cslib.Algorithms.WordRAM.DFS.topoWords diamondG = [0, 2, 1, 3] := by decide +kernel
  have hm : diamondG.m = 4 := by decide +kernel
  dsimp only at h
  rwa [hw, hm] at h

/-- The triangle, a self-loop, parallel arcs `0 ⇉ 1`, the edgeless graph on three vertices, and
the empty graph. -/
abbrev triangleG : Cslib.Algorithms.WordRAM.DFS.Graph := ⟨3, triangle⟩
abbrev selfLoopG : Cslib.Algorithms.WordRAM.DFS.Graph := ⟨1, selfLoop⟩
abbrev parallelG : Cslib.Algorithms.WordRAM.DFS.Graph :=
  ⟨2, fun v => if v = 0 then [1, 1] else []⟩
abbrev edgelessG : Cslib.Algorithms.WordRAM.DFS.Graph := ⟨3, fun _ => []⟩
abbrev emptyG : Cslib.Algorithms.WordRAM.DFS.Graph := ⟨0, fun v => v.elim0⟩

/-- info: some ([0, 2, 1, 3], true) -/
#guard_msgs in
#eval runTopo diamondG 16

/-- info: (some ([0, 1, 2], true), some ([0], true), some ([0, 1], true)) -/
#guard_msgs in
#eval (runTopo triangleG 16, runTopo selfLoopG 16, runTopo parallelG 16)

/-- info: (some ([2, 1, 0], true), some ([], true)) -/
#guard_msgs in
#eval (runTopo edgelessG 16, runTopo emptyG 16)

end CslibFrontierTests.DFS
