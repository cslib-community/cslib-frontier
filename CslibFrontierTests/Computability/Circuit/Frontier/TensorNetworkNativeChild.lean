/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.NativeCall
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.NativeChildPorts

public section

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.NativeChild

namespace Cslib.Tests.TensorNetworkNativeChild

/-! ### A path with one row and two columns

The row `0` joins the columns `1` and `2` by the edges `0` and `1`, and the vertices carry tables.
The network is rows-first at `1`, and the ends of its edges are computed from the ports. -/

/-- The tables of the vertices. -/
def table (n : ℕ) : VertexDesc (List ℕ) := .inl (List.replicate n 1)

/-- The row `0` with ports `1, 0` (not in edge order), the columns `1` and `2`. -/
def path : DescribedNetwork (VertexDesc (List ℕ)) :=
  ⟨2, [([1, 0], table 4), ([0], table 2), ([1], table 2)]⟩

example : path.IsRowsFirstBipartite 1 := by decide

example : ¬ path.IsRowsFirstBipartite 2 := by decide

example : path.edgeEnds = [(0, 1), (0, 2)] := by decide

/-- The native child of group `0` for a packing that puts the row and the column `1` in group `0`,
the column `2` in group `1`, and both edges in packet `0` with slots `0` and `1`. -/
def child : DescribedNetwork (VertexDesc (List ℕ)) :=
  nativeChild [1] 1 0 3 (-1) [0] 1 path (([[0]], [[0], [1]]), 1, [(0, 0), (0, 1)]) [] 0

/-- The child keeps the row and the column `1`, and adds the packet: three child edges, the two
row ports of group `0` and the column port of edge `0`. -/
example : child.numEdges = 3 := by decide

/-- The row keeps its parent's port order, renumbered (edge `1` is row port `1`, edge `0` row port
`0`); the column `1` reads the column port `2`; the packet reads all three child edges in order. -/
example : child.vertices.map Prod.fst = [[1, 0], [2], [0, 1, 2]] := by decide

/-- The packet tags its ports as row ports, row ports and a column port, with the slots of their
parent edges. -/
example : (child.vertices.getD 2 ([], .inl [])).2.getRight?.map (fun d => d.2.1) =
    some [(true, 0), (true, 1), (false, 0)] := by decide

example : childRows 1 0 path (([[0]], [[0], [1]]), 1, [(0, 0), (0, 1)]) 0 = 2 := by decide

example : child.IsRowsFirstBipartite 2 := by decide

-- Rows-first validity permits unsorted ports, and the native child does preserve that order.
-- Consequently the sorted-port preservation theorem needs its parent-order hypothesis.
example : ¬ (path.vertices.getD 0 ([], .inl [])).1.Pairwise (· < ·) ∧
    ¬ (child.vertices.getD 0 ([], .inl [])).1.Pairwise (· < ·) := by decide

private def sortedPath : DescribedNetwork (VertexDesc (List ℕ)) :=
  ⟨2, [([0, 1], table 4), ([0], table 2), ([1], table 2)]⟩

private theorem sortedPath_ports : ∀ v ∈ sortedPath.vertices, v.1.Pairwise (· < ·) := by
  intro v hv
  simp only [sortedPath, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl <;> decide

-- The same topology with sorted parent ports propagates the invariant to retained vertices and
-- the new packet together, without a separate permutation witness.
example : ∀ v ∈ (nativeChild [1] 1 0 3 (-1) [0] 1 sortedPath
    (([[0]], [[0], [1]]), 1, [(0, 0), (0, 1)]) [] 0).vertices,
    v.1.Pairwise (· < ·) := by
  exact pairwise_ports_nativeChild (by decide) sortedPath_ports _ _ _ _ _ _ _ _ _

-- Endpoint incidence recovers the precise ordered ports for this invariant, including columns.
example (v : Fin sortedPath.vertices.length) :
    sortedPath.vertices[v].1 = (List.range sortedPath.numEdges).filter (fun e =>
      (sortedPath.edgeEnds.getD e (0, 0)).1 = v ∨
        (sortedPath.edgeEnds.getD e (0, 0)).2 = v) :=
  DescribedNetwork.ports_eq_filter_edgeEnds (r := 1) (by decide) v
    (sortedPath_ports _ (List.getElem_mem _))

-- Equal incidence alone does not recover the arbitrary order of the unsorted parent.
example : path.vertices[0].1 ≠ (List.range path.numEdges).filter (fun e =>
    (path.edgeEnds.getD e (0, 0)).1 = 0 ∨ (path.edgeEnds.getD e (0, 0)).2 = 0) := by decide

/-! ### The modes of a node -/

example : modeWeights 2 2 3 = [1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3] := by decide

example : betaSlice 0 3 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] 1 = [7, 8, 9, 10, 11, 12] := by
  decide

end Cslib.Tests.TensorNetworkNativeChild
