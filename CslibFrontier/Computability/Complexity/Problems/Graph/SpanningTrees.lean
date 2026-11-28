/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Rational.Runtime.Determinant
public import CslibFrontier.Computability.Complexity.Problems.Graph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MatrixTree
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Counting spanning trees in polynomial time

The number of spanning trees of the graph `G.induced` of a vertex and edge list `G : Graph` is
computable in polynomial time (`Cslib.Complexity.Graph.computableInPolyTime_spanningTreeCount`).
The program `Cslib.Complexity.Graph.spanningTreeCount` tabulates the reduced Laplacian of
`G.induced` on the distinct declared vertices other than the first one, and returns its
determinant by Bird's division-free algorithm `Cslib.Circuits.Rational.detRows`. By Kirchhoff's
matrix-tree theorem `SimpleGraph.det_lapMatrix_submatrix_eq_natCard_isTree`, this is the number of
spanning trees (`Cslib.Complexity.Graph.spanningTreeCount_eq_natCard`). A graph without declared
vertices has no spanning tree, since a tree is nonempty.

## Main definitions

* `Cslib.Complexity.Graph.laplacianEntry`: an entry of the Laplacian of `G.induced`, from the edge
  list.
* `Cslib.Complexity.Graph.reducedLaplacianRows`: the reduced Laplacian as a list of integer rows.
* `Cslib.Complexity.Graph.spanningTreeCount`: its determinant, or `0` without vertices.

## Main results

* `Cslib.Complexity.Graph.spanningTreeCount_eq_natCard`: `spanningTreeCount G` is the number of
  spanning trees `T ≤ G.induced`.
* `Cslib.Complexity.Graph.computableInPolyTime_spanningTreeCount`: it is computable in polynomial
  time from `Cslib.Complexity.encGraph` to binary integers.
* `Cslib.Complexity.Graph.computableInPolyTime_natCard_isTree`: the number of spanning trees of
  `G.induced` is computable in polynomial time from `encGraph` to binary natural numbers.

## References

* [G. Kirchhoff, *Ueber die Auflösung der Gleichungen, auf welche man bei der Untersuchung der
  linearen Vertheilung galvanischer Ströme geführt wird*][Kirchhoff1847]
-/

public section

namespace Cslib.Complexity.Graph

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Circuits.Rational

/-- The entry at `(u, v)` of the Laplacian of `G.induced` on the distinct declared vertices: the
number of neighbours of `u` on the diagonal, and `-1` or `0` off the diagonal according to
adjacency. -/
@[expose] def laplacianEntry (G : Graph) (u v : ℕ) : ℤ :=
  if u = v then ((G.distinctVertices.filter fun w => G.adjBool u w).length : ℤ)
  else if G.adjBool u v then -1 else 0

/-- The reduced Laplacian of `G.induced` on the distinct declared vertices other than the first,
as a list of integer rows. -/
@[expose] def reducedLaplacianRows (G : Graph) : List (List ℤ) :=
  G.distinctVertices.tail.map fun u => G.distinctVertices.tail.map fun v => G.laplacianEntry u v

/-- The number of spanning trees of `G.induced`, computed by the matrix-tree theorem as the
determinant of the reduced Laplacian; `0` when `G` declares no vertex. -/
@[expose] def spanningTreeCount (G : Graph) : ℤ :=
  if G.distinctVertices = [] then 0 else detRows G.reducedLaplacianRows

/-! ### Correctness -/

/-- The degree of a declared vertex in `G.induced` is its number of neighbours among the distinct
declared vertices. -/
private theorem degree_induced (G : Graph) (u : {v // v ∈ G.vertices}) :
    G.induced.degree u = (G.distinctVertices.filter fun w => G.adjBool u w).length := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← List.toFinset_card_of_nodup (G.nodup_distinctVertices.filter _)]
  refine Finset.card_bij (fun v _ => (v : ℕ))
    (fun v hv => by
      simp only [List.mem_toFinset, List.mem_filter, mem_distinctVertices, adjBool_eq_true_iff]
      exact ⟨v.2, (G.induced.mem_neighborFinset u v).1 hv⟩)
    (fun _ _ _ _ h => Subtype.ext h) fun w hw => ?_
  simp only [List.mem_toFinset, List.mem_filter, mem_distinctVertices, adjBool_eq_true_iff] at hw
  exact ⟨⟨w, hw.1⟩, (G.induced.mem_neighborFinset u ⟨w, hw.1⟩).2 hw.2, rfl⟩

/-- The entries of a tabulated square table over a list. -/
private theorem rowEntry_map_map (l : List ℕ) (g : ℕ → ℕ → ℤ) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) : rowEntry (l.map fun u => l.map fun v => g u v) i j = g l[i] l[j] := by
  simp [rowEntry, List.getD_eq_getElem?_getD, hi, hj]

/-- The entries of the reduced Laplacian rows are Laplacian entries of the remaining vertices. -/
private theorem rowEntry_reducedLaplacianRows (G : Graph) {i j : ℕ}
    (hi : i < G.distinctVertices.tail.length) (hj : j < G.distinctVertices.tail.length) :
    rowEntry G.reducedLaplacianRows i j =
      G.laplacianEntry G.distinctVertices.tail[i] G.distinctVertices.tail[j] :=
  rowEntry_map_map _ _ hi hj

/-- **Correctness of `spanningTreeCount`**: it is the number of spanning trees of `G.induced`, by
Kirchhoff's matrix-tree theorem. -/
theorem spanningTreeCount_eq_natCard (G : Graph) :
    G.spanningTreeCount =
      Nat.card {T : SimpleGraph {v // v ∈ G.vertices} // T ≤ G.induced ∧ T.IsTree} := by
  unfold spanningTreeCount
  split_ifs with h
  · have : IsEmpty {v // v ∈ G.vertices} :=
      ⟨fun v => by simpa [h] using mem_distinctVertices.2 v.2⟩
    rw [Nat.card_eq_zero.2 (Or.inl ⟨fun T => this.elim T.2.2.connected.nonempty.some⟩)]
    rfl
  · obtain ⟨a, rest, hvs⟩ := List.exists_cons_of_ne_nil h
    have hnd := List.nodup_cons.1 (hvs ▸ G.nodup_distinctVertices)
    have htail : G.distinctVertices.tail = rest := by rw [hvs, List.tail_cons]
    have hmem : ∀ {w}, w ∈ rest → w ∈ G.vertices :=
      fun hw => mem_distinctVertices.1 (hvs ▸ List.mem_cons_of_mem _ hw)
    set r : {v // v ∈ G.vertices} := ⟨a, mem_distinctVertices.1 (hvs ▸ List.mem_cons_self)⟩
    have hlen : G.reducedLaplacianRows.length = rest.length := by
      rw [reducedLaplacianRows, List.length_map, htail]
    let f : Fin G.reducedLaplacianRows.length → {v : {v // v ∈ G.vertices} // v ≠ r} := fun i =>
      ⟨⟨rest[i.1]'(hlen ▸ i.2), hmem (List.getElem_mem _)⟩, fun hr => hnd.1 <| by
        rw [← show rest[i.1]'(hlen ▸ i.2) = a from congrArg Subtype.val hr]
        exact List.getElem_mem _⟩
    have hf : Function.Bijective f :=
      ⟨fun _ _ hij => Fin.ext ((hnd.2.getElem_inj_iff).1 (congrArg (fun v => v.1.1) hij)),
       fun ⟨⟨w, hw⟩, hwr⟩ =>
        let ⟨k, hk, hkw⟩ := List.getElem_of_mem <|
          (List.mem_cons.1 (hvs ▸ mem_distinctVertices.2 hw)).resolve_left fun h =>
            hwr (Subtype.ext h)
        ⟨⟨k, hlen ▸ hk⟩, by simp [f, hkw]⟩⟩
    rw [detRows_eq_det_ofRows, ← SimpleGraph.det_lapMatrix_submatrix_eq_natCard_isTree r,
      ← Matrix.det_submatrix_equiv_self (Equiv.ofBijective f hf)]
    congr 1
    ext i j
    simp only [ofRows, Matrix.of_apply, Matrix.submatrix_apply]
    rw [rowEntry_reducedLaplacianRows G (htail ▸ hlen ▸ i.2) (htail ▸ hlen ▸ j.2)]
    simp only [f, Equiv.ofBijective_apply, SimpleGraph.lapMatrix, Matrix.sub_apply,
      SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply, laplacianEntry, htail]
    by_cases hij : i = j
    · subst hij
      simp [degree_induced]
    · have hne : rest[i.1]'(hlen ▸ i.2) ≠ rest[j.1]'(hlen ▸ j.2) :=
        fun h => hij (Fin.ext ((hnd.2.getElem_inj_iff).1 h))
      have hne' : (⟨rest[i.1]'(hlen ▸ i.2), hmem (List.getElem_mem _)⟩ : {v // v ∈ G.vertices}) ≠
          ⟨rest[j.1]'(hlen ▸ j.2), hmem (List.getElem_mem _)⟩ :=
        fun h => hne (congrArg Subtype.val h)
      by_cases hadj : G.toSimpleGraph.Adj (rest[i.1]'(hlen ▸ i.2)) (rest[j.1]'(hlen ▸ j.2)) <;>
        simp [hne, hne', hadj]

/-! ### Polynomial time -/

/-- Dropping the first distinct vertex is polynomial-time. -/
private theorem computableInPolyTime_tail_distinctVertices :
    ComputableInPolyTime (fun G : Graph => G.distinctVertices.tail) encGraph (encList encNat) := by
  simpa only [Function.comp_def, List.drop_one] using
    (dropUnary (encA := encNat)).comp (computableInPolyTime_distinctVertices.prod (const 1))

/-- Tabulating a Laplacian entry is polynomial-time. -/
private theorem computableInPolyTime_laplacianEntry :
    ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => p.1.1.laplacianEntry p.1.2 p.2)
      (encPair (encPair encGraph encNat) encNat) encIntBin := by
  fun_prop [laplacianEntry]

/-- Tabulating the reduced Laplacian rows is polynomial-time. -/
private theorem computableInPolyTime_reducedLaplacianRows :
    ComputableInPolyTime reducedLaplacianRows encGraph (encList (encList encIntBin)) :=
  mapWithInput computableInPolyTime_tail_distinctVertices <|
    mapWithInput (computableInPolyTime_tail_distinctVertices.comp (fst _ _))
      computableInPolyTime_laplacianEntry

/-- **Counting spanning trees is polynomial-time**: `spanningTreeCount` is computable in
polynomial time from encoded graphs to binary integers. -/
theorem computableInPolyTime_spanningTreeCount :
    ComputableInPolyTime spanningTreeCount encGraph encIntBin :=
  ite_decide (decide_eq' computableInPolyTime_distinctVertices (const []))
    (const 0) (detRows_polytime.comp computableInPolyTime_reducedLaplacianRows)

/-- **Counting spanning trees is polynomial-time**: the number of spanning trees of the graph
`G.induced` induced on the declared vertices is computable in polynomial time from encoded graphs to
binary natural numbers. -/
theorem computableInPolyTime_natCard_isTree :
    ComputableInPolyTime
      (fun G : Graph =>
        Nat.card {T : SimpleGraph {v // v ∈ G.vertices} // T ≤ G.induced ∧ T.IsTree})
      encGraph encNat := by
  have hfun : (fun G : Graph =>
      Nat.card {T : SimpleGraph {v // v ∈ G.vertices} // T ≤ G.induced ∧ T.IsTree}) =
      fun G => G.spanningTreeCount.toNat :=
    funext fun G => by rw [spanningTreeCount_eq_natCard, Int.toNat_natCast]
  rw [hfun]
  exact intBin_toNat.comp computableInPolyTime_spanningTreeCount

end Cslib.Complexity.Graph
