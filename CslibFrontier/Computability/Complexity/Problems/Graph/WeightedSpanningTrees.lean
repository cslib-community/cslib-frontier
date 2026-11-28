/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.ReducedLaplacian
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MatrixTree
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Foundations.Data.List.OfFn

/-!
# Polynomial-time weighted spanning-tree summation

Polynomial-time evaluation of the weighted spanning-tree sum of a finite integer-weighted graph via
Kirchhoff's weighted matrix-tree theorem and `Cslib.Circuits.Rational.detRows_polytime`.

## Main definitions

* `Cslib.Complexity.WeightedEdge`, `Cslib.Complexity.encWeightedEdge`: integer-weighted edges and
  their binary structure encoding.
* `Cslib.Complexity.WeightedGraph`, `Cslib.Complexity.encWeightedGraph`: vertex list paired with
  weighted edge list and its binary structure encoding.
* `Cslib.Complexity.WeightedGraph.pairWeight`: total integer weight between distinct endpoints
  `u` and `v`, ignoring self-loops and combining parallel or opposite-order pairs.
* `Cslib.Complexity.WeightedGraph.weightedSpanningTreeCount`: reduced weighted Laplacian determinant
  over `WG.toGraph.distinctVertices` (`0` when `WG.vertices` is empty).

## Main results

* `Cslib.Complexity.WeightedGraph.weightedSpanningTreeCount_eq_finsum`: equality between
  `weightedSpanningTreeCount WG` and the sum over spanning trees `T ≤ WG.toGraph.induced` of the
  product of edge weights `symWeight WG`.
* `Cslib.Complexity.WeightedGraph.computableInPolyTime_weightedSpanningTreeCount`:
  `weightedSpanningTreeCount` is computable in polynomial time.
* `Cslib.Complexity.WeightedGraph.computableInPolyTime_finsum_isTree`: the weighted spanning-tree
  sum is computable in polynomial time on `encWeightedGraph`.
-/

public section

namespace Cslib.Complexity

open Turing MultiTapeTM

/-- An integer-weighted edge between `u` and `v` of weight `weight`. -/
structure WeightedEdge where
  /-- The first endpoint. -/
  u : ℕ
  /-- The second endpoint. -/
  v : ℕ
  /-- The integer edge weight. -/
  weight : ℤ
  deriving DecidableEq, Repr

/-- Weighted edges are encoded as `(u, v, weight)` in binary. -/
enc_structure encWeightedEdge : WeightedEdge where
  u : encNat, v : encNat, weight : encIntBin

/-- A finite integer-weighted graph: declared vertices `vertices` paired with integer-weighted
edges `edges`. Self-loops (`u = v`) are ignored; parallel or reversed entries contribute additively
to the undirected edge `{u, v}`. -/
structure WeightedGraph where
  /-- The declared vertices of the graph. -/
  vertices : List ℕ
  /-- The integer-weighted edges of the graph. -/
  edges : List WeightedEdge
  deriving DecidableEq, Repr

/-- Weighted graphs are encoded as `(vertices, edges)` in binary. -/
enc_structure encWeightedGraph : WeightedGraph where
  vertices : (encList encNat), edges : (encList encWeightedEdge)

namespace WeightedGraph

/-- Forget the integer weights of a `WeightedGraph` to obtain its underlying `Graph`. -/
abbrev toGraph (WG : WeightedGraph) : Graph :=
  ⟨WG.vertices, WG.edges.map fun e => (e.u, e.v)⟩

/-- Total integer weight assigned by `WG` to the unordered pair of distinct vertices `u ≠ v`
(`0` when `u = v`). -/
@[expose]
def pairWeight (WG : WeightedGraph) (u v : ℕ) : ℤ :=
  if u = v then 0
  else
    ((WG.edges.filter fun e => decide ((e.u = u ∧ e.v = v) ∨ (e.u = v ∧ e.v = u))).map
      WeightedEdge.weight).sum

theorem pairWeight_comm (WG : WeightedGraph) (u v : ℕ) : WG.pairWeight u v = WG.pairWeight v u := by
  by_cases huv : u = v
  · subst huv; rfl
  · simp only [pairWeight, huv, Ne.symm huv, ↓reduceIte, or_comm]

/-- Symmetric `Sym2 ℕ → ℤ` weight function induced by `pairWeight`. -/
def symWeight (WG : WeightedGraph) : Sym2 ℕ → ℤ :=
  Sym2.lift ⟨WG.pairWeight, WG.pairWeight_comm⟩

@[simp]
theorem symWeight_mk (WG : WeightedGraph) (u v : ℕ) :
    WG.symWeight s(u, v) = WG.pairWeight u v :=
  Sym2.lift_mk _ _ _

/-- Entry `(u, v)` of the integer weighted Laplacian of `WG`. -/
@[expose]
def weightedLaplacianEntry (WG : WeightedGraph) (u v : ℕ) : ℤ :=
  if u = v then
    (WG.toGraph.distinctVertices.map fun w => WG.pairWeight u w).sum
  else -WG.pairWeight u v

/-- Exact weighted spanning-tree sum of `WG` computed by evaluating the reduced weighted
Laplacian determinant (`0` when `WG.vertices` is empty). -/
@[expose]
def weightedSpanningTreeCount (WG : WeightedGraph) : ℤ :=
  if WG.toGraph.distinctVertices.isEmpty then 0
  else
    let r := WG.toGraph.distinctVertices.headD 0
    let rest := WG.toGraph.distinctVertices.filter fun v => decide (v ≠ r)
    Cslib.Circuits.Rational.detRows
      (rest.map fun u => rest.map fun v => WG.weightedLaplacianEntry u v)

private theorem distinctVertices_eq_nil_iff {G : Graph} :
    G.distinctVertices = [] ↔ G.1 = [] := by
  rw [← List.length_eq_zero_iff, Graph.length_distinctVertices, Finset.card_eq_zero,
    List.toFinset_eq_empty_iff]

private theorem pairWeight_eq_zero_of_not_adj {WG : WeightedGraph}
    {u v : {v // v ∈ WG.vertices}} (hnadj : ¬ WG.toGraph.induced.Adj u v) :
    WG.pairWeight u.1 v.1 = 0 := by
  by_cases huv : u.1 = v.1
  · simp [pairWeight, huv]
  · simp only [pairWeight, huv, ↓reduceIte]
    have hnot : (u.1, v.1) ∉ WG.toGraph.edges ∧ (v.1, u.1) ∉ WG.toGraph.edges := by
      have : ¬ WG.toGraph.toSimpleGraph.Adj u.1 v.1 := hnadj
      rw [Graph.toSimpleGraph_adj] at this; tauto
    rw [List.filter_eq_nil_iff.2 fun e he hdec => by
      rcases of_decide_eq_true hdec with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hnot.1 (List.mem_map.2 ⟨e, he, Prod.ext h1 h2⟩)
      · exact hnot.2 (List.mem_map.2 ⟨e, he, Prod.ext h1 h2⟩)]
    simp

open Classical in
private lemma weightedLaplacianEntry_eq {WG : WeightedGraph} (u v : {v // v ∈ WG.vertices}) :
    WG.weightedLaplacianEntry u.1 v.1 =
      ((WG.toGraph.induced.weightedAdjMatrix fun e => WG.symWeight (e.map Subtype.val)).laplacian
        u v) := by
  rw [Matrix.laplacian_apply]
  by_cases huv : u = v
  · subst huv
    simp only [weightedLaplacianEntry, ↓reduceIte, SimpleGraph.weightedAdjMatrix_apply,
      SimpleGraph.irrefl, sub_zero]
    rw [← Equiv.sum_comp WG.toGraph.vertexEquiv
        (fun x => if WG.toGraph.induced.Adj u x then WG.symWeight (Sym2.map Subtype.val s(u, x))
          else 0),
      ← Fin.sum_univ_fun_getElem]
    refine Finset.sum_congr rfl fun i _ => ?_
    change WG.pairWeight u.1 WG.toGraph.distinctVertices[i] = _
    rw [← Graph.vertexEquiv_getElem WG.toGraph i]
    split_ifs with hadj
    · simp [symWeight_mk]
    · exact pairWeight_eq_zero_of_not_adj hadj
  · have hne : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
    simp only [weightedLaplacianEntry, hne, ↓reduceIte, huv, SimpleGraph.weightedAdjMatrix_apply,
      zero_sub]
    split_ifs with hadj
    · simp [symWeight_mk]
    · simp [pairWeight_eq_zero_of_not_adj hadj]

/-- **Weighted matrix-tree theorem for `WeightedGraph`**: `weightedSpanningTreeCount WG` equals
the sum over all spanning trees `T ≤ WG.toGraph.induced` of the product of their edge weights. -/
theorem weightedSpanningTreeCount_eq_finsum (WG : WeightedGraph) :
    WG.weightedSpanningTreeCount =
      ∑ᶠ (T : SimpleGraph {v // v ∈ WG.vertices}) (_ : T ≤ WG.toGraph.induced ∧ T.IsTree),
        ∏ᶠ e ∈ T.edgeSet, WG.symWeight (e.map Subtype.val) := by
  classical
  by_cases hempty : WG.toGraph.distinctVertices.isEmpty
  · have h1 : WG.vertices = [] := distinctVertices_eq_nil_iff.1 (List.isEmpty_iff.1 hempty)
    have hno : ∀ T : SimpleGraph {v // v ∈ WG.vertices}, ¬ T.IsTree := fun T hT => by
      obtain ⟨⟨v, hv⟩⟩ := hT.connected.nonempty
      simp [h1] at hv
    simp [weightedSpanningTreeCount, hempty, hno]
  · obtain ⟨r, tail, hd⟩ := List.exists_cons_of_ne_nil (List.isEmpty_iff.not.1 hempty)
    have hr : r ∈ WG.toGraph.distinctVertices := by simp [hd]
    simp only [weightedSpanningTreeCount, hd, List.isEmpty_cons, List.headD_cons,
      Bool.false_eq_true, ↓reduceIte]
    have hdet := detRows_filter_ne_equiv_eq WG.toGraph.nodup_distinctVertices
      (Equiv.subtypeEquivRight fun _ => Graph.mem_distinctVertices) hr
      (WG.toGraph.induced.weightedAdjMatrix fun e => WG.symWeight (e.map Subtype.val)).laplacian
      WG.weightedLaplacianEntry
      fun u v _ _ => weightedLaplacianEntry_eq ⟨u.1, Graph.mem_distinctVertices.1 u.2⟩
        ⟨v.1, Graph.mem_distinctVertices.1 v.2⟩
    simp only [← hd] at hdet ⊢
    rw [hdet]
    exact SimpleGraph.det_laplacian_weightedAdjMatrix_submatrix_eq_finsum_isTree
      (G := WG.toGraph.induced) (fun e => WG.symWeight (e.map Subtype.val))
      ⟨r, Graph.mem_distinctVertices.1 hr⟩

/-! ### Polynomial-time computability -/

@[fun_prop]
theorem computableInPolyTime_toGraph :
    ComputableInPolyTime toGraph encWeightedGraph encGraph := by
  unfold toGraph
  fun_prop

@[fun_prop]
theorem computableInPolyTime_pairWeight :
    ComputableInPolyTime (fun p : (WeightedGraph × ℕ) × ℕ => p.1.1.pairWeight p.1.2 p.2)
      (encPair (encPair encWeightedGraph encNat) encNat) encIntBin := by
  unfold pairWeight
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_pairWeight_comp {γ : Type} {enc : γ ↪ List Bool}
    {WG : γ → WeightedGraph} {u v : γ → ℕ}
    (hWG : ComputableInPolyTime WG enc encWeightedGraph)
    (hu : ComputableInPolyTime u enc encNat) (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun x => (WG x).pairWeight (u x) (v x)) enc encIntBin :=
  computableInPolyTime_pairWeight.comp ((hWG.prod hu).prod hv)

@[fun_prop]
theorem computableInPolyTime_weightedLaplacianEntry :
    ComputableInPolyTime
      (fun p : (WeightedGraph × ℕ) × ℕ => p.1.1.weightedLaplacianEntry p.1.2 p.2)
      (encPair (encPair encWeightedGraph encNat) encNat) encIntBin := by
  unfold weightedLaplacianEntry
  fun_prop

/-- `WeightedGraph.weightedSpanningTreeCount` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_weightedSpanningTreeCount :
    ComputableInPolyTime weightedSpanningTreeCount encWeightedGraph encIntBin := by
  unfold weightedSpanningTreeCount
  exact ComputableInPolyTime.ite' (by fun_prop) (ComputableInPolyTime.const 0)
    (computableInPolyTime_detRows_map (by fun_prop) computableInPolyTime_weightedLaplacianEntry)

/-- The weighted spanning-tree sum of a finite integer-weighted graph is computable in polynomial
time on `encWeightedGraph`. -/
theorem computableInPolyTime_finsum_isTree :
    ComputableInPolyTime
      (fun WG : WeightedGraph =>
        ∑ᶠ (T : SimpleGraph {v // v ∈ WG.vertices}) (_ : T ≤ WG.toGraph.induced ∧ T.IsTree),
          ∏ᶠ e ∈ T.edgeSet, WG.symWeight (e.map Subtype.val))
      encWeightedGraph encIntBin :=
  computableInPolyTime_weightedSpanningTreeCount.of_enc_eq fun WG => by
    rw [weightedSpanningTreeCount_eq_finsum]

end WeightedGraph

end Cslib.Complexity
