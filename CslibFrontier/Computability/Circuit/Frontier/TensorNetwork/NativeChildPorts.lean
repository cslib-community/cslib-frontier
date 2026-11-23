/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.NativeChild
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Increasing port order through native child networks

The native child preserves each retained vertex's port order. For a rows-first parent whose
ports are increasing, that order agrees with increasing child edge numbers: all ports of a
vertex use the same side, and their new numbers are strict prefix ranks on that side. Packet
ports are increasing by construction.

`DescribedNetwork.ports_eq_filter_edgeEnds` identifies an increasing port list with the incident
edge numbers obtained from endpoint lookup. This lets endpoint access recover the original port
order, without a permutation witness.

`NativeChild.pairwise_ports_nativeChild` is an original invariant for repeated native child
construction. It does not require the generic construction to sort arbitrary parent port lists.
-/

public section

namespace Cslib.Circuits.Frontier.DescribedNetwork

/-- In a rows-first network, increasing ports are exactly the edge numbers whose endpoints
contain the vertex, in increasing order. The ordering assumption is needed to recover the
vertex's assignment order from its incidence relation. -/
theorem ports_eq_filter_edgeEnds {T : Type} {D : DescribedNetwork T} {r : ℕ}
    (hD : D.IsRowsFirstBipartite r) (v : Fin D.vertices.length)
    (hports : D.vertices[v].1.Pairwise (· < ·)) :
    D.vertices[v].1 = (List.range D.numEdges).filter (fun e =>
      (D.edgeEnds.getD e (0, 0)).1 = v ∨ (D.edgeEnds.getD e (0, 0)).2 = v) := by
  apply hports.eq_of_mem_iff (List.pairwise_lt_range.filter _)
  intro e
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · intro he
    have hem : e < D.numEdges := hD.1 _ (List.getElem_mem _) e he
    refine ⟨hem, ?_⟩
    rw [edgeEnds_eq hD, List.getD_ofFn_of_lt _ hem]
    simpa only [Fin.ext_iff] using (mem_ports_iff hD v ⟨e, hem⟩).mp he
  · rintro ⟨hem, he⟩
    apply (mem_ports_iff hD v ⟨e, hem⟩).mpr
    rw [edgeEnds_eq hD, List.getD_ofFn_of_lt _ hem] at he
    simpa only [Fin.ext_iff] using he

end Cslib.Circuits.Frontier.DescribedNetwork

namespace Cslib.Circuits.Frontier.NativeChild

open ChildNumbering

private theorem portRank_lt (groups : List ℕ) (g : ℕ) (ends : List (ℕ × ℕ))
    (sel : ℕ × ℕ → ℕ) {e e' : ℕ}
    (he : groups.getD (sel (ends.getD e (0, 0))) 0 = g) (hee' : e < e') :
    portRank groups g ends sel e < portRank groups g ends sel e' := by
  have hle := (List.range_sublist.2 (Nat.succ_le_of_lt hee')).countP_le
    (p := fun j => decide (groups.getD (sel (ends.getD j (0, 0))) 0 = g))
  simp only [List.range_succ, List.countP_append, List.countP_singleton, he,
    decide_true, ite_true] at hle
  exact hle

private theorem childEdgeOf_lt {T : Type} {D : DescribedNetwork (VertexDesc T)} {r : ℕ}
    (hD : D.IsRowsFirstBipartite r) (groups : List ℕ) (g : ℕ)
    (v : Fin D.vertices.length) (hv : groups.getD v 0 = g) {e e' : ℕ}
    (he : e ∈ D.vertices[v].1) (hee' : e < e') :
    childEdgeOf r groups g D.edgeEnds v e < childEdgeOf r groups g D.edgeEnds v e' := by
  have hem : e < D.numEdges := hD.1 _ (List.getElem_mem _) e he
  have hincident := (DescribedNetwork.mem_ports_iff hD v ⟨e, hem⟩).mp he
  have hends : D.edgeEnds.getD e (0, 0) =
      ((D.srcFin hD ⟨e, hem⟩ : ℕ), (D.tgtFin hD ⟨e, hem⟩ : ℕ)) := by
    rw [DescribedNetwork.edgeEnds_eq hD, List.getD_ofFn_of_lt _ hem]
  by_cases hvr : (v : ℕ) < r
  · have hsrc : D.srcFin hD ⟨e, hem⟩ = v := hincident.resolve_right fun h => by
      have := DescribedNetwork.le_tgtFin hD ⟨e, hem⟩
      rw [h] at this
      omega
    simp only [childEdgeOf, ite_eq_left hvr]
    apply portRank_lt _ _ _ _ _ hee'
    simpa only [hends, hsrc] using hv
  · have htgt : D.tgtFin hD ⟨e, hem⟩ = v := hincident.resolve_left fun h => by
      have := DescribedNetwork.srcFin_lt hD ⟨e, hem⟩
      rw [h] at this
      omega
    simp only [childEdgeOf, ite_eq_right hvr, Nat.add_lt_add_iff_left]
    apply portRank_lt _ _ _ _ _ hee'
    simpa only [hends, htgt] using hv

/-- A native child of a rows-first network with increasing ports again has increasing ports.
The result is independent of the packing's validity: retained ports are renamed monotonically
on their common parent side, and packet ports are filtered edge ranges. -/
theorem pairwise_ports_nativeChild {T : Type} {D : DescribedNetwork (VertexDesc T)} {r : ℕ}
    (hD : D.IsRowsFirstBipartite r) (hports : ∀ v ∈ D.vertices, v.1.Pairwise (· < ·))
    (fl : List ℕ) (a i pt : ℕ) (t : ℤ) (ζ : List ℕ)
    (pk : (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ)) (β : List ℕ) (g : ℕ) :
    ∀ v ∈ (nativeChild fl a i pt t ζ r D pk β g).vertices, v.1.Pairwise (· < ·) := by
  intro w hw
  simp only [nativeChild, List.mem_append, List.mem_map] at hw
  rcases hw with ⟨v, hv, rfl⟩ | ⟨q, _, rfl⟩
  · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hv
    rw [List.getD_eq_getElem _ _ hv.1]
    apply List.pairwise_map.mpr
    exact (hports _ (List.getElem_mem _)).imp_of_mem fun he _ hee' =>
      childEdgeOf_lt hD _ _ ⟨v, hv.1⟩ hv.2 he hee'
  · exact List.pairwise_lt_range.filter _

end Cslib.Circuits.Frontier.NativeChild
