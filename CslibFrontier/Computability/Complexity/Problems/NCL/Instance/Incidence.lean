/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance
import Mathlib.Data.List.Permutation
import Mathlib.Data.Multiset.Filter

/-!
# Checking edge incidences in explicit graph data

For each edge, collect its listed ports and compare them with a pair of opposite directions
carrying one common weight. The weight is read from an actual port.

## Main definitions

* `Cslib.Complexity.NCL.AndOrGraph.checkEdge`: check the two weighted ports of one edge.
* `Cslib.Complexity.NCL.AndOrGraph.checkIncidences`: check all declared edges.
* `Cslib.Complexity.NCL.AndOrGraph.checkValid`: check every structural instance condition.

## Main results

* `Cslib.Complexity.NCL.AndOrGraph.checkEdge_eq_true_iff`: the local check records exact
  multiplicity, opposite directions, and equal weights.
* `Cslib.Complexity.NCL.AndOrGraph.checkValid_eq_true_iff`: recognize exactly valid graph data.
-/

public section

namespace Cslib.Complexity.NCL.AndOrGraph

/-- Check that an edge's listed ports are one opposite pair with a common weight. -/
@[expose] def checkEdge (ps : List (WeightedPort ℕ)) (e : ℕ) : Bool :=
  let qs := ps.filter (fun p => decide (p.port.edge = e))
  qs.any fun p =>
    decide (qs = [⟨⟨e, false⟩, p.weight⟩, ⟨⟨e, true⟩, p.weight⟩]) ||
      decide (qs = [⟨⟨e, true⟩, p.weight⟩, ⟨⟨e, false⟩, p.weight⟩])

private theorem checkEdge_perm_iff (ps : List (WeightedPort ℕ)) (e : ℕ) :
    checkEdge ps e = true ↔ ∃ w, (ps.filter (fun p => decide (p.port.edge = e))).Perm
      [⟨⟨e, false⟩, w⟩, ⟨⟨e, true⟩, w⟩] := by
  unfold checkEdge
  refine ⟨fun h => ?_, fun ⟨w, hw⟩ => List.any_eq_true.2
    ⟨⟨⟨e, false⟩, w⟩, hw.mem_iff.2 (by simp),
      by rcases List.perm_pair.1 hw with hw | hw <;> simp [hw]⟩⟩
  obtain ⟨p, _, hp⟩ := List.any_eq_true.1 h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hp
  exact ⟨p.weight, List.perm_pair.2 hp⟩

/-- The local check is equivalent to exactly two opposite ports of equal weight. -/
theorem checkEdge_eq_true_iff (ps : List (WeightedPort ℕ)) (e : ℕ) :
    checkEdge ps e = true ↔ ∃ w,
      (↑ps : Multiset (WeightedPort ℕ)).filter (fun p => p.port.edge = e) =
        {⟨⟨e, false⟩, w⟩} + {⟨⟨e, true⟩, w⟩} :=
  (checkEdge_perm_iff ps e).trans (exists_congr fun _ => Multiset.coe_eq_coe.symm)

private theorem map_filter_graph (g : AndOrGraph) (hb : g.Bounded) (e : Fin g.edgeCount) :
    Multiset.map (WeightedPort.map Fin.val)
        (g.graph.portMultiset.filter (fun p => p.port.edge = e)) =
      (↑(g.vertices.flatMap Vertex.ports) : Multiset (WeightedPort ℕ)).filter
        (fun p => p.port.edge = e.val) := by
  rw [← graph_portMultiset g hb, Multiset.filter_map]
  congr 1

/-- The raw port records check the same per-edge incidences as the finite semantics. -/
theorem wellFormed_iff_checkEdge (g : AndOrGraph) (hb : g.Bounded) :
    g.graph.WellFormed ↔
      ∀ e : Fin g.edgeCount, checkEdge (g.vertices.flatMap Vertex.ports) e = true := by
  rw [ConstraintGraph.wellFormed_iff_filter]
  refine forall_congr' fun e => ?_
  rw [checkEdge_eq_true_iff]
  refine exists_congr fun w => ?_
  have hp : Multiset.map (WeightedPort.map Fin.val)
      ({⟨⟨e, false⟩, w⟩} + {⟨⟨e, true⟩, w⟩}) =
        {⟨⟨e.val, false⟩, w⟩} + {⟨⟨e.val, true⟩, w⟩} := by
    simp [WeightedPort.map, Port.map]
  rw [← hp, ← map_filter_graph g hb e]
  exact ((Multiset.map_injective (WeightedPort.map_injective Fin.val_injective)).eq_iff).symm

/-- Bounded well-formed data have exactly two listed ports per declared edge. -/
theorem portCount_eq_two_mul (g : AndOrGraph) (hb : g.Bounded) (hw : g.graph.WellFormed) :
    (g.vertices.flatMap Vertex.ports).length = 2 * g.edgeCount := by
  rw [← Multiset.coe_card, ← graph_portMultiset g hb, Multiset.card_map]
  simpa only [Fintype.card_fin] using hw.card_portMultiset

/-- Check every declared edge, scanning only as many indices as there are listed ports. -/
@[expose] def checkIncidences (g : AndOrGraph) : Bool :=
  let ps := g.vertices.flatMap Vertex.ports
  decide (g.edgeCount ≤ ps.length) &&
    (List.range ps.length).all (fun e => if e < g.edgeCount then checkEdge ps e else true)

/-- On bounded data, the incidence checker recognizes precisely well-formed graphs. -/
theorem checkIncidences_eq_true_iff (g : AndOrGraph) (hb : g.Bounded) :
    g.checkIncidences = true ↔ g.graph.WellFormed := by
  simp only [checkIncidences, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range]
  refine ⟨fun ⟨hc, he⟩ => (wellFormed_iff_checkEdge g hb).2 fun e =>
    by simpa only [ite_eq_left e.isLt] using he e (e.isLt.trans_le hc), fun hw => ?_⟩
  have hc := portCount_eq_two_mul g hb hw
  refine ⟨by omega, fun e _ => ?_⟩
  split_ifs with he
  · exact (wellFormed_iff_checkEdge g hb).1 hw ⟨e, he⟩
  · rfl

/-- Check bounded names, AND/OR vertices and consistent opposite endpoints. -/
@[expose] def checkValid (g : AndOrGraph) : Bool :=
  g.checkBounded && (g.checkVertices && g.checkIncidences)

/-- The finite data checker recognizes exactly the graph predicate used by all NCL languages. -/
theorem checkValid_eq_true_iff (g : AndOrGraph) : g.checkValid = true ↔ g.Valid := by
  simp only [checkValid, Bool.and_eq_true, checkBounded_eq_true_iff, Valid]
  exact and_congr_right fun hb =>
    and_congr (checkVertices_eq_true_iff g hb) (checkIncidences_eq_true_iff g hb)

end Cslib.Complexity.NCL.AndOrGraph
