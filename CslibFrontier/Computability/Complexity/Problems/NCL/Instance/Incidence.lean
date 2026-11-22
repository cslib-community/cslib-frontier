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
@[expose] def checkEdge (ps : List (Port ℕ × ℕ)) (e : ℕ) : Bool :=
  let qs := ps.filter (fun p => decide (p.1.edge = e))
  qs.any fun p =>
    decide (qs = [(⟨e, false⟩, p.2), (⟨e, true⟩, p.2)]) ||
      decide (qs = [(⟨e, true⟩, p.2), (⟨e, false⟩, p.2)])

private theorem checkEdge_perm_iff (ps : List (Port ℕ × ℕ)) (e : ℕ) :
    checkEdge ps e = true ↔ ∃ w, (ps.filter (fun p => decide (p.1.edge = e))).Perm
      [(⟨e, false⟩, w), (⟨e, true⟩, w)] := by
  unfold checkEdge
  constructor
  · intro h
    obtain ⟨p, _, hp⟩ := List.any_eq_true.1 h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hp
    exact ⟨p.2, List.perm_pair.2 hp⟩
  · rintro ⟨w, hw⟩
    have hp : (⟨e, false⟩, w) ∈ ps.filter (fun p => decide (p.1.edge = e)) :=
      hw.mem_iff.2 (by simp)
    refine List.any_eq_true.2 ⟨(⟨e, false⟩, w), hp, ?_⟩
    rcases List.perm_pair.1 hw with hw | hw <;> simp [hw]

/-- The local check is equivalent to exactly two opposite ports of equal weight. -/
theorem checkEdge_eq_true_iff (ps : List (Port ℕ × ℕ)) (e : ℕ) :
    checkEdge ps e = true ↔ ∃ w,
      (↑ps : Multiset (Port ℕ × ℕ)).filter (fun p => p.1.edge = e) =
        {(⟨e, false⟩, w)} + {(⟨e, true⟩, w)} := by
  rw [checkEdge_perm_iff]
  apply exists_congr
  intro w
  exact Multiset.coe_eq_coe.symm

private theorem map_filter_graph (g : AndOrGraph) (hb : g.Bounded) (e : Fin g.edgeCount) :
    Port.mapMultiset Fin.val (g.graph.portMultiset.filter (fun p => p.1.edge = e)) =
      (↑(g.vertices.flatMap Vertex.ports) : Multiset (Port ℕ × ℕ)).filter
        (fun p => p.1.edge = e.val) := by
  rw [← graph_portMultiset g hb]
  change Multiset.map (fun p : Port (Fin g.edgeCount) × ℕ => (p.1.map Fin.val, p.2)) _ =
    (Multiset.map (fun p : Port (Fin g.edgeCount) × ℕ => (p.1.map Fin.val, p.2)) _).filter _
  rw [Multiset.filter_map]
  congr 1

/-- The raw port records check the same per-edge incidences as the finite semantics. -/
theorem wellFormed_iff_checkEdge (g : AndOrGraph) (hb : g.Bounded) :
    g.graph.WellFormed ↔
      ∀ e : Fin g.edgeCount, checkEdge (g.vertices.flatMap Vertex.ports) e = true := by
  rw [ConstraintGraph.wellFormed_iff_filter]
  apply forall_congr'
  intro e
  rw [checkEdge_eq_true_iff]
  apply exists_congr
  intro w
  have hp : Port.mapMultiset Fin.val
      ({(⟨e, false⟩, w)} + {(⟨e, true⟩, w)}) =
        {(⟨e.val, false⟩, w)} + {(⟨e.val, true⟩, w)} := by
    simp [Port.mapMultiset, Port.map]
  constructor
  · intro h
    have hh := congrArg (Port.mapMultiset Fin.val) h
    rwa [map_filter_graph g hb e, hp] at hh
  · intro h
    apply Port.mapMultiset_injective Fin.val_injective
    rw [map_filter_graph g hb e, hp]
    exact h

/-- Bounded well-formed data have exactly two listed ports per declared edge. -/
theorem portCount_eq_two_mul (g : AndOrGraph) (hb : g.Bounded) (hw : g.graph.WellFormed) :
    (g.vertices.flatMap Vertex.ports).length = 2 * g.edgeCount := by
  have hh := congrArg Multiset.card (graph_portMultiset g hb)
  change (Multiset.map (fun p : Port (Fin g.edgeCount) × ℕ => (p.1.map Fin.val, p.2))
    g.graph.portMultiset).card = (g.vertices.flatMap Vertex.ports).length at hh
  rw [Multiset.card_map] at hh
  rw [← hh]
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
  constructor
  · rintro ⟨hc, he⟩
    apply (wellFormed_iff_checkEdge g hb).2
    intro e
    simpa only [ite_eq_left e.isLt] using he e (e.isLt.trans_le hc)
  · intro hw
    have hc := portCount_eq_two_mul g hb hw
    refine ⟨by omega, fun e _ => ?_⟩
    split_ifs with he
    · exact (wellFormed_iff_checkEdge g hb).1 hw ⟨e, he⟩
    · rfl

/-- Check bounded names, AND/OR vertices, self-loops, and consistent opposite endpoints. -/
@[expose] def checkValid (g : AndOrGraph) : Bool :=
  g.checkBounded && (g.checkVertices && g.checkIncidences)

/-- The finite data checker recognizes exactly the graph predicate used by all NCL languages. -/
theorem checkValid_eq_true_iff (g : AndOrGraph) : g.checkValid = true ↔ g.Valid := by
  simp only [checkValid, Bool.and_eq_true]
  constructor
  · rintro ⟨hb, hv, hi⟩
    have hb := (checkBounded_eq_true_iff g).1 hb
    have hv := (checkVertices_eq_true_iff g hb).1 hv
    exact ⟨hb, hv.1, (checkIncidences_eq_true_iff g hb).1 hi, hv.2⟩
  · rintro ⟨hb, ha, hw, hl⟩
    exact ⟨(checkBounded_eq_true_iff g).2 hb, (checkVertices_eq_true_iff g hb).2 ⟨ha, hl⟩,
      (checkIncidences_eq_true_iff g hb).2 hw⟩

end Cslib.Complexity.NCL.AndOrGraph
