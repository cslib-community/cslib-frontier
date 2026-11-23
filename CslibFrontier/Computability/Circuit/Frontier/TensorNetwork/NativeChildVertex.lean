/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.NativeChildPolyTime
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.SortedCount

/-!
# Numbered vertex provenance in a native child

A retained parent vertex occupies the position given by the number of earlier vertices in its
group. Packet vertices follow all retained vertices, in packet order. The lookup theorems identify
the complete vertex at each such number: the retained descriptor with renumbered ports, or the
packet context, ordered port tags and packet-major exponent slice.

These are original list semantics of `NativeChild.nativeChild`. They apply even to arbitrary
packing data and do not assert a machine resource bound.

## Main results

* `NativeChild.getElem?_vertices_nativeChild_retained`: the exact vertex at a selected parent's
  prefix-count position.
* `NativeChild.getElem?_vertices_nativeChild_packet`: the exact vertex at a packet's offset.
* `NativeChild.getElem?_vertices_nativeChild_iff`: every successful numbered lookup has one of
  these two forms, with the precise parent rank or packet offset.
-/

public section

namespace Cslib.Circuits.Frontier.NativeChild

open ChildNumbering

private theorem countP_take_range_groupsOf (r i k : ℕ)
    (words : List (List ℕ) × List (List ℕ)) (g v : ℕ) :
    ((List.range k).take v).countP (fun u => (groupsOf r i k words).getD u 0 = g) =
      ((groupsOf r i k words).take v).count g := by
  simp only [groupsOf, ← List.map_take, List.count_eq_countP, List.countP_map]
  apply List.countP_congr
  intro u hu
  have hu' : u < k := List.mem_range.mp (List.mem_of_mem_take hu)
  simp only [Function.comp_apply, List.getD_map_range _ 0 hu', beq_eq_decide]

private theorem length_filter_range_groupsOf (r i k : ℕ)
    (words : List (List ℕ) × List (List ℕ)) (g : ℕ) :
    ((List.range k).filter fun u => (groupsOf r i k words).getD u 0 = g).length =
      (groupsOf r i k words).count g := by
  have h := countP_take_range_groupsOf r i k words g k
  rw [List.take_range, Nat.min_self,
    List.take_of_length_le (by simp [groupsOf]), List.countP_eq_length_filter] at h
  exact h

private theorem getElem?_filter_range_groupsOf (r i k : ℕ)
    (words : List (List ℕ) × List (List ℕ)) (g : ℕ) {v : ℕ} (hv : v < k)
    (hg : (groupsOf r i k words).getD v 0 = g) :
    ((List.range k).filter fun u => (groupsOf r i k words).getD u 0 = g)[
      ((groupsOf r i k words).take v).count g]? = some v := by
  have h := List.getElem?_filter_countP_take
    (fun u => decide ((groupsOf r i k words).getD u 0 = g))
    (l := List.range k) (r := v) (by simpa using hv) (by simpa using hg)
  rwa [countP_take_range_groupsOf, List.getElem_range] at h

variable {T : Type} (fl : List ℕ) (a i pt : ℕ) (t : ℤ) (ζ : List ℕ) (r : ℕ)
  (D : DescribedNetwork (VertexDesc T))
  (pk : (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ)) (β : List ℕ) (g : ℕ)

/-- At its prefix-count number, a selected parent vertex keeps its descriptor and the order of
its ports, with every port replaced by its numbered child edge. -/
theorem getElem?_vertices_nativeChild_retained {v : ℕ} (hv : v < D.vertices.length)
    (hg : (groupsOf r i D.vertices.length pk.1).getD v 0 = g) :
    let groups := groupsOf r i D.vertices.length pk.1
    (nativeChild fl a i pt t ζ r D pk β g).vertices[(groups.take v).count g]? =
      some (((D.vertices.getD v defaultVertex).1.map (childEdgeOf r groups g D.edgeEnds v)),
        (D.vertices.getD v defaultVertex).2) := by
  dsimp only
  have hsel := getElem?_filter_range_groupsOf r i D.vertices.length pk.1 g hv hg
  have hbound := (List.getElem?_eq_some_iff.mp hsel).1
  simp only [nativeChild]
  rw [List.getElem?_append_left (by simpa only [List.length_map] using hbound),
    List.getElem?_map, hsel]
  rfl

/-- Packet `q` occupies the first packet position plus `q`, with its exact context, ordered row
and slot tags, and packet-major exponent slice. -/
theorem getElem?_vertices_nativeChild_packet {q : ℕ}
    (hq : let (_, numPackets, _) := pk; q < numPackets) :
    let (wordTables, _, packetSlots) := pk
    let groups := groupsOf r i D.vertices.length wordTables
    let cedges := childEdgeList groups g D.edgeEnds (packetSlots.map Prod.fst)
    let ports := childPorts cedges (groups.count g + q)
    (nativeChild fl a i pt t ζ r D pk β g).vertices[groups.count g + q]? =
      some (ports, .inr (packetCtx fl a i pt t ζ g q,
        ports.map (fun j =>
          (decide (j < (portEdges groups g D.edgeEnds Prod.fst).length),
            (packetSlots.getD (parentEdge groups g D.edgeEnds j) (0, 0)).2)),
        betaSlice i pt β q)) := by
  dsimp only
  simp only [nativeChild, List.getElem?_append, List.length_map,
    length_filter_range_groupsOf]
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, List.getElem?_map,
    List.getElem?_range hq]
  rfl

/-- A successful numbered lookup identifies either a selected parent at its exact prefix-count
position or a packet at its exact offset, including the complete descriptor and ordered ports.
The bounds exclude defaulted parent reads and out-of-range packet numbers. -/
theorem getElem?_vertices_nativeChild_iff {k : ℕ} {vertex : List ℕ × VertexDesc T} :
    let (wordTables, numPackets, packetSlots) := pk
    let groups := groupsOf r i D.vertices.length wordTables
    let cedges := childEdgeList groups g D.edgeEnds (packetSlots.map Prod.fst)
    (nativeChild fl a i pt t ζ r D pk β g).vertices[k]? = some vertex ↔
      (∃ v, v < D.vertices.length ∧ groups.getD v 0 = g ∧ (groups.take v).count g = k ∧
        vertex = (((D.vertices.getD v defaultVertex).1.map
            (childEdgeOf r groups g D.edgeEnds v)),
          (D.vertices.getD v defaultVertex).2)) ∨
      ∃ q, q < numPackets ∧ groups.count g + q = k ∧
        vertex = (childPorts cedges (groups.count g + q),
          .inr (packetCtx fl a i pt t ζ g q,
            (childPorts cedges (groups.count g + q)).map (fun j =>
              (decide (j < (portEdges groups g D.edgeEnds Prod.fst).length),
                (packetSlots.getD (parentEdge groups g D.edgeEnds j) (0, 0)).2)),
            betaSlice i pt β q)) := by
  dsimp only
  constructor
  · intro h
    by_cases hk : k < (groupsOf r i D.vertices.length pk.1).count g
    · have hk' : k < ((List.range D.vertices.length).filter fun u =>
          (groupsOf r i D.vertices.length pk.1).getD u 0 = g).length := by
        rwa [length_filter_range_groupsOf]
      let v := ((List.range D.vertices.length).filter fun u =>
        (groupsOf r i D.vertices.length pk.1).getD u 0 = g)[k]
      have hv := List.mem_filter.mp (List.getElem_mem hk')
      have hbound : v < D.vertices.length := List.mem_range.mp hv.1
      have hgroup : (groupsOf r i D.vertices.length pk.1).getD v 0 = g :=
        of_decide_eq_true hv.2
      obtain ⟨hrank, hget⟩ := List.getElem?_eq_some_iff.mp
        (getElem?_filter_range_groupsOf r i D.vertices.length pk.1 g hbound hgroup)
      have hindex : ((groupsOf r i D.vertices.length pk.1).take v).count g = k :=
        (List.nodup_range.filter _).getElem_inj_iff.mp hget
      have hvget := getElem?_vertices_nativeChild_retained fl a i pt t ζ r D pk β g hbound hgroup
      dsimp only at hvget
      rw [hindex] at hvget
      exact Or.inl ⟨v, hbound, hgroup, hindex, Option.some.inj (h.symm.trans hvget)⟩
    · have hbound := (List.getElem?_eq_some_iff.mp h).1
      rw [length_vertices_nativeChild, childRows] at hbound
      have hq : k - (groupsOf r i D.vertices.length pk.1).count g < pk.2.1 := by omega
      have hindex : (groupsOf r i D.vertices.length pk.1).count g +
          (k - (groupsOf r i D.vertices.length pk.1).count g) = k := by omega
      have hqget := getElem?_vertices_nativeChild_packet fl a i pt t ζ r D pk β g hq
      dsimp only at hqget
      rw [hindex] at hqget
      refine Or.inr ⟨_, hq, hindex, ?_⟩
      simpa only [hindex] using Option.some.inj (h.symm.trans hqget)
  · rintro (⟨v, hv, hg, hindex, rfl⟩ | ⟨q, hq, hindex, rfl⟩)
    · rw [← hindex]
      exact getElem?_vertices_nativeChild_retained fl a i pt t ζ r D pk β g hv hg
    · rw [← hindex]
      exact getElem?_vertices_nativeChild_packet fl a i pt t ζ r D pk β g hq

end Cslib.Circuits.Frontier.NativeChild
