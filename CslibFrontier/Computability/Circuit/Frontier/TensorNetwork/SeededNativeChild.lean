/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.SeededChildEndpoints
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.NativeChildEndpoints
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.NativeChildVertex
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Native described children of a seeded packing

`Labels.nativePacking` writes the label words, packet numbers and slots of `Labels.packing`
into the format used by `NativeChild.nativeChild`. This mathematical table is used to identify
descriptors; it is not an additional input to the compressed machines.

The child is rows-first, has exactly the retained and packet vertices counted by the compressed
endpoint representation, and has exactly `Labels.edges` as its reconstructed endpoint table.
These facts use the supplied labels, including labels obtained from `Labels.ofSeed`; no equality
with the canonical full-table packing is assumed.
-/

public section

namespace Cslib.Circuits.Frontier.NativeChild.EndpointQuery

open PacketPacking ChildNumbering

/-- The word tables, packet count and packet/slot pairs of the supplied labels, in the native
child's existing format. The row boundary only splits the common vertex label table. -/
@[expose] noncomputable def Labels.nativePacking (l : Labels) (rows : ℕ)
    (es : List (ℕ × ℕ)) :
    (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ) :=
  let word v := List.ofFn fun j => ((Seeded.wordEquiv l.coordinates (l.code v)) j).val
  (((List.range rows).map word,
    (List.range (l.vertices - rows)).map fun v => word (rows + v)),
    (l.packing es).numPackets,
    List.ofFn fun e => (((l.packing es).packet e).val, ((l.packing es).slot e).val))

/-- Splitting the label words at the row boundary leaves the group at every vertex unchanged. -/
theorem Labels.groupsOf_nativePacking (l : Labels) (rows : ℕ) (es : List (ℕ × ℕ)) :
    groupsOf rows l.coordinate l.vertices (l.nativePacking rows es).1 = l.groups := by
  simp only [groupsOf, Labels.nativePacking, Labels.groups]
  apply List.map_congr_left
  intro v hv
  have hv' := List.mem_range.mp hv
  by_cases hrow : v < rows
  · simp only [hrow, ↓reduceIte, List.getD_map_range _ [] hrow, List.getD_ofFn,
      Labels.symbol]
  · have hcol : v - rows < l.vertices - rows := by omega
    have hindex : rows + (v - rows) = v := by omega
    simp only [hrow, ↓reduceIte, List.getD_map_range _ [] hcol, hindex,
      List.getD_ofFn, Labels.symbol]

/-- The packet/slot word uses precisely the numbered packing of the supplied labels. -/
theorem Labels.packetSlots_nativePacking (l : Labels) (rows : ℕ) (es : List (ℕ × ℕ))
    (e : Fin es.length) :
    ((packingPacketSlots (l.nativePacking rows es)).getD e (0, 0)) =
      (((l.packing es).packet e).val, ((l.packing es).slot e).val) := by
  simp only [packingPacketSlots, Labels.nativePacking, List.getD_ofFn]

/-- A native slot lookup reads the supplied packing's slot at a genuine parent edge and returns
zero at an out-of-range edge. -/
theorem Labels.slot_nativePacking (l : Labels) (rows : ℕ) (es : List (ℕ × ℕ)) (e : ℕ) :
    ((packingPacketSlots (l.nativePacking rows es)).getD e (0, 0)).2 =
      if h : e < es.length then ((l.packing es).slot ⟨e, h⟩).val else 0 := by
  by_cases he : e < es.length
  · rw [dite_eq_left he]
    exact congrArg Prod.snd (l.packetSlots_nativePacking rows es ⟨e, he⟩)
  · rw [dite_eq_right he,
      List.getD_eq_default _ _ (by simp [packingPacketSlots, Labels.nativePacking]; omega)]

private theorem packets_nativePacking (l : Labels) (rows : ℕ) (es : List (ℕ × ℕ)) :
    (packingPacketSlots (l.nativePacking rows es)).map Prod.fst =
      List.ofFn fun e => ((l.packing es).packet e).val := by
  simp only [packingPacketSlots, Labels.nativePacking, List.map_ofFn]
  rfl

variable {T : Type} (l : Labels) (D : DescribedNetwork (VertexDesc T))
  (hsize : l.vertices = D.vertices.length) (rows : ℕ)

include hsize in
/-- The complete native child has the exact vertex universe used by the seeded endpoint game,
including packet vertices with no incident child edges. -/
theorem Labels.length_vertices_nativeChild (fl : List ℕ) (pt : ℕ) (t : ℤ) (ζ β : List ℕ) :
    (nativeChild fl l.coordinates l.coordinate pt t ζ rows D
      (l.nativePacking rows D.edgeEnds) β l.group).vertices.length =
        l.groups.count l.group + (l.packing D.edgeEnds).numPackets := by
  rw [NativeChild.length_vertices_nativeChild, childRows]
  have hgroups := l.groupsOf_nativePacking rows D.edgeEnds
  rw [hsize] at hgroups
  rw [hgroups]
  rfl

include hsize in
/-- A packet descriptor carries the actual seeded slot of every parent edge, the row-side bit
in child-port order, and its packet-major exponent slice at the creation precision. -/
theorem Labels.getElem?_vertices_nativeChild_packet (fl : List ℕ) (pt : ℕ) (t : ℤ)
    (ζ β : List ℕ) {q : ℕ} (hq : q < (l.packing D.edgeEnds).numPackets) :
    let ports := childPorts (l.edges D.edgeEnds) (l.groups.count l.group + q)
    (nativeChild fl l.coordinates l.coordinate pt t ζ rows D
      (l.nativePacking rows D.edgeEnds) β l.group).vertices[l.groups.count l.group + q]? =
      some (ports, .inr (packetCtx fl l.coordinates l.coordinate pt t ζ l.group q,
        ports.map (fun j =>
          (decide (j < (portEdges l.groups l.group D.edgeEnds Prod.fst).length),
            if he : parentEdge l.groups l.group D.edgeEnds j < D.edgeEnds.length then
              ((l.packing D.edgeEnds).slot
                ⟨parentEdge l.groups l.group D.edgeEnds j, he⟩).val
            else 0)),
        betaSlice l.coordinate pt β q)) := by
  have h := NativeChild.getElem?_vertices_nativeChild_packet fl l.coordinates l.coordinate
    pt t ζ rows D (l.nativePacking rows D.edgeEnds) β l.group hq
  dsimp only at h
  have hgroups := l.groupsOf_nativePacking rows D.edgeEnds
  rw [hsize] at hgroups
  have hpackets := packets_nativePacking l rows D.edgeEnds
  change (l.nativePacking rows D.edgeEnds).2.2.map Prod.fst = _ at hpackets
  have hslots (e : ℕ) : ((l.nativePacking rows D.edgeEnds).2.2.getD e (0, 0)).2 =
      if he : e < D.edgeEnds.length then ((l.packing D.edgeEnds).slot ⟨e, he⟩).val else 0 :=
    l.slot_nativePacking rows D.edgeEnds e
  rw [hgroups, hpackets] at h
  simpa only [Labels.edges, hslots] using h

include hsize in
private theorem groupsOf_nativePacking_ofFn :
    groupsOf rows l.coordinate D.vertices.length (l.nativePacking rows D.edgeEnds).1 =
      List.ofFn fun v : Fin D.vertices.length =>
        ((Seeded.wordEquiv l.coordinates (l.code v)) l.coordinate).val := by
  have hgroups := l.groupsOf_nativePacking rows D.edgeEnds
  rw [hsize] at hgroups
  rw [hgroups, Labels.groups, hsize, List.map_range_eq_ofFn]
  rfl

private theorem nativePacking_data (hcount : D.edgeEnds.length = D.numEdges) :
    (packingPacketSlots (l.nativePacking rows D.edgeEnds)) = List.ofFn fun e : Fin D.numEdges =>
      (((l.packing D.edgeEnds).packet (Fin.cast hcount.symm e)).val,
        ((l.packing D.edgeEnds).slot (Fin.cast hcount.symm e)).val) :=
  List.ofFn_congr hcount _

include hsize in
private theorem nativeChild_properties (hD : D.IsRowsFirstBipartite rows)
    (hgroup : l.group < 64) (fl : List ℕ) (pt : ℕ) (t : ℤ) (ζ β : List ℕ) :
    let child := nativeChild fl l.coordinates l.coordinate pt t ζ rows D
      (l.nativePacking rows D.edgeEnds) β l.group
    child.IsRowsFirstBipartite (l.groups.count l.group) ∧ child.edgeEnds = l.edges D.edgeEnds := by
  have hcount : D.edgeEnds.length = D.numEdges := by
    simp only [DescribedNetwork.edgeEnds, List.length_map, List.length_range]
  let group (v : Fin D.vertices.length) := (Seeded.wordEquiv l.coordinates (l.code v)) l.coordinate
  let packet (e : Fin D.numEdges) := (l.packing D.edgeEnds).packet (Fin.cast hcount.symm e)
  let slot (e : Fin D.numEdges) := ((l.packing D.edgeEnds).slot (Fin.cast hcount.symm e)).val
  have hgroups := groupsOf_nativePacking_ofFn l D hsize rows
  have hdata := nativePacking_data l D rows hcount
  have hrows := isRowsFirstBipartite_nativeChild_of_packing hD group packet slot
    ⟨l.group, hgroup⟩ fl l.coordinates l.coordinate pt t ζ β
    (l.nativePacking rows D.edgeEnds) hgroups rfl hdata
  have hends := NativeChild.edgeEnds_nativeChild hD group packet slot
    ⟨l.group, hgroup⟩ fl l.coordinates l.coordinate pt t ζ β
    (l.nativePacking rows D.edgeEnds) hgroups rfl hdata
  have hwords := l.groupsOf_nativePacking rows D.edgeEnds
  rw [hsize] at hwords
  rw [hwords, packets_nativePacking] at hends
  exact ⟨by simpa only [childRows, hwords] using hrows, hends⟩

include hsize in
/-- The seeded packing produces a rows-first native child, with its retained vertices as rows. -/
theorem Labels.isRowsFirstBipartite_nativeChild (hD : D.IsRowsFirstBipartite rows)
    (hgroup : l.group < 64) (fl : List ℕ) (pt : ℕ) (t : ℤ) (ζ β : List ℕ) :
    (nativeChild fl l.coordinates l.coordinate pt t ζ rows D
      (l.nativePacking rows D.edgeEnds) β l.group).IsRowsFirstBipartite
        (l.groups.count l.group) :=
  (nativeChild_properties l D hsize rows hD hgroup fl pt t ζ β).1

include hsize in
/-- Reading endpoints back from the native child's actual port lists gives exactly the child
edge table verified by the compressed seeded endpoint game. -/
theorem Labels.edgeEnds_nativeChild (hD : D.IsRowsFirstBipartite rows)
    (hgroup : l.group < 64) (fl : List ℕ) (pt : ℕ) (t : ℤ) (ζ β : List ℕ) :
    (nativeChild fl l.coordinates l.coordinate pt t ζ rows D
      (l.nativePacking rows D.edgeEnds) β l.group).edgeEnds = l.edges D.edgeEnds :=
  (nativeChild_properties l D hsize rows hD hgroup fl pt t ζ β).2

end Cslib.Circuits.Frontier.NativeChild.EndpointQuery
