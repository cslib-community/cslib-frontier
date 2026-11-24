/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantSeededAncestry

/-!
# A seeded native child shared by compressed origin and endpoint queries

A two-vertex, one-edge parent is split with an actual finite seed. The selected row retains its
original descriptor and port, its compressed origin is unique, and the endpoint game accepts
the resulting genuine edge while rejecting the first out-of-range edge. Both interpretations
are constructed from the same seed without a label-table or endpoint-representation premise.
-/

public section

namespace Turing.MultiTapeTM.DescendantSeededAncestry.Tests

open Cslib BalancedSchedules Circuits.Frontier NativeChild NativeChild.EndpointQuery
open DescendantVertex DescendantEndpoint

/-- A rows-first parent with one edge and two distinct original descriptors. -/
@[expose] def parent : DescribedNetwork (VertexDesc ℕ) :=
  ⟨1, [([0], .inl 7), ([0], .inl 11)]⟩

private theorem parent_rows : parent.IsRowsFirstBipartite 1 := by decide

/-- One actual finite seed with all four coefficients zero. -/
@[expose] def seed : SeededLabels.Seed 2 6 := fun _ => 0

/-- The group selected by the seed at the first parent vertex. -/
@[expose] noncomputable def group : Fin 64 :=
  (PacketPacking.Seeded.wordEquiv 1 (SeededLabels.label 2 6 seed 0)) 0

/-- The common label code table for this concrete split. -/
@[expose] noncomputable def labels : Labels := Labels.ofSeed 2 1 seed 0 group

/-- The actual native child, whose new packets are created at precision three. -/
@[expose] noncomputable def child : DescribedNetwork (VertexDesc ℕ) :=
  nativeChild [1] 1 0 3 (-1) [4] 1 parent
    (labels.nativePacking 1 parent.edgeEnds) [10, 11, 12] group

/-- The compressed frame stores the exact parent sizes and the same seed. -/
@[expose] noncomputable def seedFrame : Frame :=
  Frame.ofSeed (U := 2) (a := 1) 1 seed 0 group

/-- The semantic ancestry is constructed from the seed without a label-agreement premise. -/
@[expose] noncomputable def ancestry : NativeAncestry parent [seedFrame] child :=
  NativeAncestry.cons_ofSeed (root := parent) (D := parent) .nil (a := 1)
    seed 0 group [1] 3 (-1) [4] 1 [10, 11, 12]

private theorem child_rows : child.IsRowsFirstBipartite (labels.groups.count (group : ℕ)) :=
  labels.isRowsFirstBipartite_nativeChild parent rfl 1 parent_rows group.isLt
    [1] 3 (-1) [4] [10, 11, 12]

private theorem represented : DescendantEndpoint.Represents parent.vertices.length
    parent.edgeEnds [seedFrame] child.vertices.length child.edgeEnds :=
  DescendantEndpoint.Represents.cons_nativeChild (a := 1) .nil parent_rows seed 0 group
    [1] 3 (-1) [4] [10, 11, 12]

private theorem symbol_zero : symbol seedFrame 0 = group := by
  have h := symbol_ofSeed (U := 2) (a := 1) 1 seed 0 group ⟨0, by decide⟩
  change symbol seedFrame 0 = (group : ℕ) at h
  exact h

private theorem retained_vertex : child.vertices[0]? = some ([0], .inl 7) := by
  have hg : (groupsOf 1 0 parent.vertices.length
      (labels.nativePacking 1 parent.edgeEnds).1).getD 0 0 = group := by
    change (groupsOf 1 labels.coordinate labels.vertices
      (labels.nativePacking 1 parent.edgeEnds).1).getD 0 0 = (group : ℕ)
    rw [labels.groupsOf_nativePacking]
    rfl
  have h := NativeChild.getElem?_vertices_nativeChild_retained [1] 1 0 3 (-1) [4] 1
    parent (labels.nativePacking 1 parent.edgeEnds) [10, 11, 12] group (v := 0) (by decide) hg
  simpa only [child, List.take_zero, List.count_nil, parent, List.getD_cons_zero, List.map_cons,
    List.map_nil, childEdgeOf, Nat.zero_lt_succ, ↓reduceIte, portRank, List.range_zero,
    List.countP_nil] using h

private theorem vertex_valid : 0 < child.vertices.length :=
  (List.getElem?_eq_some_iff.mp retained_vertex).1

private theorem edge_valid : 0 < child.numEdges :=
  child_rows.1 ([0], .inl 7) (List.mem_of_getElem? retained_vertex) 0 (by simp)

/-- The original descriptor and its numerical origin agree in the actual native child. -/
theorem retained_origin_and_descriptor : (child.vertices[0]?).map Prod.snd = some (.inl 7) ∧
    HasOrigin child.vertices.length 0 ⟨0, 0⟩ [seedFrame] ∧
      ∀ origin, HasOrigin child.vertices.length 0 origin [seedFrame] → origin = ⟨0, 0⟩ := by
  have horigin : HasOrigin child.vertices.length 0 ⟨0, 0⟩ [seedFrame] := by
    refine ⟨vertex_valid, Or.inr ⟨by decide, 0, by decide, symbol_zero, ?_, ?_⟩⟩
    · simp [retained]
    · exact ⟨by decide, rfl, rfl⟩
  refine ⟨by simp [retained_vertex], horigin, ?_⟩
  intro origin ho
  exact HasOrigin.unique ho horigin

/-- The root endpoint relation on the concrete parent edge table. -/
@[expose] def base : EndpointQuery :=
  ⟨parent.edgeEnds.length,
    fun e p => e < parent.edgeEnds.length ∧ parent.edgeEnds.getD e (0, 0) = p⟩

private theorem base_represents : base.Represents parent.edgeEnds := ⟨rfl, fun _ _ => Iff.rfl⟩

/-- The endpoint game accepts a genuine child edge and rejects the first invalid index. -/
theorem endpoint_boundaries :
    DescendantEndpoint.accepts base [seedFrame] 0 (child.edgeEnds.getD 0 (0, 0)) ∧
    ¬ DescendantEndpoint.accepts base [seedFrame] child.numEdges (0, 0) := by
  constructor
  · apply (accepts_iff_of_represents base base_represents represented 0 _).mpr
    exact ⟨by simpa only [DescribedNetwork.edgeEnds, List.length_map, List.length_range]
      using edge_valid, rfl⟩
  · rw [accepts_iff_of_represents base base_represents represented]
    simp only [DescribedNetwork.edgeEnds, List.length_map, List.length_range, lt_self_iff_false,
      false_and, not_false_eq_true]

/-- The constructed ancestry retrieves the original descriptor through the birth API. -/
theorem original_birth : ancestry.birthDescriptor ⟨0, 0⟩ = some (.inl 7) := rfl

/-- The genuine packet containing the sole parent edge. -/
@[expose] noncomputable def packet : Fin (labels.packing parent.edgeEnds).numPackets :=
  (labels.packing parent.edgeEnds).packet ⟨0, by decide⟩

/-- The actual seeded packet and its compressed birth lookup both retain precision three. -/
theorem packet_creation_precision :
    ((child.vertices[labels.groups.count (group : ℕ) + packet.val]?).bind fun vertex =>
      match vertex.2 with
      | .inl _ => none
      | .inr desc => some desc.1.p) = some 3 ∧
    (DescendantBirth.lookup (DescendantBirth.calls ancestry) ⟨1, packet.val⟩).map
      (fun birth => birth.parameters.precision) = some 3 := by
  constructor
  · have h := labels.getElem?_vertices_nativeChild_packet parent rfl 1 [1] 3 (-1)
      [4] [10, 11, 12] packet.isLt
    change child.vertices[labels.groups.count (group : ℕ) + packet.val]? = _ at h
    rw [h]
    rfl
  · have h := DescendantBirth.lookup_cons_ofSeed (NativeAncestry.nil (root := parent))
      (a := 1) seed 0 group [1] 3 (-1) [4] 1 [10, 11, 12] packet.val
    exact congrArg
      (Option.map (fun birth : DescendantBirth.Birth => birth.parameters.precision)) h

end Turing.MultiTapeTM.DescendantSeededAncestry.Tests
