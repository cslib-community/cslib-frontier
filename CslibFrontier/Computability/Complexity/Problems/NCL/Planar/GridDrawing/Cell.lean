/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Strand

/-!
# Drawing a cell with bypass wires

A three-port constraint vertex occupies the center of a layer. Every other strand is a bypass
joining the corresponding top and bottom ports.

## Main definitions

* `Cslib.Complexity.NCL.GridDrawing.Cell.graph`: the exact cell vertex on its strand edges.

## Main results

* `Cslib.Complexity.NCL.GridDrawing.Cell.drawing`: the complete orthogonal drawing of this graph.
-/

public section

namespace Cslib.Complexity.NCL.GridDrawing.Cell

open Diagram GridRouting GridLayout

variable {k a b r : ℕ}

/-- The cell's own input/output edges as layer strands. -/
@[expose] def embed : Fin a ⊕ Fin b → Strand k a b r := Sum.inr ∘ Sum.inl

/-- One exact constraint vertex and its bypass strands. -/
@[expose] def graph (v : Vertex (Fin a ⊕ Fin b)) : ConstraintGraph Unit (Strand k a b r) :=
  fun _ => v.map embed

/-- The port direction of each cell input and output. -/
theorem hasPort_iff {as bs : List Color} (v : Vertex (Fin as.length ⊕ Fin bs.length))
    (hp : v.ports.Perm (genVertex as bs 0).ports)
    (e : Strand k as.length bs.length r) (d : Bool) :
    HasPort (graph v) () e d ↔
      match e with
      | .inr (.inl (.inl _)) => d = true
      | .inr (.inl (.inr _)) => d = false
      | _ => False := by
  change (∃ w, ⟨⟨e, d⟩, w⟩ ∈ (v.map embed).ports) ↔ _
  simp only [Vertex.map, List.mem_map]
  constructor
  · rintro ⟨w, ⟨⟨q, w'⟩, hq, he⟩⟩
    have hq' := hp.mem_iff.1 hq
    simp only [genVertex, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hq'
    rcases hq' with ⟨i, hi⟩ | ⟨j, hi⟩
    all_goals obtain ⟨rfl, rfl⟩ := WeightedPort.mk.inj hi
    all_goals
      simp only [WeightedPort.map, WeightedPort.mk.injEq, Port.map, embed,
        Function.comp_def, Port.mk.injEq] at he
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
      rfl
  · rcases e with i | ((i | j) | j)
    · exact False.elim
    · intro hd
      subst d
      exact ⟨(as.get i).weight, ⟨⟨⟨.inl i, true⟩, (as.get i).weight⟩,
        hp.mem_iff.2 (by simp [genVertex]), rfl⟩⟩
    · intro hd
      subst d
      exact ⟨(bs.get j).weight, ⟨⟨⟨.inr j, false⟩, (bs.get j).weight⟩,
        hp.mem_iff.2 (by simp [genVertex]), rfl⟩⟩
    · exact False.elim

/-- A cell strand has the corresponding vertex incidence. -/
private theorem incident_of_cell {as bs : List Color} (v : Vertex (Fin as.length ⊕ Fin bs.length))
    (hp : v.ports.Perm (genVertex as bs 0).ports)
    {e : Strand k as.length bs.length r} (he : IsCell e) : Incident (graph v) () e := by
  obtain ⟨q, rfl⟩ := he
  cases q with
  | inl i => exact ⟨true, (hasPort_iff v hp _ _).2 rfl⟩
  | inr j => exact ⟨false, (hasPort_iff v hp _ _).2 rfl⟩

/-- The layer routes every strand and preserves the vertex's exact port incidences. -/
@[expose] def drawing {as bs : List Color} (v : Vertex (Fin as.length ⊕ Fin bs.length))
    (hp : v.ports.Perm (genVertex as bs 0).ports) (L : Layer k as.length bs.length r) :
    Open (graph (k := k) (r := r) v) inputStrand outputStrand where
  height := L.height
  height_pos := L.height_pos
  vertex _ := L.center
  vertex_injective := fun x y _ => Subsingleton.elim x y
  vertex_rows _ := L.center_rows
  vertex_separation v w h := (h (Subsingleton.elim v w)).elim
  source := L.source
  target := L.target
  trace := L.Trace
  edge_rows := L.edge_rows
  path := L.connected
  row_le := L.row_le
  top_iff e x := by
    rw [L.top_iff]
    exact ⟨fun ⟨i, hi, hx⟩ => ⟨i, inputStrand_of_index e i hi, hx⟩,
      fun ⟨i, hi, hx⟩ => ⟨i, by rw [← hi]; exact inputIndex_inputStrand i, hx⟩⟩
  bottom_iff e x := by
    rw [L.bottom_iff]
    exact ⟨fun ⟨j, hj, hx⟩ => ⟨j, outputStrand_of_index e j hj, hx⟩,
      fun ⟨j, hj, hx⟩ => ⟨j, by rw [← hj]; exact outputIndex_outputStrand j, hx⟩⟩
  source_top i := L.source_of_input _ i (inputIndex_inputStrand i)
  target_bottom j := L.target_of_output _ j (outputIndex_outputStrand j)
  source_spec e := by
    rcases e with i | ((i | j) | j)
    · exact .inl ⟨_, inputStrand_of_index _ _ rfl⟩
    · exact .inl ⟨_, inputStrand_of_index _ _ rfl⟩
    · exact .inr ⟨(), (hasPort_iff v hp _ false).2 rfl, rfl⟩
    · exact .inl ⟨_, inputStrand_of_index _ _ rfl⟩
  target_spec e := by
    rcases e with i | ((i | j) | j)
    · exact .inl ⟨_, outputStrand_of_index _ _ rfl⟩
    · exact .inr ⟨(), (hasPort_iff v hp _ true).2 rfl, rfl⟩
    · exact .inl ⟨_, outputStrand_of_index _ _ rfl⟩
    · exact .inl ⟨_, outputStrand_of_index _ _ rfl⟩
  source_port _ e he := by
    have hh := (hasPort_iff v hp e false).1 he
    rcases e with i | ((i | j) | j) <;> first | contradiction | rfl
  target_port _ e he := by
    have hh := (hasPort_iff v hp e true).1 he
    rcases e with i | ((i | j) | j) <;> first | contradiction | rfl
  vertex_meet e _ he := by exact incident_of_cell v hp (L.vertex_meet e he)
  meet e f p hef he hf := by
    obtain ⟨hpoint, he, hf⟩ := L.meet hef p he hf
    exact ⟨(), hpoint, incident_of_cell v hp he, incident_of_cell v hp hf⟩

end Cslib.Complexity.NCL.GridDrawing.Cell
