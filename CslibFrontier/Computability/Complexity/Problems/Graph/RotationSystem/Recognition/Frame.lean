/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import CslibFrontier.Tactic.EncLen

/-!
# Finite reference-frame structure and storage

Prescribed full words select distinct original dart ends, hence distinct fresh star leaves.
This module checks the reference-order carriers and bounds their full framed storage. It makes
no assertion about realizing the rank crossing bits by a proper plane drawing.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Turing.MultiTapeTM

/-- The stored complete word, or the empty selection at a free/missing entry. -/
abbrev fixedWord (I : FixedRotationInput) (v : ℕ) := (I.orders.getD v none).getD []

/-- Original selected dart indices, in dense-center and prescribed-word order. -/
@[expose] def selectedDarts (I : FixedRotationInput) : List ℕ :=
  (List.range I.graph.vertices.length).flatMap (fixedWord I)

/-- Valid selections retain exact fiber membership and have no repeated dart. -/
theorem fixedWord_spec {I : FixedRotationInput} (hI : Valid I) (v : ℕ) :
    (fixedWord I v).Nodup ∧ ∀ d ∈ fixedWord I v, d ∈ fiber I.graph v := by
  unfold fixedWord
  cases h : I.orders.getD v none with
  | none => simp
  | some word => exact ⟨(hI.2.2.2 v word h).1, fun d => ((hI.2.2.2 v word h).2 d).mp⟩

/-- Distinct original centers select disjoint darts, even when listed edges are loops/parallel. -/
theorem selectedDarts_nodup {I : FixedRotationInput} (hI : Valid I) : (selectedDarts I).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun v _ => (fixedWord_spec hI v).1,
    List.nodup_range.imp fun {u v} huv => List.disjoint_left.mpr fun d hu hv => huv ?_⟩
  exact (mem_fiber.mp ((fixedWord_spec hI u).2 d hu)).2.symm.trans
    (mem_fiber.mp ((fixedWord_spec hI v).2 d hv)).2

/-- At most one selected leaf per actual original dart. -/
theorem length_selectedDarts_le {I : FixedRotationInput} (hI : Valid I) :
    (selectedDarts I).length ≤ 2 * I.graph.edges.length := by
  refine ((selectedDarts_nodup hI).length_le_of_subset fun d hd => ?_).trans_eq
    (List.length_range ..)
  obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hd
  exact List.mem_range.mpr (mem_fiber.mp ((fixedWord_spec hI v).2 d hv)).1

/-- Centers cost one entry each; selected words cost precisely one fresh leaf per dart. -/
theorem length_centerBlocks (I : FixedRotationInput) :
    (centerBlocks I).length = I.graph.vertices.length + (selectedDarts I).length := by
  simp [centerBlocks, selectedDarts, fixedWord, List.length_flatMap, List.sum_map_add,
    Nat.add_comm]

/-- A raw reference order has at most the centers and two copies of the actual dart set. -/
theorem length_referenceOrder_le {I : FixedRotationInput} (hI : Valid I) :
    (referenceOrder I).length ≤ I.graph.vertices.length + 4 * I.graph.edges.length := by
  have hs := length_selectedDarts_le hI
  have hf := List.length_filter_le
    (fun v => !(centerBlocks I).any fun w => decide (w = v))
    ((List.range (2 * I.graph.edges.length)).map fun d => I.graph.vertices.length + d)
  simp only [List.length_map, List.length_range] at hf
  simp only [referenceOrder, List.length_append, length_centerBlocks]
  omega

/-- Every reference-order entry is an actual declared subdivision vertex. -/
theorem mem_referenceOrder_lt {I : FixedRotationInput} (hI : Valid I) {x : ℕ}
    (hx : x ∈ referenceOrder I) : x < subdivisionSize I := by
  unfold subdivisionSize
  rcases List.mem_append.mp hx with hc | hr
  · obtain ⟨v, hv, hx⟩ := List.mem_flatMap.mp hc
    have hv' := List.mem_range.mp hv
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      have := (mem_fiber.mp ((fixedWord_spec hI v).2 d (List.mem_reverse.mp hd))).1
      omega
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hr).1
    have := List.mem_range.mp hd
    omega

/-- Center blocks have distinct original centers and distinct fresh selected leaves. -/
theorem centerBlocks_nodup {I : FixedRotationInput} (hI : Valid I) : (centerBlocks I).Nodup := by
  let block (v : ℕ) := v :: ((fixedWord I v).reverse.map fun d => I.graph.vertices.length + d)
  refine List.nodup_flatMap.mpr ⟨fun v hv => List.nodup_cons.mpr ⟨fun hmem => ?_, ?_⟩,
    List.nodup_range.imp_of_mem fun {u v} hu hv huv => List.disjoint_left.mpr fun x hx hy => ?_⟩
  · obtain ⟨d, _, he⟩ := List.mem_map.mp hmem
    have := List.mem_range.mp hv
    omega
  · exact (List.nodup_reverse.mpr (fixedWord_spec hI v).1).map fun _ _ => Nat.add_left_cancel
  · have hu' := List.mem_range.mp hu
    have hv' := List.mem_range.mp hv
    rcases List.mem_cons.mp (hx : x ∈ block u) with hx | hx <;>
      rcases List.mem_cons.mp (hy : x ∈ block v) with hy | hy
    · exact huv (hx.symm.trans hy)
    · obtain ⟨_, _, he⟩ := List.mem_map.mp hy
      omega
    · obtain ⟨_, _, he⟩ := List.mem_map.mp hx
      omega
    · obtain ⟨d, hd, hdx⟩ := List.mem_map.mp hx
      obtain ⟨e, he, hex⟩ := List.mem_map.mp hy
      obtain rfl : d = e := by omega
      exact huv ((mem_fiber.mp ((fixedWord_spec hI u).2 d (List.mem_reverse.mp hd))).2.symm.trans
        (mem_fiber.mp ((fixedWord_spec hI v).2 d (List.mem_reverse.mp he))).2)

/-- The reference order contains every subdivision vertex exactly once, including isolates. -/
theorem referenceOrder_enumerates {I : FixedRotationInput} (hI : Valid I) :
    (referenceOrder I).Nodup ∧
      ∀ x, x ∈ referenceOrder I ↔ x ∈ List.range (subdivisionSize I) := by
  refine ⟨List.nodup_append'.mpr ⟨centerBlocks_nodup hI,
    (List.nodup_range.map fun _ _ => Nat.add_left_cancel).filter _,
    List.disjoint_left.mpr fun x hx hy => ?_⟩,
    fun x => ⟨fun hx => List.mem_range.mpr (mem_referenceOrder_lt hI hx), fun hx => ?_⟩⟩
  · have hnot := (List.mem_filter.mp hy).2
    rw [List.any_eq_true.mpr ⟨x, hx, by simp⟩] at hnot
    contradiction
  · by_cases hb : x ∈ centerBlocks I
    · exact List.mem_append_left _ hb
    · have hx' := List.mem_range.mp hx
      unfold subdivisionSize at hx'
      have hn : I.graph.vertices.length ≤ x := not_lt.mp fun h => hb
        (List.mem_flatMap.mpr ⟨x, List.mem_range.mpr h, List.mem_cons_self ..⟩)
      refine List.mem_append_right _ (List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨x - I.graph.vertices.length, List.mem_range.mpr (by omega), by omega⟩,
          ?_⟩)
      simp only [Bool.not_eq_true', List.any_eq_false]
      exact fun w hw he => hb (of_decide_eq_true he ▸ hw)

/-- The complete rank table has precisely the declared subdivided vertex count. -/
theorem length_referenceOrder {I : FixedRotationInput} (hI : Valid I) :
    (referenceOrder I).length = subdivisionSize I := by
  obtain ⟨hn, hm⟩ := referenceOrder_enumerates hI
  simpa using ((List.perm_ext_iff_of_nodup hn List.nodup_range).mpr hm).length_eq

/-- Spanning frozen subgraph on every subdivision vertex, retaining precisely flagged segments. -/
@[expose] def frozenGraph (I : FixedRotationInput) : Graph :=
  ⟨List.range (subdivisionSize I), ((subdivide I).filter fun e => e.2).map fun e => e.1⟩

/-- Every frozen segment joins an original center to its own occurrence-indexed fresh leaf.
The original endpoint reader fixes the center uniquely from that leaf. Middle edges are absent. -/
theorem frozen_edge_shape {I : FixedRotationInput} (hI : Valid I) {e : ℕ × ℕ}
    (he : e ∈ (frozenGraph I).edges) :
    ∃ center leaf, center < I.graph.vertices.length ∧ I.graph.vertices.length ≤ leaf ∧
      leaf < subdivisionSize I ∧ (e = (center, leaf) ∨ e = (leaf, center)) ∧
      (I.orders.getD center none).isSome = true ∧
      I.graph.incidenceVertices.getD (leaf - I.graph.vertices.length) 0 = center := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
  obtain ⟨hs, hf⟩ := List.mem_filter.mp hs
  obtain ⟨entry, he, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp he)
  obtain ⟨hu, hw⟩ := hI.edge_endpoints_lt (hv ▸ List.getElem_mem hi)
  change s ∈ [((entry.1.1, I.graph.vertices.length + 2 * entry.2), _),
    ((I.graph.vertices.length + 2 * entry.2, I.graph.vertices.length + 2 * entry.2 + 1), false),
    ((I.graph.vertices.length + 2 * entry.2 + 1, entry.1.2), _)] at hs
  rcases List.mem_cons.mp hs with rfl | hs
  · refine ⟨entry.1.1, I.graph.vertices.length + 2 * entry.2, hu, by omega,
      by unfold subdivisionSize; omega, Or.inl rfl, hf, ?_⟩
    have hr := getD_incidenceVertices_even I.graph entry.2
    rw [List.getD_eq_getElem _ _ hi, hv] at hr
    simpa using hr
  · rcases List.mem_cons.mp hs with rfl | hs
    · cases hf
    · obtain rfl := List.mem_singleton.mp hs
      refine ⟨entry.1.2, I.graph.vertices.length + 2 * entry.2 + 1, hw, by omega,
        by unfold subdivisionSize; omega, Or.inr rfl, hf, ?_⟩
      have hr := getD_incidenceVertices_odd I.graph entry.2
      rw [List.getD_eq_getElem _ _ hi, hv] at hr
      simpa only [show I.graph.vertices.length + 2 * entry.2 + 1 - I.graph.vertices.length =
        2 * entry.2 + 1 by omega] using hr

/-- Every selected subdivision leaf belongs to exactly one center. Together with
`frozen_edge_shape`, this describes disjoint spanning stars and isolated points. -/
theorem frozen_leaf_unique {I : FixedRotationInput} (hI : Valid I) {leaf u v : ℕ}
    (hl : I.graph.vertices.length ≤ leaf)
    (hu : (u, leaf) ∈ (frozenGraph I).edges ∨ (leaf, u) ∈ (frozenGraph I).edges)
    (hv : (v, leaf) ∈ (frozenGraph I).edges ∨ (leaf, v) ∈ (frozenGraph I).edges) : u = v := by
  have center (x : ℕ) (hx : (x, leaf) ∈ (frozenGraph I).edges ∨ (leaf, x) ∈ (frozenGraph I).edges) :
      I.graph.incidenceVertices.getD (leaf - I.graph.vertices.length) 0 = x := by
    rcases hx with hx | hx <;> obtain ⟨c, l, hc, _, _, he | he, _, hread⟩ := frozen_edge_shape hI hx
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact hread
    · have := (Prod.mk.inj he).2
      omega
    · have := (Prod.mk.inj he).1
      omega
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact hread
  exact (center u hu).symm.trans (center v hv)

/-- Full framed algebraic-frame storage is quadratically bounded in uniform original graph
sizes. Unary stride, binary endpoint pairs, frozen flags, and binary reference entries count. -/
theorem length_encFrame_le {I : FixedRotationInput} (hI : Valid I) {K : ℕ} (hK : 1 ≤ K)
    (hn : I.graph.vertices.length ≤ K) (hm : I.graph.edges.length ≤ K) :
    (encFrame (frame I)).length ≤ 400 * K ^ 2 := by
  have hsize : subdivisionSize I ≤ 3 * K := by unfold subdivisionSize; omega
  have hbit {x : ℕ} (hx : x < subdivisionSize I) : (encNat x).length ≤ 3 * K := by
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact (Nat.size_le_self _).trans (hx.le.trans hsize)
  have hsegments : (encList encSegment (frame I).segments).length ≤ 3 * K * (36 * K + 9) := by
    refine (length_encList_le (b := 18 * K + 4) encSegment (frame I).segments fun s hs => ?_).trans
      ?_
    · obtain ⟨ha, hb⟩ := boundedEndpoints_frame hI s hs
      have ha' := hbit ha
      have hb' := hbit hb
      dsimp only [Segment.source, Segment.target, Segment.endpoints] at ha' hb'
      enc_len [encSegment, List.length_singleton]
    · have hseglen : (frame I).segments.length ≤ 3 * K := by
        simpa only [frame, length_subdivide] using Nat.mul_le_mul_left 3 hm
      nlinarith
  have href : (encList encNat (frame I).order).length ≤ 5 * K * (6 * K + 1) := by
    refine (length_encList_le (b := 3 * K) encNat (frame I).order fun _ hx =>
      hbit (mem_referenceOrder_lt hI hx)).trans ?_
    have hord : (frame I).order.length ≤ 5 * K := (length_referenceOrder_le hI).trans (by omega)
    nlinarith
  have hcount : (frame I).vertexCount ≤ 3 * K := hsize
  simp only [encFrame_apply, encFrameFields, length_encPair, encUnary_apply, List.length_replicate]
  nlinarith [Nat.mul_self_le_mul_self hK]

end Cslib.Complexity.Graph.RotationRecognition
