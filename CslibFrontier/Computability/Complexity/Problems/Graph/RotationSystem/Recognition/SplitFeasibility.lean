/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Split
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Declarations
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Equality
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.ContractionGenus
import CslibFrontier.Foundations.GroupTheory.Perm.InsertTwo
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Feasibility of a directed consecutive-block split

The appended connector is contracted in its literal direction, from the fresh hub to the
original vertex. Splitting and contracting retain the direction of the selected block,
including a full fiber, a singleton block, and separate ends of loops. The connector need
not be a bridge. This is an original finite recovery prerequisite, not a parity-query
criterion or a Hanani–Tutte theorem.

## Main results

* `Cslib.Complexity.Graph.RotationRecognition.feasible_split_iff`: exact directed block
  feasibility on the original graph and its fresh-hub split.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Equiv RotationSystem
open Equiv.Perm.Insertion Equiv.Perm.CycleSurgery

private theorem mem_successor_block {α : Type} (f : Perm α) (L : List α)
    (hn : 0 < L.length) (hnd : L.Nodup)
    (hs : ∀ i, (hi : i + 1 < L.length) → f L[i] = L[i + 1]) (a : α) :
    f a ∈ L ↔ a = f.symm L[0] ∨ (a ∈ L ∧ a ≠ L[L.length - 1]) := by
  constructor
  · intro ha
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
    rcases eq_or_ne i 0 with rfl | hz
    · exact Or.inl (f.injective (he.symm.trans (f.apply_symm_apply _).symm))
    · have hp : i - 1 + 1 < L.length := by omega
      have heq : a = L[i - 1] := f.injective (by
        rw [hs (i - 1) hp]
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using he.symm)
      refine Or.inr ⟨heq.symm ▸ List.getElem_mem (by omega), ?_⟩
      intro h
      have := hnd.getElem_inj_iff.mp (heq.symm.trans h)
      omega
  · rintro (rfl | ⟨ha, hlast⟩)
    · rw [f.apply_symm_apply]
      exact List.getElem_mem hn
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      have hnext : i + 1 < L.length := lt_of_le_of_ne hi fun h =>
        hlast (by simp only [← h, Nat.add_sub_cancel])
      rw [hs i hnext]
      exact List.getElem_mem hnext

private theorem block_boundary {α : Type} (f : Perm α) (L : List α)
    (hn : 0 < L.length) (hnd : L.Nodup)
    (hs : ∀ i, (hi : i + 1 < L.length) → f L[i] = L[i + 1]) :
    (f.symm L[0] ∈ L ↔ f.symm L[0] = L[L.length - 1]) ∧
      (f L[L.length - 1] ∈ L ↔ f.symm L[0] = L[L.length - 1]) := by
  have hlast : L[L.length - 1] ∈ L := List.getElem_mem (by omega)
  have hmem := mem_successor_block f L hn hnd hs
  refine ⟨⟨fun ha => by_contra fun hne => ?_, fun h => h.symm ▸ hlast⟩, ?_⟩
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
    have hnext : i + 1 < L.length := lt_of_le_of_ne hi fun h =>
      hne (he.symm.trans (by simp only [← h, Nat.add_sub_cancel]))
    have hz : L[i + 1] = L[0] := (hs i hnext).symm.trans
      (congrArg f he |>.trans (f.apply_symm_apply _))
    have := hnd.getElem_inj_iff.mp hz
    omega
  · simp only [hmem, ne_self_iff_false, and_false, or_false, eq_comm]

private def splitBase (I : FixedRotationInput) (block : List ℕ) : Graph :=
  ⟨List.range (I.graph.vertices.length + 1),
    I.graph.edges.zipIdx.map fun ((source, target), index) =>
      (redirectEnd I.graph.vertices.length block (2 * index) source,
        redirectEnd I.graph.vertices.length block (2 * index + 1) target)⟩

private theorem redirect_restore {n v d old : ℕ} {block : List ℕ}
    (hold : old < n) (hb : d ∈ block → old = v) :
    Function.update id n v (redirectEnd n block d old) = old := by
  by_cases hd : d ∈ block
  · simp [redirectEnd, List.any_eq_true, hd, hb hd]
  · have ho : old ≠ n := by omega
    simp [redirectEnd, List.any_eq_true, hd, Function.update_of_ne ho]

private theorem contract_split_graph {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    {block : List ℕ} (hb : ∀ d ∈ block, d ∈ fiber I.graph v) :
    contractLastEdgeGraph (splitBase I block) I.graph.vertices.length v =
      ⟨I.graph.vertices ++ [v], I.graph.edges⟩ := by
  apply Graph.ext
  · change (List.range (I.graph.vertices.length + 1)).map
        (Function.update id I.graph.vertices.length v) = I.graph.vertices ++ [v]
    rw [map_range_update_fresh]
    exact congrArg (fun vertices => vertices ++ [v]) hI.1.symm
  · apply List.ext_getElem
    · simp [contractLastEdgeGraph, Graph.relabel, splitBase]
    · intro i hi hj
      have hi' : i < I.graph.edges.length := by
        simpa only [contractLastEdgeGraph, Graph.relabel, splitBase, List.length_map,
          List.length_zipIdx] using hi
      change ((splitBase I block).edges.map
        (Prod.map (Function.update id I.graph.vertices.length v)
          (Function.update id I.graph.vertices.length v)))[i] = I.graph.edges[i]
      simp only [splitBase, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
      have he := hI.edge_endpoints_lt (List.getElem_mem hi')
      have h0 := getD_incidenceVertices_even I.graph i
      have h1 := getD_incidenceVertices_odd I.graph i
      rw [List.getD_eq_getElem _ _ hi'] at h0 h1
      exact Prod.ext (redirect_restore he.1 fun hd => h0.symm.trans (mem_fiber.mp (hb _ hd)).2)
        (redirect_restore he.2 fun hd => h1.symm.trans (mem_fiber.mp (hb _ hd)).2)

private def splitCoordinates (I : FixedRotationInput) (v : ℕ) (block : List ℕ) :
    Dart (split I v block).graph ≃ Option (Option (Dart I.graph)) :=
  (finCongr (show (split I v block).graph.edges.length = I.graph.edges.length + 1 by
    simp)).prodCongr (Equiv.refl Bool) |>.trans (appendedDartEquiv I.graph.edges.length)

private theorem splitCoordinates_old (I : FixedRotationInput) (v : ℕ) (block : List ℕ)
    (d : Dart I.graph) :
    (splitCoordinates I v block).symm (some (some d)) =
      (⟨d.1.val, by simp⟩, d.2) := by
  rfl

private theorem splitCoordinates_vertex {I : FixedRotationInput} (v : ℕ) (block : List ℕ)
    (z : Option (Option (Dart I.graph))) :
    ((splitCoordinates I v block).symm z).vertex =
      match z with
      | none => v
      | some none => I.graph.vertices.length
      | some (some d) => redirectEnd I.graph.vertices.length block d.index d.vertex := by
  rcases z with _ | (_ | d)
  · exact edgeEndpoint_split_connector I v block true
  · exact edgeEndpoint_split_connector I v block false
  · rw [splitCoordinates_old]
    exact edgeEndpoint_split_old I v block d.1.val d.1.isLt d.2

private def blockDarts {I : FixedRotationInput} {v : ℕ} (block : List ℕ)
    (hb : ∀ d ∈ block, d ∈ fiber I.graph v) : List (Dart I.graph) :=
  block.attach.map fun d => (Dart.indexEquiv I.graph).symm
    ⟨d.val, (mem_fiber.mp (hb d.val d.property)).1⟩

private theorem indices_blockDarts {I : FixedRotationInput} {v : ℕ} (block : List ℕ)
    (hb : ∀ d ∈ block, d ∈ fiber I.graph v) :
    (blockDarts block hb).map Dart.index = block := by
  have hi (d : {d // d ∈ block}) :
      ((Dart.indexEquiv I.graph).symm
        ⟨d.val, (mem_fiber.mp (hb d.val d.property)).1⟩).index = d.val :=
    congrArg Fin.val ((Dart.indexEquiv I.graph).apply_symm_apply _)
  simp only [blockDarts, List.map_map, Function.comp_def, hi, List.attach_map_subtype_val]

private theorem blockDarts_spec {I : FixedRotationInput} {v : ℕ} {block : List ℕ}
    (hne : block ≠ []) (hnd : block.Nodup) (hb : ∀ d ∈ block, d ∈ fiber I.graph v) :
    (blockDarts block hb).length = block.length ∧
      0 < (blockDarts block hb).length ∧ (blockDarts block hb).Nodup := by
  have hlen : (blockDarts block hb).length = block.length := by simp [blockDarts]
  exact ⟨hlen, by rw [hlen]; exact List.length_pos_iff.mpr hne,
    List.Nodup.of_map Dart.index ((indices_blockDarts block hb).symm ▸ hnd)⟩

private theorem mem_blockDarts {I : FixedRotationInput} {v : ℕ} (block : List ℕ)
    (hb : ∀ d ∈ block, d ∈ fiber I.graph v) (d : Dart I.graph) :
    d ∈ blockDarts block hb ↔ d.index ∈ block := by
  rw [← List.mem_map_of_injective (f := Dart.index) fun e d h =>
    (Dart.indexEquiv I.graph).injective (Fin.ext h), indices_blockDarts]

private theorem vertex_blockDarts {I : FixedRotationInput} {v : ℕ} (block : List ℕ)
    (hb : ∀ d ∈ block, d ∈ fiber I.graph v) {d : Dart I.graph}
    (hd : d ∈ blockDarts block hb) : d.vertex = v := by
  have h := (mem_fiber.mp (hb d.index ((mem_blockDarts block hb d).mp hd))).2
  rwa [Dart.vertex_index] at h

private theorem get_blockDarts_index {I : FixedRotationInput} {v : ℕ} (block : List ℕ)
    (hb : ∀ d ∈ block, d ∈ fiber I.graph v) (i : ℕ)
    (hi : i < (blockDarts block hb).length) :
    ((blockDarts block hb)[i]).index = block.getD i 0 := by
  have h := congrArg (fun L : List ℕ => L.getD i 0) (indices_blockDarts block hb)
  rwa [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map] at h

private theorem successive_blockDarts {I : FixedRotationInput} {v : ℕ} (block : List ℕ)
    (hb : ∀ d ∈ block, d ∈ fiber I.graph v) (r : RotationSystem I.graph)
    (hc : Consecutive r block) :
    ∀ i, (hi : i + 1 < (blockDarts block hb).length) →
      r.rotate (blockDarts block hb)[i] = (blockDarts block hb)[i + 1] := by
  intro i hi
  have hmap := indices_blockDarts block hb
  have hlen : (blockDarts block hb).length = block.length := by
    simpa only [List.length_map] using congrArg List.length hmap
  apply (Dart.indexEquiv I.graph).injective
  apply Fin.ext
  exact (hc i (by omega) _ (get_blockDarts_index block hb i (by omega))).trans
    (get_blockDarts_index block hb (i + 1) hi).symm

private def cutPermutation {α : Type} [DecidableEq α] (f : Perm α)
    (first last : α) : Perm (Option (Option α)) :=
  insertAfter (insertAfter f last)
    (if f.symm first = last then none else some (f.symm first)) * swap (some none) none

private theorem cutPermutation_none {α : Type} [DecidableEq α] (f : Perm α)
    (first last : α) :
    cutPermutation f first last none =
      if f.symm first = last then none else some (some (f last)) := by
  by_cases h : f.symm first = last <;> simp [cutPermutation, h, insertAfter_other]

private theorem cutPermutation_hub {α : Type} [DecidableEq α] (f : Perm α)
    (first last : α) : cutPermutation f first last (some none) = some (some first) := by
  by_cases h : f.symm first = last
  · have hf : f last = first := by rw [← h, f.apply_symm_apply]
    simp [cutPermutation, h, hf]
  · simp [cutPermutation, h, insertAfter_other f last (f.symm first) h]

private theorem cutPermutation_old {α : Type} [DecidableEq α] (f : Perm α)
    (first last d : α) :
    cutPermutation f first last (some (some d)) =
      if d = last then some none else
        if d = f.symm first then none else some (some (f d)) := by
  by_cases h : f.symm first = last
  · by_cases hd : d = last <;> simp_all [cutPermutation, swap_apply_def, insertAfter_other]
  · by_cases hd : d = last <;> by_cases ha : d = f.symm first <;>
      simp_all [cutPermutation, swap_apply_def, insertAfter_other, Ne.symm h]

private theorem cutPermutation_orbits {α : Type} [DecidableEq α] [Finite α]
    (f : Perm α) (first last : α) (hs : f.SameCycle last first) :
    Nat.card (Quotient (Perm.SameCycle.setoid (cutPermutation f first last))) =
      Nat.card (Quotient (Perm.SameCycle.setoid f)) + 1 := by
  let t : Option α := if f.symm first = last then none else some (f.symm first)
  have ht : (insertAfter f last).SameCycle none t := by
    rw [Equiv.Perm.Insertion.sameCycle_iff]
    dsimp only [t]
    split
    · exact .rfl
    · change f.SameCycle last (f.symm first)
      exact Equiv.Perm.sameCycle_apply_right.mp (by simpa using hs)
  rw [cutPermutation, (card_orbits_mul_swap _ (some none) none (by simp)).1
      (by rwa [Equiv.Perm.Insertion.sameCycle_iff]),
    card_orbits_insertAfter, card_orbits_insertAfter]

private theorem remove_cutPermutation {α : Type} [DecidableEq α] (f : Perm α)
    (first last : α) :
    removeNone (removeNone (cutPermutation f first last * swap (some none) none)) = f := by
  rw [cutPermutation, mul_assoc, swap_mul_self, mul_one,
    removeNone_insertAfter, removeNone_insertAfter]

private theorem declared_of_valid {I : FixedRotationInput} (hI : Valid I) :
    ∀ w ∈ I.graph.incidenceVertices, w ∈ I.graph.vertices :=
  fun w hw => hI.1 ▸ List.mem_range.mpr (hI.2.1 w hw)

private theorem dart_vertex_lt {I : FixedRotationInput} (hI : Valid I) (d : Dart I.graph) :
    d.vertex < I.graph.vertices.length := by
  have h := RotationSystem.vertex_mem (declared_of_valid hI) d
  rwa [hI.1, List.mem_range] at h

private theorem split_incident_iff {I : FixedRotationInput} {v : ℕ}
    {block : List ℕ} (hne : block ≠ []) (hb : ∀ d ∈ block, d ∈ fiber I.graph v) (w : ℕ) :
    (∃ d : Dart (split I v block).graph, d.vertex = w) ↔
      (∃ d : Dart I.graph, d.vertex = w) ∨ w = I.graph.vertices.length := by
  have hv : ∃ d : Dart I.graph, d.vertex = v :=
    let ⟨d, hd⟩ := List.exists_mem_of_ne_nil (blockDarts block hb) (by simpa [blockDarts] using hne)
    ⟨d, vertex_blockDarts block hb hd⟩
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨z, rfl⟩ := (splitCoordinates I v block).symm.surjective d
    rw [splitCoordinates_vertex] at hd
    rcases z with _ | (_ | a)
    · exact Or.inl (hd ▸ hv)
    · exact Or.inr hd.symm
    · by_cases ha : a.index ∈ block
      · exact Or.inr (by simpa [redirectEnd, List.any_eq_true, ha] using hd.symm)
      · exact Or.inl ⟨a, by simpa [redirectEnd, List.any_eq_true, ha] using hd⟩
  · rintro (⟨d, hd⟩ | rfl)
    · by_cases hw : w = v
      · refine ⟨(splitCoordinates I v block).symm none, ?_⟩
        simpa only [splitCoordinates_vertex] using hw.symm
      · have hnot : d.index ∉ block := fun hm =>
          hw (hd.symm.trans (vertex_blockDarts block hb ((mem_blockDarts block hb d).mpr hm)))
        refine ⟨(splitCoordinates I v block).symm (some (some d)), ?_⟩
        simp [splitCoordinates_vertex, redirectEnd, List.any_eq_true, hnot, hd]
    · exact ⟨(splitCoordinates I v block).symm (some none), splitCoordinates_vertex v block _⟩

private noncomputable def splitIncidentEquiv {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    {block : List ℕ} (hne : block ≠ []) (hb : ∀ d ∈ block, d ∈ fiber I.graph v) :
    Option (IncidentVertex I.graph) ≃ IncidentVertex (split I v block).graph :=
  Equiv.ofBijective (fun x => match x with
    | none => ⟨I.graph.vertices.length, (split_incident_iff hne hb _).mpr (Or.inr rfl)⟩
    | some x => ⟨x.val, (split_incident_iff hne hb _).mpr (Or.inl x.property)⟩) ⟨by
      intro a b hab
      have hval := congrArg Subtype.val hab
      have hne (x : IncidentVertex I.graph) : x.val ≠ I.graph.vertices.length :=
        let ⟨d, hd⟩ := x.property; hd ▸ (dart_vertex_lt hI d).ne
      rcases a with _ | a <;> rcases b with _ | b
      · rfl
      · exact absurd hval.symm (hne b)
      · exact absurd hval (hne a)
      · exact congrArg some (Subtype.ext hval), by
      intro x
      rcases (split_incident_iff hne hb x.val).mp x.property with hx | hx
      · exact ⟨some ⟨x.val, hx⟩, Subtype.ext rfl⟩
      · exact ⟨none, Subtype.ext hx.symm⟩⟩

private theorem cut_preserves_vertex {I : FixedRotationInput} {v : ℕ} {block : List ℕ}
    (hb : ∀ d ∈ block, d ∈ fiber I.graph v) (r : RotationSystem I.graph)
    (hn : 0 < (blockDarts block hb).length) (hnd : (blockDarts block hb).Nodup)
    (hc : Consecutive r block) (z : Option (Option (Dart I.graph))) :
    ((splitCoordinates I v block).symm
      (cutPermutation r.rotate (blockDarts block hb)[0]
        (blockDarts block hb)[(blockDarts block hb).length - 1] z)).vertex =
      ((splitCoordinates I v block).symm z).vertex := by
  let L := blockDarts block hb
  let first := L[0]
  let last := L[L.length - 1]'(Nat.sub_lt hn (by decide))
  let a := r.rotate.symm first
  have hf : first ∈ L := List.getElem_mem hn
  have hl : last ∈ L := List.getElem_mem (l := L) (n := L.length - 1) (Nat.sub_lt hn (by decide))
  have hfv : first.vertex = v := vertex_blockDarts block hb hf
  have hlv : last.vertex = v := vertex_blockDarts block hb hl
  have hav : a.vertex = v := by
    simpa only [a, Equiv.apply_symm_apply, hfv] using (r.vertex_rotate a).symm
  have hmem := mem_successor_block r.rotate L hn hnd (successive_blockDarts block hb r hc)
  have hboundary := block_boundary r.rotate L hn hnd (successive_blockDarts block hb r hc)
  change ((splitCoordinates I v block).symm (cutPermutation r.rotate first last z)).vertex = _
  rcases z with _ | (_ | d)
  · rw [cutPermutation_none]
    split
    · rfl
    · rename_i ha
      have hnot : (r.rotate last).index ∉ block := fun h =>
        ha (hboundary.2.mp ((mem_blockDarts block hb _).mpr h))
      simp [splitCoordinates_vertex, redirectEnd, List.any_eq_true, hnot,
        r.vertex_rotate, hlv]
  · rw [cutPermutation_hub]
    have hfm : first.index ∈ block := (mem_blockDarts block hb first).mp hf
    simp [splitCoordinates_vertex, redirectEnd, List.any_eq_true, hfm]
  · rw [cutPermutation_old]
    by_cases hd : d = last
    · rw [ite_eq_left hd]
      have hm : d.index ∈ block := (mem_blockDarts block hb d).mp (hd.symm ▸ hl)
      simp [splitCoordinates_vertex, redirectEnd, List.any_eq_true, hm]
    · rw [ite_eq_right hd]
      by_cases ha : d = a
      · rw [ite_eq_left ha]
        have hnot : a.index ∉ block := fun hm =>
          hd (ha.trans (hboundary.1.mp ((mem_blockDarts block hb a).mpr hm)))
        rw [ha]
        simp [splitCoordinates_vertex, redirectEnd, List.any_eq_true, hnot, hav]
      · rw [ite_eq_right ha]
        have hi : (r.rotate d).index ∈ block ↔ d.index ∈ block := by
          have hL : blockDarts block hb = L := rfl
          simp only [← mem_blockDarts block hb, hL, hmem d]
          exact ⟨fun h => h.elim (fun he => (ha he).elim) And.left, fun h => Or.inr ⟨h, hd⟩⟩
        simp [splitCoordinates_vertex, r.vertex_rotate, redirectEnd, List.any_eq_true, hi]

private theorem exists_cut_rotation {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    {block : List ℕ} (hne : block ≠ []) (hnd : block.Nodup)
    (hb : ∀ d ∈ block, d ∈ fiber I.graph v) (r : RotationSystem I.graph)
    (hc : Consecutive r block) :
    ∃ s : RotationSystem (split I v block).graph,
      let L := blockDarts block hb
      let hn : 0 < L.length := by simpa [L, blockDarts] using List.length_pos_iff.mpr hne
      (splitCoordinates I v block).permCongr s.rotate =
        cutPermutation r.rotate (L[0]'hn) (L[L.length - 1]'(Nat.sub_lt hn (by decide))) := by
  classical
  let L := blockDarts block hb
  obtain ⟨hlen, hn, hL⟩ : L.length = block.length ∧ 0 < L.length ∧ L.Nodup :=
    blockDarts_spec hne hnd hb
  let first := L[0]
  let last := L[L.length - 1]'(Nat.sub_lt hn (by decide))
  let f := (splitCoordinates I v block).symm.permCongr (cutPermutation r.rotate first last)
  have hs : ∀ d : Dart (split I v block).graph, (f d).vertex = d.vertex := by
    intro d
    obtain ⟨z, rfl⟩ := (splitCoordinates I v block).symm.surjective d
    simpa only [f, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply] using
      cut_preserves_vertex hb r hn hL hc z
  let _ : Finite (IncidentVertex I.graph) := Finite.of_surjective
    r.rotateOrbitEquiv r.rotateOrbitEquiv.surjective
  have hsame : r.rotate.SameCycle last first := (r.sameCycle_iff _ _).mpr
    ((vertex_blockDarts block hb (d := last)
      (List.getElem_mem (l := L) (n := L.length - 1) (Nat.sub_lt hn (by decide)))).trans
      (vertex_blockDarts block hb (d := first) (List.getElem_mem hn)).symm)
  have hcount : Nat.card (Quotient (Perm.SameCycle.setoid f)) =
      Nat.card (IncidentVertex (split I v block).graph) := by
    rw [card_orbits_permCongr, cutPermutation_orbits r.rotate first last hsame,
      ← Nat.card_congr (splitIncidentEquiv hI hne hb), Finite.card_option,
      Nat.card_congr r.rotateOrbitEquiv]
  refine ⟨ofOrbitCount f hs hcount, Equiv.ext fun z => ?_⟩
  simp [ofOrbitCount_rotate, f, first, last, L]

private theorem exists_contract_rotation {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    (hv : v < I.graph.vertices.length) (hfree : I.orders.getD v none = none)
    {block : List ℕ} (hnd : block.Nodup) (hb : ∀ d ∈ block, d ∈ fiber I.graph v)
    (s : RotationSystem (split I v block).graph) :
    ∃ r : RotationSystem I.graph,
      (r.NumericalGenusZero ↔ s.NumericalGenusZero) ∧
      r.rotate = removeNone (removeNone
        ((splitCoordinates I v block).permCongr s.rotate * swap (some none) none)) := by
  let H := splitBase I block
  let n := I.graph.vertices.length
  have hnv : n ≠ v := by omega
  let s' : RotationSystem (lastEdgeGraph H n v) := s
  have hdecl : ∀ w ∈ (lastEdgeGraph H n v).incidenceVertices, w ∈ H.vertices :=
    declared_of_valid (valid_split hI hv hfree hnd hb)
  have hgraph : contractLastEdgeGraph H n v =
      (⟨I.graph.vertices ++ [v], I.graph.edges⟩ : Graph) := contract_split_graph hI hb
  let q := s'.contractLastEdge hnv
  let q' : RotationSystem ⟨I.graph.vertices ++ [v], I.graph.edges⟩ :=
    q.transport (graphEqDartEquiv hgraph)
      (by intro a b; rw [vertex_graphEqDartEquiv, vertex_graphEqDartEquiv])
  let r : RotationSystem I.graph := q'.redeclare I.graph.vertices
  have hvdecl : v ∈ I.graph.vertices := by rw [hI.1, List.mem_range]; exact hv
  have hg : r.NumericalGenusZero ↔ s.NumericalGenusZero :=
    (numericalGenusZero_append_duplicate_iff hvdecl q').trans
      ((numericalGenusZero_graphEqDartEquiv q hgraph).trans
        (s'.numericalGenusZero_contractLastEdge_iff hnv hdecl))
  refine ⟨r, hg, ?_⟩
  have hlen : H.edges.length = I.graph.edges.length := by simp [H, splitBase]
  let e : Dart (contractLastEdgeGraph H n v) ≃ Dart I.graph :=
    graphEqDartEquiv (H := ⟨I.graph.vertices ++ [v], I.graph.edges⟩) hgraph
  let E : Dart (split I v block).graph ≃ Option (Option (Dart (contractLastEdgeGraph H n v))) :=
    (contractLastEdgeDartEquiv H n v).trans
    (lastEdgeDartEquiv (contractLastEdgeGraph H n v) v v)
  have hcoord : E.trans e.optionCongr.optionCongr = splitCoordinates I v block := by
    rw [show E = (lastEdgeDartEquiv H n v).trans
      (Dart.relabelEquiv H (Function.update id n v)).optionCongr.optionCongr from
        contractLastEdge_coordinates H n v]
    refine Equiv.symm_bijective.injective (Equiv.ext fun z => ?_)
    rcases z with _ | (_ | d) <;> apply Prod.ext <;> first | rfl | exact Fin.ext hlen
  have hcomp (f : Perm (Dart (lastEdgeGraph H n v))) :
      e.optionCongr.optionCongr.permCongr (E.permCongr f) =
        (E.trans e.optionCongr.optionCongr).permCongr f := rfl
  let dt : Dart (split I v block).graph := lastEdgeDart H n v true
  let df : Dart (split I v block).graph := lastEdgeDart H n v false
  have hswap : (splitCoordinates I v block).permCongr
      (swap dt df) =
        swap (some none) none := by
    have ht : dt = (splitCoordinates I v block).symm none := Prod.ext (Fin.ext hlen) rfl
    have hf : df = (splitCoordinates I v block).symm (some none) := Prod.ext (Fin.ext hlen) rfl
    refine Equiv.ext fun z => ?_
    rw [Equiv.permCongr_apply, ht, hf, (splitCoordinates I v block).injective.map_swap,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, swap_comm]
  change e.permCongr q.rotate = _
  rw [rotate_contractLastEdge]
  change e.permCongr (removeNone (removeNone
    (E.permCongr (s'.rotate * swap (lastEdgeDart H n v true) (lastEdgeDart H n v false))))) = _
  rw [← removeNone_permCongr_option e, ← removeNone_permCongr_option e.optionCongr,
    hcomp, hcoord]
  change removeNone (removeNone ((splitCoordinates I v block).permCongr
    (s.rotate * swap dt df))) = _
  rw [Equiv.permCongr_mul, hswap]

private def coordinateIndex (m : ℕ) {α : Type} (index : α → ℕ) : Option (Option α) → ℕ
  | none => 2 * m + 1
  | some none => 2 * m
  | some (some d) => index d

private theorem index_splitCoordinates (I : FixedRotationInput) (v : ℕ) (block : List ℕ)
    (z : Option (Option (Dart I.graph))) :
    ((splitCoordinates I v block).symm z).index =
      coordinateIndex I.graph.edges.length Dart.index z := by
  rcases z with _ | (_ | d) <;> rfl

private theorem retained_contract_step {α : Type} [DecidableEq α]
    (f : Perm (Option (Option α))) (a b : α)
    (h : f (some (some a)) = some (some b)) :
    removeNone (removeNone (f * swap (some none) none)) a = b := by
  simp [Equiv.removeNone, Equiv.removeNoneAux, Equiv.Perm.mul_apply, swap_apply_def, h]

private theorem contract_index {I : FixedRotationInput} {v : ℕ} {block : List ℕ}
    (s : RotationSystem (split I v block).graph) (r : RotationSystem I.graph)
    (hr : r.rotate = removeNone (removeNone
      ((splitCoordinates I v block).permCongr s.rotate * swap (some none) none)))
    (d : Dart I.graph) {k : ℕ} (hk : k < 2 * I.graph.edges.length)
    (hs : (s.rotate ((splitCoordinates I v block).symm (some (some d)))).index = k) :
    (r.rotate d).index = k := by
  let E := splitCoordinates I v block
  change (s.rotate (E.symm (some (some d)))).index = k at hs
  have hz := index_splitCoordinates I v block
    (E (s.rotate (E.symm (some (some d)))))
  rw [Equiv.symm_apply_apply] at hz
  change (s.rotate (E.symm (some (some d)))).index =
    coordinateIndex I.graph.edges.length Dart.index (E (s.rotate (E.symm (some (some d))))) at hz
  rcases he : E (s.rotate (E.symm (some (some d)))) with _ | _ | e
  iterate 2 · simp only [he, coordinateIndex] at hz; omega
  have hstep : (E.permCongr s.rotate) (some (some d)) = some (some e) := by
    simpa only [Equiv.permCongr_apply] using he
  rw [hr, retained_contract_step _ d e hstep]
  simpa only [he, coordinateIndex] using hz.symm.trans hs

private theorem split_order_old {I : FixedRotationInput} (hI : Valid I) (v : ℕ)
    (block : List ℕ) {u : ℕ} (hu : u < I.graph.vertices.length) :
    (split I v block).orders.getD u none = I.orders.getD u none := by
  have hul : u < I.orders.length := by rw [hI.2.2.1]; exact hu
  rw [List.getD_eq_getElem _ _ (by simp [split]; omega), List.getD_eq_getElem _ _ hul]
  simp only [split, List.getElem_append, hul, ↓reduceDIte]

private theorem split_order_hub {I : FixedRotationInput} (hI : Valid I) (v : ℕ)
    (block : List ℕ) :
    (split I v block).orders.getD I.graph.vertices.length none =
      some (block ++ [2 * I.graph.edges.length]) := by
  change (I.orders ++ [some (block ++ [2 * I.graph.edges.length])]).getD
    I.graph.vertices.length none = _
  simp [← hI.2.2.1]

private theorem nextInWord_mem (word : List ℕ) {i : ℕ} (hi : i < word.length) :
    nextInWord word i ∈ word := by
  unfold nextInWord
  split_ifs with hnext <;> rw [List.getD_eq_getElem _ _ (by omega)] <;>
    exact List.getElem_mem _

private theorem contract_realizes {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    {block : List ℕ} (s : RotationSystem (split I v block).graph)
    (r : RotationSystem I.graph)
    (hr : r.rotate = removeNone (removeNone
      ((splitCoordinates I v block).permCongr s.rotate * swap (some none) none)))
    (hs : Realizes (split I v block) s) : Realizes I r := by
  intro u word hu i hi d hd
  have hul : u < I.graph.vertices.length := by_contra fun h =>
    nomatch (List.getD_eq_default I.orders none (n := u) (by rw [hI.2.2.1]; omega)).symm.trans hu
  have hnext := (hI.2.2.2 u word hu).2 (nextInWord word i) |>.mp (nextInWord_mem word hi)
  apply contract_index s r hr d (mem_fiber.mp hnext).1
  have hidx := index_splitCoordinates I v block (some (some d))
  exact hs u word ((split_order_old hI v block hul).trans hu) i hi _ (hidx.trans hd)

private theorem contract_consecutive {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    {block : List ℕ} (hb : ∀ d ∈ block, d ∈ fiber I.graph v)
    (s : RotationSystem (split I v block).graph) (r : RotationSystem I.graph)
    (hr : r.rotate = removeNone (removeNone
      ((splitCoordinates I v block).permCongr s.rotate * swap (some none) none)))
    (hs : Realizes (split I v block) s) : Consecutive r block := by
  intro i hi d hd
  have hmem : block.getD (i + 1) 0 ∈ block := List.getD_eq_getElem _ _ hi ▸ List.getElem_mem hi
  apply contract_index s r hr d (mem_fiber.mp (hb _ hmem)).1
  have h := hs I.graph.vertices.length (block ++ [2 * I.graph.edges.length])
    (split_order_hub hI v block) i (by simp; omega)
    ((splitCoordinates I v block).symm (some (some d)))
  have hidx := index_splitCoordinates I v block (some (some d))
  have hget : (block ++ [2 * I.graph.edges.length]).getD i 0 = block.getD i 0 := by
    rw [List.getD_eq_getElem _ _ (by simp; omega),
      List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
  specialize h (hidx.trans (hd.trans hget.symm))
  simpa only [nextInWord, List.length_append, List.length_singleton,
    show i + 1 < block.length + 1 from by omega, ↓reduceIte,
    List.getD_append _ _ _ _ hi] using h

private theorem split_dart_eq_old {I : FixedRotationInput} {v : ℕ} {block : List ℕ}
    (d : Dart (split I v block).graph) (e : Dart I.graph) (h : d.index = e.index) :
    d = (splitCoordinates I v block).symm (some (some e)) :=
  (Dart.indexEquiv (split I v block).graph).injective
    (Fin.ext (h.trans (index_splitCoordinates I v block (some (some e))).symm))

private theorem cut_realizes {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    (hfree : I.orders.getD v none = none) {block : List ℕ}
    (hne : block ≠ []) (hnd : block.Nodup)
    (hb : ∀ d ∈ block, d ∈ fiber I.graph v) (r : RotationSystem I.graph)
    (hR : Realizes I r) (hc : Consecutive r block)
    (s : RotationSystem (split I v block).graph)
    (hcut : let L := blockDarts block hb
      let hn : 0 < L.length := by simpa [L, blockDarts] using List.length_pos_iff.mpr hne
      (splitCoordinates I v block).permCongr s.rotate =
        cutPermutation r.rotate (L[0]'hn) (L[L.length - 1]'(Nat.sub_lt hn (by decide)))) :
    Realizes (split I v block) s := by
  let L := blockDarts block hb
  obtain ⟨hlen, hn, hL⟩ : L.length = block.length ∧ 0 < L.length ∧ L.Nodup :=
    blockDarts_spec hne hnd hb
  let first := L[0]
  let last := L[L.length - 1]'(Nat.sub_lt hn (by decide))
  let a := r.rotate.symm first
  let E := splitCoordinates I v block
  have hfv : first.vertex = v := vertex_blockDarts block hb (List.getElem_mem hn)
  have hlv : last.vertex = v := vertex_blockDarts block hb
    (show last ∈ L from List.getElem_mem (l := L) (n := L.length - 1) (Nat.sub_lt hn (by decide)))
  have hav : a.vertex = v := by
    simpa only [a, Equiv.apply_symm_apply, hfv] using (r.vertex_rotate a).symm
  have step (z : Option (Option (Dart I.graph))) :
      (s.rotate (E.symm z)).index =
        coordinateIndex I.graph.edges.length Dart.index (cutPermutation r.rotate first last z) := by
    have h := congrArg (fun f : Perm (Option (Option (Dart I.graph))) => f z) hcut
    change E (s.rotate (E.symm z)) = cutPermutation r.rotate first last z at h
    rw [← E.symm_apply_apply (s.rotate (E.symm z)), h]
    exact index_splitCoordinates I v block _
  intro u word hu i hi d hd
  have hul : u < I.graph.vertices.length + 1 := by_contra fun h =>
    nomatch (List.getD_eq_default (split I v block).orders none (n := u)
      (by simp [split, hI.2.2.1]; omega)).symm.trans hu
  by_cases hou : u < I.graph.vertices.length
  · have ho : I.orders.getD u none = some word := (split_order_old hI v block hou).symm.trans hu
    have huv : u ≠ v := by rintro rfl; rw [hfree] at ho; contradiction
    have hm : word.getD i 0 ∈ fiber I.graph u := (hI.2.2.2 u word ho).2 _ |>.mp (by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
    let e : Dart I.graph := (Dart.indexEquiv I.graph).symm
      ⟨word.getD i 0, (mem_fiber.mp hm).1⟩
    have hei : e.index = word.getD i 0 := congrArg Fin.val
      ((Dart.indexEquiv I.graph).apply_symm_apply _)
    have hev : e.vertex = u := by rw [← Dart.vertex_index, hei]; exact (mem_fiber.mp hm).2
    have hel : e ≠ last := fun h => huv (hev.symm.trans ((congrArg Dart.vertex h).trans hlv))
    have hea : e ≠ a := fun h => huv (hev.symm.trans ((congrArg Dart.vertex h).trans hav))
    rw [split_dart_eq_old d e (hd.trans hei.symm), step, cutPermutation_old,
      ite_eq_right hel, ite_eq_right hea]
    exact hR u word ho i hi e hei
  · obtain rfl : u = I.graph.vertices.length := by omega
    obtain rfl : word = block ++ [2 * I.graph.edges.length] :=
      Option.some.inj (hu.symm.trans (split_order_hub hI v block))
    by_cases hib : i < block.length
    · let e := L[i]'(by omega)
      have hei : e.index = block.getD i 0 :=
        get_blockDarts_index block hb i (by change i < L.length; omega)
      have hget : (block ++ [2 * I.graph.edges.length]).getD i 0 = block.getD i 0 :=
        List.getD_append _ _ _ _ hib
      rw [split_dart_eq_old d e (hd.trans (hget.trans hei.symm)), step, cutPermutation_old]
      by_cases hlast : i + 1 = block.length
      · have hel : e = last := by
          change L[i] = L[L.length - 1]
          congr 1; omega
        rw [ite_eq_left hel]
        simp only [coordinateIndex]
        unfold nextInWord
        rw [ite_eq_left (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
        simp [hlast]
      · have hi' : i + 1 < L.length := by omega
        have hel : e ≠ last := fun h => by
          have := hL.getElem_inj_iff.mp h
          omega
        have hea : e ≠ a := fun h =>
          hel (h.trans ((block_boundary r.rotate L hn hL (successive_blockDarts block hb r hc)).1.mp
            (Eq.mp (congrArg (· ∈ L) h) (List.getElem_mem (Nat.lt_of_succ_lt hi')))))
        rw [ite_eq_right hel, ite_eq_right hea]
        simp only [coordinateIndex]
        rw [successive_blockDarts block hb r hc i hi', get_blockDarts_index block hb (i + 1) hi']
        unfold nextInWord
        rw [ite_eq_left (by simpa only [List.length_append, List.length_singleton] using
          (show i + 1 < block.length + 1 from by omega)), List.getD_append _ _ _ _ (by omega)]
    · obtain rfl : i = block.length := by
        simp only [List.length_append, List.length_singleton] at hi; omega
      have hdi : d.index = 2 * I.graph.edges.length := by simpa using hd
      have hd' : d = E.symm (some none) := (Dart.indexEquiv (split I v block).graph).injective
        (Fin.ext (hdi.trans (index_splitCoordinates I v block (some none)).symm))
      rw [hd', step, cutPermutation_hub]
      simp only [coordinateIndex]
      rw [get_blockDarts_index block hb 0 hn]
      unfold nextInWord
      rw [ite_eq_right (by
        simp only [List.length_append, List.length_singleton, lt_self_iff_false,
          not_false_eq_true]),
        List.getD_append _ _ _ _ (by omega)]

/-- Splitting a nonempty directed block at a free vertex is feasible exactly when some
original genus-zero rotation realizes the fixed words and contains that consecutive block.
The block may be the whole fiber; loops, parallel occurrences and isolates are retained.
No parity-query, bridge, geometric provider or Hanani–Tutte hypothesis is needed. -/
theorem feasible_split_iff {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    (hv : v < I.graph.vertices.length) (hfree : I.orders.getD v none = none)
    {block : List ℕ} (hne : block ≠ []) (hnd : block.Nodup)
    (hb : ∀ d ∈ block, d ∈ fiber I.graph v) :
    Feasible (split I v block) ↔
      ∃ r : RotationSystem I.graph, r.NumericalGenusZero ∧ Realizes I r ∧ Consecutive r block := by
  constructor
  · rintro ⟨s, hg, hs⟩
    obtain ⟨r, hgenus, hr⟩ := exists_contract_rotation hI hv hfree hnd hb s
    exact ⟨r, hgenus.mpr hg, contract_realizes hI s r hr hs,
      contract_consecutive hI hb s r hr hs⟩
  · rintro ⟨r, hg, hR, hc⟩
    obtain ⟨s, hs⟩ := exists_cut_rotation hI hne hnd hb r hc
    obtain ⟨t, hgenus, ht⟩ := exists_contract_rotation hI hv hfree hnd hb s
    have htr : t = r := RotationSystem.ext_rotate (by rw [ht, hs, remove_cutPermutation])
    refine ⟨s, hgenus.mp (htr.symm ▸ hg), cut_realizes hI hfree hne hnd hb r hR hc s hs⟩

end Cslib.Complexity.Graph.RotationRecognition
