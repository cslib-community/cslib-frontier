/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceStar
import CslibFrontier.Foundations.Geometry.Polygonal.Germs
import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds
import CslibFrontier.Foundations.Geometry.Polygonal.RouteInterior
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.GetD

/-!
# The actual frozen part of the reference drawing

Only stored frozen segments are retained, in their existing occurrence order. All subdivision
vertices remain declared, including unused leaves and isolated original centers. The retained
routes are literal routes of the reference drawing, with the same endpoint tags and germs.

Different center blocks have disjoint real-coordinate intervals. At one center, a contact
away from the center would identify two positive outgoing rays, contradicting the internally
proved fixed-word direction injectivity. Thus the frozen part is a genuine embedding although
the full reference drawing intentionally has crossings.

This concrete embedding supplies no ambient placement or isotopy, generic-position
regularization, move parity, Hanani–Tutte or query-completeness theorem; the unfinished
recognition and source-model objective is tracked in
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Main definitions

* `Cslib.Complexity.Graph.RotationRecognition.frozenReferenceDrawing`: literal retained routes
  on the existing spanning frozen graph. `frozenReferenceDrawing_vertex` gives its coordinates.
* `Cslib.Complexity.Graph.RotationRecognition.frozenReferenceDart`: the retained indexed end
  selected by a literal stored word. `frozenReferenceDart_endpoints` specifies its tag
  and neighbors.

## Main results

* `Cslib.Complexity.Graph.RotationRecognition.referenceDrawing_frozen_edge_contacts`: actual
  flagged indexed routes meet only at common original endpoints.
* `Cslib.Complexity.Graph.RotationRecognition.frozenReferenceDrawing_isEmbedding`: the
  actual frozen restriction is a genuine embedding with all frame vertices retained.

## Retained-end interface

* `Cslib.Complexity.Graph.RotationRecognition.frozenReferenceDrawing_germ_frozenReferenceDart`:
  retaining an original fixed end preserves its actual outgoing germ.
* `Cslib.Complexity.Graph.RotationRecognition.frozenReferenceDrawing_fixedWord_clockwise_iff`:
  the retained fixed ends have their literal prescribed clockwise order.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Polygonal

private abbrev centerBlock (I : FixedRotationInput) (v : ℕ) : List ℕ :=
  v :: ((fixedWord I v).reverse.map fun d => I.graph.vertices.length + d)

private theorem centerBlocks_pairwise {I : FixedRotationInput} (hI : Valid I) :
    (centerBlocks I).Pairwise
      (fun x y => (referenceOrder I).idxOf x < (referenceOrder I).idxOf y) := by
  have hn := (referenceOrder_enumerates hI).1
  have ho : (referenceOrder I).Pairwise
      (fun x y => (referenceOrder I).idxOf x < (referenceOrder I).idxOf y) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa only [hn.idxOf_getElem i hi, hn.idxOf_getElem j hj] using hij
  exact (List.pairwise_append.mp ho).1

private theorem centerBlock_mem_reference {I : FixedRotationInput} {v x : ℕ}
    (hv : v < I.graph.vertices.length) (hx : x ∈ centerBlock I v) :
    x ∈ referenceOrder I :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hv, hx⟩)

private theorem centerBlock_pairwise {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    (hv : v < I.graph.vertices.length) : (centerBlock I v).Pairwise
      (fun x y => (referenceOrder I).idxOf x < (referenceOrder I).idxOf y) := by
  exact (List.pairwise_flatMap.mp (centerBlocks_pairwise hI)).1 v (List.mem_range.mpr hv)

private theorem centerBlocks_separated {I : FixedRotationInput} (hI : Valid I) {u v x y : ℕ}
    (hu : u < I.graph.vertices.length) (hv : v < I.graph.vertices.length) (huv : u < v)
    (hx : x ∈ centerBlock I u) (hy : y ∈ centerBlock I v) :
    (referenceOrder I).idxOf x < (referenceOrder I).idxOf y := by
  have hp := (List.pairwise_flatMap.mp (centerBlocks_pairwise hI)).2
  have h := List.pairwise_iff_getElem.mp hp u v (by simpa using hu)
    (by simpa using hv) huv
  simp only [List.getElem_range] at h
  exact h x hx y hy

private theorem fixed_end_word {I : FixedRotationInput} (hI : Valid I) (d : Dart I.graph)
    (hd : (I.orders.getD d.vertex none).isSome = true) :
    ∃ word, I.orders.getD d.vertex none = some word ∧ d.index ∈ word := by
  cases hw : I.orders.getD d.vertex none with
  | none => simp only [hw, Option.isSome_none, Bool.false_eq_true] at hd
  | some word =>
    exact ⟨word, rfl, ((hI.2.2.2 d.vertex word hw).2 d.index).mpr (index_mem_fiber d)⟩

private theorem fixed_end_reference_spec {I : FixedRotationInput} (hI : Valid I)
    (d : Dart I.graph) (hd : (I.orders.getD d.vertex none).isSome = true) :
    d.vertex < I.graph.vertices.length ∧ d.vertex ∈ referenceOrder I ∧
      I.graph.vertices.length + d.index ∈ referenceOrder I ∧
      I.graph.vertices.length + d.index ∈ centerBlock I d.vertex ∧
      (referenceOrder I).idxOf d.vertex <
        (referenceOrder I).idxOf (I.graph.vertices.length + d.index) := by
  obtain ⟨word, hw, hm⟩ := fixed_end_word hI d hd
  have hv : d.vertex < I.graph.vertices.length := by
    by_contra hn
    have ho : I.orders.length ≤ d.vertex := by rw [hI.2.2.1]; omega
    rw [List.getD_eq_default _ _ ho] at hw
    contradiction
  have hleaf : I.graph.vertices.length + d.index ∈
      (fixedWord I d.vertex).reverse.map (fun k => I.graph.vertices.length + k) := by
    apply List.mem_map.mpr
    exact ⟨d.index, List.mem_reverse.mpr (by simpa only [fixedWord, hw, Option.getD_some] using hm),
      rfl⟩
  have hblock : I.graph.vertices.length + d.index ∈ centerBlock I d.vertex :=
    List.mem_cons_of_mem _ hleaf
  exact ⟨hv, centerBlock_mem_reference hv List.mem_cons_self,
    centerBlock_mem_reference hv hblock, hblock,
    (List.pairwise_cons.mp (centerBlock_pairwise hI hv)).1 _ hleaf⟩

private theorem eval_from_original_end (I : FixedRotationInput) (d : Dart I.graph)
    (i : Fin ((referenceDrawing I).route (subdivisionDart I d).1).segments) (t : ℝ) :
    ((referenceDrawing I).route (subdivisionDart I d).1).eval i t =
      (referenceDrawing I).vertex d.vertex + Route.endTime d.2 t •
        (referenceDrawing I).germ (subdivisionDart I d) := by
  let p := (referenceDrawing I).route (subdivisionDart I d).1
  have hi : i = p.endSegment d.2 := Subsingleton.elim (α := Fin 1) _ _
  have htt : Route.endTime d.2 (Route.endTime d.2 t) = t := by
    cases d.2 <;> simp only [Route.endTime, Bool.false_eq_true, ↓reduceIte]; ring
  rw [hi]
  calc
    _ = p.endpoint d.2 + Route.endTime d.2 t • p.germ d.2 := by
      simpa only [htt] using p.eval_near_end d.2 (Route.endTime d.2 t)
    _ = _ := by
      rw [(referenceDrawing I).endpoint_eq]
      change (referenceDrawing I).vertex (subdivisionDart I d).vertex +
        Route.endTime d.2 t • p.germ d.2 = _
      rw [(subdivisionDart_endpoints I d).1]
      rfl

private theorem at_original_end_of_outgoing_zero (I : FixedRotationInput) (d : Dart I.graph)
    (i : Fin ((referenceDrawing I).route (subdivisionDart I d).1).segments) {t : ℝ}
    (ht : Route.endTime d.2 t = 0) :
    ((referenceDrawing I).route (subdivisionDart I d).1).AtEnd i t d.2 := by
  apply (Route.atEnd_line_iff _ _ i t d.2).mpr
  cases hb : d.2 <;> simp only [Route.endTime, hb, Bool.false_eq_true, ↓reduceIte] at ht ⊢
  · exact ht
  · linarith only [ht]

private theorem eval_re_mem_original_interval {I : FixedRotationInput} (hI : Valid I)
    (d : Dart I.graph) (hd : (I.orders.getD d.vertex none).isSome = true)
    (i : Fin ((referenceDrawing I).route (subdivisionDart I d).1).segments)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (((referenceDrawing I).route (subdivisionDart I d).1).eval i t).re ∈
      Set.Icc ((referenceOrder I).idxOf d.vertex : ℝ)
        ((referenceOrder I).idxOf (I.graph.vertices.length + d.index) : ℝ) := by
  obtain ⟨_, _, _, _, hr⟩ := fixed_end_reference_spec hI d hd
  have hle : ((referenceOrder I).idxOf d.vertex : ℝ) ≤
      ((referenceOrder I).idxOf (I.graph.vertices.length + d.index) : ℝ) :=
    (Nat.cast_lt.mpr hr).le
  let σ := Route.endTime d.2 t
  let a := referencePoint I d.vertex
  let b := referencePoint I (I.graph.vertices.length + d.index)
  have heval : ((referenceDrawing I).route (subdivisionDart I d).1).eval i t =
      AffineMap.lineMap a b σ := by
    rw [eval_from_original_end, referenceDrawing_subdivisionDart_germ,
      AffineMap.lineMap_apply_module']
    exact add_comm _ _
  have hpoint := lineMap_mem_segment ℝ a b (Route.endTime_mem d.2 ht)
  let reMap : ℂ →ᵃ[ℝ] ℝ := Complex.reCLM.toLinearMap.toAffineMap
  have himage := image_segment ℝ reMap a b
  have hre : (AffineMap.lineMap a b σ).re ∈ segment ℝ a.re b.re :=
    himage ▸ Set.mem_image_of_mem reMap hpoint
  rw [heval]
  simpa only [a, b, referencePoint, parabolaPoint, segment_eq_Icc hle] using hre

private theorem same_center_contacts {I : FixedRotationInput} (hI : Valid I)
    (a b : Dart I.graph) (ha : (I.orders.getD a.vertex none).isSome = true)
    (hv : a.vertex = b.vertex)
    (hab : (subdivisionDart I a).1 ≠ (subdivisionDart I b).1)
    (i : Fin ((referenceDrawing I).route (subdivisionDart I a).1).segments)
    (j : Fin ((referenceDrawing I).route (subdivisionDart I b).1).segments)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : ((referenceDrawing I).route (subdivisionDart I a).1).eval i s =
      ((referenceDrawing I).route (subdivisionDart I b).1).eval j t) :
    Route.endTime a.2 s = 0 ∧ Route.endTime b.2 t = 0 := by
  have hσ := Route.endTime_mem a.2 hs
  have hτ := Route.endTime_mem b.2 ht
  have hva := referenceDrawing_subdivisionDart_germ_ne_zero hI a
  have hvb := referenceDrawing_subdivisionDart_germ_ne_zero hI b
  rw [eval_from_original_end, eval_from_original_end, hv] at heq
  have hvec := add_left_cancel heq
  by_cases hzero : Route.endTime a.2 s = 0
  · refine ⟨hzero, ?_⟩
    rw [hzero, zero_smul] at hvec
    exact (smul_eq_zero.mp hvec.symm).resolve_right hvb
  have hσpos := lt_of_le_of_ne hσ.1 (Ne.symm hzero)
  have hτpos : 0 < Route.endTime b.2 t := by
    apply lt_of_le_of_ne hτ.1
    intro hzero'
    rw [← hzero', zero_smul] at hvec
    exact hzero ((smul_eq_zero.mp hvec).resolve_right hva)
  have harg := congrArg Complex.arg hvec
  simp only [Complex.real_smul, Complex.arg_real_mul _ hσpos,
    Complex.arg_real_mul _ hτpos] at harg
  obtain ⟨word, hw, ham⟩ := fixed_end_word hI a ha
  have hbm : b.index ∈ word :=
    ((hI.2.2.2 a.vertex word hw).2 b.index).mpr (by simpa only [hv] using index_mem_fiber b)
  have he := referenceDrawing_fixedWord_directions_injective hI hw ham hbm
    (congrArg (fun x : ℝ => (x : Real.Angle)) harg)
  exact (hab (congrArg (fun d => (subdivisionDart I d).1) he)).elim

private theorem separated_blocks_no_contact {I : FixedRotationInput} (hI : Valid I)
    (a b : Dart I.graph) (ha : (I.orders.getD a.vertex none).isSome = true)
    (hb : (I.orders.getD b.vertex none).isSome = true) (hab : a.vertex < b.vertex)
    (i : Fin ((referenceDrawing I).route (subdivisionDart I a).1).segments)
    (j : Fin ((referenceDrawing I).route (subdivisionDart I b).1).segments)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    ((referenceDrawing I).route (subdivisionDart I a).1).eval i s ≠
      ((referenceDrawing I).route (subdivisionDart I b).1).eval j t := by
  intro heq
  have ha' := fixed_end_reference_spec hI a ha
  have hb' := fixed_end_reference_spec hI b hb
  have hrea := eval_re_mem_original_interval hI a ha i hs
  have hreb := eval_re_mem_original_interval hI b hb j ht
  have hsep := centerBlocks_separated hI ha'.1 hb'.1 hab ha'.2.2.2.1
    List.mem_cons_self
  have hsep' := Nat.cast_lt (α := ℝ) |>.mpr hsep
  have hre := congrArg Complex.re heq
  linarith only [hrea.2, hreb.1, hsep', hre]

/-- Distinct actual stored frozen routes meet only at a common named endpoint. The two
parameters range over the entire closed unit intervals, including endpoint-zero branches. -/
theorem referenceDrawing_frozen_edge_contacts {I : FixedRotationInput} (hI : Valid I)
    (e f : Fin (subdivisionGraph I).edges.length) (hef : e ≠ f)
    (he : ((subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true)
    (hf : ((subdivide I)[f.val]'(by
      simpa only [subdivisionGraph, List.length_map] using f.isLt)).frozen = true)
    (i : Fin ((referenceDrawing I).route e).segments)
    (j : Fin ((referenceDrawing I).route f).segments)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : ((referenceDrawing I).route e).eval i s =
      ((referenceDrawing I).route f).eval j t) :
    ∃ b c, ((referenceDrawing I).route e).AtEnd i s b ∧
      ((referenceDrawing I).route f).AtEnd j t c ∧ Dart.vertex (e, b) = Dart.vertex (f, c) := by
  obtain ⟨a, rfl, ha⟩ := (frozen_iff_exists_subdivisionDart I e).mp he
  obtain ⟨b, rfl, hb⟩ := (frozen_iff_exists_subdivisionDart I f).mp hf
  by_cases hv : a.vertex = b.vertex
  · obtain ⟨hσ, hτ⟩ := same_center_contacts hI a b ha hv hef i j hs ht heq
    exact ⟨a.2, b.2, at_original_end_of_outgoing_zero I a i hσ,
      at_original_end_of_outgoing_zero I b j hτ,
      ((subdivisionDart_endpoints I a).1.trans hv).trans
        (subdivisionDart_endpoints I b).1.symm⟩
  rcases lt_or_gt_of_ne hv with hab | hba
  · exact (separated_blocks_no_contact hI a b ha hb hab i j hs ht heq).elim
  · exact (separated_blocks_no_contact hI b a hb ha hba j i ht hs heq.symm).elim

private noncomputable def frozenIndexData (I : FixedRotationInput) :
    { f : Fin ((subdivide I).filter Segment.frozen).length ↪o Fin (subdivide I).length //
      ∀ i, ((subdivide I).filter Segment.frozen).get i = (subdivide I).get (f i) } := by
  have h := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
    (List.filter_sublist (p := Segment.frozen) (l := subdivide I))
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

private noncomputable def frozenIndex (I : FixedRotationInput)
    (e : Fin (frozenGraph I).edges.length) : Fin (subdivisionGraph I).edges.length := by
  let i : Fin ((subdivide I).filter Segment.frozen).length :=
    ⟨e.val, by simpa only [frozenGraph, List.length_map] using e.isLt⟩
  let j := (frozenIndexData I).val i
  exact ⟨j.val, by simpa only [subdivisionGraph, List.length_map] using j.isLt⟩

private theorem frozenIndex_get (I : FixedRotationInput)
    (e : Fin (frozenGraph I).edges.length) :
    ((subdivide I).filter Segment.frozen)[e.val]'(by
      simpa only [frozenGraph, List.length_map] using e.isLt) =
      (subdivide I)[(frozenIndex I e).val]'(by
        simpa only [subdivisionGraph, List.length_map] using (frozenIndex I e).isLt) := by
  exact (frozenIndexData I).property
    ⟨e.val, by simpa only [frozenGraph, List.length_map] using e.isLt⟩

private theorem frozenIndex_injective (I : FixedRotationInput) :
    Function.Injective (frozenIndex I) := by
  intro e f hef
  have hval := congrArg Fin.val hef
  have h := (frozenIndexData I).val.injective (Fin.ext hval)
  have hv : e.val = f.val := congrArg
    (fun i : Fin ((subdivide I).filter Segment.frozen).length => i.val) h
  exact Fin.ext hv

private theorem frozenIndex_flag (I : FixedRotationInput)
    (e : Fin (frozenGraph I).edges.length) :
    ((subdivide I)[(frozenIndex I e).val]'(by
      simpa only [subdivisionGraph, List.length_map] using
        (frozenIndex I e).isLt)).frozen = true := by
  have hm := List.getElem_mem (l := (subdivide I).filter Segment.frozen)
    (n := e.val) (by simpa only [frozenGraph, List.length_map] using e.isLt)
  exact (List.mem_filter.mp ((frozenIndex_get I e) ▸ hm)).2

private theorem frozenIndex_vertex (I : FixedRotationInput)
    (e : Fin (frozenGraph I).edges.length) (b : Bool) :
    Dart.vertex (frozenIndex I e, b) = Dart.vertex (e, b) := by
  have hends := congrArg Segment.endpoints (frozenIndex_get I e)
  have hedge : (subdivisionGraph I).edges[(frozenIndex I e).val] =
      (frozenGraph I).edges[e.val] := by
    simpa only [subdivisionGraph, frozenGraph, List.getElem_map] using hends.symm
  cases b <;>
    simp only [Dart.vertex, Graph.edgeEndpoint, Bool.false_eq_true, ↓reduceIte] <;>
    rw [List.getD_eq_getElem (subdivisionGraph I).edges (0, 0) (frozenIndex I e).isLt,
      List.getD_eq_getElem (frozenGraph I).edges (0, 0) e.isLt, hedge]

/-- The literal ordered restriction to stored frozen segments. The vertex function and full
frame declaration range are retained, including every isolated subdivision point. -/
noncomputable def frozenReferenceDrawing (I : FixedRotationInput) :
    PolygonalDrawing (frozenGraph I) where
  vertex := (referenceDrawing I).vertex
  route e := (referenceDrawing I).route (frozenIndex I e)
  endpoint_eq e b := ((referenceDrawing I).endpoint_eq _ _).trans
    (congrArg (referenceDrawing I).vertex (frozenIndex_vertex I e b))

/-- Every declared and undeclared name keeps precisely its existing reference coordinate. -/
@[simp] theorem frozenReferenceDrawing_vertex (I : FixedRotationInput) (v : ℕ) :
    (frozenReferenceDrawing I).vertex v = referencePoint I v := by
  simp only [frozenReferenceDrawing, referenceDrawing]

/-- Retaining only frozen indexed routes gives an actual embedding. All vertex-contact,
simplicity and pair-contact obligations are discharged internally from valid input. -/
theorem frozenReferenceDrawing_isEmbedding {I : FixedRotationInput} (hI : Valid I) :
    (frozenReferenceDrawing I).IsEmbedding where
  vertices_injective := referenceDrawing_vertices_injective hI
  simple e := referenceDrawing_simple hI (frozenIndex I e)
  vertex_contacts := by
    intro e i t ht v hv heq
    obtain ⟨b, hb, hvertex⟩ := referenceDrawing_vertex_contacts hI (frozenIndex I e) i ht hv heq
    exact ⟨b, hb, (frozenIndex_vertex I e b).symm.trans hvertex⟩
  edge_contacts := by
    intro e f hef i j s t hs ht heq
    obtain ⟨b, c, hb, hc, hvertex⟩ := referenceDrawing_frozen_edge_contacts hI
      (frozenIndex I e) (frozenIndex I f) (fun h => hef (frozenIndex_injective I h))
      (frozenIndex_flag I e) (frozenIndex_flag I f) i j hs ht heq
    exact ⟨b, c, hb, hc, (frozenIndex_vertex I e b).symm.trans
      (hvertex.trans (frozenIndex_vertex I f c))⟩

private theorem reference_routes_eq_of_segment_eq (I : FixedRotationInput)
    {e f : Fin (subdivisionGraph I).edges.length}
    (hseg : (subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt) =
      (subdivide I)[f.val]'(by
        simpa only [subdivisionGraph, List.length_map] using f.isLt)) :
    (referenceDrawing I).route e = (referenceDrawing I).route f := by
  have hends : (subdivisionGraph I).edges[e.val] = (subdivisionGraph I).edges[f.val] := by
    simpa only [subdivisionGraph, List.getElem_map] using congrArg Segment.endpoints hseg
  simp only [referenceDrawing, Dart.vertex, Graph.edgeEndpoint, Bool.false_eq_true, ↓reduceIte,
    List.getD_eq_getElem _ _ e.isLt, List.getD_eq_getElem _ _ f.isLt, hends]

private theorem frozen_segment_index_injective {I : FixedRotationInput} (hI : Valid I)
    {e f : Fin (subdivisionGraph I).edges.length}
    (he : ((subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true)
    (hf : ((subdivide I)[f.val]'(by
      simpa only [subdivisionGraph, List.length_map] using f.isLt)).frozen = true)
    (hseg : (subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt) =
      (subdivide I)[f.val]'(by
        simpa only [subdivisionGraph, List.length_map] using f.isLt)) : e = f := by
  by_contra hne
  have hroute := reference_routes_eq_of_segment_eq I hseg
  have hpoint : ((referenceDrawing I).route e).eval 0 (1 / 2) =
      ((referenceDrawing I).route f).eval 0 (1 / 2) := by rw [hroute]
  obtain ⟨b, _, hb, _, _⟩ := referenceDrawing_frozen_edge_contacts hI e f hne he hf
    0 0 (by constructor <;> norm_num) (by constructor <;> norm_num) hpoint
  exact Route.not_atEnd_of_mem_Ioo _ 0 (by constructor <;> norm_num) b hb

private theorem frozenIndex_covers {I : FixedRotationInput} (hI : Valid I)
    (e : Fin (subdivisionGraph I).edges.length)
    (he : ((subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true) :
    ∃ f, frozenIndex I f = e := by
  have heBound : e.val < (subdivide I).length := by
    simpa only [subdivisionGraph, List.length_map] using e.isLt
  have hm : (subdivide I)[e.val]'heBound ∈ (subdivide I).filter Segment.frozen :=
    List.mem_filter.mpr ⟨List.getElem_mem heBound, he⟩
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hm
  let f : Fin (frozenGraph I).edges.length :=
    ⟨j, by simpa only [frozenGraph, List.length_map] using hj⟩
  refine ⟨f, frozen_segment_index_injective hI (frozenIndex_flag I f) he ?_⟩
  exact (frozenIndex_get I f).symm.trans hget

private theorem fixed_of_word {I : FixedRotationInput} (hI : Valid I) {v : ℕ} {word : List ℕ}
    (hw : I.orders.getD v none = some word) {d : Dart I.graph} (hd : d.index ∈ word) :
    (I.orders.getD d.vertex none).isSome = true := by
  rw [fixedWord_dart_vertex hI hw hd, hw]
  rfl

/-- The actual retained indexed end selected by a literal complete stored word. Its source
fixedness and coverage by the filtered drawing are derived internally. -/
noncomputable def frozenReferenceDart {I : FixedRotationInput} (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    (d : Dart I.graph) (hd : d.index ∈ word) : Dart (frozenGraph I) :=
  (Classical.choose (frozenIndex_covers hI (subdivisionDart I d).1
    ((frozen_iff_exists_subdivisionDart I _).mpr ⟨d, rfl, fixed_of_word hI hw hd⟩)), d.2)

private theorem frozenReferenceDart_index {I : FixedRotationInput} (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    (d : Dart I.graph) (hd : d.index ∈ word) :
    frozenIndex I (frozenReferenceDart hI hw d hd).1 = (subdivisionDart I d).1 :=
  Classical.choose_spec (frozenIndex_covers hI (subdivisionDart I d).1
    ((frozen_iff_exists_subdivisionDart I _).mpr ⟨d, rfl, fixed_of_word hI hw hd⟩))

/-- Retention preserves the original occurrence's end tag, its center and its own leaf. -/
theorem frozenReferenceDart_endpoints {I : FixedRotationInput} (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    (d : Dart I.graph) (hd : d.index ∈ word) :
    (frozenReferenceDart hI hw d hd).2 = d.2 ∧
      (frozenReferenceDart hI hw d hd).vertex = d.vertex ∧
      (frozenReferenceDart hI hw d hd).reverse.vertex = I.graph.vertices.length + d.index := by
  have hindex := frozenReferenceDart_index hI hw d hd
  have hcenter := frozenIndex_vertex I (frozenReferenceDart hI hw d hd).1 d.2
  have hleaf := frozenIndex_vertex I (frozenReferenceDart hI hw d hd).1 (!d.2)
  rw [hindex] at hcenter hleaf
  exact ⟨rfl, hcenter.symm.trans (subdivisionDart_endpoints I d).1,
    hleaf.symm.trans (subdivisionDart_endpoints I d).2⟩

/-- Every retained original fixed end has exactly its old outgoing geometric vector. -/
theorem frozenReferenceDrawing_germ_frozenReferenceDart {I : FixedRotationInput} (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    (d : Dart I.graph) (hd : d.index ∈ word) :
    (frozenReferenceDrawing I).germ (frozenReferenceDart hI hw d hd) =
      (referenceDrawing I).germ (subdivisionDart I d) := by
  change ((referenceDrawing I).route
    (frozenIndex I (frozenReferenceDart hI hw d hd).1)).germ d.2 = _
  rw [frozenReferenceDart_index]
  rfl

/-- Restriction retains the complete literal prescribed clockwise order, expressed as the
reversed `c,b,a` angular triple. The fixed-end proofs are derived from the full stored word. -/
theorem frozenReferenceDrawing_fixedWord_clockwise_iff {I : FixedRotationInput} (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    {a b c : Dart I.graph} (ha : a.index ∈ word) (hb : b.index ∈ word) (hc : c.index ∈ word)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw ((frozenReferenceDrawing I).direction (frozenReferenceDart hI hw c hc))
      ((frozenReferenceDrawing I).direction (frozenReferenceDart hI hw b hb))
      ((frozenReferenceDrawing I).direction (frozenReferenceDart hI hw a ha)) ↔
        (word.idxOf a.index < word.idxOf b.index ∧ word.idxOf b.index < word.idxOf c.index) ∨
        (word.idxOf b.index < word.idxOf c.index ∧ word.idxOf c.index < word.idxOf a.index) ∨
        (word.idxOf c.index < word.idxOf a.index ∧ word.idxOf a.index < word.idxOf b.index) := by
  simp only [PolygonalDrawing.direction, frozenReferenceDrawing_germ_frozenReferenceDart]
  exact referenceDrawing_fixedWord_clockwise_iff hI hw ha hb hc hab hbc hac

end Cslib.Complexity.Graph.RotationRecognition
