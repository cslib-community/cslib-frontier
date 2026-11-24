/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Basic
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.UnitRoute
public import CslibFrontier.Foundations.Geometry.Orthogonal.UnitSegments
public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing
import Mathlib.Data.List.FinRange

/-!
# Continuous orthogonal drawings of finite constraint graphs

Cycle erasure turns the complete grid paths into simple unit routes. The vertex row gaps rule
out a common unit segment between different edges, so every real contact is an allowed graph
vertex. The resulting certificate uses the standard finite incidence-graph drawing interface.

## Main definitions

* `GridDrawing.Closed.incidenceGraph`: one listed occurrence for every constraint-graph edge.
* `GridDrawing.Closed.orthogonalDrawing`: integer positions and simple unit routes.

## Main results

* `GridDrawing.Closed.incidenceGraph_incident_iff`: the listed endpoints are exactly the original
  port incidences.
* `GridDrawing.Closed.isPlanarOrthogonalDrawing`: the continuous standard drawing certificate.
-/

public section

namespace Cslib.Complexity.NCL.GridDrawing

open Orthogonal

variable {V E : Type*} {G : ConstraintGraph V E}

/-- A port incidence identifies one of the two prescribed path endpoints. -/
theorem Closed.incident_iff (D : Closed G) (v : V) (e : E) :
    Incident G v e ↔ v = D.source e ∨ v = D.target e := by
  constructor
  · rintro ⟨d, hd⟩
    cases d
    · exact .inl (D.source_eq v e hd).symm
    · exact .inr (D.target_eq v e hd).symm
  · rintro (rfl | rfl)
    · exact ⟨false, D.source_port e⟩
    · exact ⟨true, D.target_port e⟩

private theorem no_common_unit (D : Closed G) {e f : E} (hef : e ≠ f)
    {a b : Point} (ha : a ∈ (D.path e).unitRoute) (hb : b ∈ (D.path e).unitRoute)
    (ha' : a ∈ (D.path f).unitRoute) (hb' : b ∈ (D.path f).unitRoute)
    (hu : length a b = 1) : False := by
  obtain ⟨x, hx, hxe⟩ := (D.path e).unitRoute_trace a ha
  obtain ⟨y, hy, hye⟩ := (D.path e).unitRoute_trace b hb
  have hxf := (D.path f).contains_of_mem_unitRoute x (hx.symm ▸ ha')
  have hyf := (D.path f).contains_of_mem_unitRoute y (hy.symm ▸ hb')
  obtain ⟨v, rfl, _, _⟩ := D.meet e f x hef hxe hxf
  obtain ⟨w, rfl, _, _⟩ := D.meet e f y hef hye hyf
  rw [← hx, ← hy] at hu
  by_cases h : v = w
  · subst w
    have hz : 0 = 1 := by
      simpa only [length, sub_self, Int.natAbs_zero, Nat.zero_add] using hu
    exact Nat.zero_ne_one hz
  · have hs := D.vertex_separation v w h
    dsimp only [integerPoint, length] at hu
    omega

/-- Distinct complete grid paths meet in the real plane only at common incident vertices. -/
theorem Closed.unitRoute_meet (D : Closed G) {e f : E} (hef : e ≠ f) {p : ℝ × ℝ}
    (he : p ∈ support (D.path e).unitRoute) (hf : p ∈ support (D.path f).unitRoute) :
    ∃ v, p = realPoint (integerPoint (D.vertex v)) ∧ Incident G v e ∧ Incident G v f := by
  have hseg : ∀ a ∈ (D.path e).unitRoute.consecutivePairs,
      ∀ b ∈ (D.path f).unitRoute.consecutivePairs, a ≠ b ∧ a ≠ (b.2, b.1) := by
    intro a ha b hb
    have ham := List.of_mem_zip ha
    have hbm := List.of_mem_zip hb
    constructor
    · intro h
      subst b
      exact no_common_unit D hef ham.1 (List.mem_of_mem_tail ham.2)
        hbm.1 (List.mem_of_mem_tail hbm.2) ((D.path e).unitRoute_unit a ha)
    · intro h
      subst a
      exact no_common_unit D hef ham.1 (List.mem_of_mem_tail ham.2)
        (List.mem_of_mem_tail hbm.2) hbm.1 ((D.path e).unitRoute_unit _ ha)
  obtain ⟨u, hue, huf, hpu⟩ := contact_unit_routes
    (D.path e).unitRoute_unit (D.path f).unitRoute_unit hseg he hf
  obtain ⟨x, hx, hxe⟩ := (D.path e).unitRoute_trace u hue
  obtain ⟨v, hxv, hve, hvf⟩ :=
    D.meet e f x hef hxe ((D.path f).contains_of_mem_unitRoute x (hx.symm ▸ huf))
  refine ⟨v, ?_, hve, hvf⟩
  rw [hpu, ← hx, hxv]

variable {n m : ℕ} {G : ConstraintGraph (Fin n) (Fin m)}

/-- The finite listed incidence graph has one occurrence for each original edge. -/
@[expose] def Closed.incidenceGraph (D : Closed G) : Cslib.Complexity.Graph :=
  { vertices := List.range n
    edges := List.ofFn (fun e : Fin m => ((D.source e).val, (D.target e).val)) }

/-- The endpoints of every listed edge describe exactly the original port incidences. -/
theorem Closed.incidenceGraph_incident_iff (D : Closed G) (v : Fin n) (e : Fin m) :
    let edge := D.incidenceGraph.edges[e.val]'(by
      simpa only [Closed.incidenceGraph, List.length_ofFn] using e.isLt)
    (v.val = edge.1 ∨ v.val = edge.2) ↔ Incident G v e := by
  simp only [Closed.incidenceGraph, List.getElem_ofFn]
  rw [D.incident_iff]
  exact or_congr Fin.val_inj Fin.val_inj

/-- Integer positions and cycle-erased unit routes in their original vertex and edge orders. -/
@[expose] def Closed.orthogonalDrawing (D : Closed G) : Cslib.Complexity.Graph.OrthogonalDrawing :=
  (List.ofFn (fun v : Fin n => integerPoint (D.vertex v)),
    List.ofFn (fun e : Fin m => (D.path e).unitRoute))

private theorem getD_ofFn {α : Type*} (f : Fin m → α) (i : Fin m) (a : α) :
    (List.ofFn f).getD i.val a = f i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]

/-- The position of a declared label is its original grid vertex position. -/
theorem Closed.drawingPosition (D : Closed G) (v : Fin n) :
    Cslib.Complexity.Graph.drawingPosition D.incidenceGraph D.orthogonalDrawing v.val =
      integerPoint (D.vertex v) := by
  change (List.ofFn (fun v : Fin n => integerPoint (D.vertex v))).getD
    ((List.range n).idxOf v.val) (0, 0) = _
  have hi : (List.range n).idxOf v.val = v.val := by
    have hv : v.val < (List.range n).length := by
      simpa only [List.length_range] using v.isLt
    have h := (List.nodup_range (n := n)).idxOf_getElem v.val hv
    rw [List.getElem_range hv] at h
    exact h
  rw [hi]
  exact getD_ofFn _ v _

private theorem route_getD (D : Closed G) (i : Fin m) :
    D.orthogonalDrawing.2.getD i.val [] = (D.path i).unitRoute := getD_ofFn _ i []

private theorem edge_get (D : Closed G) (i : ℕ) (hi : i < D.incidenceGraph.edges.length) :
    D.incidenceGraph.edges[i] =
      ((D.source ⟨i, by simpa only [Closed.incidenceGraph, List.length_ofFn] using hi⟩).val,
        (D.target ⟨i, by simpa only [Closed.incidenceGraph, List.length_ofFn] using hi⟩).val) :=
  List.getElem_ofFn _

private theorem drawing_endpoints (D : Closed G) (i : ℕ) (hi : i < D.incidenceGraph.edges.length) :
    let r := D.orthogonalDrawing.2.getD i []
    let a := Cslib.Complexity.Graph.drawingPosition D.incidenceGraph D.orthogonalDrawing
      D.incidenceGraph.edges[i].1
    let b := Cslib.Complexity.Graph.drawingPosition D.incidenceGraph D.orthogonalDrawing
      D.incidenceGraph.edges[i].2
    (r.head? = some a ∧ r.getLast? = some b) ∨
      (r.head? = some b ∧ r.getLast? = some a) := by
  let e : Fin m := ⟨i, by simpa only [Closed.incidenceGraph, List.length_ofFn] using hi⟩
  dsimp only
  rw [edge_get D i hi, route_getD D e, D.drawingPosition, D.drawingPosition]
  exact .inl ⟨(D.path e).unitRoute_head, (D.path e).unitRoute_last⟩

private theorem drawing_avoids (D : Closed G) (i : ℕ) (hi : i < D.incidenceGraph.edges.length)
    (v : ℕ) (hv : v ∈ D.incidenceGraph.vertices)
    (hp : realPoint (Cslib.Complexity.Graph.drawingPosition D.incidenceGraph
      D.orthogonalDrawing v) ∈ support (D.orthogonalDrawing.2.getD i [])) :
    v = D.incidenceGraph.edges[i].1 ∨ v = D.incidenceGraph.edges[i].2 := by
  let e : Fin m := ⟨i, by simpa only [Closed.incidenceGraph, List.length_ofFn] using hi⟩
  let x : Fin n := ⟨v, List.mem_range.1 hv⟩
  rw [D.drawingPosition x, route_getD D e] at hp
  have hm := (mem_iff_realPoint_mem_support (D.path e).unitRoute_unit _).2 hp
  have hinc := D.vertex_meet e x ((D.path e).contains_of_mem_unitRoute _ hm)
  exact (D.incidenceGraph_incident_iff x e).2 hinc

private theorem drawing_contacts (D : Closed G) (i : ℕ) (hi : i < D.incidenceGraph.edges.length)
    (j : ℕ) (hj : j < D.incidenceGraph.edges.length) (hij : i ≠ j) (p : ℝ × ℝ)
    (hp : p ∈ support (D.orthogonalDrawing.2.getD i []))
    (hq : p ∈ support (D.orthogonalDrawing.2.getD j [])) :
    ∃ v ∈ D.incidenceGraph.vertices,
      (v = D.incidenceGraph.edges[i].1 ∨ v = D.incidenceGraph.edges[i].2) ∧
      (v = D.incidenceGraph.edges[j].1 ∨ v = D.incidenceGraph.edges[j].2) ∧
      p = realPoint (Cslib.Complexity.Graph.drawingPosition D.incidenceGraph
        D.orthogonalDrawing v) := by
  let e : Fin m := ⟨i, by simpa only [Closed.incidenceGraph, List.length_ofFn] using hi⟩
  let f : Fin m := ⟨j, by simpa only [Closed.incidenceGraph, List.length_ofFn] using hj⟩
  rw [route_getD D e] at hp
  rw [route_getD D f] at hq
  obtain ⟨v, hpv, hve, hvf⟩ := D.unitRoute_meet (fun h => hij (congrArg Fin.val h)) hp hq
  refine ⟨v.val, List.mem_range.2 v.isLt, ?_, ?_, ?_⟩
  · exact (D.incidenceGraph_incident_iff v e).2 hve
  · exact (D.incidenceGraph_incident_iff v f).2 hvf
  · rw [D.drawingPosition]
    exact hpv

/-- The simple unit routes certify the standard continuous planar orthogonal drawing predicate. -/
theorem Closed.isPlanarOrthogonalDrawing (D : Closed G) :
    Cslib.Complexity.Graph.IsPlanarOrthogonalDrawing D.incidenceGraph D.orthogonalDrawing := by
  refine
    { vertexCount := by simp only [Closed.orthogonalDrawing, Closed.incidenceGraph,
        List.length_ofFn, List.length_range]
      edgeCount := by simp only [Closed.orthogonalDrawing, Closed.incidenceGraph, List.length_ofFn]
      labelsNodup := List.nodup_range
      positionsNodup := List.nodup_ofFn.2 (integerPoint_injective.comp D.vertex_injective)
      endpointsDeclared := ?_
      loopless := ?_
      endpoints := drawing_endpoints D
      orthogonal := ?_
      simple := ?_
      avoidsVertices := drawing_avoids D
      contacts := drawing_contacts D }
  · intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    exact ⟨List.mem_range.2 (D.source i).isLt, List.mem_range.2 (D.target i).isLt⟩
  · intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    exact fun h => D.source_ne_target i (Fin.ext h)
  · intro i hi
    let e : Fin m := ⟨i, by simpa only [Closed.incidenceGraph, List.length_ofFn] using hi⟩
    rw [route_getD D e]
    exact fun a ha => axisAligned_of_length_eq_one ((D.path e).unitRoute_unit a ha)
  · intro i hi
    let e : Fin m := ⟨i, by simpa only [Closed.incidenceGraph, List.length_ofFn] using hi⟩
    rw [route_getD D e]
    exact isSimple_of_unit_nodup (D.path e).unitRoute_nodup (D.path e).unitRoute_unit

end Cslib.Complexity.NCL.GridDrawing
