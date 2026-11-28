/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Faces
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Certificate

/-!
# Components of the occurrence-indexed polygon graph

Replacing a positive constraint star by its indexed cyclic scope preserves connected components.
All component statements use the existing graph reachability relation on declared vertices.

## Main results

* `Cslib.Complexity.CSP.sameComponent_polygon_iff`: exact reachability correspondence.
* `Cslib.Complexity.CSP.polygonComponentEquiv`: bijection of actual graph components.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph.RotationCertificate

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

private theorem polygon_declared (o : F.Occurrence) :
    F.distinctVars.idxOf o.var ∈ (polygonGraph F).1 := by
  change F.distinctVars.idxOf o.var ∈ List.range F.numVars
  rw [List.mem_range, ← CSP.length_distinctVars]
  exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr o.var_mem)

/-- All endpoints in the flattened polygon list are declared dense vertices. -/
theorem polygon_endpoints_declared :
    ∀ v ∈ (polygonGraph F).incidenceVertices, v ∈ (polygonGraph F).1 := by
  intro v hv
  obtain ⟨edge, he, hv⟩ := List.mem_flatMap.mp hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact (polygonGraph_endpoints he).1
  · exact List.mem_singleton.mp hv ▸ (polygonGraph_endpoints he).2

/-- Consecutive scope positions are connected by their actual listed polygon edge,
including when its endpoints coincide. -/
theorem polygon_sameComponent_successor (o : F.Occurrence) :
    SameComponent (polygonGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf (argumentSuccessor o).var) := by
  have h := Graph.RotationSystem.sameComponent_reverse polygon_endpoints_declared
    (polygonDart o false)
  change SameComponent _ (polygonDart o false).vertex (polygonDart o true).vertex at h
  simpa only [vertex_polygonDart, Bool.false_eq_true, ↓reduceIte] using h

/-- All arguments of one constraint lie in the same polygon component. This includes unary
and repeated-variable scopes and does not identify different constraint positions. -/
theorem polygon_sameComponent_constraint (o p : F.Occurrence) (h : o.1 = p.1) :
    SameComponent (polygonGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf p.var) := by
  obtain ⟨n, hn⟩ := ((sameCycle_argumentPermutation o p).mpr h).exists_nat_pow_eq
  have hi (k : ℕ) : SameComponent (polygonGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf ((argumentPermutation F)^[k] o).var) := by
    induction k with
    | zero => exact .refl (polygon_declared o)
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (polygon_sameComponent_successor _)
  simpa only [Equiv.Perm.iterate_eq_pow, hn] using hi n

private theorem polygon_sameComponent_incidence_vertex (o p : F.Occurrence) (b c : Bool)
    (h : (incidenceDart o b).vertex = (incidenceDart p c).vertex) :
    SameComponent (polygonGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf p.var) := by
  have ho : F.distinctVars.idxOf o.var < F.numVars := by
    rw [← CSP.length_distinctVars]
    exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr o.var_mem)
  have hp : F.distinctVars.idxOf p.var < F.numVars := by
    rw [← CSP.length_distinctVars]
    exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr p.var_mem)
  rw [vertex_incidenceDart, vertex_incidenceDart] at h
  cases b <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  · rw [h]
    exact .refl (polygon_declared p)
  · omega
  · omega
  · exact polygon_sameComponent_constraint o p (by omega)

private theorem incidence_adj_occurrence {u v : ℕ}
    (h : (incidenceGraph F).toSimpleGraph.Adj u v) :
    ∃ o : F.Occurrence, ∃ b : Bool,
      (incidenceDart o b).vertex = u ∧ (incidenceDart o (!b)).vertex = v := by
  rcases (Graph.toSimpleGraph_adj.mp h).2 with h | h <;>
    obtain ⟨_, hr, he⟩ := List.mem_map.mp (incidenceGraph_edges F ▸ h) <;>
    obtain ⟨o, rfl⟩ := CSP.mem_occurrences.mp hr
  · exact ⟨o, false, (vertex_incidenceDart o false).trans (congrArg Prod.fst he),
      (vertex_incidenceDart o true).trans (congrArg Prod.snd he)⟩
  · exact ⟨o, true, (vertex_incidenceDart o true).trans (congrArg Prod.snd he),
      (vertex_incidenceDart o false).trans (congrArg Prod.fst he)⟩

/-- Every incidence path between occurring variables becomes a polygon path. -/
theorem polygon_sameComponent_of_incidence (o p : F.Occurrence)
    (h : SameComponent (incidenceGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf p.var)) :
    SameComponent (polygonGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf p.var) := by
  let P (v : ℕ) : Prop := ∃ q : F.Occurrence, ∃ b : Bool,
    (incidenceDart q b).vertex = v ∧ SameComponent (polygonGraph F)
      (F.distinctVars.idxOf o.var) (F.distinctVars.idxOf q.var)
  have step {u v : {v // v ∈ (incidenceGraph F).1}}
      (hadj : (incidenceGraph F).induced.Adj u v) (hu : P u.val) : P v.val := by
    obtain ⟨q, b, hq, hu⟩ := hu
    obtain ⟨t, c, ht, hv⟩ := incidence_adj_occurrence hadj
    exact ⟨t, !c, hv, hu.trans
      (polygon_sameComponent_incidence_vertex q t b c (hq.trans ht.symm))⟩
  obtain ⟨hu, hv, ⟨w⟩⟩ := h
  have transport {u v : {v // v ∈ (incidenceGraph F).1}}
      (w : (incidenceGraph F).induced.Walk u v) : P u.val → P v.val := by
    induction w with
    | nil => exact id
    | cons hadj w ih => exact fun h => ih (step hadj h)
  obtain ⟨q, b, hq, hconn⟩ := transport w
    ⟨o, false, vertex_incidenceDart o false, .refl (polygon_declared o)⟩
  exact hconn.trans (polygon_sameComponent_incidence_vertex q p b false
    (hq.trans (vertex_incidenceDart p false).symm))

/-- The two variables of a polygon edge are connected through its original constraint star. -/
theorem incidence_sameComponent_polygonEdge (o : F.Occurrence) :
    SameComponent (incidenceGraph F) (F.distinctVars.idxOf o.var)
      (F.distinctVars.idxOf (argumentSuccessor o).var) := by
  have h (p : F.Occurrence) : SameComponent (incidenceGraph F)
      (F.distinctVars.idxOf p.var) (F.numVars + p.1) := by
    have h := Graph.RotationSystem.sameComponent_reverse (incidenceVertices_declared F)
      (incidenceDart p false)
    change SameComponent _ (incidenceDart p false).vertex (incidenceDart p true).vertex at h
    simpa only [vertex_incidenceDart, Bool.false_eq_true, ↓reduceIte] using h
  exact (h o).trans (h (argumentSuccessor o)).symm

private theorem polygon_vertex_incidence_declared {v : ℕ} (h : v ∈ (polygonGraph F).1) :
    v ∈ (incidenceGraph F).1 := by
  rw [incidenceGraph_vertices, List.mem_range]
  have hv : v < F.numVars := List.mem_range.mp h
  omega

/-- Every polygon path lifts to an incidence path, using the two original star edges for
each listed polygon edge. -/
theorem incidence_sameComponent_of_polygon {u v : ℕ}
    (h : SameComponent (polygonGraph F) u v) : SameComponent (incidenceGraph F) u v := by
  have edge {x y : ℕ} (he : (x, y) ∈ (polygonGraph F).edges) :
      SameComponent (incidenceGraph F) x y := by
    obtain ⟨_, hr, he⟩ := List.mem_map.mp he
    obtain ⟨o, rfl⟩ := CSP.mem_occurrences.mp hr
    have hu : F.distinctVars.idxOf o.var = x := congrArg Prod.fst he
    have hv : F.distinctVars.idxOf (argumentSuccessor o).var = y :=
      (polygonNext_occurrence o).symm.trans (congrArg Prod.snd he)
    exact hu ▸ hv ▸ incidence_sameComponent_polygonEdge o
  have lift {x y : {v // v ∈ (polygonGraph F).1}} (w : (polygonGraph F).induced.Walk x y) :
      SameComponent (incidenceGraph F) x.val y.val := by
    induction w with
    | @nil v => exact .refl (polygon_vertex_incidence_declared v.property)
    | cons hadj _ ih =>
      exact ((Graph.toSimpleGraph_adj.mp hadj).2.elim edge fun he => (edge he).symm).trans ih
  obtain ⟨_, _, ⟨w⟩⟩ := h
  exact lift w

/-- Every dense variable vertex has an actual occurrence, even with enormous sparse source
names. No finite universe of source variables is required. -/
theorem exists_occurrence_dense (v : ℕ) (hv : v < F.numVars) :
    ∃ o : F.Occurrence, F.distinctVars.idxOf o.var = v := by
  have hv' : v < F.distinctVars.length := by rwa [CSP.length_distinctVars]
  obtain ⟨o, ho⟩ := (CSP.exists_occurrence_iff F.distinctVars[v]).mpr
    (CSP.mem_distinctVars.mp (List.getElem_mem hv'))
  exact ⟨o, ho ▸ (nodup_selectDistinct _ _).idxOf_getElem v hv'⟩

/-- Exact component correspondence on all dense variable vertices. -/
theorem sameComponent_polygon_iff {u v : ℕ} (hu : u < F.numVars) (hv : v < F.numVars) :
    SameComponent (polygonGraph F) u v ↔ SameComponent (incidenceGraph F) u v := by
  refine ⟨incidence_sameComponent_of_polygon, ?_⟩
  obtain ⟨o, rfl⟩ := exists_occurrence_dense u hu
  obtain ⟨p, rfl⟩ := exists_occurrence_dense v hv
  exact polygon_sameComponent_of_incidence o p

/-- The inclusion of dense variable vertices induces the actual map of graph components. -/
noncomputable def polygonComponentMap (F : CSP Rel V) :
    (polygonGraph F).induced.ConnectedComponent → (incidenceGraph F).induced.ConnectedComponent :=
  Quot.map (fun v => ⟨v.val, polygon_vertex_incidence_declared v.property⟩)
    (fun u v h => by
      obtain ⟨_, _, reachable⟩ := incidence_sameComponent_of_polygon ⟨u.property, v.property, h⟩
      exact reachable)

/-- Distinct polygon components remain distinct incidence components. -/
theorem polygonComponentMap_injective (F : CSP Rel V) :
    Function.Injective (polygonComponentMap F) := by
  refine SimpleGraph.ConnectedComponent.ind fun u =>
    SimpleGraph.ConnectedComponent.ind fun v h => SimpleGraph.ConnectedComponent.sound ?_
  exact ((sameComponent_polygon_iff (List.mem_range.mp u.property)
    (List.mem_range.mp v.property)).mpr ⟨_, _, SimpleGraph.ConnectedComponent.exact h⟩).2.2

/-- Positive scopes ensure that no incidence component consists of a deleted nullary
constraint vertex. Thus every incidence component contains a polygon vertex. -/
theorem polygonComponentMap_surjective (F : CSP Rel V)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) :
    Function.Surjective (polygonComponentMap F) := by
  refine SimpleGraph.ConnectedComponent.ind fun v => ?_
  if hv : v.val < F.numVars then
    exact ⟨(polygonGraph F).induced.connectedComponentMk ⟨v.val, List.mem_range.mpr hv⟩, rfl⟩
  else
    have hb : v.val < F.numVars + F.length := by simpa [incidenceGraph_vertices] using v.property
    let o : F.Occurrence := ⟨⟨v.val - F.numVars, by omega⟩, ⟨0, hPos _⟩⟩
    refine ⟨(polygonGraph F).induced.connectedComponentMk
      ⟨F.distinctVars.idxOf o.var, polygon_declared o⟩, SimpleGraph.ConnectedComponent.sound ?_⟩
    have hc := Graph.RotationSystem.sameComponent_reverse (incidenceVertices_declared F)
      (incidenceDart o false)
    change SameComponent _ (incidenceDart o false).vertex (incidenceDart o true).vertex at hc
    rw [vertex_incidenceDart, vertex_incidenceDart] at hc
    exact (show SameComponent (incidenceGraph F) (F.distinctVars.idxOf o.var) v.val by
      simpa [o, show F.numVars + (v.val - F.numVars) = v.val by omega] using hc).2.2

/-- Exact component bijection for positive scopes, including disconnected and empty bodies. -/
noncomputable def polygonComponentEquiv (F : CSP Rel V)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].scope.length) :
    (polygonGraph F).induced.ConnectedComponent ≃ (incidenceGraph F).induced.ConnectedComponent :=
  Equiv.ofBijective (polygonComponentMap F)
    ⟨polygonComponentMap_injective F, polygonComponentMap_surjective F hPos⟩

end Cslib.Complexity.CSP
