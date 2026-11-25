/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.AndOr
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Replacement.Enumeration
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Vertices
public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.NodupEquivFin

/-!
# Computable numbering of selector-network implementations

Enumerate source cells in the supplied order, then enumerate each cell's vertices and private
wires in creation order. Each shared edge is emitted at its false endpoint cell.
The resulting finite graph is an exact renaming of the complete implementation.

## Main definitions

* `SelectorNetwork.AndOr.Numbering.vertexList`: the implementation's vertex enumeration.
* `SelectorNetwork.AndOr.Numbering.edgeList`: its shared and private edges.
* `SelectorNetwork.AndOr.Numbering.graph`: the graph on finite intervals.

## Main results

* `SelectorNetwork.AndOr.Numbering.simulation`: finite numbering preserves all dynamics.
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner

namespace Cslib.Complexity.NCL.SelectorNetwork.AndOr.Numbering

open Diagram

variable {U C R : Type*} [DecidableEq U] [DecidableEq C]
variable (N : SelectorNetwork U C R) (A : RowSection N)
variable {m : ℕ} (order : Vert U C R ≃ Fin m)

private def sourceList : List (Vert U C R) := List.ofFn order.symm

omit [DecidableEq U] [DecidableEq C] in
private theorem sourceList_nodup : (sourceList order).Nodup :=
  List.nodup_ofFn.mpr order.symm.injective

omit [DecidableEq U] [DecidableEq C] in
private theorem mem_sourceList (v : Vert U C R) : v ∈ sourceList order := by
  exact List.mem_ofFn.mpr ⟨order v, order.symm_apply_apply v⟩

/-- Standard vertices in source-cell order and local creation order. The dependent sum is the
vertex index type of `ConstraintGraph.Replacement.graph`. -/
@[expose] def vertexList : List (TargetVertex N A) :=
  (List.ofFn order.symm).sigma fun v =>
    List.ofFn (Diagram.vertexEquiv Prim.interp (cell N A v).diagram).symm

/-- Local creation order gives decidable equality of implementation vertices. -/
instance instDecidableEqTargetVertex [DecidableEq R] : DecidableEq (TargetVertex N A) :=
  letI := fun v : Vert U C R =>
    (Diagram.vertexEquiv Prim.interp (cell N A v).diagram).decidableEq
  inferInstanceAs (DecidableEq ((v : Vert U C R) × (cell N A v).diagram.Vtx Prim.interp))

/-- Each implementation vertex occurs once. -/
theorem vertexList_nodup : (vertexList N A order).Nodup :=
  (sourceList_nodup order).sigma fun v =>
    List.nodup_ofFn.mpr (Diagram.vertexEquiv Prim.interp (cell N A v).diagram).symm.injective

/-- The vertex enumeration is complete. -/
theorem mem_vertexList (v : TargetVertex N A) : v ∈ vertexList N A order := by
  refine List.mem_sigma.mpr ⟨mem_sourceList order v.1, ?_⟩
  exact List.mem_ofFn.mpr ⟨Diagram.vertexEquiv Prim.interp (cell N A v.1).diagram v.2,
    Equiv.symm_apply_apply _ _⟩

/-- Shared edges whose false endpoint belongs to the indicated source cell. -/
@[expose] def ownedShared : Vert U C R → List (Edge C R)
  | .inl _ => []
  | .inr (.inl c) => [.inl c]
  | .inr (.inr r) => [.inr (r, false), .inr (r, true)]

/-- The source cell owning a shared edge, or containing a private wire. -/
@[expose] def edgeOwner : Edge C R ⊕ Private N A → Vert U C R
  | .inl (.inl c) => .inr (.inl c)
  | .inl (.inr e) => .inr (.inr e.1)
  | .inr e => e.1

/-- All edges first created at one source cell, with shared edges before its private wires. -/
@[expose] def localEdges (v : Vert U C R) : List (Edge C R ⊕ Private N A) :=
  (ownedShared v).map Sum.inl ++
    (Diagram.Replacement.innerList (cell N A v).openSim).map fun e => .inr ⟨v, e⟩

private theorem localEdges_nodup (v : Vert U C R) : (localEdges N A v).Nodup := by
  have hs : (ownedShared v).Nodup := by rcases v with u | (c | r) <;> simp [ownedShared]
  apply List.nodup_append.mpr
  refine ⟨hs.map Sum.inl_injective,
    (Diagram.Replacement.innerList_nodup (cell N A v).openSim).map
      (Sum.inr_injective.comp sigma_mk_injective), ?_⟩
  intro e he f hf hef
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp he
  obtain ⟨f, _, rfl⟩ := List.mem_map.mp hf
  cases hef

/-- Every edge emitted by a cell belongs to that cell's ownership block. -/
theorem owner_mem_localEdges (v : Vert U C R) (e : Edge C R ⊕ Private N A)
    (he : e ∈ localEdges N A v) : edgeOwner N A e = v := by
  rcases List.mem_append.mp he with hs | hp
  · obtain ⟨e, he', rfl⟩ := List.mem_map.mp hs
    rcases v with u | (c | r)
    · exact (List.not_mem_nil he').elim
    · simp only [ownedShared, List.mem_singleton] at he'
      subst e
      rfl
    · simp only [ownedShared, List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl <;> rfl
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hp
    rfl

/-- Enumerate edges in source-cell order, so row-local cells retain row-local edge numbering. -/
@[expose] def edgeList : List (Edge C R ⊕ Private N A) :=
  (List.ofFn order.symm).flatMap (localEdges N A)

/-- No two shared or private implementation edges receive the same number. -/
theorem edgeList_nodup : (edgeList N A order).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun v _ => localEdges_nodup N A v, (sourceList_nodup order).imp ?_⟩
  intro v w hvw e he hf
  exact hvw ((owner_mem_localEdges N A v e he).symm.trans (owner_mem_localEdges N A w e hf))

/-- Every implementation edge is represented in the explicit edge list. -/
theorem mem_edgeList (e : Edge C R ⊕ Private N A) : e ∈ edgeList N A order := by
  apply List.mem_flatMap.mpr
  rcases e with (c | ⟨r, b⟩) | ⟨v, e⟩
  · refine ⟨.inr (.inl c), mem_sourceList order _, List.mem_append_left _ ?_⟩
    exact List.mem_map.mpr ⟨.inl c, List.mem_singleton_self _, rfl⟩
  · refine ⟨.inr (.inr r), mem_sourceList order _, List.mem_append_left _ ?_⟩
    apply List.mem_map.mpr
    refine ⟨.inr (r, b), ?_, rfl⟩
    cases b <;> simp [ownedShared]
  · refine ⟨v, mem_sourceList order _, List.mem_append_right _ ?_⟩
    exact List.mem_map.mpr ⟨e, Diagram.Replacement.mem_innerList (cell N A v).openSim e, rfl⟩

variable [DecidableEq R]

/-- Exact finite vertex numbering, computed by list lookup. -/
@[expose] def vertexEquiv : TargetVertex N A ≃ Fin (vertexList N A order).length :=
  (List.Nodup.getEquivOfForallMemList _ (vertexList_nodup N A order)
    (mem_vertexList N A order)).symm

/-- Exact finite edge numbering, computed by list lookup. -/
@[expose] def edgeEquiv : (Edge C R ⊕ Private N A) ≃ Fin (edgeList N A order).length :=
  (List.Nodup.getEquivOfForallMemList _ (edgeList_nodup N A order)
    (mem_edgeList N A order)).symm

/-- An edge number is its first index in the explicit edge enumeration. -/
private theorem edgeEquiv_val (e : Edge C R ⊕ Private N A) :
    (edgeEquiv N A order e).val = (edgeList N A order).idxOf e := by
  have hget : (edgeList N A order).get (edgeEquiv N A order e) = e :=
    (edgeEquiv N A order).symm_apply_apply e
  have h := List.get_idxOf (edgeList_nodup N A order) (edgeEquiv N A order e)
  rw [hget] at h
  exact h.symm

/-- The same implementation on finite vertex and edge intervals. -/
@[expose] def graph : ConstraintGraph (Fin (vertexList N A order).length)
    (Fin (edgeList N A order).length) :=
  ConstraintGraph.map (AndOr.graph N A ∘ (vertexEquiv N A order).symm) (edgeEquiv N A order)

/-- Serialization is a direct list emission followed by first-index lookup of edge names. -/
theorem serialize_vertices : (AndOrGraph.ofFinite (graph N A order)).vertices =
    (vertexList N A order).map fun v => (AndOr.graph N A v).map
      (fun e => (edgeList N A order).idxOf e) := by
  change List.ofFn (fun i =>
    ((AndOr.graph N A ((vertexList N A order).get i)).map (edgeEquiv N A order)).map Fin.val) = _
  simp only [Vertex.map_map, Function.comp_def, edgeEquiv_val]
  rw [List.ofFn_comp', List.ofFn_comp', List.ofFn_get, List.map_map]
  rfl

/-- Explicit numbering is an exact simulation of the complete implementation. -/
def simulation : ConstraintGraph.Simulation (AndOr.graph N A) (graph N A order) :=
  ConstraintGraph.Simulation.ofEquiv _ (edgeEquiv N A order) (vertexEquiv N A order).symm

/-- Numbered canonical directions are emitted in the explicit edge-list order. -/
theorem bits_enc (s : Edge C R ⊕ Private N A → Bool) :
    List.ofFn ((simulation N A order).enc s) = (edgeList N A order).map s := by
  change List.ofFn (fun i => s ((edgeList N A order).get i)) = _
  rw [List.ofFn_comp', List.ofFn_get]

/-- Every numbered vertex remains standard AND or OR. -/
theorem isAndOr : (graph N A order).IsAndOr :=
  fun i => (AndOr.isAndOr N A ((vertexEquiv N A order).symm i)).map _

/-- Exact edge numbering preserves absence of self-loops. -/
theorem loopFree : (graph N A order).LoopFree := by
  apply ConstraintGraph.LoopFree.map
  · intro i
    exact AndOr.loopFree N A ((vertexEquiv N A order).symm i)
  · exact (edgeEquiv N A order).injective

/-- Numbering preserves the same two opposite, equally weighted ports per edge. -/
theorem wellFormed : (graph N A order).WellFormed := by
  let : Fintype U := Fintype.ofInjective (fun u => order (.inl u))
    (order.injective.comp Sum.inl_injective)
  let : Fintype C := Fintype.ofInjective (fun c => order (.inr (.inl c)))
    (order.injective.comp (Sum.inr_injective.comp Sum.inl_injective))
  let : Fintype R := Fintype.ofInjective (fun r => order (.inr (.inr r)))
    (order.injective.comp (Sum.inr_injective.comp Sum.inr_injective))
  exact ((AndOr.wellFormed N A).reindex (vertexEquiv N A order).symm).map (edgeEquiv N A order)

end Cslib.Complexity.NCL.SelectorNetwork.AndOr.Numbering
