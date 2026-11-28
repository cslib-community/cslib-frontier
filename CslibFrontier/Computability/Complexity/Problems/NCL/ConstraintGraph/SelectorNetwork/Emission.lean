/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Template
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Sparse
import CslibFrontier.Foundations.Data.List.IdxOf
import Mathlib.Data.List.GetD

/-!
# Instantiating the actual network's portable templates

The context reads shared boundary names from the sparse address map and places private creation
numbers after the owning source-cell prefix. This connects portable polynomial-time emission
to the very same certified implementation graph.

## Main definitions

* `SelectorNetwork.AndOr.Sparse.context`: the actual context of one source cell.

## Main results

* `SelectorNetwork.AndOr.Sparse.data_eq_ofFinite`: portable emission serializes exactly the
  certified numbered graph.
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner

namespace Cslib.Complexity.NCL.SelectorNetwork.AndOr.Sparse

open Diagram

variable {U C R : Type*} [DecidableEq U] [DecidableEq C]
variable (N : SelectorNetwork U C R) (A : RowSection N)
variable {m : ℕ} (order : Vert U C R ≃ Fin m) (budget : ℕ)

/-- The local boundary and private names of an actual network cell. -/
@[expose] def context (v : Vert U C R) : TemplateContext where
  boundaryNames := List.ofFn fun i : Fin ((cell N A v).top.length + (cell N A v).bottom.length) =>
    code N A order budget (.inl (port N A v (finSumFinEquiv.symm i)))
  privateBase := budget * (order v).val + 2
  reverse := match v with | .inl _ => true | .inr _ => false
  anchor := match v with
    | .inl u => code N A order budget (.inl (.inl (A.character u)))
    | .inr _ => 0

/-- Sparse names on one cell's shared/private split. -/
private def localCode (v : Vert U C R)
    (e : Edge C R ⊕ Diagram.Replacement.Inner (cell N A v).openSim) : ℕ :=
  code N A order budget (Sum.map id (fun i => (⟨v, i⟩ : Private N A)) e)

/-- Resolving a portable reference gives the original cell wire's actual sparse address. -/
private theorem resolve_wireRef (v : Vert U C R) (e : (cell N A v).diagram.Edge) :
    WireRef.resolve (context N A order budget v) ((cell N A v).wireRef e) =
      localCode N A order budget v
        (Diagram.Replacement.label (cell N A v).openSim (port N A v) e) := by
  classical
  let S := (cell N A v).openSim
  unfold Cell.wireRef
  by_cases he : e ∈ Set.range S.ι
  · obtain ⟨x, rfl⟩ := he
    rw [Diagram.Replacement.label_ι, Diagram.Replacement.label_ι]
    change (context N A order budget v).boundaryNames.getD (finSumFinEquiv x).val 0 = _
    rw [List.getD_eq_getElem _ _
      (by simpa only [context, List.length_ofFn] using (finSumFinEquiv x).isLt)]
    simp only [context, List.getElem_ofFn, finSumFinEquiv.symm_apply_apply]; rfl
  · rw [Diagram.Replacement.label_private S (fun x => (finSumFinEquiv x).val) ⟨e, he⟩,
      Diagram.Replacement.label_private S (port N A v) ⟨e, he⟩]
    exact Nat.add_assoc _ _ _

private theorem map_reorient {E F : Type*} (v : Vertex E) (f : E → F)
    (mask : E → Bool) (target : F → Bool) (h : ∀ e, mask e = target (f e)) :
    (v.reorient mask).map f = (v.map f).reorient target := by
  simp only [Vertex.map, WeightedPort.map, Vertex.reorient, WeightedPort.reorient,
    List.map_map, Function.comp_def,
    Port.map, Port.reorient, h]

section

variable [DecidableEq R]

private theorem mask_localCode
    (hbudget : ∀ v, (cell N A v).top.length + (cell N A v).diagram.innerCount + 2 ≤ budget)
    (v : Vert U C R) (e : Edge C R ⊕ Diagram.Replacement.Inner (cell N A v).openSim) :
    Sum.elim (polarity N A v) (fun _ => false) e =
      ((context N A order budget v).reverse &&
        decide (localCode N A order budget v e = (context N A order budget v).anchor)) := by
  have hinj := code_injective N A order budget hbudget
  rcases v with u | w
  · cases e <;> simp [context, localCode, polarity, hinj.eq_iff]
  · cases e <;> rfl

/-- Instantiating the portable template emits exactly the original local graph's sparse data. -/
private theorem instantiate_template
    (hbudget : ∀ v, (cell N A v).top.length + (cell N A v).diagram.innerCount + 2 ≤ budget)
    (v : Vert U C R) :
    ((cell N A v).template).instantiate (context N A order budget v) =
      ((cell N A v).diagram.vertexList Prim.interp).map (fun w =>
        ((w.map (Diagram.Replacement.label (cell N A v).openSim (port N A v))).reorient
          (Sum.elim (polarity N A v) (fun _ => false))).map (localCode N A order budget v)) := by
  simp only [Template.instantiate, Cell.template, Template.instantiateVertex, List.map_map,
    Function.comp_def]
  refine List.map_congr_left fun w _ => ?_
  rw [Vertex.map_map, show WireRef.resolve (context N A order budget v) ∘ (cell N A v).wireRef =
      localCode N A order budget v ∘ Diagram.Replacement.label (cell N A v).openSim (port N A v)
      from funext (resolve_wireRef N A order budget v),
    map_reorient _ _ _ (fun e : ℕ => (context N A order budget v).reverse &&
      decide (e = (context N A order budget v).anchor))
      (mask_localCode N A order budget hbudget v), Vertex.map_map]

/-- Portable-template vertices emitted in the source-cell order. -/
@[expose] def rawVertices : List (Vertex ℕ) :=
  (List.ofFn order.symm).flatMap fun v =>
    ((cell N A v).template).instantiate (context N A order budget v)

private theorem enumerated_vertices {a b : List Color} (D : Diagram Prim a b)
    (f : Vertex D.Edge → Vertex ℕ) :
    (List.ofFn (Diagram.vertexEquiv Prim.interp D).symm).map (fun w => f (D.graph Prim.interp w)) =
      (D.vertexList Prim.interp).map f := by
  rw [List.map_ofFn]
  simp only [Function.comp_def, ← get_vertexList, List.ofFn_comp', List.ofFn_get]

/-- Complete portable emission is the original standard graph with sparse edge names. -/
private theorem rawVertices_eq
    (hbudget : ∀ v, (cell N A v).top.length + (cell N A v).diagram.innerCount + 2 ≤ budget) :
    rawVertices N A order budget = (Numbering.vertexList N A order).map
      (fun v => (AndOr.graph N A v).map (code N A order budget)) := by
  simp only [rawVertices, Numbering.vertexList, List.sigma, List.map_flatMap, List.map_map]
  refine List.flatMap_congr fun v _ => ?_
  rw [instantiate_template N A order budget hbudget v]
  have hcode : localCode N A order budget v =
      fun e => code N A order budget (Sum.map id (Sigma.mk v) e) := rfl
  simpa only [hcode, AndOr.graph, ConstraintGraph.Replacement.graph, localGraph,
    ConstraintGraph.reorient, ConstraintGraph.map, Diagram.Replacement.graph,
    Vertex.map_map, Function.comp_def] using
    (enumerated_vertices (cell N A v).diagram _).symm

end

private theorem code_private (v : Vert U C R)
    (e : Diagram.Replacement.Inner (cell N A v).openSim) :
    code N A order budget (.inr ⟨v, e⟩) =
      budget * (order v).val + 2 + (cell N A v).diagram.num e.val :=
  (Nat.add_assoc _ _ _).symm

/-- Actual sparse wire names in owner-cell and local creation order. -/
@[expose] def names : List ℕ :=
  (List.ofFn order.symm).flatMap fun v =>
    (Numbering.ownedShared v).map (fun e => code N A order budget (.inl e)) ++
      ((cell N A v).template).privateWires.map (fun j => budget * (order v).val + 2 + j)

private theorem names_eq : names N A order budget =
    (Numbering.edgeList N A order).map (code N A order budget) := by
  simp only [names, Numbering.edgeList, Numbering.localEdges, List.map_flatMap,
    List.map_append, List.map_map, Cell.template, Function.comp_def, code_private]

/-- The explicit standard graph program, with sparse addresses compacted by first-index lookup. -/
@[expose] def data : AndOrGraph where
  vertices := (rawVertices N A order budget).map
    (Vertex.map (fun e => (names N A order budget).idxOf e))
  edgeCount := (names N A order budget).length

/-- The explicit list program serializes exactly the original complete implementation. -/
theorem data_eq_ofFinite [DecidableEq R]
    (hbudget : ∀ v, (cell N A v).top.length + (cell N A v).diagram.innerCount + 2 ≤ budget) :
    data N A order budget = AndOrGraph.ofFinite (Numbering.graph N A order) := by
  apply AndOrGraph.ext
  · rw [data, rawVertices_eq N A order budget hbudget, names_eq]
    simp only [List.map_map, Vertex.map_map, Function.comp_def]
    simp_rw [List.idxOf_map_of_injective (code_injective N A order budget hbudget)]
    exact (Numbering.serialize_vertices N A order).symm
  · rw [data, names_eq, List.length_map]
    rfl

end Cslib.Complexity.NCL.SelectorNetwork.AndOr.Sparse
