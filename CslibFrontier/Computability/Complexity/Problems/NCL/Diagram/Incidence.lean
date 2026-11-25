/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CheckGens
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.WellFormed
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Incidence accounting for diagrams

A generator uses every boundary wire once with its declared color and direction. Composing such
generators consumes each created wire once. Closing the diagram therefore gives two opposite
ports of equal weight for every edge.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.Interp.checkPorts`: check a generator's weighted incidences.

## Main results

* `Cslib.Complexity.NCL.Diagram.wellFormed_of_checkGens`: checked closed diagrams are well formed.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type}

/-- Check that the generator uses each boundary wire exactly once with its color and direction. -/
@[expose] def Interp.checkPorts (I : Interp Γ) {a b : List Color} (g : Γ a b) : Bool :=
  decide (((I.verts g).flatMap Vertex.ports).Perm (genVertex a b 0).ports)

private def boundaryPorts {E : Type*} (a : List Color) (f : Fin a.length → E) (d : Bool) :
    Multiset (WeightedPort E) :=
  ↑(List.ofFn (fun i => ⟨⟨f i, d⟩, (a.get i).weight⟩) : List (WeightedPort E))
private def createdPorts : {a b : List Color} → (D : Diagram Γ a b) → Bool →
    Multiset (WeightedPort D.Edge)
  | _, b, .gen _, d => boundaryPorts b Sum.inr d
  | _, _, .id _, _ => 0
  | _, _, .swap .., _ => 0
  | _, _, .comp D₁ D₂, d =>
    (createdPorts D₁ d).map (WeightedPort.map (compLeft D₁ D₂)) +
      (createdPorts D₂ d).map (WeightedPort.map (compRight D₁ D₂))
  | _, _, .tensor D₁ D₂, d =>
    (createdPorts D₁ d).map (WeightedPort.map (tensorLeft D₁ D₂)) +
      (createdPorts D₂ d).map (WeightedPort.map (tensorRight D₁ D₂))
private theorem boundaryPorts_map {E E' : Type*} (a : List Color) (f : Fin a.length → E)
    (g : E → E') (d : Bool) :
    (boundaryPorts a f d).map (WeightedPort.map g) = boundaryPorts a (g ∘ f) d := by
  simp only [boundaryPorts, Multiset.map_coe, List.map_ofFn]
  rfl

private theorem boundaryPorts_eq_sum {E : Type*} (a : List Color)
    (f : Fin a.length → E) (d : Bool) :
    boundaryPorts a f d = ∑ i, {⟨⟨f i, d⟩, (a.get i).weight⟩} := by
  unfold boundaryPorts
  refine (Multiset.sum_map_singleton _).symm.trans ?_
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn]; rfl

private theorem boundaryPorts_append {E : Type*} (a b : List Color)
    (f : Fin (a ++ b).length → E) (d : Bool) :
    boundaryPorts (a ++ b) f d =
      boundaryPorts a (fun i => f ((List.appendIndexEquiv a b) (.inl i))) d +
        boundaryPorts b (fun j => f ((List.appendIndexEquiv a b) (.inr j))) d := by
  unfold boundaryPorts
  rw [List.ofFn_appendIndexEquiv a b, Multiset.coe_add]
  congr 1
  congr 1 <;> apply congrArg List.ofFn <;> funext i
  · simp [List.appendIndexEquiv]
  · simp [List.appendIndexEquiv]
private def listedPorts {E : Type*} (vs : List (Vertex E)) : Multiset (WeightedPort E) :=
  ↑(vs.flatMap Vertex.ports)
private theorem listedPorts_map {E E' : Type*} (vs : List (Vertex E)) (f : E → E') :
    listedPorts (vs.map (Vertex.map f)) =
      (listedPorts vs).map (WeightedPort.map f) := by
  simp only [listedPorts, List.flatMap_map, Vertex.map, Multiset.map_coe, List.map_flatMap]
private theorem listedPorts_append {E : Type*} (vs ws : List (Vertex E)) :
    listedPorts (vs ++ ws) = listedPorts vs + listedPorts ws := by
  simp only [listedPorts, List.flatMap_append, Multiset.coe_add]
private theorem boundaryPorts_comp {a b c : List Color} (D₁ : Diagram Γ a b)
    (D₂ : Diagram Γ b c) (d : Bool) :
    (boundaryPorts b D₁.bottom d).map (WeightedPort.map (compLeft D₁ D₂)) =
      (boundaryPorts b Sum.inl d).map (WeightedPort.map (compRight D₁ D₂)) := by
  rw [boundaryPorts_map, boundaryPorts_map]
  rfl
private def PortBalance (I : Interp Γ) {a b : List Color} (D : Diagram Γ a b) : Prop :=
  listedPorts (D.vertexList I) + boundaryPorts b D.bottom true =
    boundaryPorts a Sum.inl true + createdPorts D false + createdPorts D true

private theorem portBalance_comp (I : Interp Γ) {a b c : List Color}
    (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (ih₁ : PortBalance I D₁) (ih₂ : PortBalance I D₂) : PortBalance I (D₁.comp D₂) := by
  unfold PortBalance at ih₁ ih₂ ⊢
  let f := WeightedPort.map (compLeft D₁ D₂)
  let g := WeightedPort.map (compRight D₁ D₂)
  have h₁ := congrArg (Multiset.map f) ih₁
  have h₂ := congrArg (Multiset.map g) ih₂
  simp only [Multiset.map_add] at h₁ h₂
  have hb : boundaryPorts _ (D₁.comp D₂).bottom true =
      (boundaryPorts _ D₂.bottom true).map g := by
    rw [boundaryPorts_map]
    exact congrArg (boundaryPorts _ · true) (funext (bottom_comp D₁ D₂))
  simp only [vertexList, listedPorts_append, listedPorts_map, createdPorts, hb]
  change (listedPorts (D₁.vertexList I)).map f + (listedPorts (D₂.vertexList I)).map g +
    (boundaryPorts _ D₂.bottom true).map g = _
  have hp : (boundaryPorts a Sum.inl true).map f = boundaryPorts a Sum.inl true :=
    boundaryPorts_map a Sum.inl _ true
  rw [add_assoc, h₂, (boundaryPorts_comp D₁ D₂ true).symm]
  calc _ = ((listedPorts (D₁.vertexList I)).map f + (boundaryPorts _ D₁.bottom true).map f) +
        (createdPorts D₂ false).map g + (createdPorts D₂ true).map g := by ac_rfl
    _ = _ := by rw [h₁, hp]; ac_rfl

private theorem portBalance_tensor (I : Interp Γ) {a b c d : List Color}
    (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (ih₁ : PortBalance I D₁) (ih₂ : PortBalance I D₂) : PortBalance I (D₁.tensor D₂) := by
  unfold PortBalance at ih₁ ih₂ ⊢
  let f := WeightedPort.map (tensorLeft D₁ D₂)
  let g := WeightedPort.map (tensorRight D₁ D₂)
  have h₁ := congrArg (Multiset.map f) ih₁
  have h₂ := congrArg (Multiset.map g) ih₂
  simp only [Multiset.map_add] at h₁ h₂
  have hb : boundaryPorts _ (D₁.tensor D₂).bottom true =
      (boundaryPorts _ D₁.bottom true).map f + (boundaryPorts _ D₂.bottom true).map g := by
    rw [boundaryPorts_append, boundaryPorts_map, boundaryPorts_map]
    simp only [Function.comp_def, bottom_tensor_left, bottom_tensor_right]
  have ht : boundaryPorts _ Sum.inl true =
      (boundaryPorts a Sum.inl true).map f + (boundaryPorts c Sum.inl true).map g := by
    rw [boundaryPorts_append, boundaryPorts_map, boundaryPorts_map]
    rfl
  simp only [vertexList, listedPorts_append, listedPorts_map, createdPorts, hb, ht]
  change (listedPorts (D₁.vertexList I)).map f + (listedPorts (D₂.vertexList I)).map g +
    ((boundaryPorts _ D₁.bottom true).map f + (boundaryPorts _ D₂.bottom true).map g) = _
  calc
    _ = ((listedPorts (D₁.vertexList I)).map f + (boundaryPorts _ D₁.bottom true).map f) +
        ((listedPorts (D₂.vertexList I)).map g + (boundaryPorts _ D₂.bottom true).map g) := by
      ac_rfl
    _ = _ := by rw [h₁, h₂]; ac_rfl

private theorem portBalance_of_checkGens (I : Interp Γ) {a b : List Color}
    (D : Diagram Γ a b) (h : D.checkGens I.checkPorts = true) : PortBalance I D := by
  induction D with
  | @gen a b g =>
    have hg : ((I.verts g).flatMap Vertex.ports).Perm (genVertex a b 0).ports :=
      of_decide_eq_true h
    unfold PortBalance
    change (↑((I.verts g).flatMap Vertex.ports) :
      Multiset (WeightedPort (Fin a.length ⊕ Fin b.length))) + _ = _
    rw [Multiset.coe_eq_coe.2 hg]
    simp only [genVertex, createdPorts, bottom, boundaryPorts,
      List.ofFn_eq_map, ← Multiset.coe_add]
    rfl
  | id a => simp [PortBalance, vertexList, listedPorts, createdPorts, boundaryPorts, bottom]
  | swap x y =>
    unfold PortBalance
    simp only [vertexList, listedPorts, List.flatMap_nil, Multiset.coe_nil, createdPorts,
      zero_add, add_zero, boundaryPorts, bottom, List.ofFn_succ, Fin.rev]
    simp only [List.get_eq_getElem, List.ofFn_zero, Multiset.coe_eq_coe]
    exact List.Perm.swap ..
  | comp D₁ D₂ ih₁ ih₂ =>
    simp only [checkGens, Bool.and_eq_true] at h
    exact portBalance_comp I D₁ D₂ (ih₁ h.1) (ih₂ h.2)
  | tensor D₁ D₂ ih₁ ih₂ =>
    simp only [checkGens, Bool.and_eq_true] at h
    exact portBalance_tensor I D₁ D₂ (ih₁ h.1) (ih₂ h.2)

/-- The color of a wire created below a generator. -/
@[expose] def innerColor : {a b : List Color} → (D : Diagram Γ a b) → D.Inner → Color
  | _, b, .gen _, e => b.get e
  | _, _, .id _, e => e.elim
  | _, _, .swap .., e => e.elim
  | _, _, .comp D₁ D₂, e => Sum.elim (innerColor D₁) (innerColor D₂) e
  | _, _, .tensor D₁ D₂, e => Sum.elim (innerColor D₁) (innerColor D₂) e

/-- The weight of a diagram wire, inherited from its colored creation point. -/
@[expose] def edgeWeight {a b : List Color} (D : Diagram Γ a b) : D.Edge → ℕ :=
  Sum.elim (fun i => (a.get i).weight) (fun e => (innerColor D e).weight)

/-- An incoming wire has its declared color weight. -/
@[simp] theorem edgeWeight_top {a b : List Color} (D : Diagram Γ a b) (i : Fin a.length) :
    D.edgeWeight (.inl i) = (a.get i).weight := rfl

private theorem createdPorts_eq_sum {a b : List Color} (D : Diagram Γ a b) (d : Bool) :
    createdPorts D d = ∑ e : D.Inner, {⟨⟨Sum.inr e, d⟩, (innerColor D e).weight⟩} := by
  induction D with
  | gen g => exact boundaryPorts_eq_sum _ _ _
  | id _ | swap _ _ =>
    change 0 = ∑ e : Empty, _
    simp
  | comp D₁ D₂ ih₁ ih₂ | tensor D₁ D₂ ih₁ ih₂ =>
    simp only [createdPorts, ih₁, ih₂]
    rw [← Multiset.coe_mapAddMonoidHom, ← Multiset.coe_mapAddMonoidHom, map_sum, map_sum]
    change _ = ∑ e : D₁.Inner ⊕ D₂.Inner,
      {(⟨⟨Sum.inr e, d⟩, (Sum.elim (innerColor D₁) (innerColor D₂) e).weight⟩ :
        WeightedPort (Fin _ ⊕ (D₁.Inner ⊕ D₂.Inner)))}
    simp only [Fintype.sum_sum_type, Multiset.coe_mapAddMonoidHom, WeightedPort.map, Port.map,
      compLeft, compRight, tensorLeft, tensorRight, Sum.map, Sum.elim_inl, Sum.elim_inr]
    rfl

/-- The interpreted graph and its vertex list have the same ports, including multiplicities. -/
theorem portMultiset_vertexList (I : Interp Γ) {a b : List Color}
    (D : Diagram Γ a b) :
    (D.graph I).portMultiset = ↑((D.vertexList I).flatMap Vertex.ports) := by
  change (D.graph I).portMultiset = listedPorts (D.vertexList I)
  induction D with
  | gen g => exact ConstraintGraph.portMultiset_get _
  | id _ | swap _ _ =>
    change (∑ v : Empty, _) = 0
    simp
  | comp D₁ D₂ ih₁ ih₂ =>
    change ConstraintGraph.portMultiset
      (Sum.elim ((D₁.graph I).map (compLeft D₁ D₂))
        ((D₂.graph I).map (compRight D₁ D₂))) = _
    rw [ConstraintGraph.portMultiset_sumElim_map, ih₁, ih₂]
    simp only [vertexList, listedPorts_append, listedPorts_map]
  | tensor D₁ D₂ ih₁ ih₂ =>
    change ConstraintGraph.portMultiset
      (Sum.elim ((D₁.graph I).map (tensorLeft D₁ D₂))
        ((D₂.graph I).map (tensorRight D₁ D₂))) = _
    rw [ConstraintGraph.portMultiset_sumElim_map, ih₁, ih₂]
    simp only [vertexList, listedPorts_append, listedPorts_map]

/-- A threshold generator has precisely the declared boundary ports. -/
theorem ports_genVertex (a b : List Color) (need : ℕ) :
    (↑(genVertex a b need).ports : Multiset (WeightedPort (Fin a.length ⊕ Fin b.length))) =
      (∑ i : Fin a.length, {⟨⟨Sum.inl i, true⟩, (a.get i).weight⟩}) +
      ∑ j : Fin b.length, {⟨⟨Sum.inr j, false⟩, (b.get j).weight⟩} := by
  rw [← boundaryPorts_eq_sum, ← boundaryPorts_eq_sum]
  simp only [genVertex, boundaryPorts, List.ofFn_eq_map, Multiset.coe_add]

/-- Closing every boundary wire by an opposite endpoint gives two consistent ports per wire. -/
theorem portMultiset_add_boundary (I : Interp Γ) {a b : List Color} (D : Diagram Γ a b)
    (h : D.checkGens I.checkPorts = true) :
    (D.graph I).portMultiset +
        (∑ i : Fin a.length, {⟨⟨Sum.inl i, false⟩, (a.get i).weight⟩}) +
        (∑ j : Fin b.length, {⟨⟨D.bottom j, true⟩, (b.get j).weight⟩}) =
      ∑ e : D.Edge, ({⟨⟨e, false⟩, D.edgeWeight e⟩} + {⟨⟨e, true⟩, D.edgeWeight e⟩}) := by
  have hp := portBalance_of_checkGens I D h
  rw [PortBalance, listedPorts, ← portMultiset_vertexList, boundaryPorts_eq_sum,
    boundaryPorts_eq_sum, createdPorts_eq_sum, createdPorts_eq_sum] at hp
  rw [add_right_comm, hp, add_comm _ (∑ i : Fin a.length, _)]
  simp only [Fintype.sum_sum_type, edgeWeight, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_add_distrib, add_assoc]
  exact congrArg (_ + ·) (add_left_comm _ _ _)

/-- A checked outgoing wire has its declared color weight. -/
theorem edgeWeight_bottom (I : Interp Γ) {a b : List Color} (D : Diagram Γ a b)
    (h : D.checkGens I.checkPorts = true) (j : Fin b.length) :
    D.edgeWeight (D.bottom j) = (b.get j).weight := by
  have hm : ⟨(⟨D.bottom j, true⟩ : Port D.Edge), (b.get j).weight⟩ ∈
      (∑ e : D.Edge, ({⟨⟨e, false⟩, D.edgeWeight e⟩} + {⟨⟨e, true⟩, D.edgeWeight e⟩}) :
        Multiset (WeightedPort D.Edge)) := by
    rw [← portMultiset_add_boundary I D h]
    exact Multiset.mem_add.2 (Or.inr (Multiset.mem_sum.2
      ⟨j, Finset.mem_univ j, Multiset.mem_singleton.2 rfl⟩))
  simp only [Multiset.mem_sum, Finset.mem_univ, true_and, Multiset.mem_add,
    Multiset.mem_singleton] at hm
  obtain ⟨e, he | he⟩ := hm
  · cases congrArg (fun q => q.port.dir) he
  · exact (congrArg D.edgeWeight (congrArg (fun q => q.port.edge) he)).trans
      (congrArg WeightedPort.weight he).symm

/-- Checking the local port tables suffices for consistent incidences in a closed diagram. -/
theorem wellFormed_of_checkGens (I : Interp Γ) (D : Diagram Γ [] [])
    (h : D.checkGens I.checkPorts = true) : (D.graph I).WellFormed := by
  have hp := portBalance_of_checkGens I D h
  simp only [PortBalance, boundaryPorts, List.ofFn_zero, Multiset.coe_nil, add_zero, zero_add]
    at hp
  refine ⟨Sum.elim Fin.elim0 (fun e => (innerColor D e).weight), ?_⟩
  rw [portMultiset_vertexList]
  change listedPorts (D.vertexList I) = ∑ e : Fin 0 ⊕ D.Inner, _
  rw [hp, createdPorts_eq_sum, createdPorts_eq_sum, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, Sum.elim_inr,
    Finset.sum_add_distrib]

end Cslib.Complexity.NCL.Diagram
