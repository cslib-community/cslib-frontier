/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Basic
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.Order.Group.Multiset

/-!
# Consistent edge incidences

A well-formed finite constraint graph lists each edge exactly twice: once at each direction,
with the same weight. The multiset of weighted ports records multiplicity, including repeated
ports in a single vertex.

## Main definitions

* `Cslib.Complexity.NCL.ConstraintGraph.portMultiset`: all weighted ports of a finite graph.
* `Cslib.Complexity.NCL.ConstraintGraph.WellFormed`: one port per direction with equal weights.

## Main results

* `Cslib.Complexity.NCL.ConstraintGraph.wellFormed_iff_filter` checks incidences one edge at a time.

## References

* Constraint graphs are defined in [Hearn and Demaine][HearnDemaine2005, Section 2.1].
-/

public section

namespace Cslib.Complexity.NCL

variable {V E E' : Type*}

namespace ConstraintGraph

/-- All weighted ports, counted with their multiplicities. -/
@[expose] def portMultiset [Fintype V] (G : ConstraintGraph V E) : Multiset (WeightedPort E) :=
  ∑ v, (↑(G v).ports : Multiset (WeightedPort E))

/-- Every edge has exactly one endpoint of each direction, both carrying the same weight. -/
@[expose] def WellFormed [Fintype V] [Fintype E] (G : ConstraintGraph V E) : Prop :=
  ∃ weight : E → ℕ, G.portMultiset =
    ∑ e, ({⟨⟨e, false⟩, weight e⟩} + {⟨⟨e, true⟩, weight e⟩})

/-- Collecting ports commutes with edge renaming. -/
theorem portMultiset_map [Fintype V] (G : ConstraintGraph V E) (f : E → E') :
    (G.map f).portMultiset = Multiset.map (WeightedPort.map f) G.portMultiset := by
  rw [← Multiset.coe_mapAddMonoidHom, portMultiset, portMultiset, map_sum]
  rfl

/-- A vertex list interpreted on its positions has the same multiset of ports. -/
theorem portMultiset_get (vs : List (Vertex E)) :
    portMultiset (fun i : Fin vs.length => vs.get i) = ↑(vs.flatMap Vertex.ports) := by
  induction vs with
  | nil => simp [portMultiset]
  | cons v vs ih =>
    simp only [portMultiset, List.length_cons, Fin.sum_univ_succ, List.get_eq_getElem,
      List.flatMap_cons, ← Multiset.coe_add]
    congr 1

/-- Ports of two graphs embedded in a common edge type add with multiplicity. -/
theorem portMultiset_sumElim_map {V₁ V₂ E₁ E₂ : Type*} [Fintype V₁] [Fintype V₂]
    (G₁ : ConstraintGraph V₁ E₁) (G₂ : ConstraintGraph V₂ E₂) (f₁ : E₁ → E) (f₂ : E₂ → E) :
    portMultiset (Sum.elim (G₁.map f₁) (G₂.map f₂)) =
      Multiset.map (WeightedPort.map f₁) G₁.portMultiset +
        Multiset.map (WeightedPort.map f₂) G₂.portMultiset := by
  rw [portMultiset, Fintype.sum_sum_type]
  exact congrArg₂ (· + ·) (portMultiset_map G₁ f₁) (portMultiset_map G₂ f₂)

/-- Bijective edge renaming preserves consistent incidences. -/
theorem WellFormed.map [Fintype V] [Fintype E] [Fintype E']
    {G : ConstraintGraph V E} (h : G.WellFormed) (f : E ≃ E') : (G.map f).WellFormed := by
  obtain ⟨weight, hw⟩ := h
  refine ⟨weight ∘ f.symm, ?_⟩
  rw [portMultiset_map, hw, ← Multiset.coe_mapAddMonoidHom, map_sum]
  exact Fintype.sum_equiv f _ _ fun _ => by simp [WeightedPort.map, Port.map]

/-- Reindexing vertices bijectively preserves every endpoint occurrence. -/
theorem WellFormed.reindex {V' : Type*} [Fintype V] [Fintype V'] [Fintype E]
    {G : ConstraintGraph V E} (h : G.WellFormed) (f : V' ≃ V) :
    WellFormed (G ∘ f) := by
  obtain ⟨weight, hw⟩ := h
  refine ⟨weight, ?_⟩
  calc
    _ = G.portMultiset := Fintype.sum_equiv f _ _ (fun _ => rfl)
    _ = _ := hw

private theorem sum_filter_edge [Fintype E] [DecidableEq E] (ps : Multiset (WeightedPort E)) :
    (∑ e, ps.filter (fun p => p.port.edge = e)) = ps := by
  induction ps using Multiset.induction_on with
  | empty => simp
  | @cons p ps ih =>
    rw [← Multiset.singleton_add]
    simp only [Multiset.filter_add, Multiset.filter_singleton, Finset.sum_add_distrib, ih]
    simp

/-- Consistent incidences can be checked independently at each edge. -/
theorem wellFormed_iff_filter [Fintype V] [Fintype E] [DecidableEq E]
    (G : ConstraintGraph V E) : G.WellFormed ↔
      ∀ e, ∃ w, G.portMultiset.filter (fun p => p.port.edge = e) =
        {⟨⟨e, false⟩, w⟩} + {⟨⟨e, true⟩, w⟩} := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨weight, hw⟩ e
    refine ⟨weight e, ?_⟩
    let F : Multiset (WeightedPort E) →+ Multiset (WeightedPort E) :=
      { toFun := Multiset.filter (fun p => p.port.edge = e)
        map_zero' := Multiset.filter_zero _
        map_add' := Multiset.filter_add _ }
    have hh := (congrArg F hw).trans (map_sum F _ _)
    simp only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Multiset.filter_add,
      Multiset.filter_singleton, Finset.sum_add_distrib] at hh
    simpa using hh
  · choose weight hw using h
    refine ⟨weight, ?_⟩
    calc
      _ = ∑ e, G.portMultiset.filter (fun p => p.port.edge = e) := (sum_filter_edge _).symm
      _ = _ := Finset.sum_congr rfl (fun e _ => hw e)

/-- A well-formed graph has two ports per edge, counted with multiplicity. -/
theorem WellFormed.card_portMultiset [Fintype V] [Fintype E]
    {G : ConstraintGraph V E} (h : G.WellFormed) :
    G.portMultiset.card = 2 * Fintype.card E := by
  obtain ⟨_, hw⟩ := h
  simp [hw, Nat.mul_comm]

end ConstraintGraph

end Cslib.Complexity.NCL
