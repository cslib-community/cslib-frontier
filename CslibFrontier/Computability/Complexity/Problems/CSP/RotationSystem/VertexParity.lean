/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.VertexFibers
public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Enumeration
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexParityWords
import CslibFrontier.Computability.Complexity.Problems.CSP.IncidenceEnumeration
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Incidence parity in positional CSP coordinates

Filtering the existing typed occurrence scan gives exactly a variable or constraint endpoint
fiber. Its edge-bit sum is the original graph incidence parity, retaining all repeated positions.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- Any exact duplicate-free word of occurrence indices at a variable computes its graph
incidence parity. The edge bits are read by bounded finite-list lookup at those actual indices. -/
theorem vertexParity_eq_sum_incidenceWord
    (x : Fin (incidenceGraph F).edges.length → Bool) (o : F.Occurrence)
    (word : List ℕ) (hn : word.Nodup)
    (hw : ∀ i, i ∈ word ↔ ∃ p : F.Occurrence, incidenceEdgeIndex p = i ∧ p.var = o.var) :
    (incidenceGraph F).vertexParity x (incidenceDart o false).vertex =
      (word.map fun i => (List.ofFn x).getD i false).sum := by
  classical
  rw [Graph.vertexParity, ← Finset.sum_filter, ← List.sum_toFinset _ hn]
  have hside (d : Dart (incidenceGraph F))
      (hd : d.vertex = (incidenceDart o false).vertex) : d.2 = false := by
    obtain ⟨p, hp⟩ := exists_incidenceDart d
    exact ((vertex_incidenceDart_eq_iff p o d.2 false).mp (hp ▸ hd)).1
  refine Finset.sum_bij (fun d _ => d.1.val) (fun d hd => ?_)
    (fun d hd e he hde => Prod.ext (Fin.ext hde)
      ((hside d (Finset.mem_filter.mp hd).2).trans (hside e (Finset.mem_filter.mp he).2).symm))
    (fun i hi => ?_) fun d _ => (List.getD_ofFn x d.1 false).symm
  · obtain ⟨p, hp⟩ := exists_incidenceDart d
    have hv := (vertex_incidenceDart_eq_iff p o d.2 false).mp (hp ▸ (Finset.mem_filter.mp hd).2)
    exact List.mem_toFinset.mpr ((hw _).mpr ⟨p, congrArg (·.1.val) hp,
      by simpa only [hv.1, Bool.false_eq_true, ite_false] using hv.2⟩)
  · obtain ⟨p, hp, hv⟩ := (hw i).mp (List.mem_toFinset.mp hi)
    exact ⟨incidenceDart p false, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (vertex_incidenceDart_eq_iff p o false false).mpr ⟨rfl, hv⟩⟩, hp⟩

/-- Every exact variable-fiber word of a vertex-even labeling has zero sum. Empty
fibers are included, without requiring that their label occurs in the body. -/
theorem sum_eq_false_of_vertexEven_word
    (x : Fin (incidenceGraph F).edges.length → Bool) (hx : (incidenceGraph F).VertexEven x)
    (word : List ℕ) (hn : word.Nodup) (label fallback : V)
    (hf : ∀ i, i ∈ word ↔ i < F.vars.length ∧ F.vars.getD i fallback = label) :
    (word.map fun i => (List.ofFn x).getD i false).sum = false := by
  by_cases he : word = []
  · simp [he, Bool.zero_eq_false]
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil word he
  have hlen : (incidenceGraph F).edges.length = F.vars.length := by
    simp only [incidenceGraph_edges, List.length_map, ← CSP.map_occurrences]
  obtain ⟨o, ho⟩ := exists_incidenceEdgeIndex (F := F) i (hlen ▸ ((hf i).mp hi).1)
  have hvar : o.var = label :=
    (getD_vars_incidenceEdgeIndex o fallback).symm.trans (ho ▸ ((hf i).mp hi).2)
  have hw (j : ℕ) : j ∈ word ↔ ∃ p : F.Occurrence,
      incidenceEdgeIndex p = j ∧ p.var = o.var := by
    rw [hf]
    refine ⟨fun ⟨hj, hread⟩ => ?_, fun ⟨p, hpeq, hp⟩ => ⟨hpeq ▸ incidenceEdgeIndex_lt_vars p,
      (hpeq ▸ getD_vars_incidenceEdgeIndex p fallback).trans (hp.trans hvar)⟩⟩
    obtain ⟨p, hp⟩ := exists_incidenceEdgeIndex (F := F) j (hlen ▸ hj)
    exact ⟨p, hp, by rw [← getD_vars_incidenceEdgeIndex p fallback, hp, hread, hvar]⟩
  rw [← vertexParity_eq_sum_incidenceWord x o word hn hw]
  exact hx _


/-- The actual graph parity at an occurrence endpoint is the sum over its complete positional
fiber. The two endpoint sides use original variable equality and constraint-index equality. -/
theorem vertexParity_incidenceDart (x : Fin (incidenceGraph F).edges.length → Bool)
    (o : F.Occurrence) (side : Bool) :
    (incidenceGraph F).vertexParity x (incidenceDart o side).vertex =
      (((CSP.incidenceList F).filter fun p =>
        decide (if side then p.1 = o.1 else p.var = o.var)).map
          fun p => x (incidenceDart p side).1).sum := by
  let selected := (CSP.incidenceList F).filter fun p =>
    decide (if side then p.1 = o.1 else p.var = o.var)
  have hn : (selected.map fun p => incidenceDart p side).Nodup :=
    ((CSP.incidenceList_nodup F).filter _).map (incidenceDart_injective side)
  have hw (d : Dart (incidenceGraph F)) :
      d ∈ selected.map (fun p => incidenceDart p side) ↔
        d.vertex = (incidenceDart o side).vertex := by
    obtain ⟨p, hp⟩ := exists_incidenceDart d
    refine ⟨fun hd => ?_, fun hd => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
      exact (vertex_incidenceDart_eq_iff q o side side).mpr
        ⟨rfl, of_decide_eq_true (List.mem_filter.mp hq).2⟩
    · have hv := (vertex_incidenceDart_eq_iff p o d.2 side).mp (hp ▸ hd)
      exact List.mem_map.mpr ⟨p,
        List.mem_filter.mpr ⟨CSP.mem_incidenceList p, decide_eq_true (hv.1 ▸ hv.2)⟩, hv.1 ▸ hp⟩
  rw [(incidenceGraph F).vertexParity_eq_sum_word x _ _ hn hw, List.map_map]; rfl

end Cslib.Complexity.CSP
