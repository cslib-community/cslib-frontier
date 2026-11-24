/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sort

/-!
# Running the optimal comparison program on an edge subset

Each invocation uses only the selected edges and their incident vertices. Compact local labels
determine the topology used for synthesis, while the resulting program queries the original
edge oracle and returns original edge labels.
-/

public section

namespace Cslib.Query.LEQuery

/-- Interpret each local comparison as a comparison between its two ambient labels. -/
@[expose] def relabel (f : A → B) (p : FreeM (LEQuery A) O) : FreeM (LEQuery B) O :=
  p.liftM fun | .le a b => FreeM.lift (.le (f a) (f b))

theorem relabel_spec {W : Type*} [LinearOrder W] (f : A → B) (p : FreeM (LEQuery A) O) (w : B → W) :
    (relabel f p).eval (keyOracle w) = p.eval (keyOracle (w ∘ f)) ∧
    (relabel f p).countQueries (keyOracle w) = p.countQueries (keyOracle (w ∘ f)) := by
  induction p with
  | pure => exact ⟨rfl,rfl⟩
  | lift_bind op cont ih =>
    cases op with
    | le a b =>
      obtain ⟨v,c⟩ := ih (decide (w (f a) ≤ w (f b)))
      exact ⟨v,congrArg (1 + ·) c⟩

end Cslib.Query.LEQuery

namespace Cslib.Multigraph

open Cslib.Query
open scoped Sym2

namespace OptimalTree

variable {E V : Type} [LinearOrder E] [LinearOrder V]

/-- The vertices incident to any edge of the selected subgraph, including ends of self-loops. -/
@[expose] def vertices (ends : E → Sym2 V) (S : Finset E) : Finset V :=
  S.biUnion fun e => (ends e).toFinset

omit [LinearOrder E] in
theorem card_vertices_le (ends : E → Sym2 V) (S : Finset E) :
    (vertices ends S).card ≤ S.card * 2 := by
  apply Finset.card_biUnion_le_card_mul
  intro e _
  rw [Sym2.card_toFinset]
  split <;> omega

/-- The compact topology of a selected edge set. Edge and vertex labels are both dense. -/
@[expose] def localEnds (ends : E → Sym2 V) (S : Finset E) :
    Fin S.card → Sym2 (Fin (vertices ends S).card) := fun i =>
  let e := (S.orderIsoOfFin rfl) i
  let z := (ends e).attachWith (P := fun v => v ∈ vertices ends S)
    (fun _ hv => Finset.mem_biUnion.mpr ⟨e,e.property,Sym2.mem_toFinset.mpr hv⟩)
  z.map ((vertices ends S).orderIsoOfFin rfl).symm

theorem map_localEnds (ends : E → Sym2 V) (S : Finset E) :
    Sym2.map ((vertices ends S).orderEmbOfFin rfl) ∘ localEnds ends S =
      ends ∘ (S.orderEmbOfFin rfl) := by
  funext i
  unfold localEnds
  simp only [Function.comp_apply, Sym2.map_map]
  have eq : (fun x => ((vertices ends S).orderEmbOfFin rfl) (((vertices ends S).orderIsoOfFin rfl).symm x)) =
      (Subtype.val : (vertices ends S) → V) := by
    funext v
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  rw [eq]
  exact Sym2.attachWith_map_subtypeVal _

omit [LinearOrder E] [LinearOrder V] in
/-- Restricting the edge labels to the image of an embedding commutes with the MSF. -/
theorem map_msf_edges {A : Type} {W : Type*} [LinearOrder W] [DecidableEq E] (j : A ↪ E)
    (ends : E → Sym2 V) (w : E → W) (T : Finset A) :
    (msf (ends ∘ j) (w ∘ j) T).map j = msf ends w (T.map j) := by
  classical
  ext e
  by_cases he : e ∈ T.map j
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp he
    have ex : ∃ a b, ends (j i) = s(a,b) := by
      induction ends (j i) using Sym2.ind with | _ a b => exact ⟨a,b,rfl⟩
    obtain ⟨a,b,hab⟩ := ex
    have connected :
        Joins (ends ∘ j) {f | f ∈ T ∧ (w ∘ j) f < (w ∘ j) i} a b ↔
        Joins ends {f | f ∈ T.map j ∧ w f < w (j i)} a b := by
      constructor
      · exact Joins.lift id fun f hf x y hxy => Joins.of_mem
          (e := j f) ⟨Finset.mem_map.mpr ⟨f,hf.1,rfl⟩,hf.2⟩ hxy
      · apply Joins.lift id
        rintro f ⟨hf,lighter⟩ x y hxy
        obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hf
        exact Joins.of_mem (e := k) ⟨hk,lighter⟩ hxy
    rw [Finset.mem_map', mem_msf_iff (w ∘ j) (show (ends ∘ j) i = _ from hab),
      mem_msf_iff w hab, connected]
    simp [hi]
  · have no : e ∉ (msf (ends ∘ j) (w ∘ j) T).map j := by
      intro h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp h
      exact he (Finset.mem_map.mpr ⟨i, msf_subset _ hi, rfl⟩)
    exact iff_of_false no (fun h => he (msf_subset _ h))

theorem map_msf_localEnds {W : Type*} [LinearOrder W] (ends : E → Sym2 V) (S : Finset E)
    (w : E → W) (hw : Set.InjOn w S) :
    (msf (localEnds ends S) (w ∘ S.orderEmbOfFin rfl) Finset.univ).map
      (S.orderEmbOfFin rfl).toEmbedding = msf ends w S := by
  let v := (vertices ends S).orderEmbOfFin rfl
  let e := S.orderEmbOfFin rfl
  have hwi : Function.Injective (w ∘ e) := by
    intro a b h
    exact e.injective (hw (S.orderEmbOfFin_mem rfl a) (S.orderEmbOfFin_mem rfl b) h)
  have remap := msf_eq_union_msf_map (ends := localEnds ends S) (w ∘ e) (S := Finset.univ)
    (C := ∅) (q := v) hwi (Finset.empty_subset _) (by simp)
  simp only [Finset.sdiff_empty, Finset.empty_union] at remap
  rw [show Sym2.map v ∘ localEnds ends S = ends ∘ e from map_localEnds ends S] at remap
  rw [remap]
  exact (map_msf_edges e.toEmbedding ends w Finset.univ).trans
    (congrArg (msf ends w) (Finset.map_orderEmbOfFin_univ S rfl))

end OptimalTree

variable {E V : Type} [LinearOrder E] [LinearOrder V]

/-- Solve the MSF on the given edge subset with an optimal program on its compact topology. -/
@[expose] def optimalMSFOn (ends : E → Sym2 V) (S : Finset E) :
    FreeM (LEQuery E) (Finset E) :=
  let e := S.orderEmbOfFin rfl
  (Finset.map e.toEmbedding) <$> LEQuery.relabel e (optimalMSFProgram (OptimalTree.localEnds ends S))

/-- This invocation uses at most the fixed-topology optimum for the selected subgraph. Only
weights of selected edges have to be distinct. -/
theorem optimalMSFOn_spec {W : Type*} [LinearOrder W] (ends : E → Sym2 V) (S : Finset E)
    (w : E → W) (hw : Set.InjOn w S) :
    (optimalMSFOn ends S).eval (LEQuery.keyOracle w) = msf ends w S ∧
      (optimalMSFOn ends S).countQueries (LEQuery.keyOracle w) ≤
        optimalMSFComparisons (OptimalTree.localEnds ends S) := by
  let e := S.orderEmbOfFin rfl
  have hwi : Function.Injective (w ∘ e) := by
    intro a b h
    exact e.injective (hw (S.orderEmbOfFin_mem rfl a) (S.orderEmbOfFin_mem rfl b) h)
  obtain ⟨v,c⟩ := optimalMSFProgram_spec (OptimalTree.localEnds ends S) (w ∘ e) hwi
  obtain ⟨vr,cr⟩ := LEQuery.relabel_spec e (optimalMSFProgram (OptimalTree.localEnds ends S)) w
  simp only [optimalMSFOn, FreeM.eval_map, FreeM.countQueries_map]
  exact ⟨(congrArg (Finset.map e.toEmbedding) (vr.trans v)).trans
    (OptimalTree.map_msf_localEnds ends S w hw), cr.le.trans c⟩

end Cslib.Multigraph
