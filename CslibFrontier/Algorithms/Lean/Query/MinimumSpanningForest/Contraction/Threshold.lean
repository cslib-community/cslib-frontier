/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Kruskal.Basic
public import CslibFrontier.Foundations.Combinatorics.Multigraph.MinimumSpanningForest
public import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Count

/-!
# Threshold-Rank MSF Characterization and Contraction Preservation

Threshold-rank and contraction infrastructure toward Theorem 5.8 of [PettieRamachandran2002]
(#8624). Bridges `Cslib.Algorithms.Lean.Kruskal` (`WeightedEdge n ℕ`, `edgePartition`,
`IsMinSpanningForest`) with `Cslib.Multigraph` (`Joins`, `msf`, `isAcyclic_msf`,
`isSpanningForest_msf`, `joins_msf_lt_iff`), proves the threshold-rank characterization of
`IsMinSpanningForest` over `ℕ` weights (handling arbitrary duplicate edge weights), defines
`WeaklySupported` (the `WeightedEdge`-list / `edgePartition` counterpart of
`Cslib.Multigraph.Supported` from [KhannaPuttermanSong2026], Sections 1.2 and 3.1, generalized to
allow equal-weight substitutions), and proves weak-support filtering and contraction preservation
(`exists_extend_isMinSpanningForest_of_cutStep`, `isMinSpanningForest_append_of_contract`).

## Main definitions

* `Cslib.Query.MinimumSpanningForest.edgeEnds`: view `es : List (WeightedEdge n ℕ)` as a
  multigraph `Fin es.length → Sym2 (Fin n)`.
* `Cslib.Query.MinimumSpanningForest.edgeWeight`: injective lexicographic edge weights in `ℕ ×ₗ ℕ`.
* `Cslib.Query.MinimumSpanningForest.msfEdges`: edge list extracted from `Cslib.Multigraph.msf`.
* `Cslib.Query.MinimumSpanningForest.WeaklySupported`: `WeightedEdge`-list counterpart of
  `Cslib.Multigraph.Supported` ([KhannaPuttermanSong2026], Sections 1.2 and 3.1) allowing
  equal-weight substitutions.
* `Cslib.Query.MinimumSpanningForest.contractEdge`,
  `Cslib.Query.MinimumSpanningForest.contractEdgeList`: graph contraction along `Fin n → Fin n'`.

## Main results

* `Cslib.Query.MinimumSpanningForest.isMinSpanningForest_iff_threshold_partition`: threshold-rank
  characterization of `Kruskal.IsMinSpanningForest`.
* `Cslib.Query.MinimumSpanningForest.isMinSpanningForest_of_weakSupport`: `WeaklySupported`
  preservation for `Kruskal.IsMinSpanningForest`.
* `Cslib.Query.MinimumSpanningForest.exists_extend_isMinSpanningForest_of_cutStep`,
  `Cslib.Query.MinimumSpanningForest.isMinSpanningForest_append_of_contract`: contraction
  correctness for cut steps and contraction rounds.
-/

public section

namespace Cslib.Query.MinimumSpanningForest

open Cslib.DataStructure DisjointSet
open Cslib.Algorithms.Lean.Kruskal

/-! ## Multigraph Bridge via `Cslib.Multigraph` and Lexicographic Weights -/

/-- Edge endpoint map of a `WeightedEdge n ℕ` list as a multigraph
`Fin es.length → Sym2 (Fin n)`. -/
@[expose] def edgeEnds {n : ℕ} (es : List (WeightedEdge n ℕ)) :
    Fin es.length → Sym2 (Fin n) :=
  fun i => s(es[i.val].u, es[i.val].v)

/-- Injective lexicographic weight `(weight, index)` breaking ties by list position. -/
@[expose] def edgeWeight {n : ℕ} (es : List (WeightedEdge n ℕ)) (i : Fin es.length) :
    ℕ ×ₗ ℕ :=
  toLex (es[i.val].weight, i.val)

theorem edgeWeight_injective {n : ℕ} (es : List (WeightedEdge n ℕ)) :
    Function.Injective (edgeWeight es) := fun _ _ h =>
  Fin.ext (congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) h)

private def edgeWeightPrefer {n : ℕ} (es : List (WeightedEdge n ℕ))
    (i₀ i : Fin es.length) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (es[i.val].weight, toLex (if i = i₀ then 0 else 1, i.val))

private theorem edgeWeightPrefer_injective {n : ℕ} (es : List (WeightedEdge n ℕ))
    (i₀ : Fin es.length) : Function.Injective (edgeWeightPrefer es i₀) := fun _ _ h =>
  Fin.ext (congrArg (fun p : ℕ ×ₗ (ℕ ×ₗ ℕ) => (ofLex (ofLex p).2).2) h)

private theorem edgeWeightPrefer_lt_self_iff {n : ℕ} (es : List (WeightedEdge n ℕ))
    (i₀ f : Fin es.length) :
    edgeWeightPrefer es i₀ f < edgeWeightPrefer es i₀ i₀ ↔
      es[f.val].weight < es[i₀.val].weight := by
  dsimp only [edgeWeightPrefer]
  rw [Prod.Lex.lt_iff, Prod.Lex.lt_iff]
  simp only [ofLex_toLex, ↓reduceIte]
  constructor
  · rintro (h | ⟨_, h | ⟨h1, h2⟩⟩)
    · exact h
    · split_ifs at h <;> omega
    · by_cases hf : f = i₀
      · subst hf; exact absurd h2 (Nat.lt_irrefl _)
      · simp [hf] at h1
  · exact .inl

theorem rel_edgePartition_map_iff_joins {n : ℕ} (es : List (WeightedEdge n ℕ))
    (S : Finset (Fin es.length)) (u v : Fin n) :
    (edgePartition (S.toList.map fun i => es[i.val])).rel u v = true ↔
      Cslib.Multigraph.Joins (edgeEnds es) (S : Set (Fin es.length)) u v := by
  rw [rel_edgePartition_iff_eqvGen]
  constructor
  · intro h
    induction h with
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    | rel x y hxy =>
      obtain ⟨e, he, rfl, rfl⟩ := hxy
      rw [List.mem_map] at he
      obtain ⟨i, hi, rfl⟩ := he
      exact Cslib.Multigraph.Joins.of_mem (Finset.mem_toList.mp hi) rfl
  · intro h
    induction h with
    | refl => exact .refl _
    | @tail b c _ hstep ih =>
      obtain ⟨i, hiS, hbc⟩ := hstep
      have him : es[i.val] ∈ S.toList.map fun k => es[k.val] :=
        List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hiS, rfl⟩
      rcases Sym2.eq_iff.mp hbc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ih.trans _ _ _ (.rel _ _ ⟨es[i.val], him, h1.symm, h2.symm⟩)
      · exact ih.trans _ _ _ (.symm _ _ (.rel _ _ ⟨es[i.val], him, h1.symm, h2.symm⟩))

/-- MSF edge list extracted from `Cslib.Multigraph.msf` under weight function `w`. -/
noncomputable def msfEdges {n : ℕ} {W : Type} [LinearOrder W]
    (es : List (WeightedEdge n ℕ)) (w : Fin es.length → W) : List (WeightedEdge n ℕ) :=
  (Cslib.Multigraph.msf (edgeEnds es) w Finset.univ).toList.map fun i => es[i.val]

theorem msfEdges_subperm {n : ℕ} {W : Type} [LinearOrder W]
    (es : List (WeightedEdge n ℕ)) (w : Fin es.length → W) :
    (msfEdges es w).Subperm es := by
  have hsub : (Cslib.Multigraph.msf (edgeEnds es) w Finset.univ).toList.Subperm
      (List.finRange es.length) :=
    List.subperm_of_subset (Finset.nodup_toList _) fun i _ => List.mem_finRange i
  obtain ⟨s, hp, hs⟩ := List.subperm_iff.mp hsub
  have hm := List.subperm_iff.mpr ⟨s.map fun i => es[i.val], hp.map _, hs.map _⟩
  rwa [List.map_getElem_finRange] at hm

private theorem kruskalIsAcyclic_of_multigraph {n : ℕ} (es : List (WeightedEdge n ℕ))
    (M : Finset (Fin es.length))
    (hM : Cslib.Multigraph.IsAcyclic (edgeEnds es) (M : Set (Fin es.length))) :
    IsAcyclic (M.toList.map fun i => es[i.val]) := by
  classical
  induction M using Finset.induction with
  | empty =>
    rw [isAcyclic_iff]
    simp [edgePartition, Partition.numComponents_discrete]
  | @insert i M hi ih =>
    have hM' : Cslib.Multigraph.IsAcyclic (edgeEnds es) (M : Set (Fin es.length)) :=
      hM.mono fun _ hx => Finset.mem_insert_of_mem hx
    have ih_ac := (isAcyclic_iff _).mp (ih hM')
    have hperm : ((insert i M).toList.map fun k => es[k.val]).Perm
        ((M.toList.map fun k => es[k.val]) ++ [es[i.val]]) := by
      have h1 := (Finset.toList_insert hi).map fun k => es[k.val]
      rw [List.map_cons] at h1
      exact h1.trans (List.perm_append_comm (l₁ := [es[i.val]]))
    have hnot : ¬ Cslib.Multigraph.Joins (edgeEnds es) (M : Set (Fin es.length))
        es[i.val].u es[i.val].v := by
      have hset : ((insert i M : Finset (Fin es.length)) : Set (Fin es.length)) \ {i} = M := by
        simp [Finset.coe_insert, Set.insert_sdiff_self_of_notMem hi]
      rw [← hset]
      exact (Cslib.Multigraph.isAcyclic_iff.mp hM) i (Finset.mem_insert_self i M)
        es[i.val].u es[i.val].v rfl
    have hrel_false : (edgePartition (M.toList.map fun k => es[k.val])).rel
        es[i.val].u es[i.val].v = false := by
      rw [Bool.eq_false_iff]
      intro hrel
      exact hnot ((rel_edgePartition_map_iff_joins es M es[i.val].u es[i.val].v).mp hrel)
    rw [Perm.isAcyclic_iff hperm, isAcyclic_iff, edgePartition, edgePartitionFrom_append,
      edgePartitionFrom_cons, edgePartitionFrom_nil]
    have hdrop := Partition.numComponents_merge_of_not_rel hrel_false
    change ((edgePartition (M.toList.map fun k => es[k.val])).merge
      es[i.val].u es[i.val].v).numComponents +
      ((M.toList.map fun k => es[k.val]) ++ [es[i.val]]).length = n
    simp only [List.length_append, List.length_map, List.length_singleton] at ih_ac ⊢
    omega

theorem msfEdges_isAcyclic {n : ℕ} {W : Type} [LinearOrder W]
    (es : List (WeightedEdge n ℕ)) (w : Fin es.length → W) (hw : Function.Injective w) :
    IsAcyclic (msfEdges es w) :=
  kruskalIsAcyclic_of_multigraph es _ (Cslib.Multigraph.isAcyclic_msf w hw)

theorem msfEdges_isSpanningForest {n : ℕ} {W : Type} [LinearOrder W]
    (es : List (WeightedEdge n ℕ)) (w : Fin es.length → W) (hw : Function.Injective w) :
    IsSpanningForest es (msfEdges es w) := by
  have hsf := Cslib.Multigraph.isSpanningForest_msf (ends := edgeEnds es) w (S := Finset.univ) hw
  refine ⟨msfEdges_subperm es w, kruskalIsAcyclic_of_multigraph es _ hsf.isAcyclic, ?_⟩
  have heq_es : ((Finset.univ : Finset (Fin es.length)).toList.map fun i => es[i.val]).Perm es := by
    have hm := (List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList Finset.univ)
      (List.nodup_finRange _) (Finset.ext fun _ => by simp)).map fun i : Fin es.length => es[i.val]
    rwa [List.map_getElem_finRange] at hm
  ext u v
  rw [Bool.eq_iff_iff, ← Perm.edgePartition_eq heq_es, rel_edgePartition_map_iff_joins,
    msfEdges, rel_edgePartition_map_iff_joins]
  exact ⟨fun h => h.mono (by simp), fun h => h.of_forall fun e _ a b hab =>
    (hsf.joins e (Finset.mem_univ e) a b hab).mono (by simp)⟩

theorem msfEdges_threshold_partition {n : ℕ} {W : Type} [LinearOrder W]
    (es : List (WeightedEdge n ℕ)) (w : Fin es.length → W)
    (hcut : ∀ t : ℕ, ∃ k : W, ∀ i : Fin es.length, w i < k ↔ es[i.val].weight ≤ t) (t : ℕ) :
    edgePartition ((msfEdges es w).filter fun e => decide (e.weight ≤ t)) =
      edgePartition (es.filter fun e => decide (e.weight ≤ t)) := by
  classical
  obtain ⟨k, hk⟩ := hcut t
  let M := Cslib.Multigraph.msf (edgeEnds es) w Finset.univ
  have hl_perm : ((msfEdges es w).filter fun e => decide (e.weight ≤ t)).Perm
      ((M.filter fun i => decide (es[i.val].weight ≤ t)).toList.map fun i => es[i.val]) := by
    rw [msfEdges, List.filter_map]
    exact (List.perm_of_nodup_nodup_toFinset_eq ((Finset.nodup_toList _).filter _)
      (Finset.nodup_toList _) (Finset.ext fun _ => by simp [M])).map _
  have hr_perm : (es.filter fun e => decide (e.weight ≤ t)).Perm
      (((Finset.univ : Finset (Fin es.length)).filter fun i =>
        decide (es[i.val].weight ≤ t)).toList.map fun i => es[i.val]) := by
    conv_lhs => rw [← List.map_getElem_finRange es, List.filter_map]
    exact (List.perm_of_nodup_nodup_toFinset_eq ((List.nodup_finRange _).filter _)
      (Finset.nodup_toList _) (Finset.ext fun _ => by simp)).map _
  ext u v
  rw [Bool.eq_iff_iff, Perm.edgePartition_eq hl_perm, Perm.edgePartition_eq hr_perm,
    rel_edgePartition_map_iff_joins, rel_edgePartition_map_iff_joins]
  have h1 : (((M.filter fun i => decide (es[i.val].weight ≤ t)) : Finset (Fin es.length)) :
      Set (Fin es.length)) = {f | f ∈ M ∧ w f < k} := Set.ext fun _ => by simp [M, hk]
  have h2 : (((Finset.univ.filter fun i : Fin es.length =>
      decide (es[i.val].weight ≤ t)) : Finset (Fin es.length)) : Set (Fin es.length)) =
      {f | f ∈ (Finset.univ : Finset (Fin es.length)) ∧ w f < k} := Set.ext fun _ => by simp [hk]
  rw [h1, h2]
  exact Cslib.Multigraph.joins_msf_lt_iff w

/-! ## Threshold-Rank Characterization and Weak Support -/

/-- Edge `e` is weakly supported by `G_b` if `e.u` and `e.v` are connected in `G_b` using only
edges of weight at most `e.weight`. This is the `WeightedEdge`-list / `edgePartition`
counterpart of `Cslib.Multigraph.Supported` ([KhannaPuttermanSong2026], Sections 1.2 and 3.1)
generalized to permit equal-weight substitutions (`f.weight ≤ e.weight`). -/
@[expose] def WeaklySupported {n : ℕ} (G_b : List (WeightedEdge n ℕ))
    (e : WeightedEdge n ℕ) : Prop :=
  (edgePartition (G_b.filter fun f => decide (f.weight ≤ e.weight))).rel e.u e.v = true

private theorem numComponents_edgePartitionFrom_le {n : ℕ} (p : Partition n)
    (es : List (WeightedEdge n ℕ)) :
    (edgePartitionFrom p es).numComponents ≤ p.numComponents := by
  induction es generalizing p with
  | nil => exact le_rfl
  | cons e es ih =>
    rw [edgePartitionFrom_cons]
    have h1 := ih (p.merge e.u e.v)
    cases hrel : p.rel e.u e.v
    · have := Partition.numComponents_merge_of_not_rel hrel; omega
    · have := Partition.numComponents_merge_of_rel hrel; omega

private theorem edgePartitionFrom_eq_self_of_forall {n : ℕ}
    (F₁ F₂ : List (WeightedEdge n ℕ))
    (hconn : ∀ e ∈ F₂, (edgePartition F₁).rel e.u e.v = true) :
    edgePartitionFrom (edgePartition F₁) F₂ = edgePartition F₁ := by
  induction F₂ with
  | nil => rfl
  | cons e rest ih =>
    rw [edgePartitionFrom_cons, Partition.merge_of_rel (hconn e List.mem_cons_self)]
    exact ih fun f hf => hconn f (List.mem_cons_of_mem _ hf)

theorem edgePartition_mono_subperm {n : ℕ} {F G : List (WeightedEdge n ℕ)} (hsub : F.Subperm G)
    {u v : Fin n} (hrel : (edgePartition F).rel u v = true) :
    (edgePartition G).rel u v = true := by
  rw [rel_edgePartition_iff_eqvGen] at hrel ⊢
  exact hrel.mono fun _ _ ⟨e, he, h⟩ => ⟨e, hsub.subset he, h⟩

private theorem edgePartitionFrom_subperm_eq {n : ℕ} {F G : List (WeightedEdge n ℕ)}
    (hsub : F.Subperm G) :
    edgePartitionFrom (edgePartition F) G = edgePartition G := by
  ext u v
  rw [Bool.eq_iff_iff]
  dsimp only [edgePartition]
  rw [rel_edgePartitionFrom_iff_eqvGen, rel_edgePartitionFrom_iff_eqvGen]
  constructor
  · intro h
    induction h with
    | rel a b hab =>
      rcases hab with hF | ⟨e, heG, rfl, rfl⟩
      · exact (rel_edgePartitionFrom_iff_eqvGen (Partition.discrete n) G a b).mp
          (edgePartition_mono_subperm hsub hF)
      · exact .rel _ _ (.inr ⟨e, heG, rfl, rfl⟩)
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2
  · intro h
    induction h with
    | rel a b hab =>
      rcases hab with h0 | ⟨e, heG, rfl, rfl⟩
      · exact .rel _ _ (.inl ((rel_edgePartitionFrom_iff_eqvGen _ F a b).mpr (.rel _ _ (.inl h0))))
      · exact .rel _ _ (.inr ⟨e, heG, rfl, rfl⟩)
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

private theorem numComponents_edgePartition_subperm_ge {n : ℕ} {F G : List (WeightedEdge n ℕ)}
    (hsub : F.Subperm G) :
    (edgePartition G).numComponents ≤ (edgePartition F).numComponents := by
  rw [← edgePartitionFrom_subperm_eq hsub]
  exact numComponents_edgePartitionFrom_le (edgePartition F) G

private theorem edgePartition_eq_of_subperm_of_numComponents_eq {n : ℕ}
    {F G : List (WeightedEdge n ℕ)} (hsub : F.Subperm G)
    (hc : (edgePartition F).numComponents = (edgePartition G).numComponents) :
    edgePartition F = edgePartition G := by
  rw [← edgePartitionFrom_subperm_eq hsub]
  symm
  have hcard : (edgePartitionFrom (edgePartition F) G).numComponents =
      (edgePartition F).numComponents := by
    rw [edgePartitionFrom_subperm_eq hsub]
    exact hc.symm
  suffices ∀ p : Partition n, ∀ L : List (WeightedEdge n ℕ),
      (edgePartitionFrom p L).numComponents = p.numComponents → edgePartitionFrom p L = p by
    exact this (edgePartition F) G hcard
  intro p L
  induction L generalizing p with
  | nil => intro _; rfl
  | cons x xs ihx =>
    intro hx
    rw [edgePartitionFrom_cons] at hx ⊢
    cases hrel : p.rel x.u x.v
    · exfalso
      have hdrop := Partition.numComponents_merge_of_not_rel hrel
      have hmon := numComponents_edgePartitionFrom_le (p.merge x.u x.v) xs
      omega
    · rw [Partition.merge_of_rel hrel] at hx ⊢
      exact ihx p hx

theorem isAcyclic_sublist {n : ℕ} {F G : List (WeightedEdge n ℕ)} (hsub : F.Sublist G)
    (hG : IsAcyclic G) : IsAcyclic F := by
  obtain ⟨K, hK⟩ := hsub.exists_perm_append
  have ha : IsAcyclic (F ++ K) := (Perm.isAcyclic_iff hK.symm).mpr hG
  rw [isAcyclic_iff, edgePartition, edgePartitionFrom_append, List.length_append] at ha
  change (edgePartitionFrom (edgePartition F) K).numComponents + (F.length + K.length) = n at ha
  have hnc := numComponents_le_edgePartitionFrom_add_length (edgePartition F) K
  have hup := numComponents_le_edgePartitionFrom_add_length (Partition.discrete n) F
  rw [Partition.numComponents_discrete] at hup
  rw [isAcyclic_iff]
  change n ≤ (edgePartition F).numComponents + F.length at hup
  omega

theorem isAcyclic_subperm {n : ℕ} {F G : List (WeightedEdge n ℕ)} (hsub : F.Subperm G)
    (hG : IsAcyclic G) : IsAcyclic F := by
  obtain ⟨G', hperm, hsl⟩ := List.subperm_iff.mp hsub
  exact isAcyclic_sublist hsl ((Perm.isAcyclic_iff hperm).mpr hG)

private theorem layer_cake_totalWeight {n : ℕ} (W : ℕ) (L : List (WeightedEdge n ℕ))
    (hW : ∀ e ∈ L, e.weight < W) :
    totalWeight L = ∑ t ∈ Finset.range W,
      (L.length - (L.filter fun e => decide (e.weight ≤ t)).length) := by
  induction L with
  | nil => simp [totalWeight]
  | cons e L ih =>
    have heW : e.weight < W := hW e List.mem_cons_self
    have hLW : ∀ f ∈ L, f.weight < W := fun f hf => hW f (List.mem_cons_of_mem _ hf)
    rw [totalWeight_cons, ih hLW]
    have hsplit : (∑ t ∈ Finset.range W,
        ((e :: L).length - ((e :: L).filter fun f => decide (f.weight ≤ t)).length)) =
        (∑ t ∈ Finset.range W, if e.weight ≤ t then 0 else 1) +
          ∑ t ∈ Finset.range W, (L.length - (L.filter fun f => decide (f.weight ≤ t)).length) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hfl : (L.filter fun f => decide (f.weight ≤ t)).length ≤ L.length :=
        List.length_filter_le _ _
      simp only [List.length_cons, List.filter_cons]
      by_cases hwt : e.weight ≤ t
      · rw [decide_eq_true hwt]; simp only [↓reduceIte, hwt, List.length_cons]; omega
      · rw [decide_eq_false hwt]; simp only [Bool.false_eq_true, ↓reduceIte, hwt]; omega
    have hcnt : (∑ t ∈ Finset.range W, if e.weight ≤ t then 0 else 1) = e.weight := by
      have hflt : (Finset.range W).filter (fun t => ¬ (e.weight ≤ t)) = Finset.range e.weight := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hflt, Finset.card_range]
    rw [hsplit, hcnt]

private theorem weight_le_totalWeight_of_mem {n : ℕ} {es : List (WeightedEdge n ℕ)}
    {e : WeightedEdge n ℕ} (he : e ∈ es) : e.weight ≤ totalWeight es :=
  List.le_sum_of_mem (List.mem_map_of_mem he)

private theorem isAcyclic_filter_numComponents {n : ℕ} {F : List (WeightedEdge n ℕ)}
    (hF : IsAcyclic F) (t : ℕ) :
    (edgePartition (F.filter fun e => decide (e.weight ≤ t))).numComponents +
      (F.filter fun e => decide (e.weight ≤ t)).length = n :=
  (isAcyclic_iff _).mp (isAcyclic_sublist List.filter_sublist hF)

private theorem filter_length_le_of_threshold {n : ℕ} {es U G' : List (WeightedEdge n ℕ)}
    (hU_sf : IsSpanningForest es U) (hG' : IsSpanningForest es G')
    (hU_thresh : ∀ t : ℕ,
      edgePartition (U.filter fun e => decide (e.weight ≤ t)) =
        edgePartition (es.filter fun e => decide (e.weight ≤ t))) (t : ℕ) :
    (G'.filter fun e => decide (e.weight ≤ t)).length ≤
      (U.filter fun e => decide (e.weight ≤ t)).length := by
  have hGt_sub : (G'.filter fun e => decide (e.weight ≤ t)).Subperm
      (es.filter fun e => decide (e.weight ≤ t)) := hG'.1.filter _
  have hGt_ac := isAcyclic_filter_numComponents hG'.2.1 t
  have hUt_ac := isAcyclic_filter_numComponents hU_sf.2.1 t
  have hnc := numComponents_edgePartition_subperm_ge hGt_sub
  rw [← hU_thresh t] at hnc
  omega

private theorem isMinSpanningForest_of_threshold {n : ℕ} (es U : List (WeightedEdge n ℕ))
    (hU_sf : IsSpanningForest es U)
    (hU_thresh : ∀ t : ℕ,
      edgePartition (U.filter fun e => decide (e.weight ≤ t)) =
        edgePartition (es.filter fun e => decide (e.weight ≤ t))) :
    IsMinSpanningForest es U := by
  refine ⟨hU_sf, fun G' hG' => ?_⟩
  let W := 1 + totalWeight es
  have hU_bound : ∀ e ∈ U, e.weight < W := fun e he => by
    have := weight_le_totalWeight_of_mem (hU_sf.1.subset he); omega
  have hG_bound : ∀ e ∈ G', e.weight < W := fun e he => by
    have := weight_le_totalWeight_of_mem (hG'.1.subset he); omega
  rw [layer_cake_totalWeight W U hU_bound, layer_cake_totalWeight W G' hG_bound]
  refine Finset.sum_le_sum fun t _ => ?_
  have hlen_eq : G'.length = U.length := hG'.length_eq hU_sf
  have hflt := filter_length_le_of_threshold hU_sf hG' hU_thresh t
  omega

private theorem edgeWeight_cut {n : ℕ} (es : List (WeightedEdge n ℕ)) (t : ℕ) :
    ∃ k : ℕ ×ₗ ℕ, ∀ i : Fin es.length, edgeWeight es i < k ↔ es[i.val].weight ≤ t :=
  ⟨toLex (t + 1, 0), fun i => by
    dsimp only [edgeWeight]
    rw [Prod.Lex.lt_iff]
    simp only [ofLex_toLex]
    omega⟩

private theorem filter_eq_self_of_subperm_totalWeight {n : ℕ} {F G : List (WeightedEdge n ℕ)}
    (hsub : F.Subperm G) {t : ℕ} (ht : totalWeight G ≤ t) :
    F.filter (fun e => decide (e.weight ≤ t)) = F := by
  rw [List.filter_eq_self]
  intro e he
  have := weight_le_totalWeight_of_mem (hsub.subset he)
  exact decide_eq_true (by omega)

/-- Threshold-rank characterization of `Kruskal.IsMinSpanningForest` over `ℕ` weights (handles
arbitrary equal edge weights via `layer_cake_totalWeight`). -/
theorem isMinSpanningForest_iff_threshold_partition {n : ℕ} (es F : List (WeightedEdge n ℕ)) :
    IsMinSpanningForest es F ↔
      IsSpanningForest es F ∧ ∀ t : ℕ,
        edgePartition (F.filter fun e => decide (e.weight ≤ t)) =
          edgePartition (es.filter fun e => decide (e.weight ≤ t)) := by
  let U := msfEdges es (edgeWeight es)
  have hU_sf : IsSpanningForest es U :=
    msfEdges_isSpanningForest es (edgeWeight es) (edgeWeight_injective es)
  have hU_thresh : ∀ t : ℕ,
      edgePartition (U.filter fun e => decide (e.weight ≤ t)) =
        edgePartition (es.filter fun e => decide (e.weight ≤ t)) :=
    msfEdges_threshold_partition es (edgeWeight es) (edgeWeight_cut es)
  have hU_msf : IsMinSpanningForest es U := isMinSpanningForest_of_threshold es U hU_sf hU_thresh
  let W := 1 + totalWeight es
  have hU_bound : ∀ e ∈ U, e.weight < W := fun e he => by
    have := weight_le_totalWeight_of_mem (hU_sf.1.subset he); omega
  constructor
  · intro hF
    refine ⟨hF.1, fun t => ?_⟩
    by_cases htW : t < W
    · have hF_bound : ∀ e ∈ F, e.weight < W := fun e he => by
        have := weight_le_totalWeight_of_mem (hF.1.1.subset he); omega
      have hlen_eq : F.length = U.length := hF.1.length_eq hU_sf
      have htw := hF.2 U hU_sf
      rw [layer_cake_totalWeight W F hF_bound, layer_cake_totalWeight W U hU_bound] at htw
      have hpt : ∀ s ∈ Finset.range W,
          (U.length - (U.filter fun e => decide (e.weight ≤ s)).length) ≤
            (F.length - (F.filter fun e => decide (e.weight ≤ s)).length) := fun s _ => by
        have hs := filter_length_le_of_threshold hU_sf hF.1 hU_thresh s
        omega
      have hsum_eq : ∑ s ∈ Finset.range W,
            (U.length - (U.filter fun e => decide (e.weight ≤ s)).length) =
          ∑ s ∈ Finset.range W,
            (F.length - (F.filter fun e => decide (e.weight ≤ s)).length) :=
        le_antisymm (Finset.sum_le_sum hpt) htw
      have heq_t := (Finset.sum_eq_sum_iff_of_le hpt).mp hsum_eq t (Finset.mem_range.mpr htW)
      have hUt_le : (U.filter fun e => decide (e.weight ≤ t)).length ≤ U.length :=
        List.length_filter_le _ _
      have hFt_le := filter_length_le_of_threshold hU_sf hF.1 hU_thresh t
      have hlen_t : (F.filter fun e => decide (e.weight ≤ t)).length =
          (U.filter fun e => decide (e.weight ≤ t)).length := by omega
      have hF_ac := isAcyclic_filter_numComponents hF.1.2.1 t
      have hU_ac := isAcyclic_filter_numComponents hU_sf.2.1 t
      have hnc_eq : (edgePartition (F.filter fun e => decide (e.weight ≤ t))).numComponents =
          (edgePartition (es.filter fun e => decide (e.weight ≤ t))).numComponents := by
        rw [← hU_thresh t]; omega
      exact edgePartition_eq_of_subperm_of_numComponents_eq (hF.1.1.filter _) hnc_eq
    · have ht_le : totalWeight es ≤ t := by dsimp only [W] at htW; omega
      rw [filter_eq_self_of_subperm_totalWeight hF.1.1 ht_le,
        filter_eq_self_of_subperm_totalWeight (.refl es) ht_le, hF.1.2.2]
  · rintro ⟨hF_sf, hF_thresh⟩
    exact isMinSpanningForest_of_threshold es F hF_sf hF_thresh

theorem weaklySupported_mono_subperm {n : ℕ} {G₁ G₂ : List (WeightedEdge n ℕ)}
    (hsub : G₁.Subperm G₂) {e : WeightedEdge n ℕ}
    (hws : WeaklySupported G₁ e) : WeaklySupported G₂ e :=
  edgePartition_mono_subperm (hsub.filter _) hws

private theorem filter_sublist_of_imp {α : Type*} (p q : α → Bool)
    (hpq : ∀ x, p x = true → q x = true) (xs : List α) :
    (xs.filter p).Sublist (xs.filter q) := by
  induction xs with
  | nil => exact .slnil
  | cons x xs ih =>
    rw [List.filter_cons, List.filter_cons]
    cases hp : p x
    · cases q x <;> simp [ih, List.Sublist.cons]
    · simp only [hpq x hp, ↓reduceIte]
      exact List.Sublist.cons_cons x ih

/-- Monotonicity of threshold `edgePartition` connectivity in both the edge list (`F.Subperm G`)
and the weight threshold (`t₁ ≤ t₂`). -/
theorem edgePartition_filter_mono_subperm {n : ℕ} {F G : List (WeightedEdge n ℕ)}
    (hsub : F.Subperm G) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) {u v : Fin n}
    (hrel : (edgePartition (F.filter fun e => decide (e.weight ≤ t₁))).rel u v = true) :
    (edgePartition (G.filter fun e => decide (e.weight ≤ t₂))).rel u v = true :=
  edgePartition_mono_subperm
    ((filter_sublist_of_imp _ _ (fun g hg => by
      simp only [decide_eq_true_eq] at hg ⊢; omega) F).subperm.trans (hsub.filter _))
    hrel

private theorem rel_edgePartitionFrom_mono_init {n : ℕ} (p : Partition n)
    (L : List (WeightedEdge n ℕ)) {u v : Fin n} (h : (edgePartition L).rel u v = true) :
    (edgePartitionFrom p L).rel u v = true := by
  rw [edgePartition, rel_edgePartitionFrom_iff_eqvGen] at h
  rw [rel_edgePartitionFrom_iff_eqvGen]
  induction h with
  | rel a b hab =>
    rcases hab with h0 | ⟨e, he, rfl, rfl⟩
    · rw [Partition.rel_discrete_eq_true.mp h0]
      exact .refl _
    · exact .rel _ _ (.inr ⟨e, he, rfl, rfl⟩)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private theorem edgePartitionFrom_filter_eq_of_weakSupport {n : ℕ}
    (A B : List (WeightedEdge n ℕ)) (hAB : ∀ f ∈ A, WeaklySupported B f) (t : ℕ) :
    edgePartitionFrom (edgePartition (B.filter fun g => decide (g.weight ≤ t)))
      (A.filter fun f => decide (f.weight ≤ t)) =
      edgePartition (B.filter fun g => decide (g.weight ≤ t)) := by
  refine edgePartitionFrom_eq_self_of_forall _ _ fun f hf => ?_
  rw [List.mem_filter, decide_eq_true_eq] at hf
  exact edgePartition_filter_mono_subperm (List.Subperm.refl _) hf.2 (hAB f hf.1)

theorem weaklySupported_trans {n : ℕ} (A B : List (WeightedEdge n ℕ))
    (hAB : ∀ f ∈ A, WeaklySupported B f) {e : WeightedEdge n ℕ}
    (he : WeaklySupported A e) : WeaklySupported B e := by
  dsimp only [WeaklySupported] at he ⊢
  rw [← edgePartitionFrom_filter_eq_of_weakSupport A B hAB e.weight]
  exact rel_edgePartitionFrom_mono_init _ _ he

theorem isMinSpanningForest_of_weakSupport {n : ℕ} (G G_b F : List (WeightedEdge n ℕ))
    (hsub : G_b.Subperm G) (hws : ∀ e ∈ G, WeaklySupported G_b e)
    (hF : IsMinSpanningForest G_b F) : IsMinSpanningForest G F := by
  have hF_thresh := (isMinSpanningForest_iff_threshold_partition G_b F).mp hF
  have hthresh_eq : ∀ t : ℕ,
      edgePartition (G_b.filter fun e => decide (e.weight ≤ t)) =
        edgePartition (G.filter fun e => decide (e.weight ≤ t)) := fun t => by
    rw [← edgePartitionFrom_subperm_eq (hsub.filter _),
      edgePartitionFrom_filter_eq_of_weakSupport G G_b hws t]
  have hF_G_thresh : ∀ t : ℕ,
      edgePartition (F.filter fun e => decide (e.weight ≤ t)) =
        edgePartition (G.filter fun e => decide (e.weight ≤ t)) := fun t =>
    (hF_thresh.2 t).trans (hthresh_eq t)
  have hFG_part : edgePartition F = edgePartition G := by
    simpa only [filter_eq_self_of_subperm_totalWeight (hF.1.1.trans hsub) le_rfl,
      filter_eq_self_of_subperm_totalWeight (.refl G) le_rfl] using hF_G_thresh (totalWeight G)
  exact (isMinSpanningForest_iff_threshold_partition G F).mpr
    ⟨⟨hF.1.1.trans hsub, hF.1.2.1, hFG_part⟩, hF_G_thresh⟩

/-! ## Graph Contraction and Cut-Step Extension -/

/-- Remap a weighted edge's endpoints along a vertex contraction map `c : Fin n → Fin n'`. -/
@[expose] def contractEdge {n n' : ℕ} (c : Fin n → Fin n')
    (e : WeightedEdge n ℕ) : WeightedEdge n' ℕ :=
  ⟨c e.u, c e.v, e.weight⟩

/-- Remap every edge in `es` along a vertex contraction map `c : Fin n → Fin n'`. -/
@[expose] def contractEdgeList {n n' : ℕ} (c : Fin n → Fin n')
    (es : List (WeightedEdge n ℕ)) : List (WeightedEdge n' ℕ) :=
  es.map (contractEdge c)

theorem totalWeight_contractEdgeList {n n' : ℕ} (c : Fin n → Fin n')
    (es : List (WeightedEdge n ℕ)) :
    totalWeight (contractEdgeList c es) = totalWeight es := by
  dsimp only [totalWeight, contractEdgeList]
  rw [List.map_map]
  rfl

private theorem edgePartitionFrom_contract_rel {n n' : ℕ} (p : Partition n) (c : Fin n → Fin n')
    (hc : ∀ x y : Fin n, c x = c y ↔ p.rel x y = true) (M : List (WeightedEdge n ℕ))
    (u v : Fin n) :
    (edgePartition (contractEdgeList c M)).rel (c u) (c v) = true ↔
      (edgePartitionFrom p M).rel u v = true := by
  have hrel_p : ∀ a b : Fin n, p.rel a b = true → (edgePartitionFrom p M).rel a b = true :=
    fun a b hab => (rel_edgePartitionFrom_iff_eqvGen p M a b).mpr (.rel _ _ (.inl hab))
  constructor
  · intro h
    rw [rel_edgePartition_iff_eqvGen] at h
    have hgen : ∀ x' y' : Fin n',
        Relation.EqvGen (fun a b => ∃ e' ∈ contractEdgeList c M, a = e'.u ∧ b = e'.v) x' y' →
        x' = y' ∨ ∃ a b : Fin n, c a = x' ∧ c b = y' ∧ (edgePartitionFrom p M).rel a b = true := by
      intro x' y' hxy
      induction hxy with
      | refl _ => exact .inl rfl
      | rel a' b' hab =>
        obtain ⟨e', he', rfl, rfl⟩ := hab
        simp only [contractEdgeList, List.mem_map] at he'
        obtain ⟨e, heM, rfl⟩ := he'
        refine .inr ⟨e.u, e.v, rfl, rfl, ?_⟩
        rw [rel_edgePartitionFrom_iff_eqvGen]
        exact .rel _ _ (.inr ⟨e, heM, rfl, rfl⟩)
      | symm _ _ _ ih =>
        rcases ih with rfl | ⟨a, b, ha, hb, hrel⟩
        · exact .inl rfl
        · exact .inr ⟨b, a, hb, ha, (edgePartitionFrom p M).symm hrel⟩
      | trans _ _ _ _ _ ih1 ih2 =>
        rcases ih1 with rfl | ⟨a, y₁, ha, hy₁, h1⟩
        · exact ih2
        · rcases ih2 with rfl | ⟨y₂, b, hy₂, hb, h2⟩
          · exact .inr ⟨a, y₁, ha, hy₁, h1⟩
          · have hy_rel : (edgePartitionFrom p M).rel y₁ y₂ = true :=
              hrel_p _ _ ((hc _ _).mp (hy₁.trans hy₂.symm))
            exact .inr ⟨a, b, ha, hb,
              (edgePartitionFrom p M).trans h1 ((edgePartitionFrom p M).trans hy_rel h2)⟩
    rcases hgen _ _ h with heq | ⟨a, b, ha, hb, hrel⟩
    · exact hrel_p _ _ ((hc _ _).mp heq)
    · exact (edgePartitionFrom p M).trans (hrel_p _ _ ((hc _ _).mp ha.symm))
        ((edgePartitionFrom p M).trans hrel (hrel_p _ _ ((hc _ _).mp hb)))
  · intro h
    rw [rel_edgePartitionFrom_iff_eqvGen] at h
    induction h with
    | rel a b hab =>
      rcases hab with hp | ⟨e, heM, rfl, rfl⟩
      · rw [(hc _ _).mpr hp]
        exact (edgePartition (contractEdgeList c M)).refl _
      · exact rel_edgePartitionFrom_of_mem (Partition.discrete n')
          (List.mem_map_of_mem (f := contractEdge c) heM)
    | refl _ => exact (edgePartition (contractEdgeList c M)).refl _
    | symm _ _ _ ih => exact (edgePartition (contractEdgeList c M)).symm ih
    | trans _ _ _ _ _ ih1 ih2 => exact (edgePartition (contractEdgeList c M)).trans ih1 ih2

private theorem numComponents_contract_eq {n n' : ℕ} (p : Partition n) (c : Fin n → Fin n')
    (hc : ∀ x y : Fin n, c x = c y ↔ p.rel x y = true)
    (hsurj : Function.Surjective c) (M : List (WeightedEdge n ℕ)) :
    (edgePartition (contractEdgeList c M)).numComponents =
      (edgePartitionFrom p M).numComponents := by
  let Q := edgePartitionFrom p M
  let Q' := edgePartition (contractEdgeList c M)
  have himg_eq : ∀ x : Fin n, (Q.classOf x).image c = Q'.classOf (c x) := fun x => by
    ext y'
    obtain ⟨y, rfl⟩ := hsurj y'
    simp only [Finset.mem_image, Partition.classOf, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨z, hxz, hzy⟩
      have hrel_zy : Q.rel z y = true :=
        (rel_edgePartitionFrom_iff_eqvGen p M z y).mpr (.rel _ _ (.inl ((hc _ _).mp hzy)))
      exact (edgePartitionFrom_contract_rel p c hc M x y).mpr (Q.trans hxz hrel_zy)
    · intro hrel'
      exact ⟨y, (edgePartitionFrom_contract_rel p c hc M x y).mp hrel', rfl⟩
  symm
  refine Finset.card_bij (fun C _ => C.image c) ?_ ?_ ?_
  · intro C hC
    simp only [Partition.components, Finset.mem_image, Finset.mem_univ, true_and] at hC ⊢
    obtain ⟨x, rfl⟩ := hC
    exact ⟨c x, (himg_eq x).symm⟩
  · intro C₁ hC₁ C₂ hC₂ heq
    simp only [Partition.components, Finset.mem_image, Finset.mem_univ, true_and] at hC₁ hC₂
    obtain ⟨x₁, rfl⟩ := hC₁
    obtain ⟨x₂, rfl⟩ := hC₂
    rw [himg_eq x₁, himg_eq x₂, Partition.classOf_eq_iff] at heq
    rw [Partition.classOf_eq_iff]
    exact (edgePartitionFrom_contract_rel p c hc M x₁ x₂).mp heq
  · intro C' hC'
    simp only [Partition.components, Finset.mem_image, Finset.mem_univ, true_and] at hC'
    obtain ⟨x', rfl⟩ := hC'
    obtain ⟨x, rfl⟩ := hsurj x'
    exact ⟨Q.classOf x, Q.classOf_mem_components x, himg_eq x⟩

theorem exists_extend_isMinSpanningForest_of_cutStep {n : ℕ}
    (es : List (WeightedEdge n ℕ)) (e : WeightedEdge n ℕ) (he : e ∈ es)
    (A : Finset (Fin n)) (hcut : e.u ∈ A ↔ e.v ∉ A)
    (hmin : ∀ f ∈ es, (f.u ∈ A ↔ f.v ∉ A) → e.weight ≤ f.weight) :
    ∃ F_ext : List (WeightedEdge n ℕ), IsMinSpanningForest es (e :: F_ext) := by
  obtain ⟨k, hk, he_i₀⟩ := List.mem_iff_getElem.mp he
  let i₀ : Fin es.length := ⟨k, hk⟩
  let w := edgeWeightPrefer es i₀
  have hcut_w : ∀ t : ℕ, ∃ m : ℕ ×ₗ (ℕ ×ₗ ℕ), ∀ i : Fin es.length,
      w i < m ↔ es[i.val].weight ≤ t := fun t =>
    ⟨toLex (t + 1, toLex (0, 0)), fun i => by
      dsimp only [w, edgeWeightPrefer]
      simp only [Prod.Lex.lt_iff, ofLex_toLex, Nat.not_lt_zero, and_false, or_false,
        Nat.lt_succ_iff]⟩
  let U := msfEdges es w
  have hU_sf := msfEdges_isSpanningForest es w (edgeWeightPrefer_injective es i₀)
  have hU_thresh := msfEdges_threshold_partition es w hcut_w
  have hU_msf : IsMinSpanningForest es U := isMinSpanningForest_of_threshold es U hU_sf hU_thresh
  have hi₀_in : i₀ ∈ Cslib.Multigraph.msf (edgeEnds es) w Finset.univ := by
    have he_ends : edgeEnds es i₀ = s(e.u, e.v) := by simp [edgeEnds, i₀, he_i₀]
    rw [Cslib.Multigraph.mem_msf_iff w he_ends]
    refine ⟨Finset.mem_univ _, fun hj => ?_⟩
    have not_joins_cut : ∀ {x y : Fin n}, x ∈ A → y ∉ A →
        ¬ Cslib.Multigraph.Joins (edgeEnds es)
          {f | f ∈ (Finset.univ : Finset (Fin es.length)) ∧ w f < w i₀} x y := by
      intro x y hx hy hxy
      obtain ⟨f, ⟨_, hwf⟩, hfcut⟩ := hxy.exists_mem_edgeCut (P := (A : Set (Fin n))) hx hy
      obtain ⟨a, b, hab, ha, hb⟩ := Graph.mem_edgeCut_iff.1 hfcut
      change edgeEnds es f = s(a, b) at hab
      have hcross : es[f.val].u ∈ A ↔ es[f.val].v ∉ A := by
        dsimp only [edgeEnds] at hab
        rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨fun _ => hb, fun _ => ha⟩
        · exact ⟨fun h => absurd h hb, fun h => absurd ha h⟩
      have hge := hmin es[f.val] (List.getElem_mem f.isLt) hcross
      have hlt := (edgeWeightPrefer_lt_self_iff es i₀ f).mp hwf
      rw [he_i₀] at hlt
      omega
    by_cases hu : e.u ∈ A
    · exact not_joins_cut hu (hcut.mp hu) hj
    · exact not_joins_cut (by by_contra hv; exact hu (hcut.mpr hv)) hu hj.symm
  have he_U : e ∈ U := by
    dsimp only [U, msfEdges]
    exact List.mem_map.mpr ⟨i₀, Finset.mem_toList.mpr hi₀_in, he_i₀⟩
  let F_ext := U.erase e
  have hperm : (e :: F_ext).Perm U := (List.perm_cons_erase he_U).symm
  refine ⟨F_ext, ⟨hperm.subperm.trans hU_msf.1.1,
    (Perm.isAcyclic_iff hperm).mpr hU_msf.1.2.1,
    (Perm.edgePartition_eq hperm).trans hU_msf.1.2.2⟩, fun G' hG' => ?_⟩
  rw [Perm.totalWeight_eq hperm]
  exact hU_msf.2 G' hG'

theorem exists_extend_isMinSpanningForest_of_subperm_msfEdges {n : ℕ}
    (es F' : List (WeightedEdge n ℕ)) (hsub : F'.Subperm (msfEdges es (edgeWeight es))) :
    ∃ F_ext : List (WeightedEdge n ℕ), IsMinSpanningForest es (F' ++ F_ext) := by
  let U := msfEdges es (edgeWeight es)
  obtain ⟨U', hperm, hsublist⟩ := List.subperm_iff.mp hsub
  obtain ⟨F_ext, hK⟩ := hsublist.exists_perm_append
  have hcomb : (F' ++ F_ext).Perm U := hK.symm.trans hperm
  have hU_msf : IsMinSpanningForest es U :=
    isMinSpanningForest_of_threshold es U
      (msfEdges_isSpanningForest es (edgeWeight es) (edgeWeight_injective es))
      (msfEdges_threshold_partition es (edgeWeight es) (edgeWeight_cut es))
  refine ⟨F_ext, ⟨hcomb.subperm.trans hU_msf.1.1,
    (Perm.isAcyclic_iff hcomb).mpr hU_msf.1.2.1,
    (Perm.edgePartition_eq hcomb).trans hU_msf.1.2.2⟩, fun G' hG' => ?_⟩
  rw [Perm.totalWeight_eq hcomb]
  exact hU_msf.2 G' hG'

theorem isMinSpanningForest_append_of_contract {n n' : ℕ}
    (es F' L : List (WeightedEdge n ℕ)) (c : Fin n → Fin n')
    (hF'_sub : F'.Subperm es) (hF'_ac : IsAcyclic F')
    (hc : ∀ x y : Fin n, c x = c y ↔ (edgePartition F').rel x y = true)
    (hsurj : Function.Surjective c)
    (hext : ∃ F_ext : List (WeightedEdge n ℕ), IsMinSpanningForest es (F' ++ F_ext))
    (hL_sub : L.Subperm es)
    (hL_msf : IsMinSpanningForest (contractEdgeList c es) (contractEdgeList c L)) :
    IsMinSpanningForest es (F' ++ L) := by
  obtain ⟨F_ext, hF_ext⟩ := hext
  let p := edgePartition F'
  have hF'_ac_n : p.numComponents + F'.length = n := (isAcyclic_iff F').mp hF'_ac
  have hp_eq : p.numComponents = n' := by
    have := numComponents_contract_eq p c hc hsurj []
    simpa [p, contractEdgeList, edgePartition, Partition.numComponents_discrete] using this.symm
  have hSF_to_c : ∀ K : List (WeightedEdge n ℕ), IsSpanningForest es (F' ++ K) →
      IsSpanningForest (contractEdgeList c es) (contractEdgeList c K) := fun K hK => by
    refine ⟨?_, ?_, ?_⟩
    · have hsub_k : K.Subperm es := (List.sublist_append_right F' K).subperm.trans hK.1
      obtain ⟨s, hp, hs⟩ := List.subperm_iff.mp hsub_k
      exact List.subperm_iff.mpr ⟨s.map (contractEdge c), hp.map _, hs.map _⟩
    · rw [isAcyclic_iff, numComponents_contract_eq p c hc hsurj K]
      have hK_ac := (isAcyclic_iff (F' ++ K)).mp hK.2.1
      rw [edgePartition, edgePartitionFrom_append, List.length_append] at hK_ac
      have hK_ac' : (edgePartitionFrom p K).numComponents + (F'.length + K.length) = n := hK_ac
      rw [contractEdgeList, List.length_map]
      omega
    · ext u' v'
      obtain ⟨u, rfl⟩ := hsurj u'
      obtain ⟨v, rfl⟩ := hsurj v'
      rw [Bool.eq_iff_iff, edgePartitionFrom_contract_rel p c hc K u v,
        edgePartitionFrom_contract_rel p c hc es u v, edgePartitionFrom_subperm_eq hF'_sub,
        ← hK.2.2, edgePartition, edgePartitionFrom_append]
      exact Iff.rfl
  have hL_sf_es : IsSpanningForest es (F' ++ L) := by
    have hdisj : ∀ e ∈ F', e ∉ L := fun e heF heL =>
      hL_msf.1.2.1.ne_of_mem (List.mem_map_of_mem (f := contractEdge c) heL)
        ((hc e.u e.v).mpr (rel_edgePartitionFrom_of_mem (Partition.discrete n) heF))
    have hsub_app : (F' ++ L).Subperm es := by
      rw [List.subperm_iff_count]
      intro a
      rw [List.count_append]
      by_cases ha : a ∈ F'
      · rw [List.count_eq_zero.mpr (hdisj a ha), add_zero]
        exact hF'_sub.count_le a
      · rw [List.count_eq_zero.mpr ha, zero_add]
        exact hL_sub.count_le a
    refine ⟨hsub_app, ?_, ?_⟩
    · rw [isAcyclic_iff, edgePartition, edgePartitionFrom_append, List.length_append]
      have hL_ac := (isAcyclic_iff (contractEdgeList c L)).mp hL_msf.1.2.1
      rw [numComponents_contract_eq p c hc hsurj L, contractEdgeList, List.length_map] at hL_ac
      change (edgePartitionFrom p L).numComponents + (F'.length + L.length) = n
      omega
    · ext u v
      rw [Bool.eq_iff_iff, edgePartition, edgePartitionFrom_append]
      have hrel' : (edgePartition (contractEdgeList c L)).rel (c u) (c v) =
          (edgePartition (contractEdgeList c es)).rel (c u) (c v) :=
        congrArg (·.rel (c u) (c v)) hL_msf.1.2.2
      rw [Bool.eq_iff_iff, edgePartitionFrom_contract_rel p c hc L u v,
        edgePartitionFrom_contract_rel p c hc es u v] at hrel'
      have hcomb_es := congrArg (·.rel u v) (edgePartitionFrom_subperm_eq hF'_sub)
      rw [Bool.eq_iff_iff] at hcomb_es
      exact hrel'.trans hcomb_es
  refine ⟨hL_sf_es, fun G' hG' => ?_⟩
  have hF_ext_c := hSF_to_c F_ext hF_ext.1
  have htw_c := hL_msf.2 (contractEdgeList c F_ext) hF_ext_c
  rw [totalWeight_contractEdgeList, totalWeight_contractEdgeList] at htw_c
  have htw_G := hF_ext.2 G' hG'
  rw [totalWeight_append] at htw_G ⊢
  omega

end Cslib.Query.MinimumSpanningForest
