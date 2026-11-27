/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Robust
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Canonical
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.IndexedEdges
import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Decomp
import CslibFrontier.Foundations.Data.List.Subperm
import Mathlib.Data.Nat.Find

/-!
# Partition Round Bridges: Decision-Tree Depth, Conglomerate Size, and MSF Lifting

Steps toward Theorem 5.8 of [PettieRamachandran2002] (#8624) over caller-supplied dynamic-DJP
round witnesses (`PartitionRoundWitness`), connecting `PartitionRoundWitness` lists to upstream
`Cslib.Query.MinimumSpanningForest` theorems (`sum_optDepth_le_optDepthMN`,
`maxsize_le_card_biUnion_of_stop`, `DynamicDJPTree.rel_treeEdges_filter_of_border`,
`edgePartition_rel_of_contracted_bridge`, and `isMinSpanningForest_of_weakSupport`) for Lemma 3.2
(§3.1, p. 20), Lemma 3.3 (§3.2, pp. 21–22), and Property 5.3 / Corollary 5.6 (§5.1, pp. 25–26).

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.PartitionRoundWitness`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.PartitionRoundWitness.compGlobal`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.PartitionRoundWitness.verts`: mathematical
  witness for one dynamic-DJP partition round, its lifted global edge list, and its vertex set.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.PartitionRoundMeta`: shared per-round metadata
  and structural invariants for partition rounds stored in memory.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.PartitionRoundMeta.congr`: frame-preservation
  lemma lifting `PartitionRoundMeta` across memory states agreeing below `bound`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partition_optDepth_sum_le`: decision-tree
  depth sum bound `(rounds.map ...).sum ≤ optDepthMN es.length n`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partition_conglom_active_verts_le`: active
  conglomerate vertex bound `n_a * maxsize ≤ n`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partition_isMinSpanningForest`: multi-round
  conglomerate weak-support MSF lifting theorem.

## References

* [S. Pettie and V. Ramachandran, *An Optimal Minimum Spanning Tree
  Algorithm*][PettieRamachandran2002]
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.DataStructure.DisjointSet Cslib.Algorithms.Lean.Kruskal
open Cslib.Query.MinimumSpanningForest

/-! ## Section 1: Partition Round Witness -/

/-- Mathematical witness for one dynamic-DJP partition round. -/
structure PartitionRoundWitness (n : ℕ) where
  /-- Dynamic Soft-Heap DJP tree grown in this round. -/
  tree : DynamicDJPTree n
  /-- Vertex count `|V_i|` of the dense local vertex set `Fin numVerts`. -/
  numVerts : ℕ
  /-- Map from dense local vertices `Fin numVerts` to global vertices `Fin n`. -/
  lift : Fin numVerts → Fin n
  /-- Local edge list `C_i` on `Fin numVerts`. -/
  compLocal : List (IndexedEdge numVerts)
  /-- Corrupted edges `M_i` collected at the end of this round. -/
  corrEdges : List (IndexedEdge n)

/-- Lift `compLocal` back to global vertices `Fin n` via `lift`. -/
@[expose] def PartitionRoundWitness.compGlobal {n : ℕ} (r : PartitionRoundWitness n) :
    List (IndexedEdge n) :=
  r.compLocal.map fun e => ⟨r.lift e.u, r.lift e.v, e.weight, e.id⟩

/-- Vertex set `V_i = tree.treeVerts tree.numSteps` of round `r`. -/
@[expose] def PartitionRoundWitness.verts {n : ℕ} (r : PartitionRoundWitness n) :
    Finset (Fin n) :=
  r.tree.treeVerts r.tree.numSteps

/-- Shared per-round metadata and structural invariants for `rounds` stored at `compMetaBase` and
`liftMetaBase` in memory `mem`. -/
structure PartitionRoundMeta {n : ℕ} (maxsize compMetaBase liftMetaBase : ℕ)
    (rounds : List (PartitionRoundWitness n)) (mem : ℕ → ℕ) : Prop where
  /-- Component vertex count recorded at `compMetaBase + 3 * i`. -/
  numVerts_eq : ∀ i : Fin rounds.length,
    mem (compMetaBase + 3 * i.val) = (rounds[i.val]'i.isLt).numVerts
  /-- Component edge count recorded at `compMetaBase + 3 * i + 1`. -/
  numEdges_eq : ∀ i : Fin rounds.length,
    mem (compMetaBase + 3 * i.val + 1) = (rounds[i.val]'i.isLt).compLocal.length
  /-- Stride-4 local edge array stored at `mem (compMetaBase + 3 * i + 2)`. -/
  holdsEdges : ∀ i : Fin rounds.length,
    HoldsIndexedEdges (mem (compMetaBase + 3 * i.val + 2))
      (rounds[i.val]'i.isLt).compLocal mem
  /-- Local-to-global vertex lift map stored at `mem (liftMetaBase + i)`. -/
  lift_eq : ∀ i : Fin rounds.length, ∀ k : Fin (rounds[i.val]'i.isLt).numVerts,
    mem (mem (liftMetaBase + i.val) + k.val) = ((rounds[i.val]'i.isLt).lift k).val
  /-- Each component has at most `maxsize` vertices. -/
  numVerts_le : ∀ i : Fin rounds.length, (rounds[i.val]'i.isLt).numVerts ≤ maxsize
  /-- Non-empty edge components have at most `2 * compLocal.length` vertices. -/
  numVerts_le_two_mul : ∀ i : Fin rounds.length,
    1 ≤ (rounds[i.val]'i.isLt).compLocal.length →
    (rounds[i.val]'i.isLt).numVerts ≤ 2 * (rounds[i.val]'i.isLt).compLocal.length
  /-- The local-to-global vertex lift map of each round is injective. -/
  lift_injective : ∀ i : Fin rounds.length, Function.Injective (rounds[i.val]'i.isLt).lift
  /-- Each component's local edge multigraph is simple. -/
  isSimple : ∀ i : Fin rounds.length,
    IsSimple (edgeEnds ((rounds[i.val]'i.isLt).compLocal.map IndexedEdge.toWeighted))
  /-- Every lifted edge has both endpoints in that round's vertex set `verts`. -/
  compGlobal_verts : ∀ i : Fin rounds.length,
    ∀ e ∈ (rounds[i.val]'i.isLt).compGlobal,
      e.u ∈ (rounds[i.val]'i.isLt).verts ∧ e.v ∈ (rounds[i.val]'i.isLt).verts
  /-- Each round intersects previous rounds' vertices in at most one vertex. -/
  inter_prev_card_le_one : ∀ i : Fin rounds.length,
    ((rounds[i.val]'i.isLt).verts ∩ (Finset.univ.filter fun j : Fin rounds.length =>
      j.val < i.val).biUnion (fun j => (rounds[j.val]'j.isLt).verts)).card ≤ 1

/-- Frame-preservation lemma for `PartitionRoundMeta`: lifts metadata and structural invariants from
`mem₁` to `mem₂` when `mem₂` agrees with `mem₁` below `bound`. -/
theorem PartitionRoundMeta.congr {n maxsize compMetaBase liftMetaBase bound : ℕ}
    {rounds : List (PartitionRoundWitness n)} {mem₁ mem₂ : ℕ → ℕ}
    (hagree : ∀ a < bound, mem₂ a = mem₁ a)
    (hcomp : compMetaBase + 3 * rounds.length ≤ bound)
    (hlift : liftMetaBase + rounds.length ≤ bound)
    (hbounds : ∀ i : Fin rounds.length,
      let r := rounds[i.val]'i.isLt
      mem₁ (compMetaBase + 3 * i.val + 2) + 4 * r.compLocal.length ≤ bound ∧
      mem₁ (liftMetaBase + i.val) + r.numVerts ≤ bound)
    (h : PartitionRoundMeta maxsize compMetaBase liftMetaBase rounds mem₁) :
    PartitionRoundMeta maxsize compMetaBase liftMetaBase rounds mem₂ := by
  refine
    { numVerts_eq := fun i => (hagree _ (by have := i.isLt; omega)).trans (h.numVerts_eq i)
      numEdges_eq := fun i => (hagree _ (by have := i.isLt; omega)).trans (h.numEdges_eq i)
      holdsEdges := fun i => by
        have heb : mem₂ (compMetaBase + 3 * i.val + 2) = mem₁ (compMetaBase + 3 * i.val + 2) :=
          hagree _ (by have := i.isLt; omega)
        rw [heb]
        have hbi := (hbounds i).1
        exact (h.holdsEdges i).congr fun a ha1 ha2 => hagree a (by omega)
      lift_eq := fun i k => by
        have hlb : mem₂ (liftMetaBase + i.val) = mem₁ (liftMetaBase + i.val) :=
          hagree _ (by have := i.isLt; omega)
        rw [hlb]
        have hk := k.isLt
        have hbi := (hbounds i).2
        exact (hagree _ (by omega)).trans (h.lift_eq i k)
      numVerts_le := h.numVerts_le
      numVerts_le_two_mul := h.numVerts_le_two_mul
      lift_injective := h.lift_injective
      isSimple := h.isSimple
      compGlobal_verts := h.compGlobal_verts
      inter_prev_card_le_one := h.inter_prev_card_le_one }

/-! ## Section 2: Decision-Tree Depth Sum Bridge -/

private def toGlobalEnds {n : ℕ} (r : PartitionRoundWitness n) : Σ e, Fin e → Sym2 (Fin n) :=
  ⟨(r.compGlobal.map IndexedEdge.toWeighted).length,
    edgeEnds (r.compGlobal.map IndexedEdge.toWeighted)⟩

private theorem optDepth_compLocal_eq_global {n : ℕ} (r : PartitionRoundWitness n)
    (hlift_inj : Function.Injective r.lift) :
    optDepth (edgeEnds (r.compLocal.map IndexedEdge.toWeighted)) =
      optDepth (toGlobalEnds r).2 := by
  let G₁ := edgeEnds (r.compLocal.map IndexedEdge.toWeighted)
  let G₂ := (toGlobalEnds r).2
  have hlen : (r.compLocal.map IndexedEdge.toWeighted).length =
      (r.compGlobal.map IndexedEdge.toWeighted).length := by
    simp [PartitionRoundWitness.compGlobal]
  let σ : Fin (r.compLocal.map IndexedEdge.toWeighted).length ≃
      Fin (r.compGlobal.map IndexedEdge.toWeighted).length :=
    ⟨Fin.cast hlen, Fin.cast hlen.symm, fun _ => rfl, fun _ => rfl⟩
  let φ : Fin r.numVerts ↪ Fin n := ⟨r.lift, hlift_inj⟩
  refine optDepth_reindex G₁ G₂ σ φ fun i => ?_
  dsimp only [G₁, G₂, toGlobalEnds, edgeEnds, PartitionRoundWitness.compGlobal,
    IndexedEdge.toWeighted, σ, φ]
  simp only [List.getElem_map, Sym2.map_mk]
  rfl

private theorem compVertsList_subset_rounds {n : ℕ} (qs : List (PartitionRoundWitness n))
    (hverts : ∀ q ∈ qs, ∀ e ∈ q.compGlobal, e.u ∈ q.verts ∧ e.v ∈ q.verts) :
    ∀ x ∈ compVertsList (qs.map toGlobalEnds), ∃ q ∈ qs, x ∈ q.verts := by
  induction qs with
  | nil => intro x hx; simp [compVertsList] at hx
  | cons q rest ih =>
    intro x hx
    simp only [List.map_cons, compVertsList, Finset.mem_union] at hx
    rcases hx with hq | hr
    · simp only [compVerts, Finset.mem_biUnion, Finset.mem_univ, Sym2.mem_toFinset, true_and]
        at hq
      obtain ⟨i, hxi⟩ := hq
      have hi : i.val < q.compGlobal.length := by simpa [toGlobalEnds] using i.isLt
      have he := hverts q List.mem_cons_self _ (List.getElem_mem hi)
      dsimp only [toGlobalEnds, edgeEnds] at hxi
      simp only [List.getElem_map, IndexedEdge.toWeighted, Sym2.mem_iff] at hxi
      rcases hxi with rfl | rfl
      exacts [⟨q, List.mem_cons_self, he.1⟩, ⟨q, List.mem_cons_self, he.2⟩]
    · obtain ⟨q', hq', hxq⟩ := ih (fun a ha => hverts a (List.mem_cons_of_mem _ ha)) x hr
      exact ⟨q', List.mem_cons_of_mem _ hq', hxq⟩

private theorem validDecomp_rounds_take_reverse {n : ℕ}
    (rounds : List (PartitionRoundWitness n))
    (hrounds : ∀ i : Fin rounds.length,
      (∀ e ∈ (rounds[i.val]'i.isLt).compGlobal,
        e.u ∈ (rounds[i.val]'i.isLt).verts ∧ e.v ∈ (rounds[i.val]'i.isLt).verts) ∧
      ((rounds[i.val]'i.isLt).verts ∩ (Finset.univ.filter fun j : Fin rounds.length =>
        j.val < i.val).biUnion (fun j => (rounds[j.val]'j.isLt).verts)).card ≤ 1) :
    ∀ t ≤ rounds.length, ValidDecomp ((rounds.take t).reverse.map toGlobalEnds) := by
  intro t ht
  induction t with
  | zero => exact validDecomp_nil
  | succ t ih =>
    have ht_lt : t < rounds.length := ht
    have htake : rounds.take (t + 1) = rounds.take t ++ [rounds[t]'ht_lt] := by
      rw [List.take_add_one, List.getElem?_eq_getElem ht_lt]; rfl
    rw [htake, List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons]
    rw [validDecomp_cons]
    refine ⟨?_, ih (Nat.le_of_lt ht_lt)⟩
    let r := rounds[t]'ht_lt
    let prev := (Finset.univ.filter fun j : Fin rounds.length =>
      j.val < t).biUnion (fun j => (rounds[j.val]'j.isLt).verts)
    have hsub1 : compVerts (toGlobalEnds r).2 ⊆ r.verts := by
      intro x hx
      simp only [compVerts, Finset.mem_biUnion, Finset.mem_univ, Sym2.mem_toFinset, true_and] at hx
      obtain ⟨i, hxi⟩ := hx
      have hi : i.val < r.compGlobal.length := by simpa [toGlobalEnds] using i.isLt
      have he := (hrounds ⟨t, ht_lt⟩).1 _ (List.getElem_mem hi)
      dsimp only [toGlobalEnds, edgeEnds] at hxi
      simp only [List.getElem_map, IndexedEdge.toWeighted, Sym2.mem_iff] at hxi
      rcases hxi with rfl | rfl
      exacts [he.1, he.2]
    have hsub2 : compVertsList ((rounds.take t).reverse.map toGlobalEnds) ⊆ prev := by
      intro x hx
      obtain ⟨q, hq_rev, hxq⟩ := compVertsList_subset_rounds (rounds.take t).reverse
        (fun q hq => by
          have hq_take : q ∈ rounds.take t := List.mem_reverse.mp hq
          obtain ⟨j, hj, hqj⟩ := List.getElem_of_mem hq_take
          have hj_lt : j < t := by
            rw [List.length_take] at hj; exact lt_of_lt_of_le hj (Nat.min_le_left _ _)
          have hj_r : j < rounds.length := lt_trans hj_lt ht_lt
          have hqr : q = rounds[j]'hj_r := by simpa [List.getElem_take] using hqj.symm
          rw [hqr]
          exact (hrounds ⟨j, hj_r⟩).1) x hx
      have hq_take : q ∈ rounds.take t := List.mem_reverse.mp hq_rev
      obtain ⟨j, hj, hqj⟩ := List.getElem_of_mem hq_take
      have hj_lt : j < t := by
        rw [List.length_take] at hj; exact lt_of_lt_of_le hj (Nat.min_le_left _ _)
      have hj_r : j < rounds.length := lt_trans hj_lt ht_lt
      have hqr : q = rounds[j]'hj_r := by simpa [List.getElem_take] using hqj.symm
      exact Finset.mem_biUnion.mpr ⟨⟨j, hj_r⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_lt⟩, hqr ▸ hxq⟩
    exact (Finset.card_le_card (Finset.inter_subset_inter hsub1 hsub2)).trans
      (hrounds ⟨t, ht_lt⟩).2

private theorem edgeUnionList_ends_equiv {n : ℕ} (L : List (List (WeightedEdge n ℕ))) :
    let Cs := L.map fun xs => (⟨xs.length, edgeEnds xs⟩ : Σ e, Fin e → Sym2 (Fin n))
    ∃ σ : Fin (edgeCountList Cs) ≃ Fin L.flatten.length,
      ∀ i : Fin (edgeCountList Cs),
        edgeUnionList Cs i = s(L.flatten[(σ i).val].u, L.flatten[(σ i).val].v) := by
  induction L with
  | nil =>
    simp only [List.flatten_nil, List.length_nil]
    exact ⟨Equiv.refl (Fin 0), fun i => Fin.elim0 i⟩
  | cons xs rest ih =>
    obtain ⟨σ_r, hσ_r⟩ := ih
    dsimp only [List.map_cons, edgeCountList, edgeUnionList, List.flatten_cons]
    let m1 := xs.length
    let m2 := edgeCountList (rest.map fun ys => (⟨ys.length, edgeEnds ys⟩ :
      Σ e, Fin e → Sym2 (Fin n)))
    have hlen : m1 + rest.flatten.length = (xs ++ rest.flatten).length := by simp [m1]
    let e_sum : Fin (m1 + m2) ≃ Fin m1 ⊕ Fin m2 := finSumFinEquiv.symm
    let e_rhs : Fin m1 ⊕ Fin rest.flatten.length ≃ Fin (xs ++ rest.flatten).length :=
      finSumFinEquiv.trans (Fin.castOrderIso hlen).toEquiv
    let σ : Fin (m1 + m2) ≃ Fin (xs ++ rest.flatten).length :=
      (e_sum.trans (Equiv.sumCongr (Equiv.refl _) σ_r)).trans e_rhs
    refine ⟨σ, fun i => ?_⟩
    have hi_lt : i.val < m1 + m2 := i.isLt
    rcases Nat.lt_or_ge i.val m1 with hi | hi
    · let j : Fin m1 := ⟨i.val, hi⟩
      have hj : Fin.castAdd m2 j = i := Fin.ext rfl
      have h1 : e_sum i = .inl j := by
        change finSumFinEquiv.symm i = .inl j
        rw [← hj]; exact finSumFinEquiv.symm_apply_apply (.inl j)
      have hσ_val : (σ i).val = j.val := by
        change ((finSumFinEquiv.trans (Fin.castOrderIso hlen).toEquiv)
          ((Equiv.sumCongr (Equiv.refl _) σ_r) (e_sum i))).val = j.val
        rw [h1]; rfl
      have hσ_val' : (σ (Fin.castAdd m2 j)).val = j.val := by rw [hj]; exact hσ_val
      rw [← hj]
      change edgeUnion (edgeEnds xs) _ (Fin.castAdd m2 j) = _
      rw [edgeUnion_castAdd]
      simp only [hσ_val', List.getElem_append_left j.isLt]
      rfl
    · let j : Fin m2 := ⟨i.val - m1, Nat.sub_lt_left_of_lt_add hi hi_lt⟩
      have hj : Fin.natAdd m1 j = i := Fin.ext (Nat.add_sub_cancel' hi)
      have h1 : e_sum i = .inr j := by
        change finSumFinEquiv.symm i = .inr j
        rw [← hj]; exact finSumFinEquiv.symm_apply_apply (.inr j)
      have hσ_val : (σ i).val = m1 + (σ_r j).val := by
        change ((finSumFinEquiv.trans (Fin.castOrderIso hlen).toEquiv)
          ((Equiv.sumCongr (Equiv.refl _) σ_r) (e_sum i))).val = m1 + (σ_r j).val
        rw [h1]; rfl
      have hσ_val' : (σ (Fin.natAdd m1 j)).val = m1 + (σ_r j).val := by rw [hj]; exact hσ_val
      rw [← hj]
      change edgeUnion (edgeEnds xs) _ (Fin.natAdd m1 j) = _
      rw [edgeUnion_natAdd]
      have hge : m1 ≤ m1 + (σ_r j).val := Nat.le_add_right _ _
      simp only [hσ_val', List.getElem_append_right hge, m1, Nat.add_sub_cancel_left]
      exact hσ_r j

private theorem edgeUnionList_isSimple_of_subperm {n : ℕ}
    (L : List (List (WeightedEdge n ℕ))) (es : List (WeightedEdge n ℕ))
    (hsub : L.flatten.Subperm es) (hsimp : IsSimple (edgeEnds es)) :
    IsSimple (edgeUnionList (L.map fun xs =>
      (⟨xs.length, edgeEnds xs⟩ : Σ e, Fin e → Sym2 (Fin n)))) := by
  obtain ⟨σ, hσ⟩ := edgeUnionList_ends_equiv L
  have hsimp' := (isSimple_iff _).mp hsimp
  have hnd_es : (es.map fun e : WeightedEdge n ℕ => s(e.u, e.v)).Nodup :=
    List.nodup_iff_injective_get.mpr fun i j hij => by
      have heq : edgeEnds es ⟨i.val, by simpa only [List.length_map] using i.isLt⟩ =
          edgeEnds es ⟨j.val, by simpa only [List.length_map] using j.isLt⟩ := by
        simpa [edgeEnds, List.get_eq_getElem] using hij
      exact Fin.ext (congrArg (Fin.val : Fin es.length → ℕ) (hsimp'.2 heq))
  let endsFlat := L.flatten.map fun e : WeightedEdge n ℕ => s(e.u, e.v)
  have hnd_flat : endsFlat.Nodup := (List.subperm_map _ hsub).nodup hnd_es
  rw [isSimple_iff]
  refine ⟨fun i => ?_, fun i₁ i₂ hij => ?_⟩
  · rw [hσ i]
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem (hsub.subset (List.getElem_mem (σ i).isLt))
    have hne := hsimp'.1 ⟨j, by simpa using hj⟩
    dsimp only [edgeEnds] at hne
    rwa [hje] at hne
  · rw [hσ i₁, hσ i₂] at hij
    have heq : endsFlat.get ⟨(σ i₁).val, by simpa only [endsFlat, List.length_map] using
          (σ i₁).isLt⟩ =
        endsFlat.get ⟨(σ i₂).val, by simpa only [endsFlat, List.length_map] using
          (σ i₂).isLt⟩ := by
      simpa only [endsFlat, List.get_eq_getElem, List.getElem_map] using hij
    exact σ.injective (Fin.ext (congrArg (Fin.val : Fin endsFlat.length → ℕ)
      (List.nodup_iff_injective_get.mp hnd_flat heq)))

private theorem map_compGlobal_flatten {n : ℕ} (qs : List (PartitionRoundWitness n)) :
    (qs.map fun r => r.compGlobal.map IndexedEdge.toWeighted).flatten =
      (qs.flatMap PartitionRoundWitness.compGlobal).map IndexedEdge.toWeighted := by
  rw [List.flatMap_def, List.map_flatten, List.map_map]; rfl

private theorem sum_compGlobal_length {n : ℕ} (qs : List (PartitionRoundWitness n)) :
    ((qs.map toGlobalEnds).map Sigma.fst).sum =
      (qs.map fun r => r.compGlobal.map IndexedEdge.toWeighted).flatten.length := by
  rw [List.length_flatten, List.map_map, List.map_map]; rfl

/-- Step toward Theorem 5.8 of [PettieRamachandran2002] (#8624), adapting Lemma 3.3 (§3.2,
pp. 21–22) via Property 5.3 and Corollary 5.6 (§5.1, pp. 25–26): for component subgraphs
`r.compLocal` emitted across a witness list `rounds` whose global vertex sets `r.verts` overlap
earlier rounds in at most one vertex (`(r.verts ∩ ...).card ≤ 1`), the sum of optimal
decision-tree depths `optDepth` is at most `optDepthMN es.length n`. -/
theorem partition_optDepth_sum_le {n : ℕ} {es : List (IndexedEdge n)}
    {rounds : List (PartitionRoundWitness n)}
    (hsimp : IsSimple (edgeEnds (es.map IndexedEdge.toWeighted)))
    (hsub : (rounds.flatMap PartitionRoundWitness.compGlobal).Subperm es)
    (hrounds : ∀ i : Fin rounds.length,
      let r := rounds[i.val]'i.isLt
      Function.Injective r.lift ∧
      (∀ e ∈ r.compGlobal, e.u ∈ r.verts ∧ e.v ∈ r.verts) ∧
      (r.verts ∩ (Finset.univ.filter fun j : Fin rounds.length =>
        j.val < i.val).biUnion (fun j => (rounds[j.val]'j.isLt).verts)).card ≤ 1) :
    (rounds.map fun r =>
      optDepth (edgeEnds (r.compLocal.map IndexedEdge.toWeighted))).sum ≤
      optDepthMN es.length n := by
  let Cs := rounds.reverse.map toGlobalEnds
  have hV : ValidDecomp Cs := by
    have h := validDecomp_rounds_take_reverse rounds
      (fun i => ⟨(hrounds i).2.1, (hrounds i).2.2⟩) rounds.length le_rfl
    rw [List.take_length] at h
    exact h
  have hsub_es : ((rounds.reverse.map fun r =>
      r.compGlobal.map IndexedEdge.toWeighted).flatten).Subperm
      (es.map IndexedEdge.toWeighted) := by
    rw [map_compGlobal_flatten]
    have hp1 : (rounds.reverse.flatMap PartitionRoundWitness.compGlobal).Perm
        (rounds.flatMap PartitionRoundWitness.compGlobal) :=
      (List.reverse_perm _).flatMap fun _ _ => List.Perm.refl _
    exact List.subperm_map _ (hp1.subperm.trans hsub)
  have hCs_eq : Cs = (rounds.reverse.map fun r =>
      r.compGlobal.map IndexedEdge.toWeighted).map fun xs =>
      (⟨xs.length, edgeEnds xs⟩ : Σ e, Fin e → Sym2 (Fin n)) := by
    simp [Cs, List.map_map, Function.comp_def, toGlobalEnds]
  have hCs_simp : IsSimple (edgeUnionList Cs) := by
    rw [hCs_eq]
    exact edgeUnionList_isSimple_of_subperm _ _ hsub_es hsimp
  have hm_le : (Cs.map Sigma.fst).sum ≤ es.length := by
    have h1 := hsub_es.length_le
    rw [List.length_map] at h1
    have hsum_eq := sum_compGlobal_length rounds.reverse
    exact (le_of_eq hsum_eq).trans h1
  have hlem := sum_optDepth_le_optDepthMN Cs hV hCs_simp hm_le
  have hsum_loc : (rounds.map fun r =>
      optDepth (edgeEnds (r.compLocal.map IndexedEdge.toWeighted))).sum =
      (Cs.map fun c => optDepth c.2).sum := by
    have heq_r : rounds.map (fun r => optDepth (edgeEnds
        (r.compLocal.map IndexedEdge.toWeighted))) =
        rounds.map (fun r => optDepth (toGlobalEnds r).2) := by
      refine List.map_congr_left fun r hr => ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      exact optDepth_compLocal_eq_global _ (hrounds ⟨i, hi⟩).1
    rw [heq_r]
    have hperm_m : (rounds.map fun r => optDepth (toGlobalEnds r).2).Perm
        (Cs.map fun c => optDepth c.2) := by
      dsimp only [Cs]
      rw [List.map_map]
      exact (List.reverse_perm rounds).symm.map _
    exact hperm_m.sum_eq
  exact hsum_loc ▸ hlem

/-! ## Section 3: Conglomerate Active-Vertex Bound -/

private theorem verts_conglom_eq {n nConglom : ℕ}
    {rounds : List (PartitionRoundWitness n)} {conglomFn : Fin n → Fin nConglom}
    (hconglom_rel : ∀ x y : Fin n, conglomFn x = conglomFn y ↔
      (edgePartition (rounds.flatMap fun r => r.tree.treeEdges)).rel x y = true)
    {r : PartitionRoundWitness n} (hr : r ∈ rounds) {x : Fin n} (hx : x ∈ r.verts) :
    conglomFn x = conglomFn r.tree.root := by
  have hc := r.tree.joins_treeVerts hx
  clear hx
  have hrel_r : (edgePartition r.tree.treeEdges).rel r.tree.root x = true := by
    induction hc with
    | refl => exact (edgePartition _).refl _
    | @tail b c _ hstep ih =>
      obtain ⟨s, _, hends⟩ := hstep
      have he_mem : r.tree.edge s ∈ r.tree.treeEdges :=
        List.mem_map.mpr ⟨s, List.mem_finRange s, rfl⟩
      have hrel_s := rel_edgePartitionFrom_of_mem (Partition.discrete n) he_mem
      dsimp only [DynamicDJPTree.ends] at hends
      rcases Sym2.eq_iff.mp hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (edgePartition _).trans ih hrel_s
      · exact (edgePartition _).trans ih ((edgePartition _).symm hrel_s)
  have hsub : r.tree.treeEdges.Subperm (rounds.flatMap fun q => q.tree.treeEdges) := by
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hr
    simp only [List.flatMap_append, List.flatMap_cons]
    exact ((List.sublist_append_left _ _).trans (List.sublist_append_right _ _)).subperm
  exact ((hconglom_rel x r.tree.root).mpr
    ((edgePartition _).symm (edgePartition_mono_subperm hsub hrel_r)))

/-- Step toward Theorem 5.8 of [PettieRamachandran2002] (#8624), proving the
active-conglomerate stopping bound of Lemma 3.3 (§3.2, pp. 21–22): any set of `n_a` conglomerate
labels incident to edges in `H_rem` satisfies `n_a * maxsize ≤ n`. -/
theorem partition_conglom_active_verts_le {n nConglom n_a maxsize : ℕ}
    {rounds : List (PartitionRoundWitness n)} {H_rem : List (IndexedEdge n)}
    {conglomFn : Fin n → Fin nConglom} {lift_a : Fin n_a → Fin nConglom}
    (hcov : ∀ x : Fin n, ∃ r ∈ rounds, x ∈ r.verts)
    (hconglom_rel : ∀ x y : Fin n, conglomFn x = conglomFn y ↔
      (edgePartition (rounds.flatMap fun r => r.tree.treeEdges)).rel x y = true)
    (hstop : ∀ i : Fin rounds.length,
      maxsize ≤ (rounds[i.val]'i.isLt).verts.card ∨
      (∃ j : Fin rounds.length, j.val < i.val ∧
        ((rounds[i.val]'i.isLt).verts ∩ (rounds[j.val]'j.isLt).verts).Nonempty) ∨
      ((∀ j : Fin rounds.length, j ≠ i →
        ¬((rounds[i.val]'i.isLt).verts ∩ (rounds[j.val]'j.isLt).verts).Nonempty) ∧
        ∀ e ∈ H_rem, e.u ∉ (rounds[i.val]'i.isLt).verts ∧
          e.v ∉ (rounds[i.val]'i.isLt).verts))
    (hlift_inj : Function.Injective lift_a)
    (hactive : ∀ y : Fin n_a, ∃ e ∈ H_rem,
      conglomFn e.u = lift_a y ∨ conglomFn e.v = lift_a y) :
    n_a * maxsize ≤ n := by
  let V_comp : Fin rounds.length → Finset (Fin n) := fun i => (rounds[i.val]'i.isLt).verts
  have hstop' : ∀ i : Fin rounds.length,
      maxsize ≤ (V_comp i).card ∨
      (∃ j : Fin rounds.length, j.val < i.val ∧ (V_comp i ∩ V_comp j).Nonempty) ∨
      ¬ ∃ i' : Fin rounds.length, i' ≠ i ∧ (V_comp i ∩ V_comp i').Nonempty := fun i => by
    rcases hstop i with h1 | h2 | ⟨h3, _⟩
    · exact .inl h1
    · exact .inr (.inl h2)
    · exact .inr (.inr fun ⟨i', hne, hinter⟩ => h3 i' hne hinter)
  have hcard_c : ∀ y : Fin n_a,
      maxsize ≤ (Finset.univ.filter fun x : Fin n => conglomFn x = lift_a y).card := by
    intro y
    let c := lift_a y
    let I_c : Finset (Fin rounds.length) := Finset.univ.filter fun i =>
      conglomFn (rounds[i.val]'i.isLt).tree.root = c
    obtain ⟨e_act, he_act, hact_eq⟩ := hactive y
    let x_act : Fin n := if conglomFn e_act.u = c then e_act.u else e_act.v
    have hx_act_c : conglomFn x_act = c := by
      dsimp only [x_act]; split_ifs with h
      · exact h
      · exact hact_eq.resolve_left h
    obtain ⟨r_act, hr_act, hxr_act⟩ := hcov x_act
    obtain ⟨i_act, hi_act, rfl⟩ := List.getElem_of_mem hr_act
    have hI_ne : I_c.Nonempty := ⟨⟨i_act, hi_act⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (verts_conglom_eq hconglom_rel hr_act hxr_act).symm.trans hx_act_c⟩⟩
    have hclosed : ∀ i ∈ I_c, ∀ j : Fin rounds.length,
        (V_comp i ∩ V_comp j).Nonempty → j ∈ I_c := by
      intro i hi j ⟨z, hz⟩
      rw [Finset.mem_inter] at hz
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hzi := verts_conglom_eq hconglom_rel (List.getElem_mem i.isLt) hz.1
      have hzj := verts_conglom_eq hconglom_rel (List.getElem_mem j.isLt) hz.2
      exact hzj.symm.trans (hzi.trans hi.2)
    have hI_conn : ∀ J : Finset (Fin rounds.length), J.Nonempty → J ⊂ I_c →
        ∃ a ∈ J, ∃ b ∈ I_c \ J, (V_comp a ∩ V_comp b).Nonempty := by
      intro J ⟨a₀, ha₀⟩ hJ_sub
      have hne_diff : (I_c \ J).Nonempty := Finset.sdiff_nonempty.mpr (fun h => hJ_sub.not_subset h)
      obtain ⟨b₀, hb₀⟩ := hne_diff
      have hca := (Finset.mem_filter.mp (hJ_sub.1 ha₀)).2
      have hcb := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb₀).1).2
      have hrel := (hconglom_rel _ _).mp (hca.trans hcb.symm)
      rw [rel_edgePartition_iff_eqvGen] at hrel
      let U_J : Finset (Fin n) := J.biUnion V_comp
      have ha₀_mem : (rounds[a₀.val]'a₀.isLt).tree.root ∈ U_J :=
        Finset.mem_biUnion.mpr ⟨a₀, ha₀,
          mem_djpVerts_mono _ _ (Nat.zero_le _) (Finset.mem_singleton_self _)⟩
      have hb₀_mem : (rounds[b₀.val]'b₀.isLt).tree.root ∈ V_comp b₀ :=
        mem_djpVerts_mono _ _ (Nat.zero_le _) (Finset.mem_singleton_self _)
      by_cases hb_in : (rounds[b₀.val]'b₀.isLt).tree.root ∈ U_J
      · rw [Finset.mem_biUnion] at hb_in
        obtain ⟨a, haJ, hba⟩ := hb_in
        exact ⟨a, haJ, b₀, hb₀, _, Finset.mem_inter.mpr ⟨hba, hb₀_mem⟩⟩
      · have hbridge : ∀ u v : Fin n,
            Relation.EqvGen (fun a b => ∃ f ∈ rounds.flatMap (fun r => r.tree.treeEdges),
              a = f.u ∧ b = f.v) u v →
            (u ∈ U_J → v ∉ U_J →
              ∃ a ∈ J, ∃ b ∈ I_c \ J, (V_comp a ∩ V_comp b).Nonempty) ∧
            (v ∈ U_J → u ∉ U_J →
              ∃ a ∈ J, ∃ b ∈ I_c \ J, (V_comp a ∩ V_comp b).Nonempty) := by
          intro u v huv
          induction huv with
          | refl _ => exact ⟨fun hu hnu => absurd hu hnu, fun hu hnu => absurd hu hnu⟩
          | symm _ _ _ ih => exact ⟨ih.2, ih.1⟩
          | trans _ y _ _ _ ih1 ih2 =>
            refine ⟨fun hx hnz => ?_, fun hz hnx => ?_⟩
            · by_cases hy : y ∈ U_J
              · exact ih2.1 hy hnz
              · exact ih1.1 hx hy
            · by_cases hy : y ∈ U_J
              · exact ih1.2 hy hnx
              · exact ih2.2 hz hy
          | rel _ _ hxy =>
            obtain ⟨f, hf, rfl, rfl⟩ := hxy
            rw [List.mem_flatMap] at hf
            obtain ⟨q, hq, hfq⟩ := hf
            obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
            dsimp only [DynamicDJPTree.treeEdges] at hfq
            rw [List.mem_map] at hfq
            obtain ⟨s_step, _, hfs⟩ := hfq
            have hmem_e := (rounds[k]'hk).tree.mem_treeVerts_of_edge s_step
            have hfu : f.u ∈ V_comp ⟨k, hk⟩ := by
              rw [← hfs]; exact mem_djpVerts_mono _ _ s_step.isLt hmem_e.1
            have hfv : f.v ∈ V_comp ⟨k, hk⟩ := by
              rw [← hfs]; exact mem_djpVerts_mono _ _ s_step.isLt hmem_e.2
            have step : ∀ {p₁ p₂ : Fin n}, p₁ ∈ V_comp ⟨k, hk⟩ → p₂ ∈ V_comp ⟨k, hk⟩ →
                p₁ ∈ U_J → p₂ ∉ U_J →
                ∃ a ∈ J, ∃ b ∈ I_c \ J, (V_comp a ∩ V_comp b).Nonempty :=
              fun hp₁ hp₂ hp₁U hp₂nU => by
                rw [Finset.mem_biUnion] at hp₁U
                obtain ⟨a, haJ, hpa⟩ := hp₁U
                have hk_I : ⟨k, hk⟩ ∈ I_c :=
                  hclosed a (hJ_sub.1 haJ) ⟨k, hk⟩ ⟨_, Finset.mem_inter.mpr ⟨hpa, hp₁⟩⟩
                have hk_notJ : (⟨k, hk⟩ : Fin rounds.length) ∉ J := fun hkJ =>
                  hp₂nU (Finset.mem_biUnion.mpr ⟨⟨k, hk⟩, hkJ, hp₂⟩)
                exact ⟨a, haJ, ⟨k, hk⟩, Finset.mem_sdiff.mpr ⟨hk_I, hk_notJ⟩,
                  ⟨_, Finset.mem_inter.mpr ⟨hpa, hp₁⟩⟩⟩
            exact ⟨step hfu hfv, step hfv hfu⟩
        exact (hbridge _ _ hrel).1 ha₀_mem hb_in
    have hlem := maxsize_le_card_biUnion_of_stop V_comp hstop' I_c hI_ne hclosed hI_conn
    have hsub_Sc : I_c.biUnion V_comp ⊆
        Finset.univ.filter fun x : Fin n => conglomFn x = c := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_univ _,
        (verts_conglom_eq hconglom_rel (List.getElem_mem i.isLt) hxi).trans hi.2⟩
    have hsz_big : maxsize ≤ (I_c.biUnion V_comp).card := by
      rcases hlem with hbig | ⟨hcard1, i₀, hi₀, hiso⟩
      · exact hbig
      · rcases hstop i₀ with h1 | ⟨j, hj_lt, hj_int⟩ | ⟨_, hno_rem⟩
        · exact h1.trans (Finset.card_le_card (Finset.subset_biUnion_of_mem V_comp hi₀))
        · exact absurd ⟨j, fun h => by subst h; exact Nat.lt_irrefl _ hj_lt, hj_int⟩ hiso
        · exfalso
          have hi_eq : (⟨i_act, hi_act⟩ : Fin rounds.length) = i₀ :=
            Finset.card_le_one.mp hcard1.le ⟨i_act, hi_act⟩
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                (verts_conglom_eq hconglom_rel hr_act hxr_act).symm.trans hx_act_c⟩)
              i₀ hi₀
          have hx_i0 : x_act ∈ (rounds[i₀.val]'i₀.isLt).verts := by
            rw [← hi_eq]; exact hxr_act
          have hno := hno_rem e_act he_act
          dsimp only [x_act] at hx_i0
          split_ifs at hx_i0
          · exact hno.1 hx_i0
          · exact hno.2 hx_i0
    exact hsz_big.trans (Finset.card_le_card hsub_Sc)
  let S : Fin n_a → Finset (Fin n) := fun y =>
    Finset.univ.filter fun x : Fin n => conglomFn x = lift_a y
  have hdisj : ((Finset.univ : Finset (Fin n_a)) : Set (Fin n_a)).PairwiseDisjoint S :=
    fun y₁ _ y₂ _ hne => Finset.disjoint_left.mpr fun x hx1 hx2 => by
      rw [Finset.mem_filter] at hx1 hx2
      exact hne (hlift_inj (hx1.2.symm.trans hx2.2))
  have hsum_le : ∑ y : Fin n_a, (S y).card ≤ n := by
    rw [← Finset.card_biUnion hdisj]
    have hc := Finset.card_le_univ ((Finset.univ : Finset (Fin n_a)).biUnion S)
    simpa [Fintype.card_fin] using hc
  have hmul : n_a * maxsize ≤ ∑ y : Fin n_a, (S y).card := by
    calc n_a * maxsize
        = ∑ _y : Fin n_a, maxsize := by simp
      _ ≤ ∑ y : Fin n_a, (S y).card := Finset.sum_le_sum fun y _ => hcard_c y
  exact hmul.trans hsum_le

/-! ## Section 4: Weak-Support MSF Lifting Bridge -/

private theorem edgePartition_mono_subset {n : ℕ} {A B : List (WeightedEdge n ℕ)}
    (hsub : ∀ e ∈ A, e ∈ B) {u v : Fin n} (h : (edgePartition A).rel u v = true) :
    (edgePartition B).rel u v = true := by
  rw [rel_edgePartition_iff_eqvGen] at h ⊢
  exact h.mono fun _ _ ⟨e, he, h1, h2⟩ => ⟨e, hsub e he, h1, h2⟩

private theorem mem_djpVerts_last {n : ℕ} (D : DynamicDJPTree n) (hpos : 0 < D.numSteps)
    {z : Fin n} (hz : z ∈ D.treeVerts D.numSteps)
    (hne : z ≠ D.vOut ⟨D.numSteps - 1, Nat.sub_lt hpos Nat.one_pos⟩) :
    z ∈ D.treeVerts (D.numSteps - 1) := by
  have h : ∀ s : ℕ, s = (D.numSteps - 1) + 1 →
      z ∈ djpVerts D.root D.vOut s → z ∈ djpVerts D.root D.vOut (D.numSteps - 1) := by
    rintro _ rfl hm
    dsimp only [djpVerts] at hm
    simp only [Nat.sub_lt hpos Nat.one_pos, ↓reduceDIte, Finset.mem_insert] at hm
    exact hm.resolve_left hne
  exact h D.numSteps (Nat.sub_add_cancel hpos).symm hz

private theorem djpVerts_truncate {n : ℕ} (D : DynamicDJPTree n) (k : ℕ) (hk : k ≤ D.numSteps) :
    ∀ m ≤ k, djpVerts D.root (fun s : Fin k => D.vOut ⟨s.val, Nat.lt_of_lt_of_le s.isLt hk⟩) m =
      djpVerts D.root D.vOut m
  | 0, _ => rfl
  | m + 1, hm => by
    have hmk : m < k := hm
    have hmd : m < D.numSteps := Nat.lt_of_lt_of_le hmk hk
    dsimp only [djpVerts]
    simp only [hmk, hmd, ↓reduceDIte]
    rw [djpVerts_truncate D k hk m (Nat.le_of_lt hmk)]

private def truncateDJP {n : ℕ} (D : DynamicDJPTree n) (k : ℕ) (hk : k ≤ D.numSteps) :
    DynamicDJPTree n where
  numSteps := k
  root := D.root
  edge s := D.edge ⟨s.val, Nat.lt_of_lt_of_le s.isLt hk⟩
  wPop s := D.wPop ⟨s.val, Nat.lt_of_lt_of_le s.isLt hk⟩
  vIn s := D.vIn ⟨s.val, Nat.lt_of_lt_of_le s.isLt hk⟩
  vOut s := D.vOut ⟨s.val, Nat.lt_of_lt_of_le s.isLt hk⟩
  edge_weight_le_wPop s := D.edge_weight_le_wPop ⟨s.val, Nat.lt_of_lt_of_le s.isLt hk⟩
  ends_match s := D.ends_match ⟨s.val, Nat.lt_of_lt_of_le s.isLt hk⟩
  vIn_mem s := by
    rw [djpVerts_truncate D k hk s.val (Nat.le_of_lt s.isLt)]
    exact D.vIn_mem ⟨s.val, Nat.lt_of_lt_of_le s.isLt hk⟩
  vOut_not_mem s := by
    rw [djpVerts_truncate D k hk s.val (Nat.le_of_lt s.isLt)]
    exact D.vOut_not_mem ⟨s.val, Nat.lt_of_lt_of_le s.isLt hk⟩
  djp_future s s' hlt hcross := by
    rw [djpVerts_truncate D k hk s.val (Nat.le_of_lt s.isLt)] at hcross
    exact D.djp_future ⟨s.val, Nat.lt_of_lt_of_le s.isLt hk⟩
      ⟨s'.val, Nat.lt_of_lt_of_le s'.isLt hk⟩ hlt hcross

private def partPrevSet {n : ℕ} (rounds : List (PartitionRoundWitness n))
    (k : Fin rounds.length) : Finset (Fin n) :=
  (Finset.univ.filter fun j : Fin rounds.length => j.val < k.val).biUnion
    (fun j => (rounds[j.val]'j.isLt).verts)

private theorem exists_round_of_mem {n : ℕ} (rounds : List (PartitionRoundWitness n))
    (hcov : ∀ x : Fin n, ∃ r ∈ rounds, x ∈ r.verts) (z : Fin n) :
    ∃ i : ℕ, ∃ hi : i < rounds.length, z ∈ (rounds[i]'hi).verts := by
  obtain ⟨r, hr, hzr⟩ := hcov z
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  exact ⟨i, hi, hzr⟩

private noncomputable def partRoundOf {n : ℕ} (rounds : List (PartitionRoundWitness n))
    (hcov : ∀ x : Fin n, ∃ r ∈ rounds, x ∈ r.verts) (z : Fin n) : Fin rounds.length :=
  ⟨Nat.find (exists_round_of_mem rounds hcov z),
   (Nat.find_spec (exists_round_of_mem rounds hcov z)).1⟩

private theorem partRoundOf_mem {n : ℕ} (rounds : List (PartitionRoundWitness n))
    (hcov : ∀ x : Fin n, ∃ r ∈ rounds, x ∈ r.verts) (z : Fin n) :
    z ∈ (rounds[(partRoundOf rounds hcov z).val]'(partRoundOf rounds hcov z).isLt).verts :=
  (Nat.find_spec (exists_round_of_mem rounds hcov z)).2

private theorem partRoundOf_min {n : ℕ} (rounds : List (PartitionRoundWitness n))
    (hcov : ∀ x : Fin n, ∃ r ∈ rounds, x ∈ r.verts) (z : Fin n) (j : Fin rounds.length)
    (hj : j.val < (partRoundOf rounds hcov z).val) :
    z ∉ (rounds[j.val]'j.isLt).verts := fun hmem =>
  Nat.find_min (exists_round_of_mem rounds hcov z) hj ⟨j.isLt, hmem⟩

private noncomputable def partRootOf {n : ℕ} (rounds : List (PartitionRoundWitness n))
    (hcov : ∀ x : Fin n, ∃ r ∈ rounds, x ∈ r.verts)
    (k : Fin rounds.length) : Fin rounds.length :=
  if h : (partPrevSet rounds k ∩ (rounds[k.val]'k.isLt).verts).Nonempty then
    partRootOf rounds hcov (partRoundOf rounds hcov h.choose)
  else k
termination_by k.val
decreasing_by
  have hmem : h.choose ∈ partPrevSet rounds k := (Finset.mem_inter.mp h.choose_spec).1
  dsimp only [partPrevSet] at hmem
  rw [Finset.mem_biUnion] at hmem
  obtain ⟨j, hj, hxj⟩ := hmem
  rw [Finset.mem_filter] at hj
  by_contra hge
  have hlt : j.val < (partRoundOf rounds hcov h.choose).val := lt_of_lt_of_le hj.2 (not_lt.mp hge)
  exact partRoundOf_min rounds hcov h.choose j hlt hxj

private theorem partRootOf_eq_of_inter {n : ℕ} (rounds : List (PartitionRoundWitness n))
    (hcov : ∀ x : Fin n, ∃ r ∈ rounds, x ∈ r.verts)
    (hstop_prev : ∀ i : Fin rounds.length, ∀ x ∈ (rounds[i.val]'i.isLt).verts,
      x ∈ partPrevSet rounds i → ∃ hpos : 0 < (rounds[i.val]'i.isLt).tree.numSteps,
        x = (rounds[i.val]'i.isLt).tree.vOut
          ⟨(rounds[i.val]'i.isLt).tree.numSteps - 1, Nat.sub_lt hpos Nat.one_pos⟩) :
    ∀ s : ℕ, ∀ j₁ j₂ : Fin rounds.length, j₁.val + j₂.val ≤ s →
      ((rounds[j₁.val]'j₁.isLt).verts ∩ (rounds[j₂.val]'j₂.isLt).verts).Nonempty →
      partRootOf rounds hcov j₁ = partRootOf rounds hcov j₂ := by
  intro s
  induction s with
  | zero =>
    intro j₁ j₂ hs _
    have h1 : j₁.val = 0 := by omega
    have h2 : j₂.val = 0 := by omega
    exact congrArg (partRootOf rounds hcov) (Fin.ext (h1.trans h2.symm))
  | succ s ih =>
    have step : ∀ {a b : Fin rounds.length} {z : Fin n},
        a.val < b.val → a.val + b.val ≤ s + 1 →
        z ∈ (rounds[a.val]'a.isLt).verts → z ∈ (rounds[b.val]'b.isLt).verts →
        partRootOf rounds hcov a = partRootOf rounds hcov b := by
      intro a b z hlt hs hza hzb
      have hz_prev : z ∈ partPrevSet rounds b := Finset.mem_biUnion.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, hza⟩
      have hne : (partPrevSet rounds b ∩ (rounds[b.val]'b.isLt).verts).Nonempty :=
        ⟨z, Finset.mem_inter.mpr ⟨hz_prev, hzb⟩⟩
      have hchoose_eq : hne.choose = z := by
        have hc := Finset.mem_inter.mp hne.choose_spec
        obtain ⟨_, heq1⟩ := hstop_prev b hne.choose hc.2 hc.1
        obtain ⟨_, heq2⟩ := hstop_prev b z hzb hz_prev
        exact heq1.trans heq2.symm
      conv_rhs => rw [partRootOf]; simp only [hne, ↓reduceDIte]
      have hjr_le : (partRoundOf rounds hcov hne.choose).val ≤ a.val := by
        by_contra hgt'
        exact partRoundOf_min rounds hcov hne.choose a (not_le.mp hgt') (hchoose_eq ▸ hza)
      exact ih a (partRoundOf rounds hcov hne.choose) (by omega)
        ⟨z, Finset.mem_inter.mpr ⟨hza, hchoose_eq ▸ partRoundOf_mem rounds hcov hne.choose⟩⟩
    intro j₁ j₂ hs ⟨z, hz⟩
    rw [Finset.mem_inter] at hz
    rcases Nat.lt_trichotomy j₁.val j₂.val with hlt | heq | hgt
    · exact step hlt hs hz.1 hz.2
    · exact congrArg (partRootOf rounds hcov) (Fin.ext heq)
    · exact (step hgt (by omega) hz.2 hz.1).symm

/-- Step toward Theorem 5.8 of [PettieRamachandran2002] (#8624), proving the multi-round
dynamic-DJP conglomerate weak-support lifting step of Lemma 3.2 (§3.1, p. 20): if `F_comps[i]` is
an MSF of `rounds[i].compGlobal` for each round `i`, `H_lift` is a subpermutation of `H_rem` whose
contraction along `conglomFn` is an MSF of the contracted `H_rem`, and `F` is an MSF of
`F_comps.flatten ++ H_lift ++ M_C`, then `F` is an MSF of the full input graph `es`. -/
theorem partition_isMinSpanningForest {n nConglom : ℕ}
    {es : List (WeightedEdge n ℕ)} {rounds : List (PartitionRoundWitness n)}
    {H_rem : List (IndexedEdge n)} {conglomFn : Fin n → Fin nConglom}
    {F_comps : List (List (WeightedEdge n ℕ))} {H_lift F : List (WeightedEdge n ℕ)}
    (hperm : (((rounds.flatMap PartitionRoundWitness.compGlobal) ++ H_rem ++
      (rounds.flatMap PartitionRoundWitness.corrEdges)).map IndexedEdge.toWeighted).Perm es)
    (hcov : ∀ x : Fin n, ∃ r ∈ rounds, x ∈ r.verts)
    (hconglom_rel : ∀ x y : Fin n, conglomFn x = conglomFn y ↔
      (edgePartition (rounds.flatMap fun r => r.tree.treeEdges)).rel x y = true)
    (hrounds : ∀ i : Fin rounds.length,
      let r := rounds[i.val]'i.isLt
      r.tree.treeEdges.Subperm (r.compGlobal.map IndexedEdge.toWeighted) ∧
      (∀ x ∈ r.verts, x ∈ (Finset.univ.filter fun j : Fin rounds.length =>
          j.val < i.val).biUnion (fun j => (rounds[j.val]'j.isLt).verts) →
        ∃ hpos : 0 < r.tree.numSteps,
          x = r.tree.vOut ⟨r.tree.numSteps - 1, Nat.sub_lt hpos Nat.one_pos⟩))
    (huncorr_rem : ∀ i : Fin rounds.length, ∀ e ∈ H_rem,
      ¬(e.u ∈ (rounds[i.val]'i.isLt).verts ∧ e.v ∈ (rounds[i.val]'i.isLt).verts) ∧
      ∀ s_step : Fin (rounds[i.val]'i.isLt).tree.numSteps,
        (e.u ∈ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val ↔
          e.v ∉ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val) →
        (rounds[i.val]'i.isLt).tree.wPop s_step ≤ e.weight)
    (huncorr_tree : ∀ i j : Fin rounds.length, i.val < j.val →
      ∀ e ∈ (rounds[j.val]'j.isLt).tree.treeEdges,
        ∀ s_step : Fin (rounds[i.val]'i.isLt).tree.numSteps,
          (e.u ∈ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val ↔
            e.v ∉ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val) →
          (rounds[i.val]'i.isLt).tree.wPop s_step ≤ e.weight)
    (hF_len : F_comps.length = rounds.length)
    (hF_msf : ∀ i : Fin rounds.length,
      IsMinSpanningForest ((rounds[i.val]'i.isLt).compGlobal.map IndexedEdge.toWeighted)
        (F_comps[i.val]'(by omega)))
    (hHL_sub : H_lift.Subperm (H_rem.map IndexedEdge.toWeighted))
    (hHL_msf : IsMinSpanningForest
      (contractEdgeList conglomFn (H_rem.map IndexedEdge.toWeighted))
      (contractEdgeList conglomFn H_lift))
    (hF : IsMinSpanningForest
      (F_comps.flatten ++ H_lift ++
        (rounds.flatMap PartitionRoundWitness.corrEdges).map IndexedEdge.toWeighted) F) :
    IsMinSpanningForest es F := by
  classical
  let C_list := rounds.map fun r => r.compGlobal.map IndexedEdge.toWeighted
  let C_all := (rounds.flatMap PartitionRoundWitness.compGlobal).map IndexedEdge.toWeighted
  let M_C := (rounds.flatMap PartitionRoundWitness.corrEdges).map IndexedEdge.toWeighted
  let H_edges := H_rem.map IndexedEdge.toWeighted
  have hC_flat : C_list.flatten = C_all := map_compGlobal_flatten rounds
  have hFC_sub : F_comps.flatten.Subperm C_all := by
    rw [← hC_flat]
    exact List.Subperm.flatten_of_forall₂ (List.forall₂_iff_get.mpr ⟨by simp [C_list, hF_len],
      fun i hi₁ hi₂ => by simpa [C_list] using (hF_msf ⟨i, by omega⟩).1.1⟩)
  have hsub_base : (F_comps.flatten ++ H_lift ++ M_C).Subperm es := by
    have h2 : (F_comps.flatten ++ H_lift ++ M_C).Subperm (C_all ++ H_edges ++ M_C) :=
      (hFC_sub.append hHL_sub).append (.refl M_C)
    have hp_swap : (C_all ++ H_edges ++ M_C).Perm (C_all ++ M_C ++ H_edges) := by
      rw [List.append_assoc, List.append_assoc]
      exact List.Perm.append_left C_all List.perm_append_comm
    have hp_es : (C_all ++ M_C ++ H_edges).Perm es := by
      have hp' := hperm
      simp only [List.map_append] at hp'
      exact hp_swap.symm.trans hp'
    exact h2.trans (hp_swap.trans hp_es).subperm
  have hws : ∀ e ∈ es, WeaklySupported (F_comps.flatten ++ H_lift ++ M_C) e := by
    intro e he
    have hmem_e : e ∈ C_all ∨ e ∈ M_C ∨ e ∈ H_edges := by
      have hp := hperm.symm.subset he
      simp only [List.map_append, List.mem_append] at hp
      rcases hp with (h | h) | h
      · exact .inl h
      · exact .inr (.inr h)
      · exact .inr (.inl h)
    rcases hmem_e with heC | heM | heH
    · dsimp only [WeaklySupported]
      rw [← hC_flat, List.mem_flatten] at heC
      obtain ⟨xs, hxs_mem, he_xs⟩ := heC
      rw [List.mem_map] at hxs_mem
      obtain ⟨q, hq_mem, rfl⟩ := hxs_mem
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq_mem
      have hFC_t := ((isMinSpanningForest_iff_threshold_partition _ _).mp
        (hF_msf ⟨i, hi⟩)).2 e.weight
      have hrel_q : (edgePartition ((rounds[i]'hi).compGlobal.map IndexedEdge.toWeighted |>.filter
          fun f => decide (f.weight ≤ e.weight))).rel e.u e.v = true :=
        rel_edgePartitionFrom_of_mem (Partition.discrete n)
          (List.mem_filter.mpr ⟨he_xs, decide_eq_true le_rfl⟩)
      rw [← hFC_t] at hrel_q
      have hsub_Fi : (F_comps[i]'(by omega)).Subperm F_comps.flatten :=
        (List.sublist_flatten_of_mem (List.getElem_mem (by omega))).subperm
      have hsub_tot : ((F_comps[i]'(by omega)).filter fun f =>
          decide (f.weight ≤ e.weight)).Subperm
          ((F_comps.flatten ++ H_lift ++ M_C).filter fun f => decide (f.weight ≤ e.weight)) := by
        have hsl : (F_comps[i]'(by omega)).Subperm (F_comps.flatten ++ H_lift ++ M_C) :=
          hsub_Fi.trans ((List.sublist_append_left _ _).trans
            (List.sublist_append_left _ _)).subperm
        exact hsl.filter _
      exact edgePartition_mono_subperm hsub_tot hrel_q
    · dsimp only [WeaklySupported]
      exact rel_edgePartitionFrom_of_mem (Partition.discrete n)
        (List.mem_filter.mpr ⟨List.mem_append_right _ heM, decide_eq_true le_rfl⟩)
    · dsimp only [WeaklySupported]
      let w := e.weight
      let U := (F_comps.flatten ++ H_lift ++ M_C).filter fun f => decide (f.weight ≤ w)
      let H' := H_lift.filter fun f => decide (f.weight ≤ w)
      have hfilt_c : ∀ xs : List (WeightedEdge n ℕ),
          (contractEdgeList conglomFn xs).filter (fun f => decide (f.weight ≤ w)) =
            contractEdgeList conglomFn (xs.filter fun f => decide (f.weight ≤ w)) := fun xs => by
        simp only [contractEdgeList, List.filter_map]; rfl
      have hHL_thresh := ((isMinSpanningForest_iff_threshold_partition
        (contractEdgeList conglomFn H_edges) (contractEdgeList conglomFn H_lift)).mp hHL_msf).2 w
      have hc_H : (edgePartition (contractEdgeList conglomFn H')).rel
          (conglomFn e.u) (conglomFn e.v) = true := by
        have hce : (edgePartition ((contractEdgeList conglomFn H_edges).filter
            fun f => decide (f.weight ≤ w))).rel (conglomFn e.u) (conglomFn e.v) = true :=
          rel_edgePartitionFrom_of_mem (Partition.discrete nConglom)
            (List.mem_filter.mpr ⟨List.mem_map.mpr ⟨e, heH, rfl⟩, decide_eq_true le_rfl⟩)
        rw [← hHL_thresh, hfilt_c] at hce
        exact hce
      have htree_to_U : ∀ k : Fin rounds.length,
          ∀ a b : Fin n, (edgePartition ((rounds[k.val]'k.isLt).tree.treeEdges.filter
            fun f => decide (f.weight ≤ w))).rel a b = true →
          (edgePartition U).rel a b = true := by
        intro k a b hrel
        have hsub_t : ((rounds[k.val]'k.isLt).tree.treeEdges.filter fun f =>
            decide (f.weight ≤ w)).Subperm (((rounds[k.val]'k.isLt).compGlobal.map
            IndexedEdge.toWeighted).filter fun f => decide (f.weight ≤ w)) :=
          (hrounds k).1.filter _
        have hrel_c := edgePartition_mono_subperm hsub_t hrel
        have hFC_t := ((isMinSpanningForest_iff_threshold_partition _ _).mp
          (hF_msf k)).2 w
        rw [← hFC_t] at hrel_c
        have hsub_Fi : (F_comps[k.val]'(by omega)).Subperm F_comps.flatten :=
          (List.sublist_flatten_of_mem (List.getElem_mem (by omega))).subperm
        have hsub_tot : ((F_comps[k.val]'(by omega)).filter fun f =>
            decide (f.weight ≤ w)).Subperm U :=
          (hsub_Fi.trans ((List.sublist_append_left _ _).trans
            (List.sublist_append_left _ _)).subperm).filter _
        exact edgePartition_mono_subperm hsub_tot hrel_c
      have hroot_conglom : ∀ x y : Fin n, conglomFn x = conglomFn y →
          partRootOf rounds hcov (partRoundOf rounds hcov x) =
            partRootOf rounds hcov (partRoundOf rounds hcov y) := by
        intro x y hxy
        have hrel := (hconglom_rel x y).mp hxy
        clear hxy
        rw [rel_edgePartition_iff_eqvGen] at hrel
        induction hrel with
        | refl _ => rfl
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
        | rel _ _ hab =>
          obtain ⟨f, hf, rfl, rfl⟩ := hab
          rw [List.mem_flatMap] at hf
          obtain ⟨q, hq, hfq⟩ := hf
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
          dsimp only [DynamicDJPTree.treeEdges] at hfq
          rw [List.mem_map] at hfq
          obtain ⟨s_step, _, hfs⟩ := hfq
          have hmem_e := (rounds[k]'hk).tree.mem_treeVerts_of_edge s_step
          have hfu : f.u ∈ (rounds[k]'hk).verts := by
            rw [← hfs]; exact mem_djpVerts_mono _ _ s_step.isLt hmem_e.1
          have hfv : f.v ∈ (rounds[k]'hk).verts := by
            rw [← hfs]; exact mem_djpVerts_mono _ _ s_step.isLt hmem_e.2
          have h1 := partRootOf_eq_of_inter rounds hcov (fun i => (hrounds i).2)
            (2 * rounds.length) (partRoundOf rounds hcov f.u) ⟨k, hk⟩
            (by have := (partRoundOf rounds hcov f.u).isLt; omega)
            ⟨f.u, Finset.mem_inter.mpr ⟨partRoundOf_mem rounds hcov f.u, hfu⟩⟩
          have h2 := partRootOf_eq_of_inter rounds hcov (fun i => (hrounds i).2)
            (2 * rounds.length) (partRoundOf rounds hcov f.v) ⟨k, hk⟩
            (by have := (partRoundOf rounds hcov f.v).isLt; omega)
            ⟨f.v, Finset.mem_inter.mpr ⟨partRoundOf_mem rounds hcov f.v, hfv⟩⟩
          exact h1.trans h2.symm
      have htrace : ∀ m : ℕ, ∀ (k : Fin rounds.length), k.val ≤ m →
          ∀ (z : Fin n) (ez : WeightedEdge n ℕ),
            z ∈ (rounds[k.val]'k.isLt).verts →
            (∀ j : Fin rounds.length, j.val < k.val → z ∉ (rounds[j.val]'j.isLt).verts) →
            ez.weight ≤ w →
            ((ez.u = z ∧ ez.v ∉ (rounds[k.val]'k.isLt).verts) ∨
              (ez.v = z ∧ ez.u ∉ (rounds[k.val]'k.isLt).verts)) →
            (∀ s_step : Fin (rounds[k.val]'k.isLt).tree.numSteps,
              (ez.u ∈ (rounds[k.val]'k.isLt).tree.treeVerts s_step.val ↔
                ez.v ∉ (rounds[k.val]'k.isLt).tree.treeVerts s_step.val) →
              (rounds[k.val]'k.isLt).tree.wPop s_step ≤ ez.weight) →
            ∃ z₀ : Fin n, ∃ ez₀ : WeightedEdge n ℕ,
              (edgePartition U).rel z z₀ = true ∧
              z₀ ∈ (rounds[(partRootOf rounds hcov k).val]'
                (partRootOf rounds hcov k).isLt).verts ∧
              ez₀.weight ≤ w ∧
              ((ez₀.u = z₀ ∧ ez₀.v ∉ (rounds[(partRootOf rounds hcov k).val]'
                  (partRootOf rounds hcov k).isLt).verts) ∨
                (ez₀.v = z₀ ∧ ez₀.u ∉ (rounds[(partRootOf rounds hcov k).val]'
                  (partRootOf rounds hcov k).isLt).verts)) ∧
              (∀ s_step : Fin (rounds[(partRootOf rounds hcov k).val]'
                  (partRootOf rounds hcov k).isLt).tree.numSteps,
                (ez₀.u ∈ (rounds[(partRootOf rounds hcov k).val]'
                    (partRootOf rounds hcov k).isLt).tree.treeVerts s_step.val ↔
                  ez₀.v ∉ (rounds[(partRootOf rounds hcov k).val]'
                    (partRootOf rounds hcov k).isLt).tree.treeVerts s_step.val) →
                (rounds[(partRootOf rounds hcov k).val]'
                    (partRootOf rounds hcov k).isLt).tree.wPop s_step ≤ ez₀.weight) := by
        intro m
        induction m with
        | zero =>
          intro k hk z ez hz _ hw hcut hun
          have hk0 : k.val = 0 := by omega
          have hno : ¬(partPrevSet rounds k ∩ (rounds[k.val]'k.isLt).verts).Nonempty := by
            rintro ⟨y, hy⟩
            dsimp only [partPrevSet] at hy
            rw [Finset.mem_inter, Finset.mem_biUnion] at hy
            obtain ⟨j, hj, _⟩ := hy.1
            rw [Finset.mem_filter] at hj
            omega
          have hrt : partRootOf rounds hcov k = k := by
            rw [partRootOf]; simp only [hno, ↓reduceDIte]
          rw [hrt]
          exact ⟨z, ez, (edgePartition U).refl z, hz, hw, hcut, hun⟩
        | succ m ih =>
          intro k hk z ez hz hmin hw hcut hun
          by_cases hne : (partPrevSet rounds k ∩ (rounds[k.val]'k.isLt).verts).Nonempty
          · have hch := Finset.mem_inter.mp hne.choose_spec
            let v_stop := hne.choose
            obtain ⟨hpos, hv_eq⟩ := (hrounds k).2 v_stop hch.2 hch.1
            let s_last : Fin (rounds[k.val]'k.isLt).tree.numSteps :=
              ⟨(rounds[k.val]'k.isLt).tree.numSteps - 1, Nat.sub_lt hpos Nat.one_pos⟩
            have hv_stop_eq : v_stop = (rounds[k.val]'k.isLt).tree.vOut s_last := hv_eq
            have hz_ne_v : z ≠ v_stop := fun h => by
              rw [h] at hmin
              have hch1 := hch.1
              dsimp only [partPrevSet] at hch1
              rw [Finset.mem_biUnion] at hch1
              obtain ⟨j, hj, hxj⟩ := hch1
              rw [Finset.mem_filter] at hj
              exact hmin j hj.2 hxj
            have hz_pre : z ∈ (rounds[k.val]'k.isLt).tree.treeVerts s_last.val :=
              mem_djpVerts_last _ hpos hz (fun h => hz_ne_v (h.trans hv_stop_eq.symm))
            have hcross_last : ez.u ∈ (rounds[k.val]'k.isLt).tree.treeVerts s_last.val ↔
                ez.v ∉ (rounds[k.val]'k.isLt).tree.treeVerts s_last.val := by
              have hsub_t : (rounds[k.val]'k.isLt).tree.treeVerts s_last.val ⊆
                  (rounds[k.val]'k.isLt).verts := fun y hy =>
                mem_djpVerts_mono _ _ s_last.isLt.le hy
              rcases hcut with ⟨rfl, hnv⟩ | ⟨rfl, hnu⟩
              · exact ⟨fun _ hv => hnv (hsub_t hv), fun _ => hz_pre⟩
              · exact ⟨fun hu => absurd (hsub_t hu) hnu, fun hnv => absurd hz_pre hnv⟩
            have hw_last : (rounds[k.val]'k.isLt).tree.wPop s_last ≤ w :=
              (hun s_last hcross_last).trans hw
            let D_pre := truncateDJP (rounds[k.val]'k.isLt).tree s_last.val s_last.isLt.le
            let vIn_last := (rounds[k.val]'k.isLt).tree.vIn s_last
            let e_stop := (rounds[k.val]'k.isLt).tree.edge s_last
            let e_stop' : WeightedEdge n ℕ :=
              ⟨e_stop.u, e_stop.v, (rounds[k.val]'k.isLt).tree.wPop s_last⟩
            have hz_dp : z ∈ D_pre.treeVerts D_pre.numSteps := by
              dsimp only [D_pre, truncateDJP, DynamicDJPTree.treeVerts]
              rw [djpVerts_truncate _ _ s_last.isLt.le _ le_rfl]; exact hz_pre
            have hvin_dp : vIn_last ∈ D_pre.treeVerts D_pre.numSteps := by
              dsimp only [D_pre, truncateDJP, DynamicDJPTree.treeVerts]
              rw [djpVerts_truncate _ _ s_last.isLt.le _ le_rfl]
              exact (rounds[k.val]'k.isLt).tree.vIn_mem s_last
            have hcut1_dp : (ez.u = z ∧ ez.v ∉ D_pre.treeVerts D_pre.numSteps) ∨
                (ez.v = z ∧ ez.u ∉ D_pre.treeVerts D_pre.numSteps) := by
              have hsub_t : D_pre.treeVerts D_pre.numSteps ⊆ (rounds[k.val]'k.isLt).verts := by
                dsimp only [D_pre, truncateDJP, DynamicDJPTree.treeVerts]
                rw [djpVerts_truncate _ _ s_last.isLt.le _ le_rfl]
                exact fun y hy => mem_djpVerts_mono _ _ s_last.isLt.le hy
              rcases hcut with ⟨rfl, hnv⟩ | ⟨rfl, hnu⟩
              · exact .inl ⟨rfl, fun hv => hnv (hsub_t hv)⟩
              · exact .inr ⟨rfl, fun hu => hnu (hsub_t hu)⟩
            have hcut2_dp : (e_stop'.u = vIn_last ∧ e_stop'.v ∉ D_pre.treeVerts D_pre.numSteps) ∨
                (e_stop'.v = vIn_last ∧ e_stop'.u ∉ D_pre.treeVerts D_pre.numSteps) := by
              have hnot_dp : (rounds[k.val]'k.isLt).tree.vOut s_last ∉
                  D_pre.treeVerts D_pre.numSteps := by
                dsimp only [D_pre, truncateDJP, DynamicDJPTree.treeVerts]
                rw [djpVerts_truncate _ _ s_last.isLt.le _ le_rfl]
                exact (rounds[k.val]'k.isLt).tree.vOut_not_mem s_last
              rcases (rounds[k.val]'k.isLt).tree.ends_match s_last with ⟨hu, hv⟩ | ⟨hv, hu⟩
              · exact .inl ⟨hu, hv ▸ hnot_dp⟩
              · exact .inr ⟨hv, hu ▸ hnot_dp⟩
            have h21 := D_pre.rel_treeEdges_filter_of_border hz_dp hvin_dp ez e_stop'
              hcut1_dp hcut2_dp
              (fun s' hs' => by
                dsimp only [D_pre, truncateDJP, DynamicDJPTree.treeVerts] at hs' ⊢
                rw [djpVerts_truncate (rounds[k.val]'k.isLt).tree s_last.val s_last.isLt.le
                  s'.val s'.isLt.le] at hs'
                exact hun ⟨s'.val, lt_trans s'.isLt s_last.isLt⟩ hs')
              (fun s' hs' => by
                dsimp only [D_pre, truncateDJP, DynamicDJPTree.treeVerts] at hs' ⊢
                rw [djpVerts_truncate (rounds[k.val]'k.isLt).tree s_last.val s_last.isLt.le
                  s'.val s'.isLt.le] at hs'
                exact (rounds[k.val]'k.isLt).tree.djp_future
                  ⟨s'.val, lt_trans s'.isLt s_last.isLt⟩ s_last s'.isLt hs')
            have hrel_z_vin : (edgePartition U).rel z vIn_last = true := by
              refine htree_to_U k z vIn_last (edgePartition_mono_subset (fun f hf => ?_) h21)
              rw [List.mem_filter, decide_eq_true_eq] at hf ⊢
              refine ⟨?_, hf.2.trans (max_le hw hw_last)⟩
              dsimp only [D_pre, DynamicDJPTree.treeEdges, truncateDJP] at hf ⊢
              rw [List.mem_map] at hf ⊢
              obtain ⟨s', _, rfl⟩ := hf.1
              exact ⟨⟨s'.val, lt_trans s'.isLt s_last.isLt⟩, List.mem_finRange _, rfl⟩
            have hrel_vin_vstop : (edgePartition U).rel vIn_last v_stop = true := by
              refine htree_to_U k vIn_last v_stop ?_
              have he_mem : e_stop ∈ (rounds[k.val]'k.isLt).tree.treeEdges.filter
                  fun f => decide (f.weight ≤ w) :=
                List.mem_filter.mpr ⟨List.mem_map.mpr ⟨s_last, List.mem_finRange _, rfl⟩,
                  decide_eq_true (((rounds[k.val]'k.isLt).tree.edge_weight_le_wPop s_last).trans
                    hw_last)⟩
              have hrel_e := rel_edgePartitionFrom_of_mem (Partition.discrete n) he_mem
              dsimp only [e_stop] at hrel_e
              dsimp only [vIn_last]
              rw [hv_stop_eq]
              rcases (rounds[k.val]'k.isLt).tree.ends_match s_last with ⟨hu, hv⟩ | ⟨hv, hu⟩
              · rw [hu, hv] at hrel_e; exact hrel_e
              · rw [hu, hv] at hrel_e; exact (edgePartition _).symm hrel_e
            have hrel_z_vstop : (edgePartition U).rel z v_stop = true :=
              (edgePartition U).trans hrel_z_vin hrel_vin_vstop
            let k' := partRoundOf rounds hcov v_stop
            have hk'_lt : k'.val < k.val := by
              have hch1 := hch.1
              dsimp only [partPrevSet] at hch1
              rw [Finset.mem_biUnion] at hch1
              obtain ⟨j, hj, hxj⟩ := hch1
              rw [Finset.mem_filter] at hj
              by_contra hge
              exact partRoundOf_min rounds hcov v_stop j
                (lt_of_lt_of_le hj.2 (not_lt.mp hge)) hxj
            have hvIn_not_k' : vIn_last ∉ (rounds[k'.val]'k'.isLt).verts := by
              intro hmem
              have h1 := (rounds[k.val]'k.isLt).tree.vIn_mem s_last
              have hvin_vk : vIn_last ∈ (rounds[k.val]'k.isLt).verts :=
                mem_djpVerts_mono _ _ s_last.isLt.le h1
              have hvin_prev : vIn_last ∈ partPrevSet rounds k := Finset.mem_biUnion.mpr
                ⟨k', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'_lt⟩, hmem⟩
              obtain ⟨_, hvin_eq⟩ := (hrounds k).2 vIn_last hvin_vk hvin_prev
              exact (rounds[k.val]'k.isLt).tree.vOut_not_mem s_last (hvin_eq ▸ h1)
            have hcut_k' : (e_stop.u = v_stop ∧ e_stop.v ∉ (rounds[k'.val]'k'.isLt).verts) ∨
                (e_stop.v = v_stop ∧ e_stop.u ∉ (rounds[k'.val]'k'.isLt).verts) := by
              rcases (rounds[k.val]'k.isLt).tree.ends_match s_last with ⟨hu, hv⟩ | ⟨hv, hu⟩
              · exact .inr ⟨hv.trans hv_stop_eq.symm, hu ▸ hvIn_not_k'⟩
              · exact .inl ⟨hu.trans hv_stop_eq.symm, hv ▸ hvIn_not_k'⟩
            have hun_k' := huncorr_tree k' k hk'_lt e_stop
              (List.mem_map.mpr ⟨s_last, List.mem_finRange _, rfl⟩)
            have hew_stop : e_stop.weight ≤ w :=
              ((rounds[k.val]'k.isLt).tree.edge_weight_le_wPop s_last).trans hw_last
            obtain ⟨z₀, ez₀, hrel₀, hz₀, hw₀, hcut₀, hun₀⟩ := ih k' (by omega) v_stop e_stop
              (partRoundOf_mem rounds hcov v_stop) (partRoundOf_min rounds hcov v_stop)
              hew_stop hcut_k' hun_k'
            have hrt_eq : partRootOf rounds hcov k = partRootOf rounds hcov k' := by
              conv_lhs => rw [partRootOf]; simp only [hne, ↓reduceDIte]
            rw [hrt_eq]
            exact ⟨z₀, ez₀, (edgePartition U).trans hrel_z_vstop hrel₀, hz₀, hw₀, hcut₀, hun₀⟩
          · have hrt : partRootOf rounds hcov k = k := by
              rw [partRootOf]; simp only [hne, ↓reduceDIte]
            rw [hrt]
            exact ⟨z, ez, (edgePartition U).refl z, hz, hw, hcut, hun⟩
      let EndOf (x : Fin n) : Prop := ∃ h ∈ H_edges, h.weight ≤ w ∧ (h.u = x ∨ h.v = x)
      have mk_cut : ∀ {k : Fin rounds.length} {z : Fin n} {ih : IndexedEdge n},
          ih ∈ H_rem → z ∈ (rounds[k.val]'k.isLt).verts → (ih.u = z ∨ ih.v = z) →
          (ih.toWeighted.u = z ∧ ih.toWeighted.v ∉ (rounds[k.val]'k.isLt).verts) ∨
            (ih.toWeighted.v = z ∧ ih.toWeighted.u ∉ (rounds[k.val]'k.isLt).verts) :=
        fun {k} {z} {ih} hih hz hEnd => by
          have hno := (huncorr_rem k ih hih).1
          rcases hEnd with h | h
          · exact .inl ⟨h, fun hv => hno ⟨by rw [show ih.u = z from h]; exact hz, hv⟩⟩
          · exact .inr ⟨h, fun hu => hno ⟨hu, by rw [show ih.v = z from h]; exact hz⟩⟩
      have hbridge : ∀ x y : Fin n, conglomFn x = conglomFn y → EndOf x → EndOf y →
          (edgePartition U).rel x y = true := by
        intro x y hxy ⟨h₁, hh₁, hw₁, hx₁⟩ ⟨h₂, hh₂, hw₂, hy₂⟩
        let kx := partRoundOf rounds hcov x
        let ky := partRoundOf rounds hcov y
        have hx_k : x ∈ (rounds[kx.val]'kx.isLt).verts := partRoundOf_mem rounds hcov x
        have hy_k : y ∈ (rounds[ky.val]'ky.isLt).verts := partRoundOf_mem rounds hcov y
        obtain ⟨ih₁, hih₁, rfl⟩ := List.mem_map.mp hh₁
        obtain ⟨ih₂, hih₂, rfl⟩ := List.mem_map.mp hh₂
        obtain ⟨z₁, ez₁, hrel₁, hz₁, hwz₁, hcutz₁, hunz₁⟩ := htrace rounds.length kx
          (Nat.le_of_lt kx.isLt) x ih₁.toWeighted hx_k (partRoundOf_min rounds hcov x) hw₁
          (mk_cut hih₁ hx_k hx₁) (huncorr_rem kx ih₁ hih₁).2
        obtain ⟨z₂, ez₂, hrel₂, hz₂, hwz₂, hcutz₂, hunz₂⟩ := htrace rounds.length ky
          (Nat.le_of_lt ky.isLt) y ih₂.toWeighted hy_k (partRoundOf_min rounds hcov y) hw₂
          (mk_cut hih₂ hy_k hy₂) (huncorr_rem ky ih₂ hih₂).2
        have hrt_xy : partRootOf rounds hcov kx = partRootOf rounds hcov ky :=
          hroot_conglom x y hxy
        rw [hrt_xy] at hz₁ hcutz₁ hunz₁
        have h21 := (rounds[(partRootOf rounds hcov ky).val]'
          (partRootOf rounds hcov ky).isLt).tree.rel_treeEdges_filter_of_border
          hz₁ hz₂ ez₁ ez₂ hcutz₁ hcutz₂ hunz₁ hunz₂
        have hrel_z : (edgePartition U).rel z₁ z₂ = true :=
          htree_to_U (partRootOf rounds hcov ky) z₁ z₂
            (edgePartition_filter_mono_subperm (.refl _) (max_le hwz₁ hwz₂) h21)
        exact (edgePartition U).trans hrel₁
          ((edgePartition U).trans hrel_z ((edgePartition U).symm hrel₂))
      refine edgePartition_rel_of_contracted_bridge conglomFn H' U EndOf (fun h hhH => ?_) hbridge
        ⟨e, heH, le_rfl, .inl rfl⟩ ⟨e, heH, le_rfl, .inr rfl⟩ hc_H
      have hh_mem := List.mem_filter.mp hhH
      have hh_edge : h ∈ H_edges := hHL_sub.subset hh_mem.1
      have hh_w : h.weight ≤ w := decide_eq_true_eq.mp hh_mem.2
      have hh_U : h ∈ U :=
        List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_right _ hh_mem.1), hh_mem.2⟩
      exact ⟨⟨h, hh_edge, hh_w, .inl rfl⟩, ⟨h, hh_edge, hh_w, .inr rfl⟩, hh_U⟩
  exact isMinSpanningForest_of_weakSupport es (F_comps.flatten ++ H_lift ++ M_C) F
    hsub_base hws hF

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
