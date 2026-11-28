/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Threshold
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.Layout
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.IndexedEdges
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.ValidProg

/-!
# Canonicalization and Single-Component Decision-Tree Evaluation on the Word RAM

Implements `evalDecisionTreeProg` and caller-scratch `evalDecisionTreeWithSlotMapProg` as steps
toward Theorem 5.8 of [PettieRamachandran2002] (`Section 4.1, p. 23; Section 5.1, pp. 25–26`,
Corollary 5.6 and Theorem 5.8, `#8624`) for evaluating a precomputed optimal MSF decision tree
stored in `HoldsDTTable` on a vertex-compacted simple component `C` (`v ≤ r0` vertices,
`m = C.length` edges). Reuses `edgePairIdx`, `dtGraphMask`, `walkCompleteTree`, `HoldsDTTable`,
`DTTableInBounds`, and `testBit_eq_decide_shift_and` from `DecisionTree.Layout`, `HoldsIndexedEdges`
from `GraphOps.IndexedEdges`, `Memory.copy` from `ArrayOps`, `framedTriple_with_realization` and
`iterate_framedTriple_of_step` from `LoopFrame`, and `Contraction.Threshold` /
`DecisionTree.Canonical` bridges.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DTQuery`: query handle (`tableBase`,
  `numVerts`, `numEdges`, `edgeBase`, `outBase`) encoded via `word_enc_structure`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DTScratchQuery`: query handle adding caller
  `slotMap` scratch buffer (`v.choose 2` words) encoded via `word_enc_structure`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.evalDecisionTreeWithSlotMapProg`: Word-RAM
  evaluation using a caller-supplied reusable `slotMap` buffer in `O(m + optDepth C + 1)` time.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.evalDecisionTreeWithSlotMapProgSafe`: native
  word-width safety predicate for `evalDecisionTreeWithSlotMapProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.evalDecisionTreeProg`: Word-RAM program
  allocating `slotMap`, canonicalizing `C`, querying `HoldsDTTable`, walking the stored complete
  decision tree, and emitting the resulting MSF at `outBase` in `O(m + optDepth C + 1)` time.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.evalDecisionTreeProgSafe`: native word-width
  safety predicate for `evalDecisionTreeProg`.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.dt_eval_msf_correct`: pure correctness bridge
  from `HoldsCompleteTree` + `MSFDT.Correct` on `endsOfMask` to `IsMinSpanningForest`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_evalDecisionTreeWithSlotMapProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.evalDecisionTreeWithSlotMapProg_spec`: uniform
  `Realizes .exact` (`work = 0`) and `Memory.FramedTriple` specification with caller-supplied
  `slotMap` (`s'.frontier ≤ s.frontier + m`).
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_evalDecisionTreeProg`: uniform
  `Realizes .exact` certificate with `work = 0`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.evalDecisionTreeProg_spec`: `Memory.FramedTriple`
  specification proving `IsMinSpanningForest`, `Subperm`, `HoldsIndexedEdges`, space bound
  `s'.frontier ≤ s.frontier + v.choose 2 + m`, and time bound `≤ 15 * (m + optDepth C + 1)`.

## References

* [PettieRamachandran2002] Seth Pettie and Vijaya Ramachandran, *An Optimal Minimum Spanning Tree
  Algorithm*, Journal of the ACM 49(1), 16–34, 2002.
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest

/-! ## Section 1: Pure Decision-Tree Readout and Reindexing Bridges -/

private theorem edgePairIdx_lt_choose_two {n : ℕ} (e : IndexedEdge n) (hne : e.u ≠ e.v) :
    edgePairIdx e.u.val e.v.val < n.choose 2 := by
  dsimp only [edgePairIdx]
  have hne' : e.u.val ≠ e.v.val := fun h => hne (Fin.ext h)
  split_ifs with huv
  · exact pairIdx_lt_choose_two huv e.v.isLt
  · exact pairIdx_lt_choose_two (by omega) e.u.isLt

private theorem edgePairIdx_sym2_eq {n : ℕ} (e₁ e₂ : IndexedEdge n)
    (hn1 : e₁.u ≠ e₁.v) (hn2 : e₂.u ≠ e₂.v)
    (he12 : edgePairIdx e₁.u.val e₁.v.val = edgePairIdx e₂.u.val e₂.v.val) :
    s(e₁.u, e₁.v) = s(e₂.u, e₂.v) := by
  have hn1' : e₁.u.val ≠ e₁.v.val := Fin.val_ne_of_ne hn1
  have hn2' : e₂.u.val ≠ e₂.v.val := Fin.val_ne_of_ne hn2
  let p1 : Fin n × Fin n := if e₁.u.val < e₁.v.val then (e₁.u, e₁.v) else (e₁.v, e₁.u)
  let p2 : Fin n × Fin n := if e₂.u.val < e₂.v.val then (e₂.u, e₂.v) else (e₂.v, e₂.u)
  have hp1 : p1.1.val < p1.2.val := by dsimp only [p1]; split_ifs <;> dsimp only <;> omega
  have hp2 : p2.1.val < p2.2.val := by dsimp only [p2]; split_ifs <;> dsimp only <;> omega
  have hi1 : pairIdx p1.1.val p1.2.val = edgePairIdx e₁.u.val e₁.v.val := by
    dsimp only [p1, edgePairIdx]; split_ifs <;> rfl
  have hi2 : pairIdx p2.1.val p2.2.val = edgePairIdx e₂.u.val e₂.v.val := by
    dsimp only [p2, edgePairIdx]; split_ifs <;> rfl
  have hall : (allPairs n)[pairIdx p1.1.val p1.2.val]'(by
      rw [length_allPairs]; exact pairIdx_lt_choose_two hp1 p1.2.isLt) =
      (allPairs n)[pairIdx p2.1.val p2.2.val]'(by
        rw [length_allPairs]; exact pairIdx_lt_choose_two hp2 p2.2.isLt) := by
    congr 1; exact hi1.trans (he12.trans hi2.symm)
  rw [getElem_allPairs_pairIdx hp1, getElem_allPairs_pairIdx hp2] at hall
  have hp_eq : p1 = p2 := Prod.ext (Fin.ext (congrArg (·.1.val) hall))
    (Fin.ext (congrArg (·.2.val) hall))
  have hs1 : s(p1.1, p1.2) = s(e₁.u, e₁.v) := by
    dsimp only [p1]; split_ifs <;> [rfl; exact Sym2.eq_swap]
  have hs2 : s(p2.1, p2.2) = s(e₂.u, e₂.v) := by
    dsimp only [p2]; split_ifs <;> [rfl; exact Sym2.eq_swap]
  rw [← hs1, ← hs2, hp_eq]

private theorem endsOfMask_reindex_indexedEdges {v : ℕ} (C : List (IndexedEdge v))
    (hsimp : IsSimple (edgeEnds (C.map IndexedEdge.toWeighted))) :
    let pairs := C.map fun e => (e.u, e.v)
    let mask := dtGraphMask pairs
    mask < 2 ^ v.choose 2 ∧
    (maskEdgePairs v mask).length = C.length ∧
    optDepth (edgeEnds (C.map IndexedEdge.toWeighted)) = optDepth (endsOfMask v mask) ∧
    ∃ σ : Fin C.length ≃ Fin (maskEdgePairs v mask).length,
      (∀ k : Fin C.length,
        pairIdx ((maskEdgePairs v mask)[(σ k).val]).1.val
          ((maskEdgePairs v mask)[(σ k).val]).2.val =
          edgePairIdx C[k.val].u.val C[k.val].v.val) ∧
      (∀ k : Fin C.length,
        s(C[k.val].u, C[k.val].v) = endsOfMask v mask (σ k)) := by
  let pairs : List (Fin v × Fin v) := C.map fun e => (e.u, e.v)
  have hlen : pairs.length = C.length := List.length_map _
  have hlen_w : (C.map IndexedEdge.toWeighted).length = C.length := List.length_map _
  have hsimp' := (isSimple_iff _).mp hsimp
  have hsimp_pairs : IsSimple (fun i : Fin pairs.length => s(pairs[i.val].1, pairs[i.val].2)) := by
    rw [isSimple_iff]
    refine ⟨fun i => ?_, fun i₁ i₂ he => ?_⟩
    · have h := hsimp'.1 ⟨i.val, hlen_w.symm ▸ hlen ▸ i.isLt⟩
      simpa [edgeEnds, pairs, IndexedEdge.toWeighted] using h
    · have h := hsimp'.2 (by simpa [edgeEnds, pairs, IndexedEdge.toWeighted] using he :
        edgeEnds (C.map IndexedEdge.toWeighted) ⟨i₁.val, hlen_w.symm ▸ hlen ▸ i₁.isLt⟩ =
        edgeEnds (C.map IndexedEdge.toWeighted) ⟨i₂.val, hlen_w.symm ▸ hlen ▸ i₂.isLt⟩)
      exact Fin.ext (congrArg (Fin.val : Fin (C.map IndexedEdge.toWeighted).length → ℕ) h)
  have hre := endsOfMask_reindex_dtGraphMask pairs hsimp_pairs
  rcases hre with ⟨hm_lt, hlen_mask, hopt_pairs, σp, hpidx, he_pairs⟩
  let σ₀ : Fin C.length ≃ Fin pairs.length := (Fin.castOrderIso hlen.symm).toEquiv
  have hopt_C : optDepth (edgeEnds (C.map IndexedEdge.toWeighted)) =
      optDepth (fun i : Fin pairs.length => s(pairs[i.val].1, pairs[i.val].2)) := by
    refine optDepth_reindex _ _ ((Fin.castOrderIso (by simp [pairs])).toEquiv)
      (Equiv.refl (Fin v)).toEmbedding fun i => ?_
    change Sym2.map id (edgeEnds (C.map IndexedEdge.toWeighted) i) = _
    rw [Sym2.map_id]
    simp [edgeEnds, pairs, IndexedEdge.toWeighted, Fin.castOrderIso]
  refine ⟨hm_lt, hlen_mask.trans hlen, hopt_C.trans hopt_pairs, σ₀.trans σp, fun k => ?_,
    fun k => ?_⟩
  · simpa [σ₀, pairs, Fin.castOrderIso] using hpidx (σ₀ k)
  · simpa [σ₀, pairs, Fin.castOrderIso] using he_pairs (σ₀ k)

/-- Correctness bridge from `HoldsCompleteTree` + `MSFDT.Correct` on `endsOfMask v mask` to
`Subperm` and `IsMinSpanningForest` on `C : List (IndexedEdge v)`. -/
theorem dt_eval_msf_correct {v mask d intBase leafBase : ℕ} {mem : ℕ → ℕ}
    {C : List (IndexedEdge v)} {T : MSFDT (maskEdgePairs v mask).length}
    (hcorr : T.Correct (endsOfMask v mask))
    (hhold : HoldsCompleteTree d intBase leafBase d 1 mem T)
    (σ : Fin C.length ≃ Fin (maskEdgePairs v mask).length)
    (hEnds : ∀ k : Fin C.length,
      s(C[k.val].u, C[k.val].v) = endsOfMask v mask (σ k)) :
    let e := (maskEdgePairs v mask).length
    let cmp : Fin e → Fin e → Bool := fun a b =>
      let i := σ.symm a
      let j := σ.symm b
      decide (C[i.val].weight < C[j.val].weight ∨
        (C[i.val].weight = C[j.val].weight ∧ i.val < j.val))
    let endNode := walkCompleteTree intBase leafBase mem cmp d 1
    let ansMask := mem (leafBase + (endNode - 2 ^ d))
    let F := ((List.finRange e).filter fun j => ansMask.testBit j.val).map
      fun j => C[(σ.symm j).val]
    F.Subperm C ∧
      IsMinSpanningForest (C.map IndexedEdge.toWeighted) (F.map IndexedEdge.toWeighted) := by
  classical
  let e := (maskEdgePairs v mask).length
  let Cw := C.map IndexedEdge.toWeighted
  have hCw_len : Cw.length = C.length := List.length_map _
  let σ' : Fin Cw.length ≃ Fin e := (Fin.castOrderIso hCw_len).toEquiv.trans σ
  let wC : Fin Cw.length → ℕ ×ₗ ℕ := edgeWeight Cw
  let wM : Fin e → ℕ ×ₗ ℕ := fun a => wC (σ'.symm a)
  have hwM : Function.Injective wM := (edgeWeight_injective Cw).comp σ'.symm.injective
  let pM : Equiv.Perm (Fin e) := orderPerm wM hwM
  let cmp : Fin e → Fin e → Bool := fun a b =>
    let i := σ.symm a
    let j := σ.symm b
    decide (C[i.val].weight < C[j.val].weight ∨
      (C[i.val].weight = C[j.val].weight ∧ i.val < j.val))
  have hcmp : ∀ a b : Fin e, cmp a b = true ↔ (pM a).val < (pM b).val := fun a b => by
    have hp : (pM a).val < (pM b).val ↔ wM a < wM b := by
      change pM a < pM b ↔ wM a < wM b
      exact orderPerm_lt_iff wM hwM a b
    rw [hp]
    have hval_symm : ∀ x : Fin e, (σ'.symm x).val = (σ.symm x).val := fun _ => rfl
    dsimp only [cmp, wM, wC, edgeWeight]
    rw [Prod.Lex.lt_iff]
    simp only [ofLex_toLex, Cw, List.getElem_map, hval_symm, decide_eq_true_eq]
    exact Iff.rfl
  have hwalk := walkCompleteTree_eval pM cmp hcmp hhold
  dsimp only at hwalk
  set endNode := walkCompleteTree intBase leafBase mem cmp d 1
  set ansMask := mem (leafBase + (endNode - 2 ^ d))
  have hans : ansMask = maskOfFinset (T.eval pM) := hwalk.2.2
  rw [(MSFDT.correct_iff _ _).mp hcorr pM] at hans
  have hEnds' : ∀ k : Fin Cw.length,
      Sym2.map (Equiv.refl (Fin v)).toEmbedding (edgeEnds Cw k) = endsOfMask v mask (σ' k) := by
    intro k
    have hm_id : Sym2.map (Equiv.refl (Fin v)).toEmbedding (edgeEnds Cw k) = edgeEnds Cw k := by
      simp [Equiv.refl_toEmbedding]
    have hk_eq : edgeEnds Cw k = s(C[k.val].u, C[k.val].v) := by
      simp [edgeEnds, Cw, IndexedEdge.toWeighted]
    rw [hm_id, hk_eq]
    exact hEnds ⟨k.val, hCw_len ▸ k.isLt⟩
  have hmem_msf : ∀ j : Fin e, j ∈ Cslib.Multigraph.msf (endsOfMask v mask) pM Finset.univ ↔
      σ'.symm j ∈ Cslib.Multigraph.msf (edgeEnds Cw) wC Finset.univ := by
    intro j
    let k := σ'.symm j
    have hkj : σ' k = j := σ'.apply_symm_apply j
    induction hk : edgeEnds Cw k using Sym2.ind with
    | _ a b =>
      have hj_ends : endsOfMask v mask j = s(a, b) := by
        have h := hEnds' k; rw [hkj, hk] at h
        simpa [Equiv.refl_toEmbedding] using h.symm
      have hflt : ((Finset.univ.filter fun f : Fin Cw.length => wC f < wC k).map
          σ'.toEmbedding : Finset (Fin e)) = Finset.univ.filter fun g => pM g < pM j := by
        ext g
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.coe_toEmbedding]
        have hlt_iff : ∀ f : Fin Cw.length, wC f < wC k ↔ pM (σ' f) < pM j := fun f => by
          rw [orderPerm_lt_iff wM hwM]; simp [wM, k]
        exact ⟨fun ⟨f, hf, hfg⟩ => hfg ▸ (hlt_iff f).mp hf,
          fun hg => ⟨σ'.symm g, by rw [hlt_iff, σ'.apply_symm_apply]; exact hg,
            σ'.apply_symm_apply g⟩⟩
      have hjoins_iff : Cslib.Multigraph.Joins (edgeEnds Cw) {f | wC f < wC k} a b ↔
          Cslib.Multigraph.Joins (endsOfMask v mask) {g | pM g < pM j} a b := by
        rw [show {f | wC f < wC k} = ((Finset.univ.filter fun f : Fin Cw.length =>
            wC f < wC k : Finset _) : Set _) from by ext f; simp,
          show {g | pM g < pM j} = ((Finset.univ.filter fun g : Fin e =>
            pM g < pM j : Finset _) : Set _) from by ext g; simp, ← hflt]
        exact joins_reindex _ _ σ'.toEmbedding (Equiv.refl (Fin v)).toEmbedding hEnds' _ a b
      rw [Cslib.Multigraph.mem_msf_iff pM hj_ends, Cslib.Multigraph.mem_msf_iff wC hk]
      simp only [Finset.mem_univ, true_and]
      exact not_congr hjoins_iff.symm
  let S := Cslib.Multigraph.msf (edgeEnds Cw) wC Finset.univ
  let F := ((List.finRange e).filter fun j => ansMask.testBit j.val).map
    fun j => C[(σ.symm j).val]
  have hF_perm_S : ((List.finRange e).filter fun j => ansMask.testBit j.val).Perm
      (S.toList.map σ'.toEmbedding) := by
    refine List.perm_of_nodup_nodup_toFinset_eq ((List.nodup_finRange e).filter _)
      ((Finset.nodup_toList S).map σ'.toEmbedding.injective) (by
        ext j; simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
          List.mem_map, Finset.mem_toList, Equiv.coe_toEmbedding, hans, testBit_maskOfFinset,
          decide_eq_true_eq]
        exact ⟨fun ⟨_, hj⟩ => ⟨σ'.symm j, (hmem_msf j).mp hj, σ'.apply_symm_apply j⟩,
          fun ⟨k, hkS, hk_eq⟩ =>
            hk_eq ▸ ⟨(σ' k).isLt, (hmem_msf (σ' k)).mpr (by simpa [S] using hkS)⟩⟩)
  have hF_sub : F.Subperm C := by
    have hperm_fin : (List.finRange e).Perm ((List.finRange C.length).map σ) := by
      refine List.perm_of_nodup_nodup_toFinset_eq (List.nodup_finRange e)
        ((List.nodup_finRange C.length).map σ.injective) (by
          ext j; simp only [List.mem_toFinset, List.mem_finRange, List.mem_map, true_and]
          exact ⟨fun _ => ⟨σ.symm j, σ.apply_symm_apply j⟩, fun _ => trivial⟩)
    have hm := hperm_fin.map fun j => C[(σ.symm j).val]
    have hcongr : ((List.finRange C.length).map ((fun j => C[(σ.symm j).val]) ∘ σ)) =
        (List.finRange C.length).map fun i => C[i.val] :=
      List.map_congr_left fun i _ => by simp
    rw [List.map_map, hcongr, List.map_getElem_finRange] at hm
    exact (List.filter_sublist.map _).subperm.trans hm.subperm
  let U := S.toList.map fun k => Cw[k.val]
  have hFw_perm : (F.map IndexedEdge.toWeighted).Perm U := by
    have hm := hF_perm_S.map fun j => Cw[(σ'.symm j).val]
    have hl : (List.map (fun j => Cw[(σ'.symm j).val])
        ((List.finRange e).filter fun j => ansMask.testBit j.val)) =
        F.map IndexedEdge.toWeighted := by
      dsimp only [F]; rw [List.map_map]
      exact List.map_congr_left fun j _ => by simp [Cw, σ', Fin.castOrderIso]
    have hr : (List.map (fun j => Cw[(σ'.symm j).val]) (S.toList.map σ'.toEmbedding)) = U := by
      dsimp only [U]; rw [List.map_map]
      exact List.map_congr_left fun k _ => by
        dsimp only [Function.comp_apply, Equiv.coe_toEmbedding]
        congr 1; exact congrArg Fin.val (σ'.symm_apply_apply k)
    rwa [hl, hr] at hm
  have hU_sf : IsSpanningForest Cw (msfEdges Cw wC) :=
    msfEdges_isSpanningForest Cw wC (edgeWeight_injective Cw)
  have hU_thresh : ∀ t : ℕ,
      edgePartition ((msfEdges Cw wC).filter fun e => decide (e.weight ≤ t)) =
        edgePartition (Cw.filter fun e => decide (e.weight ≤ t)) := fun t =>
    msfEdges_threshold_partition Cw wC (fun t => ⟨toLex (t + 1, 0), fun i => by
      dsimp only [wC, edgeWeight]; rw [Prod.Lex.lt_iff]; simp only [ofLex_toLex]; omega⟩) t
  have hF_sf : IsSpanningForest Cw (F.map IndexedEdge.toWeighted) :=
    ⟨hFw_perm.subperm.trans hU_sf.1, (Perm.isAcyclic_iff hFw_perm).mpr hU_sf.2.1,
      (Perm.edgePartition_eq hFw_perm).trans hU_sf.2.2⟩
  refine ⟨hF_sub, (isMinSpanningForest_iff_threshold_partition Cw _).mpr ⟨hF_sf, fun t => ?_⟩⟩
  rw [Perm.edgePartition_eq (hFw_perm.filter _)]
  exact hU_thresh t

/-! ## Section 2: Word-RAM Structures and Step Realizations -/

private structure DTScanState where
  idx : ℕ
  mask : ℕ
  deriving DecidableEq

private word_enc_structure encDTScanState : DTScanState where
  idx : wordWords,
  mask : wordWords

private instance : WordEncoding DTScanState := ⟨2, encDTScanState⟩

private structure DTScanEnv where
  edgeBase : ℕ
  slotMap : ℕ
  deriving DecidableEq

private word_enc_structure encDTScanEnv : DTScanEnv where
  edgeBase : wordWords,
  slotMap : wordWords

private instance : WordEncoding DTScanEnv := ⟨2, encDTScanEnv⟩

private structure DTFillEnv where
  pairsBase : ℕ
  slotMap : ℕ
  origSlot : ℕ
  deriving DecidableEq

private word_enc_structure encDTFillEnv : DTFillEnv where
  pairsBase : wordWords,
  slotMap : wordWords,
  origSlot : wordWords

private instance : WordEncoding DTFillEnv := ⟨3, encDTFillEnv⟩

private structure DTWalkBranchArgs where
  edgeBase : ℕ
  jA : ℕ
  jB : ℕ
  node : ℕ
  deriving DecidableEq

private word_enc_structure encDTWalkBranchArgs : DTWalkBranchArgs where
  edgeBase : wordWords,
  jA : wordWords,
  jB : wordWords,
  node : wordWords

private instance : WordEncoding DTWalkBranchArgs := ⟨4, encDTWalkBranchArgs⟩

private structure DTWalkEnv where
  intBase : ℕ
  origSlot : ℕ
  edgeBase : ℕ
  deriving DecidableEq

private word_enc_structure encDTWalkEnv : DTWalkEnv where
  intBase : wordWords,
  origSlot : wordWords,
  edgeBase : wordWords

private instance : WordEncoding DTWalkEnv := ⟨3, encDTWalkEnv⟩

private structure DTEmitEnv where
  ansMask : ℕ
  origSlot : ℕ
  edgeBase : ℕ
  outBase : ℕ
  deriving DecidableEq

private word_enc_structure encDTEmitEnv : DTEmitEnv where
  ansMask : wordWords,
  origSlot : wordWords,
  edgeBase : wordWords,
  outBase : wordWords

private instance : WordEncoding DTEmitEnv := ⟨4, encDTEmitEnv⟩

private structure DTSetupOut where
  entryPtr : ℕ
  edgeCount : ℕ
  origSlot : ℕ
  slotMap : ℕ
  deriving DecidableEq

private word_enc_structure encDTSetupOut : DTSetupOut where
  entryPtr : wordWords,
  edgeCount : wordWords,
  origSlot : wordWords,
  slotMap : wordWords

private instance : WordEncoding DTSetupOut := ⟨4, encDTSetupOut⟩

private structure DTRunArgs where
  setup : DTSetupOut
  edgeBase : ℕ
  outBase : ℕ
  deriving DecidableEq

private word_enc_structure encDTRunArgs : DTRunArgs where
  setup : encDTSetupOut,
  edgeBase : wordWords,
  outBase : wordWords

private instance : WordEncoding DTRunArgs := ⟨6, encDTRunArgs⟩

private structure DTSetupArgs where
  tableBase : ℕ
  numVerts : ℕ
  numEdges : ℕ
  edgeBase : ℕ
  slotMap : ℕ
  deriving DecidableEq

private word_enc_structure encDTSetupArgs : DTSetupArgs where
  tableBase : wordWords,
  numVerts : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  slotMap : wordWords

private instance : WordEncoding DTSetupArgs := ⟨5, encDTSetupArgs⟩

/-- Query handle for single-component optimal decision-tree evaluation. -/
structure DTQuery where
  /-- Base address of precomputed decision-tree lookup table. -/
  tableBase : ℕ
  /-- Compacted vertex count `v ≤ r0`. -/
  numVerts : ℕ
  /-- Edge count `m`. -/
  numEdges : ℕ
  /-- Base address of stride-4 input `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Base address of stride-4 output `IndexedEdge` array. -/
  outBase : ℕ
  deriving DecidableEq

/-- Faithful five-word encoding of `DTQuery` as
`[tableBase, numVerts, numEdges, edgeBase, outBase]`. -/
word_enc_structure encDTQuery : DTQuery where
  tableBase : wordWords,
  numVerts : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  outBase : wordWords

/-- Registered `WordEncoding` instance for `DTQuery`. -/
instance : WordEncoding DTQuery := ⟨5, encDTQuery⟩

/-- Query handle for single-component optimal decision-tree evaluation using a caller-supplied
reusable `slotMap` scratch buffer of size `v.choose 2`. -/
structure DTScratchQuery where
  /-- Base address of precomputed decision-tree lookup table. -/
  tableBase : ℕ
  /-- Compacted vertex count `v ≤ r0`. -/
  numVerts : ℕ
  /-- Edge count `m`. -/
  numEdges : ℕ
  /-- Base address of stride-4 input `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Base address of stride-4 output `IndexedEdge` array. -/
  outBase : ℕ
  /-- Base address of caller-supplied `v.choose 2`-word edge-pair scratch buffer. -/
  slotMap : ℕ
  deriving DecidableEq

/-- Faithful six-word encoding of `DTScratchQuery` as
`[tableBase, numVerts, numEdges, edgeBase, outBase, slotMap]`. -/
word_enc_structure encDTScratchQuery : DTScratchQuery where
  tableBase : wordWords,
  numVerts : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  outBase : wordWords,
  slotMap : wordWords

/-- Registered `WordEncoding` instance for `DTScratchQuery`. -/
instance : WordEncoding DTScratchQuery := ⟨6, encDTScratchQuery⟩

private theorem iterationSafe_map_fix {δ δ' σ : Type} (f : δ → δ')
    (step : δ' × σ → Memory.Prog σ) (safe : ℕ → δ' × σ → Memory.State → Prop)
    (safe' : ℕ → δ × σ → Memory.State → Prop)
    {w : ℕ} {d : δ}
    (hsafe : ∀ a s, safe w (f d, a) s → safe' w (d, a) s)
    {n : ℕ} {a : σ} {s : Memory.State}
    (h : iterationSafe step safe w (f d) n a s) :
    iterationSafe (fun x : δ × σ => step (f (Prod.fst x), Prod.snd x)) safe' w d n a s := by
  induction n generalizing a s with
  | zero => trivial
  | succ n ih => exact ⟨hsafe a s h.1, ih h.2⟩

private def copy4 (p : ℕ × ℕ) : Memory.Prog Unit :=
  Memory.copy (Prod.fst p) (Prod.snd p) 4

private theorem realizes_copy4 :
    Realizes .exact copy4 WordEncoding.encode WordEncoding.encode
      (fun w p s => Fits w 16 ∧ Prod.fst p + 4 ≤ s.frontier ∧ Prod.snd p + 4 ≤ s.frontier)
      (fun _ _ => 0) := by
  unfold copy4
  realize [realizes_copy]
  all_goals
    obtain ⟨h16, hp1, hp2⟩ := h
    first | exact hp1 | exact hp2 | fits

private def dtScanEdgeStep (x : DTScanEnv × DTScanState) : Memory.Prog DTScanState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let u ← Memory.read (env.edgeBase + 4 * st.idx)
  let v ← Memory.read (env.edgeBase + 4 * st.idx + 1)
  if u < v then
    let p := v * (v - 1) / 2 + u
    Memory.write (env.slotMap + p) st.idx
    pure ⟨st.idx + 1, st.mask ||| (1 <<< p)⟩
  else
    let p := u * (u - 1) / 2 + v
    Memory.write (env.slotMap + p) st.idx
    pure ⟨st.idx + 1, st.mask ||| (1 <<< p)⟩

private def dtScanEdgeStepSafe (w : ℕ) (x : DTScanEnv × DTScanState)
    (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  let u := s.mem (env.edgeBase + 4 * st.idx)
  let v := s.mem (env.edgeBase + 4 * st.idx + 1)
  let hi := if u < v then v else u
  let lo := if u < v then u else v
  let p := hi * (hi - 1) / 2 + lo
  Fits w 16 ∧ Fits w (st.idx + 1) ∧ 1 ≤ hi ∧ Fits w (hi * (hi - 1)) ∧
  Fits w (st.mask ||| (1 <<< p)) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtScanEdgeStep x))

private theorem realizes_dtScanEdgeStep : Realizes .exact
    dtScanEdgeStep
    (appendWords (WordEncoding.encode (α := DTScanEnv)) (WordEncoding.encode (α := DTScanState)))
    (WordEncoding.encode (α := DTScanState)) dtScanEdgeStepSafe (fun _ _ => 0) := by
  unfold dtScanEdgeStep; realize
  all_goals
    obtain ⟨h16, hidx, hhi, hmul, hor, hv⟩ := h; have hfront := hmem.frontier_fits
    dsimp only [dtScanEdgeStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.step_read, Memory.valid] at hv
    try simp only [hc, ite_true, ite_false] at hhi hmul hor hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.write, Memory.valid] at hv
    first | exact hhi | decide | fits

private def dtFillOrigStep (x : DTFillEnv × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let j := Prod.snd x
  let p ← Memory.read (env.pairsBase + j)
  let slot ← Memory.read (env.slotMap + p)
  Memory.write (env.origSlot + j) slot
  pure (j + 1)

private def dtFillOrigStepSafe (w : ℕ) (x : DTFillEnv × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (Prod.snd x + 1) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtFillOrigStep x))

private theorem realizes_dtFillOrigStep : Realizes .exact
    dtFillOrigStep
    (appendWords (WordEncoding.encode (α := DTFillEnv)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := ℕ)) dtFillOrigStepSafe (fun _ _ => 0) := by
  unfold dtFillOrigStep; realize
  all_goals
    obtain ⟨h16, hidx, hv⟩ := h; have hfront := hmem.frontier_fits
    dsimp only [dtFillOrigStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.valid] at hv
    fits

private def dtWalkBranch (d : DTWalkBranchArgs) : Memory.Prog ℕ := do
  let wA ← Memory.read (d.edgeBase + 4 * d.jA + 2)
  let wB ← Memory.read (d.edgeBase + 4 * d.jB + 2)
  if wA < wB then pure (2 * d.node)
  else if wA = wB then
    if d.jA < d.jB then pure (2 * d.node) else pure (2 * d.node + 1)
  else pure (2 * d.node + 1)

private def dtWalkBranchSafe (w : ℕ) (d : DTWalkBranchArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (2 * d.node + 1) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtWalkBranch d))

private theorem realizes_dtWalkBranch : Realizes .exact
    dtWalkBranch (WordEncoding.encode (α := DTWalkBranchArgs)) (WordEncoding.encode (α := ℕ))
    dtWalkBranchSafe (fun _ _ => 0) := by
  unfold dtWalkBranch
  realize
  all_goals
    obtain ⟨h16, hnode, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [dtWalkBranch, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.step_read, Memory.valid] at hv
    fits

private def dtWalkStep (x : DTWalkEnv × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let node := Prod.snd x
  let a ← Memory.read (env.intBase + 2 * (node - 1))
  let b ← Memory.read (env.intBase + 2 * (node - 1) + 1)
  let jA ← Memory.read (env.origSlot + a)
  let jB ← Memory.read (env.origSlot + b)
  dtWalkBranch ⟨env.edgeBase, jA, jB, node⟩

private def dtWalkStepSafe (w : ℕ) (x : DTWalkEnv × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ 1 ≤ Prod.snd x ∧ Fits w (2 * Prod.snd x + 1) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtWalkStep x))

private theorem realizes_dtWalkStep : Realizes .exact
    dtWalkStep
    (appendWords (WordEncoding.encode (α := DTWalkEnv)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := ℕ)) dtWalkStepSafe (fun _ _ => 0) := by
  unfold dtWalkStep; realize [realizes_dtWalkBranch]
  all_goals
    obtain ⟨h16, h1, hnode, hv⟩ := h; have hfront := hmem.frontier_fits
    dsimp only [dtWalkStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.step_read, Memory.valid] at hv
    first | exact h1 | exact ⟨h16, hnode, hv.right.right.right.right⟩ | fits

private def dtEmitStep (x : DTEmitEnv × DTScanState) : Memory.Prog DTScanState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let slot ← Memory.read (env.origSlot + st.idx)
  if (env.ansMask >>> st.idx) &&& 1 = 1 then
    copy4 (env.edgeBase + 4 * slot, env.outBase + 4 * st.mask)
    pure ⟨st.idx + 1, st.mask + 1⟩
  else
    pure ⟨st.idx + 1, st.mask⟩

private def dtEmitStepSafe (w : ℕ) (x : DTEmitEnv × DTScanState) (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  Fits w 16 ∧ Fits w (st.idx + 1) ∧ Fits w (st.mask + 1) ∧
  env.origSlot + st.idx < s.frontier ∧
  ((env.ansMask >>> st.idx) &&& 1 = 1 →
    env.edgeBase + 4 * s.mem (env.origSlot + st.idx) + 4 ≤ s.frontier ∧
    env.outBase + 4 * st.mask + 4 ≤ s.frontier)

private theorem realizes_dtEmitStep_history : Realizes .exact
    dtEmitStep
    (appendWords (WordEncoding.encode (α := DTEmitEnv)) (WordEncoding.encode (α := DTScanState)))
    (WordEncoding.encode (α := DTScanState))
    (fun w x s => dtEmitStepSafe w x s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtEmitStep x)))
    (fun _ _ => 0) := by
  unfold dtEmitStep; realize [realizes_copy4]
  all_goals
    obtain ⟨⟨h16, hidx, hmask, hlt, hcopy⟩, hv⟩ := h; have hfront := hmem.frontier_fits
    dsimp only [dtEmitStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.step_read, Memory.valid] at hv
    first | exact (hcopy hc).1 | exact (hcopy hc).2 | fits

private theorem realizes_dtEmitStep : Realizes .exact
    dtEmitStep
    (appendWords (WordEncoding.encode (α := DTEmitEnv)) (WordEncoding.encode (α := DTScanState)))
    (WordEncoding.encode (α := DTScanState)) dtEmitStepSafe (fun _ _ => 0) :=
  realizes_dtEmitStep_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

private def evalDTSetupWithSlotMap (d : DTSetupArgs) : Memory.Prog DTSetupOut := do
  let scan ← iterate dtScanEdgeStep ⟨d.edgeBase, d.slotMap⟩ d.numEdges ⟨0, 0⟩
  let entryPtr ← Memory.read (d.tableBase + scan.mask)
  let e ← Memory.read entryPtr
  let origSlot ← Memory.allocDirty e
  pure ⟨entryPtr, e, origSlot, d.slotMap⟩

private def evalDTSetupWithSlotMapSafe (w : ℕ) (d : DTSetupArgs) (s : Memory.State) : Prop :=
  let scan := (Memory.spec 0).clientResult s
    (iterate dtScanEdgeStep ⟨d.edgeBase, d.slotMap⟩ d.numEdges ⟨0, 0⟩)
  let s1 := (Memory.spec 0).clientState s
    (iterate dtScanEdgeStep ⟨d.edgeBase, d.slotMap⟩ d.numEdges ⟨0, 0⟩)
  let entryPtr := s1.mem (d.tableBase + scan.mask)
  let e := s1.mem entryPtr
  Fits w 16 ∧ 1 ≤ d.numVerts ∧ Fits w (d.numVerts * (d.numVerts - 1)) ∧
  Fits w (d.tableBase + scan.mask) ∧ Fits w (s1.frontier + e) ∧
  d.tableBase + scan.mask < s1.frontier ∧ entryPtr < s1.frontier ∧
  iterationSafe dtScanEdgeStep dtScanEdgeStepSafe w ⟨d.edgeBase, d.slotMap⟩ d.numEdges ⟨0, 0⟩ s

private theorem realizes_evalDTSetupWithSlotMap : Realizes .exact
    evalDTSetupWithSlotMap (WordEncoding.encode (α := DTSetupArgs))
    (WordEncoding.encode (α := DTSetupOut)) evalDTSetupWithSlotMapSafe (fun _ _ => 0) := by
  unfold evalDTSetupWithSlotMap
  realize [realizes_dtScanEdgeStep]
  all_goals
    obtain ⟨h16, hnv, hmul, htb, hs1, hlt1, hlt2, hit⟩ := h
    have hfront := hmem.frontier_fits
    have hw_sm : Fits w d.slotMap := by
      have h4 : Fits w (encDTSetupArgs d 4) := hwords 4; simpa using h4
    first
    | exact iterationSafe_map_fix
        (fun p : DTSetupArgs => (⟨p.edgeBase, p.slotMap⟩ : DTScanEnv))
        dtScanEdgeStep dtScanEdgeStepSafe _ (fun _ _ hs => hs) hit
    | fits

private def evalDTRunTree (d : DTRunArgs) : Memory.Prog ℕ := do
  let _ ← iterate dtFillOrigStep
    ⟨d.setup.entryPtr + 2, d.setup.slotMap, d.setup.origSlot⟩ d.setup.edgeCount 0
  let depth ← Memory.read (d.setup.entryPtr + 1)
  let node ← iterate dtWalkStep
    ⟨d.setup.entryPtr + 2 + d.setup.edgeCount, d.setup.origSlot, d.edgeBase⟩ depth 1
  let ansMask ← Memory.read
    (d.setup.entryPtr + 2 + d.setup.edgeCount + 2 * ((1 <<< depth) - 1) + (node - (1 <<< depth)))
  let res ← iterate dtEmitStep
    ⟨ansMask, d.setup.origSlot, d.edgeBase, d.outBase⟩ d.setup.edgeCount ⟨0, 0⟩
  pure res.mask

private def evalDTRunTreeSafe (w : ℕ) (d : DTRunArgs) (s : Memory.State) : Prop :=
  let fillEnv : DTFillEnv := ⟨d.setup.entryPtr + 2, d.setup.slotMap, d.setup.origSlot⟩
  let s1 := (Memory.spec 0).clientState s (iterate dtFillOrigStep fillEnv d.setup.edgeCount 0)
  let depth := s1.mem (d.setup.entryPtr + 1)
  let walkEnv : DTWalkEnv :=
    ⟨d.setup.entryPtr + 2 + d.setup.edgeCount, d.setup.origSlot, d.edgeBase⟩
  let node := (Memory.spec 0).clientResult s1 (iterate dtWalkStep walkEnv depth 1)
  let s2 := (Memory.spec 0).clientState s1 (iterate dtWalkStep walkEnv depth 1)
  let pow2d := 1 <<< depth
  let intBase := d.setup.entryPtr + 2 + d.setup.edgeCount
  let leafAddr := intBase + 2 * (pow2d - 1) + (node - pow2d)
  let ansMask := s2.mem leafAddr
  Fits w 16 ∧ Fits w pow2d ∧ pow2d ≤ node ∧ Fits w (intBase + 2 * (pow2d - 1)) ∧
  Fits w (d.setup.entryPtr + 2 + d.setup.edgeCount) ∧ Fits w ansMask ∧ Fits w leafAddr ∧
  d.setup.entryPtr + 1 < s1.frontier ∧ leafAddr < s2.frontier ∧
  iterationSafe dtFillOrigStep dtFillOrigStepSafe w fillEnv d.setup.edgeCount 0 s ∧
  iterationSafe dtWalkStep dtWalkStepSafe w walkEnv depth 1 s1 ∧
  iterationSafe dtEmitStep dtEmitStepSafe w
    ⟨ansMask, d.setup.origSlot, d.edgeBase, d.outBase⟩ d.setup.edgeCount ⟨0, 0⟩ s2

private theorem realizes_evalDTRunTree : Realizes .exact
    evalDTRunTree (WordEncoding.encode (α := DTRunArgs)) (WordEncoding.encode (α := ℕ))
    evalDTRunTreeSafe (fun _ _ => 0) := by
  unfold evalDTRunTree
  realize [realizes_dtFillOrigStep, realizes_dtWalkStep, realizes_dtEmitStep]
  all_goals
    obtain ⟨h16, hp, hle, hlt, hint, ham, hla, hd1, hl, hf, hw, he⟩ := h
    have hfront := hmem.frontier_fits
    have hw_ep : Fits w d.setup.entryPtr := by
      have h0 : Fits w (encDTRunArgs d 0) := hwords 0; simpa using h0
    have hw_ec : Fits w d.setup.edgeCount := by
      have h1 : Fits w (encDTRunArgs d 1) := hwords 1; simpa using h1
    have hw_os : Fits w d.setup.origSlot := by
      have h2 : Fits w (encDTRunArgs d 2) := hwords 2; simpa using h2
    have hw_sm : Fits w d.setup.slotMap := by
      have h3 : Fits w (encDTRunArgs d 3) := hwords 3; simpa using h3
    have hw_eb : Fits w d.edgeBase := by
      have h4 : Fits w (encDTRunArgs d 4) := hwords 4; simpa using h4
    have hw_ob : Fits w d.outBase := by
      have h5 : Fits w (encDTRunArgs d 5) := hwords 5; simpa using h5
    first
    | exact iterationSafe_map_fix
        (fun p : DTRunArgs =>
          (⟨p.setup.entryPtr + 2, p.setup.slotMap, p.setup.origSlot⟩ : DTFillEnv))
        dtFillOrigStep dtFillOrigStepSafe _
        (fun _ _ hs => ⟨by dsimp only; exact hint.of_le (by omega), hs⟩) hf
    | exact iterationSafe_map_fix
        (fun p : (DTRunArgs × ℕ) × ℕ =>
          (⟨p.1.1.setup.entryPtr + 2 + p.1.1.setup.edgeCount, p.1.1.setup.origSlot,
            p.1.1.edgeBase⟩ : DTWalkEnv))
        dtWalkStep dtWalkStepSafe _ (fun _ _ hs => ⟨by dsimp only; exact hint, hs⟩) hw
    | exact iterationSafe_map_fix
        (fun p : (((DTRunArgs × ℕ) × ℕ) × ℕ) × ℕ =>
          (⟨p.2, p.1.1.1.1.setup.origSlot, p.1.1.1.1.edgeBase,
            p.1.1.1.1.outBase⟩ : DTEmitEnv))
        dtEmitStep dtEmitStepSafe _ (fun _ _ hs => hs) he
    | (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow)
    | exact hle
    | fits

/-- Evaluates the precomputed optimal decision tree on a vertex-compacted simple graph `C_i`
using a caller-supplied `slotMap` buffer of size `d.numVerts.choose 2`, emitting `F_i` at
`d.outBase` and returning `|F_i|` in `O(m_i + optDepth C_i + 1)` time with `work = 0`. -/
def evalDecisionTreeWithSlotMapProg (d : DTScratchQuery) : Memory.Prog ℕ := do
  if d.numEdges = 0 then pure 0
  else if d.numEdges = 1 then
    copy4 (d.edgeBase, d.outBase)
    pure 1
  else
    let st ← evalDTSetupWithSlotMap ⟨d.tableBase, d.numVerts, d.numEdges, d.edgeBase, d.slotMap⟩
    evalDTRunTree ⟨st, d.edgeBase, d.outBase⟩

/-- Native safety domain for `evalDecisionTreeWithSlotMapProg`. -/
def evalDecisionTreeWithSlotMapProgSafe (w : ℕ) (d : DTScratchQuery) (s : Memory.State) : Prop :=
  Fits w 16 ∧
  (d.numEdges = 1 → d.edgeBase + 4 ≤ s.frontier ∧ d.outBase + 4 ≤ s.frontier) ∧
  (d.numEdges ≠ 0 → d.numEdges ≠ 1 →
    let setupArgs : DTSetupArgs :=
      ⟨d.tableBase, d.numVerts, d.numEdges, d.edgeBase, d.slotMap⟩
    let st := (Memory.spec 0).clientResult s (evalDTSetupWithSlotMap setupArgs)
    let s1 := (Memory.spec 0).clientState s (evalDTSetupWithSlotMap setupArgs)
    evalDTSetupWithSlotMapSafe w setupArgs s ∧
    evalDTRunTreeSafe w ⟨st, d.edgeBase, d.outBase⟩ s1)

/-- Uniform `Realizes .exact` certificate for `evalDecisionTreeWithSlotMapProg` with
`work = 0`. -/
theorem realizes_evalDecisionTreeWithSlotMapProg : Realizes .exact
    evalDecisionTreeWithSlotMapProg (WordEncoding.encode (α := DTScratchQuery))
    (WordEncoding.encode (α := ℕ)) evalDecisionTreeWithSlotMapProgSafe (fun _ _ => 0) := by
  unfold evalDecisionTreeWithSlotMapProg
  realize [realizes_copy4, realizes_evalDTSetupWithSlotMap, realizes_evalDTRunTree]
  all_goals
    obtain ⟨h16, h1, h2⟩ := h
    have hw_tb : Fits w d.tableBase := by
      have h0 : Fits w (encDTScratchQuery d 0) := hwords 0; simpa using h0
    have hw_nv : Fits w d.numVerts := by
      have h1 : Fits w (encDTScratchQuery d 1) := hwords 1; simpa using h1
    have hw_ne : Fits w d.numEdges := by
      have h2 : Fits w (encDTScratchQuery d 2) := hwords 2; simpa using h2
    have hw_eb : Fits w d.edgeBase := by
      have h3 : Fits w (encDTScratchQuery d 3) := hwords 3; simpa using h3
    have hw_ob : Fits w d.outBase := by
      have h4 : Fits w (encDTScratchQuery d 4) := hwords 4; simpa using h4
    have hw_sm : Fits w d.slotMap := by
      have h5 : Fits w (encDTScratchQuery d 5) := hwords 5; simpa using h5
    first
    | exact (h1 ‹_›).1
    | exact (h1 ‹_›).2
    | exact (h2 ‹_› ‹_›).1
    | exact (h2 ‹_› ‹_›).2
    | exact h16
    | fits

/-- Evaluates the precomputed optimal decision tree on a vertex-compacted simple graph `C_i`,
emitting `F_i` at `d.outBase` and returning `|F_i|` in `O(m_i + optDepth C_i + 1)` time with
`work = 0`. -/
def evalDecisionTreeProg (d : DTQuery) : Memory.Prog ℕ := do
  if d.numEdges = 0 then pure 0
  else if d.numEdges = 1 then
    copy4 (d.edgeBase, d.outBase)
    pure 1
  else
    let slotMap ← Memory.allocDirty (d.numVerts * (d.numVerts - 1) / 2)
    let st ← evalDTSetupWithSlotMap ⟨d.tableBase, d.numVerts, d.numEdges, d.edgeBase, slotMap⟩
    evalDTRunTree ⟨st, d.edgeBase, d.outBase⟩

/-- Native safety domain for `evalDecisionTreeProg`. -/
def evalDecisionTreeProgSafe (w : ℕ) (d : DTQuery) (s : Memory.State) : Prop :=
  Fits w 16 ∧
  (d.numEdges = 1 → d.edgeBase + 4 ≤ s.frontier ∧ d.outBase + 4 ≤ s.frontier) ∧
  (d.numEdges ≠ 0 → d.numEdges ≠ 1 →
    let maxE := d.numVerts * (d.numVerts - 1) / 2
    let slotMap := s.frontier
    let s0 : Memory.State := ⟨s.mem, s.frontier + maxE⟩
    let setupArgs : DTSetupArgs := ⟨d.tableBase, d.numVerts, d.numEdges, d.edgeBase, slotMap⟩
    let st := (Memory.spec 0).clientResult s0 (evalDTSetupWithSlotMap setupArgs)
    let s1 := (Memory.spec 0).clientState s0 (evalDTSetupWithSlotMap setupArgs)
    1 ≤ d.numVerts ∧ Fits w d.numVerts ∧ Fits w (d.numVerts * (d.numVerts - 1)) ∧
    Fits w maxE ∧ Fits w (s.frontier + maxE) ∧
    evalDTSetupWithSlotMapSafe w setupArgs s0 ∧
    evalDTRunTreeSafe w ⟨st, d.edgeBase, d.outBase⟩ s1)

/-- Uniform `Realizes .exact` certificate for `evalDecisionTreeProg` with `work = 0`. -/
theorem realizes_evalDecisionTreeProg : Realizes .exact
    evalDecisionTreeProg (WordEncoding.encode (α := DTQuery)) (WordEncoding.encode (α := ℕ))
    evalDecisionTreeProgSafe (fun _ _ => 0) := by
  unfold evalDecisionTreeProg
  realize [realizes_copy4, realizes_evalDTSetupWithSlotMap, realizes_evalDTRunTree]
  all_goals
    obtain ⟨h16, h1, h2⟩ := h
    have hfront := hmem.frontier_fits
    have hw_tb : Fits w d.tableBase := by
      have h0 : Fits w (encDTQuery d 0) := hwords 0; simpa using h0
    have hw_nv : Fits w d.numVerts := by
      have h1 : Fits w (encDTQuery d 1) := hwords 1; simpa using h1
    have hw_ne : Fits w d.numEdges := by
      have h2 : Fits w (encDTQuery d 2) := hwords 2; simpa using h2
    have hw_eb : Fits w d.edgeBase := by
      have h3 : Fits w (encDTQuery d 3) := hwords 3; simpa using h3
    have hw_ob : Fits w d.outBase := by
      have h4 : Fits w (encDTQuery d 4) := hwords 4; simpa using h4
    first
    | exact (h1 ‹_›).1
    | exact (h1 ‹_›).2
    | exact (h2 ‹_› ‹_›).1
    | exact (h2 ‹_› ‹_›).2.2.1
    | exact (h2 ‹_› ‹_›).2.2.2.2.2.1
    | exact (h2 ‹_› ‹_›).2.2.2.2.2.2
    | decide
    | exact h16
    | fits

/-! ## Section 3: Specifications for Setup, Tree Walk, Emission, and Main Evaluation -/

private theorem wellFormed_copy4 {w : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (src dst : ℕ) :
    Memory.WellFormed w ⟨ArrayCopy.copyPrefix s.mem src dst 4, s.frontier⟩ :=
  ⟨hwf.frontier_fits, fun a => by
    dsimp only
    by_cases ha : dst ≤ a ∧ a < dst + 4
    · rw [show a = dst + (a - dst) by omega, ArrayCopy.copyPrefix_read (by omega)]
      exact hwf.mem_fits _
    · rw [ArrayCopy.copyPrefix_outside ha]; exact hwf.mem_fits _⟩

private theorem walkCompleteTree_bounds {e dInit intBase leafBase : ℕ} {mem : ℕ → ℕ}
    (cmp : Fin e → Fin e → Bool) :
    ∀ {d node : ℕ} {T : MSFDT e},
      HoldsCompleteTree dInit intBase leafBase d node mem T →
      2 ^ dInit ≤ walkCompleteTree intBase leafBase mem cmp d node ∧
      walkCompleteTree intBase leafBase mem cmp d node < 2 ^ (dInit + 1)
  | 0, _, .node _ _ _ _, h => absurd h holdsCompleteTree_zero_node
  | 0, _, .leaf _, h => let hh := holdsCompleteTree_leaf.mp h; ⟨hh.1, hh.2.1⟩
  | _ + 1, _, .leaf _, h => absurd h holdsCompleteTree_succ_leaf
  | d + 1, node, .node a b l r, h => by
    obtain ⟨_, _, ha_m, hb_m, hl, hr⟩ := holdsCompleteTree_node.mp h
    dsimp only [walkCompleteTree]
    have ha : mem (intBase + 2 * (node - 1)) < e := ha_m ▸ a.isLt
    have hb : mem (intBase + 2 * (node - 1) + 1) < e := hb_m ▸ b.isLt
    simp only [ha, hb, and_self, ↓reduceDIte]
    split_ifs <;> [exact walkCompleteTree_bounds cmp hl; exact walkCompleteTree_bounds cmp hr]

private theorem evalDTSetupWithSlotMap_spec {w r0 tableFrontier : ℕ} {d : DTSetupArgs}
    {C : List (IndexedEdge d.numVerts)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hvr : d.numVerts ≤ r0) (hm_eq : d.numEdges = C.length) (hm_ge : 2 ≤ C.length)
    (hsimp : IsSimple (edgeEnds (C.map IndexedEdge.toWeighted)))
    (hin : HoldsIndexedEdges d.edgeBase C s.mem)
    (hin_lt : d.edgeBase + 4 * C.length ≤ s.frontier)
    (htab : HoldsDTTable r0 d.tableBase s.mem)
    (hbnd : DTTableInBounds r0 d.tableBase tableFrontier s.mem)
    (htab_fr : tableFrontier ≤ s.frontier)
    (hslot_lt : d.slotMap + d.numVerts.choose 2 ≤ s.frontier)
    (hslot_disj_in :
      d.edgeBase + 4 * C.length ≤ d.slotMap ∨ d.slotMap + d.numVerts.choose 2 ≤ d.edgeBase)
    (hslot_disj_tab : ∀ a < tableFrontier,
      ¬(d.slotMap ≤ a ∧ a < d.slotMap + d.numVerts.choose 2))
    (hfit_mul : Fits w (d.numVerts * (d.numVerts - 1)))
    (hfit : Fits w (s.frontier + C.length)) :
    Memory.FramedTriple w s (evalDTSetupWithSlotMap d) (3 * C.length + 3)
      (Set.Ico d.slotMap (d.slotMap + d.numVerts.choose 2)) fun res s' =>
      evalDTSetupWithSlotMapSafe w d s ∧
      s'.frontier = s.frontier + C.length ∧
      Memory.WellFormed w s' ∧
      res.slotMap = d.slotMap ∧
      res.origSlot = s.frontier ∧
      res.entryPtr = s.mem (d.tableBase + dtGraphMask (C.map fun e => (e.u, e.v))) ∧
      res.edgeCount = C.length ∧
      (∀ k (hk : k < C.length),
        s'.mem (res.slotMap + edgePairIdx C[k].u.val C[k].v.val) = k) := by
  have hbnd' := (dtTableInBounds_iff _ _ _ _).mp hbnd
  have hsimp' := (isSimple_iff _).mp hsimp
  have hno : ∀ e ∈ C, e.u ≠ e.v := fun e he => by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
    have hk' : k < (C.map IndexedEdge.toWeighted).length := by simpa using hk
    simpa [edgeEnds, IndexedEdge.toWeighted] using hsimp'.1 ⟨k, hk'⟩
  have hnv : 1 ≤ d.numVerts := Nat.lt_of_le_of_lt (Nat.zero_le _) (C[0]'(by omega)).u.isLt
  let maxE := d.numVerts.choose 2
  let slotMap := d.slotMap
  have hpow_v_le : 2 ^ maxE ≤ 2 ^ r0.choose 2 := Nat.pow_le_pow_right (by decide) (by
    dsimp only [maxE]; rw [Nat.choose_two_right, Nat.choose_two_right]
    exact Nat.div_le_div_right (Nat.mul_le_mul hvr (Nat.sub_le_sub_right hvr 1)))
  let scanEnv : DTScanEnv := ⟨d.edgeBase, slotMap⟩
  let S_scan : Set ℕ := Set.Ico slotMap (slotMap + maxE)
  let invCore (k : ℕ) (st : DTScanState) (t : Memory.State) : Prop :=
    st.idx = k ∧
    st.mask = ((C.take k).map fun e => (e.u, e.v)).foldl
      (fun acc e => acc ||| (1 <<< edgePairIdx e.1.val e.2.val)) 0 ∧
    t.frontier = s.frontier ∧
    (∀ a, a ∉ S_scan → t.mem a = s.mem a) ∧
    ∀ i (hi : i < k), ∀ (hiC : i < C.length),
      t.mem (slotMap + edgePairIdx (C[i]'hiC).u.val (C[i]'hiC).v.val) = i
  let inv (k : ℕ) (st : DTScanState) (t : Memory.State) : Prop :=
    invCore k st t ∧ Memory.WellFormed w t
  have hstep : ∀ k < C.length, ∀ st t, inv k st t →
      ((Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (dtScanEdgeStep (scanEnv, st))) →
        dtScanEdgeStepSafe w (scanEnv, st) t) ∧
      Memory.FramedTriple w t (dtScanEdgeStep (scanEnv, st)) 3 S_scan (inv (k + 1)) := by
    intro k hk_lt st t ⟨⟨hidx_eq, hmask_eq, htfr, hlt_s, hslots⟩, hwt⟩
    subst hidx_eq
    have hidx_fit : Fits w (st.idx + 1) := hfit.of_le (by omega)
    have hin_t : HoldsIndexedEdges d.edgeBase C t.mem :=
      hin.congr fun a ha1 ha2 => hlt_s a (by
        simp only [S_scan, Set.mem_Ico]; rcases hslot_disj_in with h | h <;> omega)
    obtain ⟨hu, hv, _, _⟩ := hin_t st.idx hk_lt
    set uM := t.mem (d.edgeBase + 4 * st.idx)
    set vM := t.mem (d.edgeBase + 4 * st.idx + 1)
    set hi := if uM < vM then vM else uM
    set lo := if uM < vM then uM else vM
    have hp_lt : edgePairIdx C[st.idx].u.val C[st.idx].v.val < maxE :=
      edgePairIdx_lt_choose_two _ (hno _ (List.getElem_mem hk_lt))
    have hhi_ge : 1 ≤ hi := by
      have hne := Fin.val_ne_of_ne (hno _ (List.getElem_mem hk_lt))
      dsimp only [hi]; rw [hu, hv]; split_ifs <;> omega
    have hhi_le : hi ≤ d.numVerts - 1 := by
      dsimp only [hi]; rw [hu, hv]; split_ifs
      · exact Nat.le_sub_one_of_lt C[st.idx].v.isLt
      · exact Nat.le_sub_one_of_lt C[st.idx].u.isLt
    have hmul_fit : Fits w (hi * (hi - 1)) :=
      hfit_mul.of_le (Nat.mul_le_mul (hhi_le.trans (Nat.sub_le _ _))
        (Nat.sub_le_sub_right (hhi_le.trans (Nat.sub_le _ _)) 1))
    have hp_eq : hi * (hi - 1) / 2 + lo = edgePairIdx C[st.idx].u.val C[st.idx].v.val := by
      dsimp only [hi, lo, edgePairIdx, pairIdx]; rw [hu, hv]; split_ifs <;> rfl
    have hmask_lt : st.mask < 2 ^ maxE := by
      rw [hmask_eq]
      exact dtGraphMask_lt ((C.take st.idx).map fun e => (e.u, e.v)) fun e he => by
        rw [List.mem_map] at he; obtain ⟨e₀, he₀, rfl⟩ := he
        exact hno e₀ (List.mem_of_mem_take he₀)
    have hor_lt : st.mask ||| (1 <<< edgePairIdx C[st.idx].u.val C[st.idx].v.val) < 2 ^ maxE := by
      refine Nat.or_lt_two_pow hmask_lt ?_
      rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by decide) hp_lt
    have hor_fit : Fits w (st.mask ||| (1 <<< (hi * (hi - 1) / 2 + lo))) := by
      rw [hp_eq]
      have hpow_le_fr : 2 ^ maxE ≤ t.frontier := by have := hbnd'.1; omega
      exact hwt.frontier_fits.of_le (by omega)
    refine ⟨fun hv_st => ⟨h16, hidx_fit, hhi_ge, hmul_fit, hor_fit, hv_st⟩,
      Memory.FramedTriple.wellFormed hwt ?_⟩
    dsimp only [dtScanEdgeStep, scanEnv]
    refine Memory.FramedTriple.read_bind (by omega) ?_
    refine Memory.FramedTriple.read_bind (by omega) ?_
    refine Memory.FramedTriple.ite (fun huv => ?_) (fun huv => ?_)
    all_goals
      have haddr : hi * (hi - 1) / 2 + lo = edgePairIdx C[st.idx].u.val C[st.idx].v.val := hp_eq
      dsimp only [hi, lo, uM, vM] at haddr
      simp only [huv, ↓reduceIte] at haddr
      refine Memory.FramedTriple.write_bind_of_mem (by rw [haddr]; omega)
        (hidx_fit.of_le (by omega))
        (by simp only [S_scan, Set.mem_Ico]; rw [haddr]; omega) ?_
      have htake : C.take (st.idx + 1) = C.take st.idx ++ [C[st.idx]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk_lt]; simp
      refine Memory.FramedTriple.pure (c := 0) ⟨rfl, ?_, htfr, fun a ha => ?_,
        fun i hi hiC => ?_⟩
      · rw [haddr, htake, List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons,
          List.foldl_nil, hmask_eq]
      · dsimp only
        rw [Function.update_of_ne (fun heq => ha (by
          simp only [S_scan, Set.mem_Ico]; rw [heq, haddr]; omega))]
        exact hlt_s a ha
      · dsimp only; rw [haddr]
        by_cases hist : i = st.idx
        · subst hist; rw [Function.update_self]
        · have hp_ne : edgePairIdx (C[i]'hiC).u.val (C[i]'hiC).v.val ≠
              edgePairIdx C[st.idx].u.val C[st.idx].v.val := fun heq => by
            have hse := edgePairIdx_sym2_eq _ _
              (hno _ (List.getElem_mem hiC)) (hno _ (List.getElem_mem hk_lt)) heq
            have hlen_w : (C.map IndexedEdge.toWeighted).length = C.length := List.length_map _
            exact hist (congrArg Fin.val (hsimp'.2 (by
              simpa [edgeEnds, IndexedEdge.toWeighted] using hse :
              edgeEnds (C.map IndexedEdge.toWeighted) ⟨i, hlen_w.symm ▸ hiC⟩ =
              edgeEnds (C.map IndexedEdge.toWeighted) ⟨st.idx, hlen_w.symm ▸ hk_lt⟩)))
          rw [Function.update_of_ne (by omega)]; exact hslots i (by omega) hiC
  obtain ⟨hsafe_loop, hft_scan⟩ :=
    iterate_framedTriple_of_step dtScanEdgeStep dtScanEdgeStepSafe w scanEnv 3 C.length
      inv S_scan hstep ⟨0, 0⟩ s
      ⟨⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩, hwf⟩
  obtain ⟨_, _, _, ⟨hscan_idx, hscan_mask, hs1_fr, hlt_s1, hslots_s1⟩, hwf1⟩ :=
    framedTriple_iff_realization.mp hft_scan
  set scan := (Memory.spec 0).clientResult s (iterate dtScanEdgeStep scanEnv C.length ⟨0, 0⟩)
  set s1 := (Memory.spec 0).clientState s (iterate dtScanEdgeStep scanEnv C.length ⟨0, 0⟩)
  rw [List.take_of_length_le le_rfl] at hscan_mask
  have hmask_lt_v : dtGraphMask (C.map fun e => (e.u, e.v)) < 2 ^ d.numVerts.choose 2 :=
    dtGraphMask_lt _ fun e he => by
      rw [List.mem_map] at he; obtain ⟨e₀, he₀, rfl⟩ := he; exact hno e₀ he₀
  have hmask_lt_r0 : dtGraphMask (C.map fun e => (e.u, e.v)) < 2 ^ r0.choose 2 :=
    hmask_lt_v.trans_le hpow_v_le
  have htab_v := holdsDTTable_for_le htab hvr hmask_lt_v
  dsimp only at htab_v; obtain ⟨_, hep_e, _, _, _, _, _, _, _⟩ := htab_v
  have hbnd_m := hbnd'.2 _ hmask_lt_r0; dsimp only at hbnd_m
  have htb_scan_eq : d.tableBase + scan.mask =
      d.tableBase + dtGraphMask (C.map fun e => (e.u, e.v)) := by rw [hscan_mask]; rfl
  have htb_lt_tab : d.tableBase + scan.mask < tableFrontier := by
    have := hbnd'.1; rw [htb_scan_eq]; omega
  have htb_not_S : d.tableBase + scan.mask ∉ S_scan := fun hx =>
    hslot_disj_tab _ htb_lt_tab hx
  have hep_s1 : s1.mem (d.tableBase + scan.mask) =
      s.mem (d.tableBase + dtGraphMask (C.map fun e => (e.u, e.v))) := by
    rw [hlt_s1 _ htb_not_S, htb_scan_eq]
  have h2d_pos : 0 <
      2 ^ s.mem (s.mem (d.tableBase + dtGraphMask (C.map fun e => (e.u, e.v))) + 1) :=
    Nat.two_pow_pos _
  have hep_lt_tab : s1.mem (d.tableBase + scan.mask) < tableFrontier := by rw [hep_s1]; omega
  have hep_not_S : s1.mem (d.tableBase + scan.mask) ∉ S_scan := fun hx =>
    hslot_disj_tab _ hep_lt_tab hx
  have he_s1 : s1.mem (s1.mem (d.tableBase + scan.mask)) = C.length := by
    rw [hep_s1, hlt_s1 _ (fun hx => hslot_disj_tab _ (by rw [← hep_s1]; exact hep_lt_tab) hx),
      hep_e]
    exact (endsOfMask_reindex_indexedEdges C hsimp).2.1
  have hfit_e : Fits w (s1.frontier + s1.mem (s1.mem (d.tableBase + scan.mask))) := by
    rw [hs1_fr, he_s1]; exact hfit
  have hscan_eq : (Memory.spec 0).clientResult s
      (iterate dtScanEdgeStep scanEnv C.length ⟨0, 0⟩) = scan := rfl
  have hs1_eq : (Memory.spec 0).clientState s
      (iterate dtScanEdgeStep scanEnv C.length ⟨0, 0⟩) = s1 := rfl
  have hsafe : evalDTSetupWithSlotMapSafe w d s := by
    refine ⟨h16, hnv, hfit_mul, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm_eq, hscan_eq]; exact hwf.frontier_fits.of_le (by omega)
    · rw [hm_eq]; exact hfit_e
    · rw [hm_eq, hscan_eq, hs1_eq]; omega
    · rw [hm_eq, hscan_eq, hs1_eq]; exact hep_lt_tab.trans_le (by omega)
    · rw [hm_eq]; exact hsafe_loop
  have hprog : evalDTSetupWithSlotMap d =
      (iterate dtScanEdgeStep ⟨d.edgeBase, d.slotMap⟩ C.length ⟨0, 0⟩ >>= fun scan' =>
        Memory.read (d.tableBase + scan'.mask) >>= fun entryPtr =>
        Memory.read entryPtr >>= fun e =>
        Memory.allocDirty e >>= fun origSlot =>
        pure (⟨entryPtr, e, origSlot, d.slotMap⟩ : DTSetupOut)) := by
    dsimp only [evalDTSetupWithSlotMap]; rw [hm_eq]
  rw [hprog]
  refine Memory.FramedTriple.mono (Memory.FramedTriple.bind_same (c₁ := 3 * C.length) (c₂ := 3)
    ((framedTriple_with_realization hft_scan).mono le_rfl (by
      rintro _ _ ⟨rfl, rfl, _⟩
      rw [hscan_eq, hs1_eq]
      refine Memory.FramedTriple.read_bind (by rw [hs1_fr]; omega) ?_
      refine Memory.FramedTriple.read_bind (hep_lt_tab.trans_le (by omega)) ?_
      refine Memory.FramedTriple.allocDirty_bind hfit_e ?_
      exact Memory.FramedTriple.pure (c := 0) ⟨hsafe, by rw [hs1_fr, he_s1],
        ⟨hfit_e, fun a => hwf1.mem_fits a⟩, rfl, hs1_fr, hep_s1, he_s1,
        fun k hk => hslots_s1 k hk hk⟩))) (by omega) fun _ _ h => h

private theorem iterate_dtFillOrigStep_spec {w e pairsBase slotMap origSlot : ℕ}
    {v : ℕ} {C : List (IndexedEdge v)} {mask : ℕ}
    (σ : Fin C.length ≃ Fin e) (hle : e = (maskEdgePairs v mask).length)
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (he_len : e = C.length)
    (hpairs_lt : pairsBase + e ≤ s.frontier)
    (horig_lt : origSlot + e ≤ s.frontier)
    (hslot_lt : ∀ j < e, slotMap + s.mem (pairsBase + j) < s.frontier)
    (hdisj_s : ∀ j < e, ¬(origSlot ≤ slotMap + s.mem (pairsBase + j) ∧
      slotMap + s.mem (pairsBase + j) < origSlot + e))
    (hdisj_p : ∀ j < e, ¬(origSlot ≤ pairsBase + j ∧ pairsBase + j < origSlot + e))
    (horig_val : ∀ j (hj : j < e),
      s.mem (slotMap + s.mem (pairsBase + j)) = (σ.symm ⟨j, hj⟩).val) :
    let env : DTFillEnv := ⟨pairsBase, slotMap, origSlot⟩
    let prog := iterate dtFillOrigStep env e 0
    iterationSafe dtFillOrigStep dtFillOrigStepSafe w env e 0 s ∧
    Memory.FramedTriple w s prog (3 * e) (Set.Ico origSlot (origSlot + e)) fun _ s' =>
      s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
      ∀ j (hj : j < e), s'.mem (origSlot + j) = (σ.symm ⟨j, hj⟩).val := by
  let env : DTFillEnv := ⟨pairsBase, slotMap, origSlot⟩
  let S : Set ℕ := Set.Ico origSlot (origSlot + e)
  let invCore (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s.frontier ∧
    (∀ x, x ∉ S → t.mem x = s.mem x) ∧
    ∀ j (hj : j < k), ∀ (hje : j < e), t.mem (origSlot + j) = (σ.symm ⟨j, hje⟩).val
  let inv (k a : ℕ) (t : Memory.State) : Prop := invCore k a t ∧ Memory.WellFormed w t
  have hstep : ∀ k < e, ∀ a t, inv k a t →
      ((Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (dtFillOrigStep (env, a))) →
        dtFillOrigStepSafe w (env, a) t) ∧
      Memory.FramedTriple w t (dtFillOrigStep (env, a)) 3 S (inv (k + 1)) := by
    intro k hk a t ⟨⟨ha, htfr, hframe, hpref⟩, hwt⟩
    subst a
    have hp_eq : t.mem (pairsBase + k) = s.mem (pairsBase + k) :=
      hframe _ (by simp only [S, Set.mem_Ico]; exact hdisj_p k hk)
    have hsm_eq : t.mem (slotMap + s.mem (pairsBase + k)) =
        s.mem (slotMap + s.mem (pairsBase + k)) :=
      hframe _ (by simp only [S, Set.mem_Ico]; exact hdisj_s k hk)
    have hfit_k1 : Fits w (k + 1) := hwf.frontier_fits.of_le (by omega)
    have hval_lt : t.mem (slotMap + t.mem (pairsBase + k)) < C.length := by
      rw [hp_eq, hsm_eq, horig_val k hk]; exact (σ.symm ⟨k, hk⟩).isLt
    have hval_fit : Fits w (t.mem (slotMap + t.mem (pairsBase + k))) :=
      hwf.frontier_fits.of_le (by omega)
    refine ⟨fun hv => ⟨h16, hfit_k1, hv⟩, Memory.FramedTriple.wellFormed hwt ?_⟩
    dsimp only [dtFillOrigStep, env]
    refine Memory.FramedTriple.read_bind (by omega) ?_
    refine Memory.FramedTriple.read_bind
      (by rw [hp_eq]; exact lt_of_lt_of_eq (hslot_lt k hk) htfr.symm) ?_
    refine Memory.FramedTriple.write_bind_of_mem (by omega) hval_fit
      (by simp only [S, Set.mem_Ico]; omega) ?_
    refine Memory.FramedTriple.pure ⟨rfl, htfr, fun x hx => ?_, fun j hj hje => ?_⟩
    · dsimp only
      rw [Function.update_of_ne (by simp only [S, Set.mem_Ico] at hx; omega)]
      exact hframe x hx
    · dsimp only
      by_cases hjk : j = k
      · subst j; rw [Function.update_self, hp_eq, hsm_eq, horig_val k hk]
      · rw [Function.update_of_ne (by omega)]; exact hpref j (by omega) hje
  obtain ⟨hsafe, hft⟩ := iterate_framedTriple_of_step dtFillOrigStep dtFillOrigStepSafe w env 3 e
    inv S hstep 0 s
    ⟨⟨rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩, hwf⟩
  exact ⟨hsafe, hft.mono le_rfl fun _ _ ⟨⟨_, hfr, _, hvals⟩, hwf'⟩ =>
    ⟨hfr, hwf', fun j hj => hvals j hj hj⟩⟩

private theorem iterate_dtWalkStep_spec {w v e dInit intBase leafBase edgeBase origSlot : ℕ}
    {C : List (IndexedEdge v)} {mask : ℕ} {T : MSFDT (maskEdgePairs v mask).length}
    {s : Memory.State} (σ : Fin C.length ≃ Fin (maskEdgePairs v mask).length)
    (he_len : e = (maskEdgePairs v mask).length)
    (hC_len : C.length = e)
    (hhold : HoldsCompleteTree dInit intBase leafBase dInit 1 s.mem T)
    (h16 : Fits w 16) (_hwf : Memory.WellFormed w s)
    (h2d_fit : Fits w (2 ^ (dInit + 1)))
    (hint_lt : intBase + 2 * (2 ^ dInit - 1) ≤ s.frontier)
    (horig_lt : origSlot + e ≤ s.frontier)
    (horig_val : ∀ j (hj : j < (maskEdgePairs v mask).length),
      s.mem (origSlot + j) = (σ.symm ⟨j, hj⟩).val)
    (hin : HoldsIndexedEdges edgeBase C s.mem)
    (hin_lt : edgeBase + 4 * C.length ≤ s.frontier) :
    let env : DTWalkEnv := ⟨intBase, origSlot, edgeBase⟩
    let cmp : Fin (maskEdgePairs v mask).length → Fin (maskEdgePairs v mask).length → Bool :=
      fun a b =>
        let i := σ.symm a
        let j := σ.symm b
        decide (C[i.val].weight < C[j.val].weight ∨
          (C[i.val].weight = C[j.val].weight ∧ i.val < j.val))
    let prog := iterate dtWalkStep env dInit 1
    iterationSafe dtWalkStep dtWalkStepSafe w env dInit 1 s ∧
    Memory.FramedTriple w s prog (6 * dInit) ∅ fun node s' =>
      s' = s ∧ node = walkCompleteTree intBase leafBase s.mem cmp dInit 1 := by
  let env : DTWalkEnv := ⟨intBase, origSlot, edgeBase⟩
  let cmp : Fin (maskEdgePairs v mask).length → Fin (maskEdgePairs v mask).length → Bool :=
    fun a b =>
      let i := σ.symm a
      let j := σ.symm b
      decide (C[i.val].weight < C[j.val].weight ∨
        (C[i.val].weight = C[j.val].weight ∧ i.val < j.val))
  let inv (k node : ℕ) (t : Memory.State) : Prop :=
    t = s ∧ node < 2 ^ (k + 1) ∧
    ∃ T' : MSFDT (maskEdgePairs v mask).length,
      HoldsCompleteTree dInit intBase leafBase (dInit - k) node s.mem T' ∧
      walkCompleteTree intBase leafBase s.mem cmp (dInit - k) node =
        walkCompleteTree intBase leafBase s.mem cmp dInit 1
  have hstep : ∀ k < dInit, ∀ node t, inv k node t →
      ((Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (dtWalkStep (env, node))) →
        dtWalkStepSafe w (env, node) t) ∧
      Memory.FramedTriple w t (dtWalkStep (env, node)) 6 ∅ (inv (k + 1)) := by
    intro k hk node t ⟨ht, hnode_lt, T', hhold', hwalk'⟩
    rcases ht.symm with rfl
    have hrem : dInit - k = (dInit - (k + 1)) + 1 := by omega
    rw [hrem] at hhold' hwalk'
    cases T' with
    | leaf _ => exact absurd hhold' holdsCompleteTree_succ_leaf
    | node a b l r =>
      obtain ⟨h1, _, ha_mem, hb_mem, hl, hr⟩ := holdsCompleteTree_node.mp hhold'
      have h2k_le : 2 ^ (k + 1) ≤ 2 ^ dInit := Nat.pow_le_pow_right (by decide) (by omega)
      have h2d_pos : 1 ≤ 2 ^ dInit := Nat.one_le_two_pow
      have hnode_lt_d : node < 2 ^ dInit := lt_of_lt_of_le hnode_lt h2k_le
      have hnode_fit : Fits w (2 * node + 1) := by
        rw [Nat.pow_succ'] at h2d_fit
        exact h2d_fit.of_le (by omega)
      have hjA_val : s.mem (origSlot + s.mem (intBase + 2 * (node - 1))) = (σ.symm a).val := by
        rw [ha_mem]; exact horig_val a.val a.isLt
      have hjB_val : s.mem (origSlot + s.mem (intBase + 2 * (node - 1) + 1)) = (σ.symm b).val := by
        rw [hb_mem]; exact horig_val b.val b.isLt
      have hft : Memory.FramedTriple w s (dtWalkStep (env, node)) 6 ∅ fun node' t' =>
          t' = s ∧
          (let wA := s.mem (edgeBase + 4 * (σ.symm a).val + 2)
           let wB := s.mem (edgeBase + 4 * (σ.symm b).val + 2)
           node' = if wA < wB then 2 * node
             else if wA = wB then
               if (σ.symm a).val < (σ.symm b).val then 2 * node else 2 * node + 1
             else 2 * node + 1) := by
        dsimp only [dtWalkStep, dtWalkBranch, env]
        refine Memory.FramedTriple.read_bind (by omega) ?_
        refine Memory.FramedTriple.read_bind (by omega) ?_
        refine Memory.FramedTriple.read_bind (by rw [ha_mem]; have := a.isLt; omega) ?_
        refine Memory.FramedTriple.read_bind (by rw [hb_mem]; have := b.isLt; omega) ?_
        refine Memory.FramedTriple.read_bind
          (by rw [hjA_val]; have := (σ.symm a).isLt; omega) ?_
        refine Memory.FramedTriple.read_bind
          (by rw [hjB_val]; have := (σ.symm b).isLt; omega) ?_
        rw [hjA_val, hjB_val]
        refine Memory.FramedTriple.ite (fun _ =>
          Memory.FramedTriple.pure (c := 0) ⟨rfl, by split_ifs; rfl⟩) fun _ =>
          Memory.FramedTriple.ite (fun _ => Memory.FramedTriple.ite
            (fun _ => Memory.FramedTriple.pure (c := 0) ⟨rfl, by split_ifs; rfl⟩)
            fun _ => Memory.FramedTriple.pure (c := 0) ⟨rfl, by split_ifs; rfl⟩)
            fun _ => Memory.FramedTriple.pure (c := 0) ⟨rfl, by split_ifs; rfl⟩
      obtain ⟨_, _, hwA, _⟩ := hin (σ.symm a).val (σ.symm a).isLt
      obtain ⟨_, _, hwB, _⟩ := hin (σ.symm b).val (σ.symm b).isLt
      have ha_e : s.mem (intBase + 2 * (node - 1)) < (maskEdgePairs v mask).length := by
        rw [ha_mem]; exact a.isLt
      have hb_e : s.mem (intBase + 2 * (node - 1) + 1) < (maskEdgePairs v mask).length := by
        rw [hb_mem]; exact b.isLt
      have ha_fin : (⟨s.mem (intBase + 2 * (node - 1)), ha_e⟩ :
          Fin (maskEdgePairs v mask).length) = a := Fin.ext ha_mem
      have hb_fin : (⟨s.mem (intBase + 2 * (node - 1) + 1), hb_e⟩ :
          Fin (maskEdgePairs v mask).length) = b := Fin.ext hb_mem
      dsimp only [walkCompleteTree] at hwalk'
      simp only [ha_e, hb_e, and_self, ↓reduceDIte, ha_fin, hb_fin] at hwalk'
      refine ⟨fun hv_st => ⟨h16, h1, hnode_fit, hv_st⟩,
        hft.mono le_rfl fun node' t' ⟨ht_eq, hnode'_eq⟩ => ?_⟩
      dsimp only at hnode'_eq; rw [hwA, hwB] at hnode'_eq
      refine ⟨ht_eq, ?_, ?_⟩
      · rw [hnode'_eq]; have h2 : 2 * node + 1 < 2 ^ (k + 1 + 1) := by rw [pow_succ']; omega
        split_ifs <;> omega
      · by_cases hc : cmp a b = true
        · have hcond := decide_eq_true_iff.mp hc
          have hn' : node' = 2 * node := by
            rw [hnode'_eq]; rcases hcond with h | ⟨_, _⟩ <;> split_ifs <;> rfl
          rw [hn']; exact ⟨l, hl, by simpa only [hc, ↓reduceIte] using hwalk'⟩
        · have hcf : cmp a b = false := Bool.eq_false_iff.mpr hc
          have hnot : ¬(C[(σ.symm a).val].weight < C[(σ.symm b).val].weight ∨
              (C[(σ.symm a).val].weight = C[(σ.symm b).val].weight ∧
               (σ.symm a).val < (σ.symm b).val)) := fun h => hc (decide_eq_true_eq.mpr h)
          have hn' : node' = 2 * node + 1 := by
            rw [hnode'_eq]; split_ifs <;> first | rfl | exact absurd (.inl ‹_›) hnot |
              exact absurd (.inr ⟨‹_›, ‹_›⟩) hnot
          rw [hn']; exact ⟨r, hr, by simpa only [hcf, Bool.false_eq_true, ↓reduceIte] using hwalk'⟩
  obtain ⟨hsafe, hft⟩ := iterate_framedTriple_of_step dtWalkStep dtWalkStepSafe w env 6 dInit
    inv ∅ hstep 1 s ⟨rfl, by decide, T, by simpa using hhold, by simp⟩
  exact ⟨hsafe, hft.mono le_rfl fun res t' ⟨ht_end, _, _, _, hwalk_end⟩ =>
    ⟨ht_end, (show walkCompleteTree intBase leafBase s.mem cmp (dInit - dInit) res = res by
      rw [Nat.sub_self]; rfl).symm.trans hwalk_end⟩⟩

private theorem iterate_dtEmitStep_spec {w v e ansMask origSlot edgeBase outBase : ℕ}
    {C : List (IndexedEdge v)} (σ : Fin C.length ≃ Fin e) (he_len : e = C.length)
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase C s.mem)
    (hin_lt : edgeBase + 4 * C.length ≤ s.frontier)
    (horig_lt : origSlot + e ≤ s.frontier)
    (hout_lt : outBase + 4 * e ≤ s.frontier)
    (hout_disj_in : edgeBase + 4 * C.length ≤ outBase ∨ outBase + 4 * e ≤ edgeBase)
    (hout_disj_orig : origSlot + e ≤ outBase ∨ outBase + 4 * e ≤ origSlot)
    (horig : ∀ j (hj : j < e), s.mem (origSlot + j) = (σ.symm ⟨j, hj⟩).val) :
    let env : DTEmitEnv := ⟨ansMask, origSlot, edgeBase, outBase⟩
    let prog := iterate dtEmitStep env e ⟨0, 0⟩
    let F := ((List.finRange e).filter fun j => ansMask.testBit j.val).map
      fun j => C[(σ.symm j).val]
    iterationSafe dtEmitStep dtEmitStepSafe w env e ⟨0, 0⟩ s ∧
    Memory.FramedTriple w s prog (9 * e) (Set.Ico outBase (outBase + 4 * e)) fun res s' =>
      res.mask = F.length ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
      HoldsIndexedEdges outBase F s'.mem := by
  let env : DTEmitEnv := ⟨ansMask, origSlot, edgeBase, outBase⟩
  let S : Set ℕ := Set.Ico outBase (outBase + 4 * e)
  let prefF : ℕ → List (IndexedEdge v) := fun k =>
    (((List.finRange e).take k).filter fun j => ansMask.testBit j.val).map
      fun j => C[(σ.symm j).val]
  let inv (k : ℕ) (st : DTScanState) (t : Memory.State) : Prop :=
    st.idx = k ∧ st.mask = (prefF k).length ∧ t.frontier = s.frontier ∧
    Memory.WellFormed w t ∧ HoldsIndexedEdges edgeBase C t.mem ∧
    (∀ j (hj : j < e), t.mem (origSlot + j) = (σ.symm ⟨j, hj⟩).val) ∧
    HoldsIndexedEdges outBase (prefF k) t.mem
  have hstep : ∀ k < e, ∀ st t, inv k st t →
      ((Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (dtEmitStep (env, st))) →
        dtEmitStepSafe w (env, st) t) ∧
      Memory.FramedTriple w t (dtEmitStep (env, st)) 9 S (inv (k + 1)) := by
    intro k hk st t ⟨hidx, hmask_len, htfr, hwt, hin_t, horig_t, ht_holds⟩
    subst hidx
    have hk_fit : Fits w (st.idx + 1) := hwf.frontier_fits.of_le (by omega)
    have hlen_le : (prefF st.idx).length ≤ st.idx := by
      dsimp only [prefF]
      rw [List.length_map]
      exact (List.length_filter_le _ _).trans (by rw [List.length_take]; exact Nat.min_le_left _ _)
    have hmask_fit : Fits w (st.mask + 1) := hwf.frontier_fits.of_le (by omega)
    have horig_eq : t.mem (origSlot + st.idx) = (σ.symm ⟨st.idx, hk⟩).val := horig_t st.idx hk
    have hslot_lt : t.mem (origSlot + st.idx) < C.length := by
      rw [horig_eq]; exact (σ.symm ⟨st.idx, hk⟩).isLt
    have htake : (List.finRange e).take (st.idx + 1) =
        (List.finRange e).take st.idx ++ [⟨st.idx, hk⟩] := by
      rw [List.take_add_one,
        List.getElem?_eq_getElem (by simp only [List.length_finRange]; exact hk)]
      simp
    refine ⟨fun _ => ⟨h16, hk_fit, hmask_fit, by dsimp only [env]; omega,
      fun _ => ⟨by dsimp only [env]; omega, by dsimp only [env]; omega⟩⟩, ?_⟩
    dsimp only [dtEmitStep, env, copy4]
    refine Memory.FramedTriple.read_bind (by omega) ?_
    refine Memory.FramedTriple.ite (fun hbit => ?_) (fun hbit => ?_)
    · have htb : ansMask.testBit st.idx = true :=
        (testBit_eq_decide_shift_and ansMask st.idx).mp hbit
      have hpref_next : prefF (st.idx + 1) =
          prefF st.idx ++ [C[(σ.symm ⟨st.idx, hk⟩).val]] := by
        dsimp only [prefF]; rw [htake, List.filter_append, List.map_append]; simp [htb]
      let src := edgeBase + 4 * t.mem (origSlot + st.idx)
      let dst := outBase + 4 * st.mask
      have hcp := Memory.FramedTriple.copy (w := w) (s := t) (src := src) (dst := dst) (n := 4)
        (by rcases hout_disj_in with h | h <;> dsimp only [src, dst] <;> omega)
        (by dsimp only [src]; omega) (by dsimp only [dst]; rw [htfr]; omega)
        (fun q _ => hwt.mem_fits _)
        (Q := fun _ s'' => inv (st.idx + 1) ⟨st.idx + 1, st.mask + 1⟩ s'')
        ⟨rfl, by rw [hpref_next]; simp [hmask_len], htfr, htfr ▸ wellFormed_copy4 hwt src dst,
          hin_t.congr (fun a ha1 ha2 => ArrayCopy.copyPrefix_outside
            (by rcases hout_disj_in with h | h <;> dsimp only [dst] <;> omega)),
          fun j hj => by
            dsimp only
            rw [ArrayCopy.copyPrefix_outside
              (by rcases hout_disj_orig with h | h <;> dsimp only [dst] <;> omega)]
            exact horig_t j hj,
          fun j hj => by
            rw [hpref_next, List.length_append, List.length_singleton] at hj
            by_cases hjl : j < (prefF st.idx).length
            · have hget : (prefF (st.idx + 1))[j] = (prefF st.idx)[j] := by
                simp only [hpref_next]; exact List.getElem_append_left hjl
              have hprev := ht_holds j hjl
              refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;>
                rw [hget, ArrayCopy.copyPrefix_outside (by dsimp only [dst]; omega)] <;>
                simp only [hprev.1, hprev.2.1, hprev.2.2.1, hprev.2.2.2]
            · have hje : j = st.mask := by omega
              subst hje
              have hget : (prefF (st.idx + 1))[st.mask] = C[(σ.symm ⟨st.idx, hk⟩).val] := by
                have hml : (prefF st.idx).length = st.mask := hmask_len.symm
                simp only [hpref_next, hml, List.getElem_append_right hml.le, Nat.sub_self,
                  List.getElem_singleton]
              obtain ⟨hu, hv, hw, hid⟩ := hin_t _ hslot_lt
              have hrd : ∀ q < 4,
                  ArrayCopy.copyPrefix t.mem src dst 4 (dst + q) = t.mem (src + q) :=
                fun _ hq => ArrayCopy.copyPrefix_read hq
              have hwr : ∀ q < 4, outBase + 4 * st.mask + q = dst + q := fun _ _ => rfl
              have hwr0 : outBase + 4 * st.mask = dst + 0 := rfl
              dsimp only
              exact ⟨by rw [hget, hwr0, hrd 0 (by decide)]; simpa [src, horig_eq] using hu,
                by rw [hget, hwr 1 (by decide), hrd 1 (by decide)]; simpa [src, horig_eq] using hv,
                by rw [hget, hwr 2 (by decide), hrd 2 (by decide)]; simpa [src, horig_eq] using hw,
                by
                  rw [hget, hwr 3 (by decide), hrd 3 (by decide)]
                  simpa [src, horig_eq] using hid⟩⟩
      exact (Memory.FramedTriple.bind_same ((hcp.frame_mono (fun a ha => by
        simp only [S, dst, Set.mem_Ico] at ha ⊢; omega)).mono le_rfl fun _ _ h =>
        Memory.FramedTriple.pure (c := 0) h)).mono (by decide) fun _ _ h => h
    · have hbf : ansMask.testBit st.idx = false :=
        Bool.eq_false_iff.mpr fun ht => hbit ((testBit_eq_decide_shift_and ansMask st.idx).mpr ht)
      have hpref_next : prefF (st.idx + 1) = prefF st.idx := by
        dsimp only [prefF]; rw [htake, List.filter_append, List.map_append]; simp [hbf]
      exact (Memory.FramedTriple.pure (c := 0)
        ⟨rfl, by rw [hpref_next, hmask_len], htfr, hwt,
          hin_t, horig_t, hpref_next ▸ ht_holds⟩).mono (by decide) fun _ _ h => h
  obtain ⟨hsafe, hft⟩ := iterate_framedTriple_of_step dtEmitStep dtEmitStepSafe w env 9 e
    inv S hstep ⟨0, 0⟩ s ⟨rfl, rfl, rfl, hwf, hin, horig, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hpref_e : prefF e = ((List.finRange e).filter fun j => ansMask.testBit j.val).map
      fun j => C[(σ.symm j).val] := by
    dsimp only [prefF]; rw [List.take_of_length_le (by simp)]
  exact ⟨hsafe, hft.mono le_rfl fun _ _ ⟨_, hmask_end, hfr_end, hwf_end, _, _, hholds_end⟩ =>
    ⟨hpref_e ▸ hmask_end, hfr_end, hwf_end, hpref_e ▸ hholds_end⟩⟩

private theorem evalDTRunTree_spec {w r0 v tableBase tableFrontier : ℕ} {d : DTRunArgs}
    {C : List (IndexedEdge v)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s) (hvr : v ≤ r0)
    (hsimp : IsSimple (edgeEnds (C.map IndexedEdge.toWeighted)))
    (hin : HoldsIndexedEdges d.edgeBase C s.mem)
    (hin_lt : d.edgeBase + 4 * C.length ≤ s.frontier)
    (hout_lt : d.outBase + 4 * C.length ≤ s.frontier)
    (hout_disj_in :
      d.edgeBase + 4 * C.length ≤ d.outBase ∨ d.outBase + 4 * C.length ≤ d.edgeBase)
    (htab : HoldsDTTable r0 tableBase s.mem)
    (hbnd : DTTableInBounds r0 tableBase tableFrontier s.mem)
    (htab_fr : tableFrontier ≤ s.frontier)
    (hsetup_ep : d.setup.entryPtr = s.mem (tableBase + dtGraphMask (C.map fun e => (e.u, e.v))))
    (hsetup_ec : d.setup.edgeCount = C.length)
    (hsetup_os : d.setup.origSlot + C.length ≤ s.frontier)
    (hsetup_sm : d.setup.slotMap + v.choose 2 ≤ s.frontier)
    (hdisj_os_sm :
      d.setup.slotMap + v.choose 2 ≤ d.setup.origSlot ∨
      d.setup.origSlot + C.length ≤ d.setup.slotMap)
    (hdisj_os_out :
      d.outBase + 4 * C.length ≤ d.setup.origSlot ∨ d.setup.origSlot + C.length ≤ d.outBase)
    (hdisj_os_in :
      d.edgeBase + 4 * C.length ≤ d.setup.origSlot ∨ d.setup.origSlot + C.length ≤ d.edgeBase)
    (hdisj_os_tab : ∀ a < tableFrontier,
      ¬(d.setup.origSlot ≤ a ∧ a < d.setup.origSlot + C.length))
    (hslots : ∀ k (hk : k < C.length),
      s.mem (d.setup.slotMap + edgePairIdx C[k].u.val C[k].v.val) = k) :
    let prog := evalDTRunTree d
    let optD := optDepth (edgeEnds (C.map IndexedEdge.toWeighted))
    Memory.FramedTriple w s prog (12 * C.length + 6 * optD + 2)
      (Set.Ico d.setup.origSlot (d.setup.origSlot + C.length) ∪
        Set.Ico d.outBase (d.outBase + 4 * C.length)) fun res s' =>
      evalDTRunTreeSafe w d s ∧
      s'.frontier = s.frontier ∧
      Memory.WellFormed w s' ∧
      res ≤ C.length ∧
      ∃ F : List (IndexedEdge v),
        F.length = res ∧
        F.Subperm C ∧
        HoldsIndexedEdges d.outBase F s'.mem ∧
        IsMinSpanningForest (C.map IndexedEdge.toWeighted) (F.map IndexedEdge.toWeighted) := by
  have hbnd' := (dtTableInBounds_iff _ _ _ _).mp hbnd
  obtain ⟨hmask_lt_v, hlen_pairs, hopt_eq, σ, hσ_pidx, hσ_ends⟩ :=
    endsOfMask_reindex_indexedEdges C hsimp
  have htab_v := holdsDTTable_for_le htab hvr hmask_lt_v
  dsimp only at htab_v
  obtain ⟨hmask_lt_r0, _, hd_eq, _, hpairs_mem, T, _, hT_corr, hT_hold⟩ := htab_v
  have hbnd_m := hbnd'.2 (dtGraphMask (C.map fun e => (e.u, e.v))) hmask_lt_r0
  dsimp only at hbnd_m
  let mask := dtGraphMask (C.map fun e => (e.u, e.v))
  let e := C.length
  let dDepth := s.mem (d.setup.entryPtr + 1)
  have he_pairs : (maskEdgePairs v mask).length = e := hlen_pairs
  have hlen_r0 : (maskEdgePairs r0 mask).length = e := by
    rw [maskEdgePairs_cast hvr hmask_lt_v, List.length_map]; exact he_pairs
  have hbnd_ep : d.setup.entryPtr + 2 + e + 2 * (2 ^ dDepth - 1) + 2 ^ dDepth ≤ tableFrontier := by
    simpa only [mask, dDepth, hsetup_ep, hlen_r0] using hbnd_m
  have h2d_pos : 0 < 2 ^ dDepth := Nat.two_pow_pos _
  have hpow2d_fit : Fits w (2 ^ dDepth) := hwf.frontier_fits.of_le (by omega)
  have hpow2d1_fit : Fits w (2 ^ (dDepth + 1)) := by
    rw [Nat.pow_succ']; exact hwf.frontier_fits.of_le (by omega)
  have hp_lt_v : ∀ j < e, s.mem (d.setup.entryPtr + 2 + j) < v.choose 2 := fun j hj => by
    have hj' : j < (maskEdgePairs v mask).length := he_pairs.symm ▸ hj
    have hpj := hpairs_mem j hj'; rw [← hsetup_ep] at hpj
    have hlt_p := pairIdx_lt_choose_two (mem_maskEdgePairs_iff.mp (List.getElem_mem hj')).1
      ((maskEdgePairs v mask)[j]'hj').2.isLt
    dsimp only [mask] at hpj hlt_p; rw [hpj]; exact hlt_p
  have hslot_lt : ∀ j < e, d.setup.slotMap + s.mem (d.setup.entryPtr + 2 + j) < s.frontier :=
    fun j hj => by have := hp_lt_v j hj; omega
  have hdisj_s : ∀ j < e, ¬(d.setup.origSlot ≤ d.setup.slotMap + s.mem (d.setup.entryPtr + 2 + j) ∧
      d.setup.slotMap + s.mem (d.setup.entryPtr + 2 + j) < d.setup.origSlot + e) := fun j hj => by
    have := hp_lt_v j hj; rcases hdisj_os_sm with h | h <;> omega
  have horig_val : ∀ j (hj : j < e),
      s.mem (d.setup.slotMap + s.mem (d.setup.entryPtr + 2 + j)) =
        (σ.symm ⟨j, he_pairs.symm ▸ hj⟩).val := fun j hj => by
    let jM : Fin (maskEdgePairs v mask).length := ⟨j, he_pairs.symm ▸ hj⟩
    let k := σ.symm jM
    have hpj := hpairs_mem j (he_pairs.symm ▸ hj); rw [← hsetup_ep] at hpj
    have hpk := hσ_pidx k
    rw [show (maskEdgePairs v mask)[(σ k).val] = (maskEdgePairs v mask)[j] by
      congr 1; exact congrArg Fin.val (σ.apply_symm_apply jM)] at hpk
    rw [hpj, hpk]; exact hslots k.val k.isLt
  let σ' : Fin C.length ≃ Fin e := σ.trans (Fin.castOrderIso he_pairs).toEquiv
  have horig_val' : ∀ j (hj : j < e),
      s.mem (d.setup.slotMap + s.mem (d.setup.entryPtr + 2 + j)) = (σ'.symm ⟨j, hj⟩).val :=
    fun j hj => by simpa [σ', Fin.castOrderIso] using horig_val j hj
  obtain ⟨hsafe_f, hft_f⟩ := @iterate_dtFillOrigStep_spec w e
    (d.setup.entryPtr + 2) d.setup.slotMap
    d.setup.origSlot v C mask σ' (by simp [e, he_pairs]) s h16 hwf rfl (by omega) hsetup_os
    hslot_lt hdisj_s (fun j hj => hdisj_os_tab _ (by omega)) horig_val'
  set s1 := (Memory.spec 0).clientState s
    (iterate dtFillOrigStep ⟨d.setup.entryPtr + 2, d.setup.slotMap, d.setup.origSlot⟩ e 0)
  obtain ⟨_, _, hmod_f, hs1_fr, hwf1, horig_s1⟩ := framedTriple_iff_realization.mp hft_f
  have hs1_pres : ∀ a < tableFrontier, s1.mem a = s.mem a := fun a ha =>
    hmod_f.mem_eq_of_not_mem (by omega) (fun hx => hdisj_os_tab a ha ⟨hx.1, hx.2⟩)
  have hT_hold_s1 : HoldsCompleteTree dDepth (d.setup.entryPtr + 2 + e)
      (d.setup.entryPtr + 2 + e + 2 * (2 ^ dDepth - 1)) dDepth 1 s1.mem T :=
    HoldsCompleteTree.congr (fun a _ _ => hs1_pres a (by omega))
      (fun a _ _ => hs1_pres a (by omega)) le_rfl le_rfl (by simp)
      (by simpa only [mask, dDepth, hsetup_ep, he_pairs] using hT_hold)
  have hin_s1 : HoldsIndexedEdges d.edgeBase C s1.mem := hin.congr fun a _ _ =>
    hmod_f.mem_eq_of_not_mem (by omega) fun hx => by
      simp only [Set.mem_Ico] at hx; rcases hdisj_os_in with h | h <;> omega
  have hdDepth_s1 : s1.mem (d.setup.entryPtr + 1) = dDepth := hs1_pres _ (by omega)
  obtain ⟨hsafe_w, hft_w⟩ := @iterate_dtWalkStep_spec w v e dDepth (d.setup.entryPtr + 2 + e)
    (d.setup.entryPtr + 2 + e + 2 * (2 ^ dDepth - 1)) d.edgeBase d.setup.origSlot C mask T s1 σ
    he_pairs.symm rfl hT_hold_s1 h16 hwf1 hpow2d1_fit (by rw [hs1_fr]; omega)
    (by rw [hs1_fr]; omega)
    (fun j hj => by simpa [σ', Fin.castOrderIso] using horig_s1 j (he_pairs ▸ hj))
    hin_s1 (by rw [hs1_fr]; omega)
  set node := (Memory.spec 0).clientResult s1
    (iterate dtWalkStep ⟨d.setup.entryPtr + 2 + e, d.setup.origSlot, d.edgeBase⟩ dDepth 1)
  set s2 := (Memory.spec 0).clientState s1
    (iterate dtWalkStep ⟨d.setup.entryPtr + 2 + e, d.setup.origSlot, d.edgeBase⟩ dDepth 1)
  obtain ⟨_, _, _, hs2_eq0, hnode_eq⟩ := framedTriple_iff_realization.mp hft_w
  have hs2_eq : s2 = s1 := hs2_eq0
  have hnode_rfl : (Memory.spec 0).clientResult s1
      (iterate dtWalkStep ⟨d.setup.entryPtr + 2 + e, d.setup.origSlot, d.edgeBase⟩ dDepth 1) =
      node := rfl
  have hbounds := walkCompleteTree_bounds (cmp := fun a b : Fin (maskEdgePairs v mask).length =>
    let i := σ.symm a; let j := σ.symm b
    decide (C[i.val].weight < C[j.val].weight ∨
      (C[i.val].weight = C[j.val].weight ∧ i.val < j.val))) hT_hold_s1
  rw [← hnode_eq, hnode_rfl] at hbounds
  let leafAddr := d.setup.entryPtr + 2 + e + 2 * (2 ^ dDepth - 1) + (node - 2 ^ dDepth)
  let ansMask := s2.mem leafAddr
  have hsub_lt : node - 2 ^ dDepth < 2 ^ dDepth := by
    have h := hbounds.2; rw [Nat.pow_succ, Nat.mul_two] at h; omega
  have hleaf_lt_tab : leafAddr < tableFrontier :=
    (Nat.add_lt_add_left hsub_lt _).trans_le hbnd_ep
  have hs2_fr : s2.frontier = s1.frontier := by rw [hs2_eq]
  have hwf2 : Memory.WellFormed w s2 := hs2_eq.symm ▸ hwf1
  have hin_s2 : HoldsIndexedEdges d.edgeBase C s2.mem := hs2_eq.symm ▸ hin_s1
  obtain ⟨hsafe_e, hft_e⟩ := @iterate_dtEmitStep_spec w v e ansMask d.setup.origSlot d.edgeBase
    d.outBase C σ' rfl s2 h16 hwf2 hin_s2 (by rw [hs2_fr, hs1_fr]; omega)
    (by rw [hs2_fr, hs1_fr]; omega) (by rw [hs2_fr, hs1_fr]; omega)
    hout_disj_in hdisj_os_out.symm fun j hj => by rw [hs2_eq]; exact horig_s1 j hj
  have hsafe_run : evalDTRunTreeSafe w d s := by
    have hs1_r : (Memory.spec 0).clientState s (iterate dtFillOrigStep
        ⟨d.setup.entryPtr + 2, d.setup.slotMap, d.setup.origSlot⟩ C.length 0) = s1 := rfl
    have hn_r : (Memory.spec 0).clientResult s1 (iterate dtWalkStep
        ⟨d.setup.entryPtr + 2 + C.length, d.setup.origSlot, d.edgeBase⟩ dDepth 1) = node := rfl
    have hs2_r : (Memory.spec 0).clientState s1 (iterate dtWalkStep
        ⟨d.setup.entryPtr + 2 + C.length, d.setup.origSlot, d.edgeBase⟩ dDepth 1) = s2 := rfl
    dsimp only [evalDTRunTreeSafe]
    rw [hsetup_ec, hs1_r, hdDepth_s1, hn_r, hs2_r, Nat.shiftLeft_eq, one_mul]
    exact ⟨h16, hpow2d_fit, hbounds.1, hwf.frontier_fits.of_le (by omega),
      hwf.frontier_fits.of_le (by omega), hwf2.mem_fits leafAddr,
      hwf.frontier_fits.of_le (by omega),
      by rw [hs1_fr]; omega, by rw [hs2_fr, hs1_fr]; omega, hsafe_f, hsafe_w, hsafe_e⟩
  have hmsf := dt_eval_msf_correct hT_corr hT_hold_s1 σ (fun k => hσ_ends k)
  dsimp only at hmsf; rw [← hnode_eq] at hmsf
  have hans_s1 : s1.mem leafAddr = ansMask := by dsimp only [ansMask]; rw [hs2_eq]
  let F_e := ((List.finRange e).filter fun j => ansMask.testBit j.val).map
    fun j => C[(σ'.symm j).val]
  have hF_perm : (((List.finRange (maskEdgePairs v mask).length).filter fun j =>
      (s1.mem leafAddr).testBit j.val).map fun j => C[(σ.symm j).val]).Perm F_e := by
    rw [hans_s1]
    have hp : ((List.finRange (maskEdgePairs v mask).length).filter fun j =>
        ansMask.testBit j.val).Perm
        (((List.finRange e).filter fun j => ansMask.testBit j.val).map
          (Fin.castOrderIso he_pairs).symm.toEquiv) := by
      refine List.perm_of_nodup_nodup_toFinset_eq ((List.nodup_finRange _).filter _)
        (((List.nodup_finRange e).filter _).map
          (Fin.castOrderIso he_pairs).symm.toEquiv.injective) ?_
      ext j
      simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
        List.mem_map, RelIso.coe_fn_toEquiv]
      constructor
      · intro hj; exact ⟨⟨j.val, he_pairs ▸ j.isLt⟩, hj, rfl⟩
      · rintro ⟨_, ha, rfl⟩; exact ha
    have hm := hp.map fun j => C[(σ.symm j).val]
    rw [List.map_map] at hm
    refine hm.trans ?_
    dsimp only [F_e]; rw [List.map_congr_left fun a _ => ?_]; simp [σ', Fin.castOrderIso]
  have hF_sub_eq : F_e.Subperm C := hF_perm.symm.subperm.trans hmsf.1
  have hF_msf_eq : IsMinSpanningForest (C.map IndexedEdge.toWeighted)
      (F_e.map IndexedEdge.toWeighted) :=
    ⟨⟨(hF_perm.symm.map IndexedEdge.toWeighted).subperm.trans hmsf.2.1.1,
      (Perm.isAcyclic_iff (hF_perm.map IndexedEdge.toWeighted)).mp hmsf.2.1.2.1,
      (Perm.edgePartition_eq (hF_perm.map IndexedEdge.toWeighted)).symm.trans hmsf.2.1.2.2⟩,
      fun G' hG' => (Perm.totalWeight_eq (hF_perm.map IndexedEdge.toWeighted)).symm ▸
        hmsf.2.2 G' hG'⟩
  have hopt_eq_dDepth : dDepth = optDepth (edgeEnds (C.map IndexedEdge.toWeighted)) := by
    dsimp only [dDepth]; rw [hsetup_ep, hd_eq, ← hopt_eq]
  have hlt_len : F_e.length ≤ C.length := by
    dsimp only [F_e]; rw [List.length_map]; exact (List.length_filter_le _ _).trans (by simp [e])
  have hprog : evalDTRunTree d =
      (iterate dtFillOrigStep ⟨d.setup.entryPtr + 2, d.setup.slotMap, d.setup.origSlot⟩ e 0 >>=
        fun _ => Memory.read (d.setup.entryPtr + 1) >>= fun depth =>
        iterate dtWalkStep ⟨d.setup.entryPtr + 2 + e, d.setup.origSlot, d.edgeBase⟩ depth 1 >>=
          fun node' =>
        Memory.read (d.setup.entryPtr + 2 + e + 2 * ((1 <<< depth) - 1) +
          (node' - (1 <<< depth))) >>= fun ansMask' =>
        iterate dtEmitStep ⟨ansMask', d.setup.origSlot, d.edgeBase, d.outBase⟩ e ⟨0, 0⟩ >>=
          fun res => pure res.mask) := by
    dsimp only [evalDTRunTree]; rw [hsetup_ec]
  rw [hprog]
  have hinner : Memory.FramedTriple w s1
      (Memory.read (d.setup.entryPtr + 1) >>= fun depth =>
        iterate dtWalkStep ⟨d.setup.entryPtr + 2 + e, d.setup.origSlot, d.edgeBase⟩ depth 1 >>=
          fun node' =>
        Memory.read (d.setup.entryPtr + 2 + e + 2 * ((1 <<< depth) - 1) +
          (node' - (1 <<< depth))) >>= fun ansMask' =>
        iterate dtEmitStep ⟨ansMask', d.setup.origSlot, d.edgeBase, d.outBase⟩ e ⟨0, 0⟩ >>=
          fun res => pure res.mask)
      (6 * dDepth + ((9 * e + 0) + 1) + 1) (∅ ∪ Set.Ico d.outBase (d.outBase + 4 * e))
      fun res s' => evalDTRunTreeSafe w d s ∧ s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧ res ≤ C.length ∧ ∃ F : List (IndexedEdge v),
        F.length = res ∧ F.Subperm C ∧ HoldsIndexedEdges d.outBase F s'.mem ∧
        IsMinSpanningForest (C.map IndexedEdge.toWeighted) (F.map IndexedEdge.toWeighted) := by
    refine Memory.FramedTriple.read_bind (by
      have : d.setup.entryPtr + 1 < tableFrontier := by omega
      exact this.trans_le (htab_fr.trans hs1_fr.ge)) ?_
    rw [hdDepth_s1]
    refine Memory.FramedTriple.bind (hft_w.mono le_rfl fun n' t' ⟨ht', hn'⟩ => ?_)
    rw [ht', hn', ← hnode_eq, hnode_rfl, Nat.shiftLeft_eq, one_mul]
    refine Memory.FramedTriple.read_bind (hleaf_lt_tab.trans_le (htab_fr.trans hs1_fr.ge)) ?_
    rw [hans_s1]; rw [hs2_eq] at hft_e
    exact Memory.FramedTriple.bind_same
      (hft_e.mono le_rfl fun r' s'' ⟨hr_len, hr_fr, hr_wf, hr_h⟩ =>
        Memory.FramedTriple.pure (c := 0) ⟨hsafe_run, hr_fr.trans hs1_fr, hr_wf,
          hr_len ▸ hlt_len, F_e, hr_len.symm, hF_sub_eq, hr_h, hF_msf_eq⟩)
  rw [Set.empty_union] at hinner
  exact Memory.FramedTriple.mono
    (Memory.FramedTriple.bind ((framedTriple_with_realization hft_f).mono le_rfl
      (by rintro _ _ ⟨_, rfl, _⟩; exact hinner)))
    (by rw [← hopt_eq_dDepth]; omega) fun _ _ h => h

private theorem evalDTCore_spec {w r0 outBase tableFrontier : ℕ} {d : DTSetupArgs}
    {C : List (IndexedEdge d.numVerts)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hvr : d.numVerts ≤ r0) (hm_eq : d.numEdges = C.length) (hm_ge : 2 ≤ C.length)
    (hsimp : IsSimple (edgeEnds (C.map IndexedEdge.toWeighted)))
    (hin : HoldsIndexedEdges d.edgeBase C s.mem)
    (hin_lt : d.edgeBase + 4 * C.length ≤ s.frontier)
    (hout_lt : outBase + 4 * C.length ≤ s.frontier)
    (hout_disj_in :
      d.edgeBase + 4 * C.length ≤ outBase ∨ outBase + 4 * C.length ≤ d.edgeBase)
    (htab : HoldsDTTable r0 d.tableBase s.mem)
    (hbnd : DTTableInBounds r0 d.tableBase tableFrontier s.mem)
    (htab_fr : tableFrontier ≤ s.frontier)
    (_hout_disj_tab : ∀ a < tableFrontier, ¬(outBase ≤ a ∧ a < outBase + 4 * C.length))
    (hslot_lt : d.slotMap + d.numVerts.choose 2 ≤ s.frontier)
    (hslot_disj_in :
      d.edgeBase + 4 * C.length ≤ d.slotMap ∨ d.slotMap + d.numVerts.choose 2 ≤ d.edgeBase)
    (_hslot_disj_out :
      outBase + 4 * C.length ≤ d.slotMap ∨ d.slotMap + d.numVerts.choose 2 ≤ outBase)
    (hslot_disj_tab : ∀ a < tableFrontier,
      ¬(d.slotMap ≤ a ∧ a < d.slotMap + d.numVerts.choose 2))
    (hfit_mul : Fits w (d.numVerts * (d.numVerts - 1)))
    (hfit : Fits w (s.frontier + C.length)) :
    let prog := evalDTSetupWithSlotMap d >>= fun st => evalDTRunTree ⟨st, d.edgeBase, outBase⟩
    let optD := optDepth (edgeEnds (C.map IndexedEdge.toWeighted))
    Memory.FramedTriple w s prog (15 * C.length + 6 * optD + 5)
      (Set.Ico d.slotMap (d.slotMap + d.numVerts.choose 2) ∪
        Set.Ico outBase (outBase + 4 * C.length)) fun res s' =>
        evalDTSetupWithSlotMapSafe w d s ∧
        evalDTRunTreeSafe w ⟨(Memory.spec 0).clientResult s (evalDTSetupWithSlotMap d),
          d.edgeBase, outBase⟩
          ((Memory.spec 0).clientState s (evalDTSetupWithSlotMap d)) ∧
        Memory.WellFormed w s' ∧
        s'.frontier ≤ s.frontier + C.length ∧
        res ≤ C.length ∧
        ∃ F : List (IndexedEdge d.numVerts),
          F.length = res ∧
          F.Subperm C ∧
          HoldsIndexedEdges outBase F s'.mem ∧
          IsMinSpanningForest (C.map IndexedEdge.toWeighted) (F.map IndexedEdge.toWeighted) := by
  have hbnd' := (dtTableInBounds_iff _ _ _ _).mp hbnd
  have hsu := @evalDTSetupWithSlotMap_spec w r0 tableFrontier d C s h16 hwf hvr hm_eq hm_ge
    hsimp hin hin_lt htab hbnd htab_fr hslot_lt hslot_disj_in hslot_disj_tab hfit_mul hfit
  set st := (Memory.spec 0).clientResult s (evalDTSetupWithSlotMap d)
  set s1 := (Memory.spec 0).clientState s (evalDTSetupWithSlotMap d)
  obtain ⟨_, _, hsu_mod, hsu_safe, hs1_fr, hwf1, hsm_eq, hos_eq, hep_eq, hec_eq, hslots⟩ :=
    framedTriple_iff_realization.mp hsu
  have hs0_le_s1 : s.frontier ≤ s1.frontier := hsu_mod.1
  have hpres_in : HoldsIndexedEdges d.edgeBase C s1.mem := hin.congr fun a _ _ =>
    hsu_mod.mem_eq_of_not_mem (by omega) (by
      simp only [Set.mem_Ico]; rcases hslot_disj_in with h | h <;> omega)
  have hpres_tab : ∀ a < tableFrontier, s1.mem a = s.mem a := fun a ha =>
    hsu_mod.mem_eq_of_not_mem (by omega) (hslot_disj_tab a ha)
  have htab_s1 : HoldsDTTable r0 d.tableBase s1.mem := htab.congr hbnd hpres_tab
  have hbnd_s1 : DTTableInBounds r0 d.tableBase tableFrontier s1.mem := hbnd.mono le_rfl hpres_tab
  have hep_s1 : st.entryPtr =
      s1.mem (d.tableBase + dtGraphMask (C.map fun e => (e.u, e.v))) := by
    have hm_lt := dtGraphMask_lt (C.map fun e => (e.u, e.v)) fun e he => by
      rw [List.mem_map] at he; obtain ⟨e₀, he₀, rfl⟩ := he
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he₀
      simpa [edgeEnds, IndexedEdge.toWeighted] using ((isSimple_iff _).mp hsimp).1
        ⟨k, by simpa using hk⟩
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show d.numVerts.choose 2 ≤
      r0.choose 2 by rw [Nat.choose_two_right, Nat.choose_two_right]; exact
      Nat.div_le_div_right (Nat.mul_le_mul hvr (Nat.sub_le_sub_right hvr 1)))
    rw [hep_eq, hpres_tab _ (by have := hbnd'.1; omega)]
  have hrun := @evalDTRunTree_spec w r0 d.numVerts d.tableBase tableFrontier
    ⟨st, d.edgeBase, outBase⟩ C s1 h16 hwf1 hvr hsimp hpres_in (by dsimp only; omega)
    (by dsimp only; omega) hout_disj_in htab_s1 hbnd_s1 (by omega) hep_s1 hec_eq
    (by dsimp only; rw [hos_eq, hs1_fr]) (by dsimp only; rw [hsm_eq]; omega)
    (by dsimp only; rw [hsm_eq, hos_eq]; exact .inl hslot_lt)
    (.inl (by dsimp only; rw [hos_eq]; omega))
    (.inl (by dsimp only; rw [hos_eq]; omega))
    (fun a _ => by dsimp only; rw [hos_eq]; omega) hslots
  dsimp only at hrun
  have hft_comb : Memory.FramedTriple w s
      (evalDTSetupWithSlotMap d >>= fun st' => evalDTRunTree ⟨st', d.edgeBase, outBase⟩)
      ((3 * C.length + 3) +
        (12 * C.length + 6 * optDepth (edgeEnds (C.map IndexedEdge.toWeighted)) + 2))
      (Set.Ico d.slotMap (d.slotMap + d.numVerts.choose 2) ∪
        (Set.Ico st.origSlot (st.origSlot + C.length) ∪
          Set.Ico outBase (outBase + 4 * C.length))) _ :=
    Memory.FramedTriple.bind ((framedTriple_with_realization hsu).mono le_rfl
      (by rintro _ _ ⟨rfl, rfl, _⟩; exact hrun))
  refine Memory.Triple.mono hft_comb (by omega) fun res s' ⟨hm, hrun_safe, hs'_fr, hwf', hres,
      F, hF_len, hF_sub, hF_holds, hF_msf⟩ => ?_
  refine ⟨⟨hm.1, fun a ha ha_not => hm.2 a ha fun hx => by
    rcases hx with hx_sm | hx_os | hx_out
    · exact ha_not (.inl hx_sm)
    · simp only [Set.mem_Ico] at hx_os; rw [hos_eq] at hx_os; omega
    · exact ha_not (.inr hx_out)⟩, hsu_safe, hrun_safe, hwf', by rw [hs'_fr, hs1_fr], hres,
    F, hF_len, hF_sub, hF_holds, hF_msf⟩

/-- Framed specification of `evalDecisionTreeWithSlotMapProg`: produces an `IsMinSpanningForest`
sublist `F` at `d.outBase` using caller-supplied `d.slotMap`, at most `m` fresh words, and at most
`15 * (m + optDepth C + 1)` memory operations, preserving all cells below `s.frontier` outside
`[d.slotMap, d.slotMap + v.choose 2) ∪ [d.outBase, d.outBase + 4 * m)`. -/
theorem evalDecisionTreeWithSlotMapProg_spec {w r0 tableFrontier : ℕ} {d : DTScratchQuery}
    {C : List (IndexedEdge d.numVerts)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hvr : d.numVerts ≤ r0) (hm_eq : d.numEdges = C.length)
    (hsimp : IsSimple (edgeEnds (C.map IndexedEdge.toWeighted)))
    (hin : HoldsIndexedEdges d.edgeBase C s.mem)
    (hin_lt : d.edgeBase + 4 * C.length ≤ s.frontier)
    (hout_lt : d.outBase + 4 * C.length ≤ s.frontier)
    (hout_disj_in :
      d.edgeBase + 4 * C.length ≤ d.outBase ∨ d.outBase + 4 * C.length ≤ d.edgeBase)
    (htab : HoldsDTTable r0 d.tableBase s.mem)
    (hbnd : DTTableInBounds r0 d.tableBase tableFrontier s.mem)
    (htab_fr : tableFrontier ≤ s.frontier)
    (hout_disj_tab : ∀ a < tableFrontier, ¬(d.outBase ≤ a ∧ a < d.outBase + 4 * C.length))
    (hslot_lt : d.slotMap + d.numVerts.choose 2 ≤ s.frontier)
    (hslot_disj_in :
      d.edgeBase + 4 * C.length ≤ d.slotMap ∨ d.slotMap + d.numVerts.choose 2 ≤ d.edgeBase)
    (hslot_disj_out :
      d.outBase + 4 * C.length ≤ d.slotMap ∨ d.slotMap + d.numVerts.choose 2 ≤ d.outBase)
    (hslot_disj_tab : ∀ a < tableFrontier,
      ¬(d.slotMap ≤ a ∧ a < d.slotMap + d.numVerts.choose 2))
    (hfit_mul : Fits w (d.numVerts * (d.numVerts - 1)))
    (hfit : Fits w (s.frontier + C.length)) :
    let prog := evalDecisionTreeWithSlotMapProg d
    let optD := optDepth (edgeEnds (C.map IndexedEdge.toWeighted))
    Memory.FramedTriple w s prog (15 * (C.length + optD + 1))
      (Set.Ico d.slotMap (d.slotMap + d.numVerts.choose 2) ∪
        Set.Ico d.outBase (d.outBase + 4 * C.length)) fun res s' =>
        evalDecisionTreeWithSlotMapProgSafe w d s ∧
        Memory.WellFormed w s' ∧
        s'.frontier ≤ s.frontier + C.length ∧
        res ≤ C.length ∧
        ∃ F : List (IndexedEdge d.numVerts),
          F.length = res ∧
          F.Subperm C ∧
          HoldsIndexedEdges d.outBase F s'.mem ∧
          IsMinSpanningForest (C.map IndexedEdge.toWeighted) (F.map IndexedEdge.toWeighted) := by
  by_cases hm0 : d.numEdges = 0
  · have hC0 : C = [] := List.eq_nil_of_length_eq_zero (hm_eq.symm.trans hm0)
    subst hC0
    have hprog : evalDecisionTreeWithSlotMapProg d = pure 0 := by
      simp [evalDecisionTreeWithSlotMapProg, hm0]
    rw [hprog]
    refine Memory.FramedTriple.pure ⟨⟨h16, fun h => by omega, fun h => by omega⟩, hwf,
      by simp, le_rfl, [], rfl, List.Subperm.refl _, fun _ hi => by simp at hi, ?_⟩
    exact (isMinSpanningForest_iff_threshold_partition _ _).mpr
      ⟨⟨List.Subperm.refl _, by simp [isAcyclic_nil], rfl⟩, fun _ => rfl⟩
  · by_cases hm1 : d.numEdges = 1
    · have hC1 : C.length = 1 := hm_eq.symm.trans hm1
      obtain ⟨e₀, rfl⟩ := List.length_eq_one_iff.mp hC1
      have hno : e₀.u ≠ e₀.v := fun heq =>
        ((isSimple_iff _).mp hsimp).1 ⟨0, by simp⟩ (Sym2.mk_isDiag_iff.mpr heq)
      have hprog : evalDecisionTreeWithSlotMapProg d = (Memory.copy d.edgeBase d.outBase 4 >>=
          fun _ => pure 1) := by
        dsimp only [evalDecisionTreeWithSlotMapProg, copy4]; simp only [hm1, ↓reduceIte]; rfl
      have hsafe : evalDecisionTreeWithSlotMapProgSafe w d s :=
        ⟨h16, fun _ => ⟨by simpa using hin_lt, by simpa using hout_lt⟩, fun _ h => absurd hm1 h⟩
      have hcp := Memory.FramedTriple.copy (w := w) (s := s) (src := d.edgeBase)
        (dst := d.outBase) (n := 4)
        (by rcases hout_disj_in with h | h <;> simp at h ⊢ <;> omega)
        (by simpa using hin_lt) (by simpa using hout_lt) (fun i _ => hwf.mem_fits _)
        (Q := fun _ s' => evalDecisionTreeWithSlotMapProgSafe w d s ∧ Memory.WellFormed w s' ∧
          s'.frontier ≤ s.frontier + [e₀].length ∧ 1 ≤ [e₀].length ∧
          ∃ F : List (IndexedEdge d.numVerts), F.length = 1 ∧ F.Subperm [e₀] ∧
            HoldsIndexedEdges d.outBase F s'.mem ∧
            IsMinSpanningForest ([e₀].map IndexedEdge.toWeighted)
              (F.map IndexedEdge.toWeighted))
        ⟨hsafe, wellFormed_copy4 hwf d.edgeBase d.outBase, by dsimp only; omega, by simp, [e₀],
          rfl, List.Subperm.refl _, fun i hi => by
            have hi0 : i = 0 := by simpa using hi
            subst hi0; obtain ⟨hu, hv, hw, hid⟩ := hin 0 (by simp)
            have hrd : ∀ q < 4, ArrayCopy.copyPrefix s.mem d.edgeBase d.outBase 4
                (d.outBase + q) = s.mem (d.edgeBase + q) := fun _ hq =>
              ArrayCopy.copyPrefix_read hq
            have hrd0 := hrd 0 (by decide); simp only [Nat.add_zero] at hrd0
            dsimp only
            exact ⟨by rw [Nat.mul_zero, Nat.add_zero, hrd0]; exact hu,
              by rw [Nat.mul_zero, hrd 1 (by decide)]; simpa using hv,
              by rw [Nat.mul_zero, hrd 2 (by decide)]; simpa using hw,
              by rw [Nat.mul_zero, hrd 3 (by decide)]; simpa using hid⟩,
          by
            refine (isMinSpanningForest_iff_threshold_partition _ _).mpr
              ⟨⟨List.Subperm.refl _, ?_, rfl⟩, fun _ => rfl⟩
            rw [isAcyclic_iff, edgePartition]
            simp only [List.map_cons, List.map_nil, edgePartitionFrom_cons, edgePartitionFrom_nil,
              IndexedEdge.toWeighted, List.length_cons, List.length_nil]
            have hnot : (DisjointSet.Partition.discrete d.numVerts).rel e₀.u e₀.v = false := by
              rw [DisjointSet.Partition.rel_discrete]; exact decide_eq_false hno
            rw [DisjointSet.Partition.numComponents_merge_of_not_rel hnot,
              DisjointSet.Partition.numComponents_discrete]⟩
      rw [hprog]
      exact Memory.FramedTriple.mono
        ((Memory.FramedTriple.bind_same (hcp.mono le_rfl fun _ _ h =>
          Memory.FramedTriple.pure (c := 0) h)).frame_mono fun a ha => Or.inr (by
          simp only [List.length_singleton, Nat.mul_one] at ha ⊢; exact ha))
        (by simp only [List.length_singleton]; omega) fun _ _ h => h
    · have hm_ge : 2 ≤ C.length := by omega
      have hcore := @evalDTCore_spec w r0 d.outBase tableFrontier
        ⟨d.tableBase, d.numVerts, d.numEdges, d.edgeBase, d.slotMap⟩ C s h16 hwf hvr hm_eq hm_ge
        hsimp hin hin_lt hout_lt hout_disj_in htab hbnd htab_fr hout_disj_tab hslot_lt
        hslot_disj_in hslot_disj_out hslot_disj_tab hfit_mul hfit
      have hprog : evalDecisionTreeWithSlotMapProg d =
          (evalDTSetupWithSlotMap ⟨d.tableBase, d.numVerts, d.numEdges, d.edgeBase, d.slotMap⟩ >>=
            fun st' => evalDTRunTree ⟨st', d.edgeBase, d.outBase⟩) := by
        dsimp only [evalDecisionTreeWithSlotMapProg]; simp only [hm0, hm1, ↓reduceIte]
      rw [hprog]
      exact hcore.mono (by omega) fun _ _ ⟨hsu_safe, hrun_safe, hwf', hfr', hres, F, hfl, hfs,
          hfh, hfm⟩ =>
        ⟨⟨h16, fun h => absurd h hm1, fun _ _ => ⟨hsu_safe, hrun_safe⟩⟩,
          hwf', hfr', hres, F, hfl, hfs, hfh, hfm⟩

/-- Framed specification of `evalDecisionTreeProg`: produces an `IsMinSpanningForest` sublist `F`
at `d.outBase` using at most `v.choose 2 + m` fresh words and `15 * (m + optDepth C + 1)` memory
operations, preserving all cells below `s.frontier` outside `[d.outBase, d.outBase + 4 * m)`. -/
theorem evalDecisionTreeProg_spec {w r0 tableFrontier : ℕ} {d : DTQuery}
    {C : List (IndexedEdge d.numVerts)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hvr : d.numVerts ≤ r0) (hm_eq : d.numEdges = C.length)
    (hsimp : IsSimple (edgeEnds (C.map IndexedEdge.toWeighted)))
    (hin : HoldsIndexedEdges d.edgeBase C s.mem)
    (hin_lt : d.edgeBase + 4 * C.length ≤ s.frontier)
    (hout_lt : d.outBase + 4 * C.length ≤ s.frontier)
    (hout_disj_in :
      d.edgeBase + 4 * C.length ≤ d.outBase ∨ d.outBase + 4 * C.length ≤ d.edgeBase)
    (htab : HoldsDTTable r0 d.tableBase s.mem)
    (hbnd : DTTableInBounds r0 d.tableBase tableFrontier s.mem)
    (htab_fr : tableFrontier ≤ s.frontier)
    (hout_disj_tab : ∀ a < tableFrontier, ¬(d.outBase ≤ a ∧ a < d.outBase + 4 * C.length))
    (hfit : Fits w (s.frontier + d.numVerts.choose 2 + C.length)) :
    let prog := evalDecisionTreeProg d
    let optD := optDepth (edgeEnds (C.map IndexedEdge.toWeighted))
    Memory.FramedTriple w s prog (15 * (C.length + optD + 1))
      (Set.Ico d.outBase (d.outBase + 4 * C.length)) fun res s' =>
        evalDecisionTreeProgSafe w d s ∧
        Memory.WellFormed w s' ∧
        s'.frontier ≤ s.frontier + d.numVerts.choose 2 + C.length ∧
        res ≤ C.length ∧
        ∃ F : List (IndexedEdge d.numVerts),
          F.length = res ∧
          F.Subperm C ∧
          HoldsIndexedEdges d.outBase F s'.mem ∧
          IsMinSpanningForest (C.map IndexedEdge.toWeighted) (F.map IndexedEdge.toWeighted) := by
  by_cases hm0 : d.numEdges = 0
  · have hC0 : C = [] := List.eq_nil_of_length_eq_zero (hm_eq.symm.trans hm0)
    subst hC0
    have hprog : evalDecisionTreeProg d = pure 0 := by simp [evalDecisionTreeProg, hm0]
    rw [hprog]
    refine Memory.FramedTriple.pure ⟨⟨h16, fun h => by omega, fun h => by omega⟩, hwf,
      by simp, le_rfl, [], rfl, List.Subperm.refl _, fun _ hi => by simp at hi, ?_⟩
    exact (isMinSpanningForest_iff_threshold_partition _ _).mpr
      ⟨⟨List.Subperm.refl _, by simp [isAcyclic_nil], rfl⟩, fun _ => rfl⟩
  · by_cases hm1 : d.numEdges = 1
    · have hC1 : C.length = 1 := hm_eq.symm.trans hm1
      obtain ⟨e₀, rfl⟩ := List.length_eq_one_iff.mp hC1
      have hno : e₀.u ≠ e₀.v := fun heq =>
        ((isSimple_iff _).mp hsimp).1 ⟨0, by simp⟩ (Sym2.mk_isDiag_iff.mpr heq)
      have hprog : evalDecisionTreeProg d = (Memory.copy d.edgeBase d.outBase 4 >>=
          fun _ => pure 1) := by
        dsimp only [evalDecisionTreeProg, copy4]; simp only [hm1, ↓reduceIte]; rfl
      have hsafe : evalDecisionTreeProgSafe w d s :=
        ⟨h16, fun _ => ⟨by simpa using hin_lt, by simpa using hout_lt⟩, fun _ h => absurd hm1 h⟩
      have hcp := Memory.FramedTriple.copy (w := w) (s := s) (src := d.edgeBase)
        (dst := d.outBase) (n := 4)
        (by rcases hout_disj_in with h | h <;> simp at h ⊢ <;> omega)
        (by simpa using hin_lt) (by simpa using hout_lt) (fun i _ => hwf.mem_fits _)
        (Q := fun _ s' => evalDecisionTreeProgSafe w d s ∧ Memory.WellFormed w s' ∧
          s'.frontier ≤ s.frontier + d.numVerts.choose 2 + [e₀].length ∧ 1 ≤ [e₀].length ∧
          ∃ F : List (IndexedEdge d.numVerts), F.length = 1 ∧ F.Subperm [e₀] ∧
            HoldsIndexedEdges d.outBase F s'.mem ∧
            IsMinSpanningForest ([e₀].map IndexedEdge.toWeighted)
              (F.map IndexedEdge.toWeighted))
        ⟨hsafe, wellFormed_copy4 hwf d.edgeBase d.outBase, by dsimp only; omega, by simp, [e₀],
          rfl, List.Subperm.refl _, fun i hi => by
            have hi0 : i = 0 := by simpa using hi
            subst hi0; obtain ⟨hu, hv, hw, hid⟩ := hin 0 (by simp)
            have hrd : ∀ q < 4, ArrayCopy.copyPrefix s.mem d.edgeBase d.outBase 4
                (d.outBase + q) = s.mem (d.edgeBase + q) := fun _ hq =>
              ArrayCopy.copyPrefix_read hq
            have hrd0 := hrd 0 (by decide); simp only [Nat.add_zero] at hrd0
            dsimp only
            exact ⟨by rw [Nat.mul_zero, Nat.add_zero, hrd0]; exact hu,
              by rw [Nat.mul_zero, hrd 1 (by decide)]; simpa using hv,
              by rw [Nat.mul_zero, hrd 2 (by decide)]; simpa using hw,
              by rw [Nat.mul_zero, hrd 3 (by decide)]; simpa using hid⟩,
          by
            refine (isMinSpanningForest_iff_threshold_partition _ _).mpr
              ⟨⟨List.Subperm.refl _, ?_, rfl⟩, fun _ => rfl⟩
            rw [isAcyclic_iff, edgePartition]
            simp only [List.map_cons, List.map_nil, edgePartitionFrom_cons, edgePartitionFrom_nil,
              IndexedEdge.toWeighted, List.length_cons, List.length_nil]
            have hnot : (DisjointSet.Partition.discrete d.numVerts).rel e₀.u e₀.v = false := by
              rw [DisjointSet.Partition.rel_discrete]; exact decide_eq_false hno
            rw [DisjointSet.Partition.numComponents_merge_of_not_rel hnot,
              DisjointSet.Partition.numComponents_discrete]⟩
      rw [hprog]
      exact Memory.FramedTriple.mono
        ((Memory.FramedTriple.bind_same (hcp.mono le_rfl fun _ _ h =>
          Memory.FramedTriple.pure (c := 0) h)).frame_mono fun a ha => by
          simp only [List.length_singleton, Nat.mul_one] at ha ⊢; exact ha)
        (by simp only [List.length_singleton]; omega) fun _ _ h => h
    · have hm_ge : 2 ≤ C.length := by omega
      let maxE := d.numVerts.choose 2
      have hmaxE_def : d.numVerts * (d.numVerts - 1) / 2 = maxE := (Nat.choose_two_right _).symm
      have h2c : 2 * maxE = d.numVerts * (d.numVerts - 1) := by
        dsimp only [maxE]
        rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self d.numVerts).two_dvd]
      have hnv1 : 1 ≤ d.numVerts := (C[0]'(by omega)).u.pos
      have hfit_nv : Fits w d.numVerts := by
        by_cases hv3 : 3 ≤ d.numVerts
        · exact hfit.of_le (by
            have hvc : d.numVerts ≤ maxE := by
              dsimp only [maxE]; rw [Nat.choose_two_right]
              exact (Nat.le_div_iff_mul_le (by decide)).mpr
                (Nat.mul_le_mul_left d.numVerts (by omega))
            omega)
        · exact h16.of_le (by omega)
      have hfit_maxE : Fits w maxE := hfit.of_le (by omega)
      have hfit_s0 : Fits w (s.frontier + maxE) := hfit.of_le (by omega)
      have hfit_mul : Fits w (d.numVerts * (d.numVerts - 1)) := by
        rw [← h2c]
        have htb_bnd := ((dtTableInBounds_iff _ _ _ _).mp hbnd).1
        have hlt_pow := Nat.lt_two_pow_self (n := maxE)
        have hpow : 2 ^ maxE ≤ 2 ^ r0.choose 2 :=
          Nat.pow_le_pow_right (by decide) (by
            dsimp only [maxE]
            rw [Nat.choose_two_right, Nat.choose_two_right]
            exact Nat.div_le_div_right (Nat.mul_le_mul hvr (Nat.sub_le_sub_right hvr 1)))
        exact hfit.of_le (by omega)
      let s0 : Memory.State := ⟨s.mem, s.frontier + maxE⟩
      have hwf0 : Memory.WellFormed w s0 := ⟨hfit_s0, hwf.mem_fits⟩
      have hcore := @evalDTCore_spec w r0 d.outBase tableFrontier
        ⟨d.tableBase, d.numVerts, d.numEdges, d.edgeBase, s.frontier⟩ C s0 h16 hwf0 hvr hm_eq
        hm_ge hsimp hin (by dsimp [s0]; omega) (by dsimp [s0]; omega) hout_disj_in htab hbnd
        (by dsimp [s0]; omega) hout_disj_tab (le_refl _) (.inl hin_lt) (.inl hout_lt)
        (fun a ha => by dsimp only; omega) hfit_mul hfit
      have hprog : evalDecisionTreeProg d =
          (Memory.allocDirty maxE >>= fun slotMap' =>
            evalDTSetupWithSlotMap ⟨d.tableBase, d.numVerts, d.numEdges, d.edgeBase, slotMap'⟩ >>=
              fun st' => evalDTRunTree ⟨st', d.edgeBase, d.outBase⟩) := by
        dsimp only [evalDecisionTreeProg]; rw [hmaxE_def]; simp only [hm0, hm1, ↓reduceIte]
      rw [hprog]
      refine Memory.Triple.mono (Memory.FramedTriple.allocDirty_bind hfit_s0 hcore)
        (by omega) fun res s' ⟨hm, hsu_safe, hrun_safe, hwf', hs'_fr, hres, F, hF_len, hF_sub,
          hF_holds, hF_msf⟩ => ?_
      refine ⟨⟨hm.1, fun a ha ha_out => hm.2 a ha fun hx => by
        rcases hx with hx_sm | hx_out
        · simp only [Set.mem_Ico] at hx_sm; omega
        · exact ha_out hx_out⟩,
        ⟨h16, fun h => absurd h hm1, fun _ _ =>
          ⟨hnv1, hfit_nv, hfit_mul, hmaxE_def ▸ hfit_maxE, hmaxE_def ▸ hfit_s0,
            hmaxE_def ▸ hsu_safe, hmaxE_def ▸ hrun_safe⟩⟩,
        hwf', by dsimp [s0] at hs'_fr; omega, hres, F, hF_len, hF_sub, hF_holds, hF_msf⟩

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
