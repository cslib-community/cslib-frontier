/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.OuterEmit
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.Bridges
import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Collect
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Tactic.Linarith

/-!
# Round Finalization and Full-Round Specifications for `Partition`

Steps toward Theorem 5.8 of [PettieRamachandran2002] (#8624), verifying post-DJP round
finalization (`partRoundFinish_spec`) and full-round dynamic-DJP execution (`partRunRound_spec`)
with explicit `PartitionRoundWitness` guarantees and amortized potential bounds (§3.1, p. 20;
§3.2, pp. 21–22; §5.1, pp. 25–26).

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partRoundFinish_spec`: verifies
  `partRoundFinish` across normal termination (`hitPrev = 0`) and prior-component overlap
  (`hitPrev ≠ 0`), resetting the Soft-Heap handle for the next round.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partRunRound_spec`: full-round specification for
  `partRunRound` constructing a `PartitionRoundWitness` and proving the round amortized bound
  `2465 * remDeg + 295 * (2 * m - itemCount) + 6 * r.numVerts + 19`.

## References

* [S. Pettie and V. Ramachandran, *An Optimal Minimum Spanning Tree
  Algorithm*][PettieRamachandran2002]
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest
open Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

private theorem shInv_next_round {w ic₀ nc₀ m : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ (2 * m) (4 * m) h roots created s)
    (hnc_le : nc₀ ≤ 2 * ic₀) :
    h.nodeCount ≤ 2 * h.itemCount ∧
    SHInv w h.itemCount h.nodeCount (2 * m) (4 * m)
      ⟨h.itemBase, h.nodeBase, 0, h.itemCount, h.nodeCount, h.rankThreshold⟩
      [] (fun _ => 0) s := by
  have hnc_roots := hinv.nc_roots_le; have hic_le := hinv.ic_le; have hic_max := hinv.ic_max
  have hnc_new : h.nodeCount ≤ 2 * h.itemCount := by omega
  have hcap_new : h.nodeCount + 2 * (2 * m - h.itemCount) ≤ 4 * m := by omega
  exact ⟨hnc_new, shInit_inv hinv.fits16 hinv.wf hic_max hcap_new hinv.item_pool_lt
    hinv.node_pool_lt hinv.pools_disj hinv.fits_fuel⟩

private theorem djp_edge_ne_of_lt {n : ℕ} (D : DynamicDJPTree n) (i j : Fin D.numSteps)
    (hlt : i.val < j.val) : D.edge i ≠ D.edge j := by
  intro hij; have h1 := D.mem_treeVerts_of_edge i
  have h2u := mem_djpVerts_mono D.root D.vOut (by omega : i.val + 1 ≤ j.val) h1.1
  have h2v := mem_djpVerts_mono D.root D.vOut (by omega : i.val + 1 ≤ j.val) h1.2
  rw [hij] at h2u h2v
  rcases D.ends_match j with ⟨_, hv⟩ | ⟨_, hu⟩
  · exact D.vOut_not_mem j (hv ▸ h2v)
  · exact D.vOut_not_mem j (hu ▸ h2u)

private theorem djp_treeEdges_nodup {n : ℕ} (D : DynamicDJPTree n) : D.treeEdges.Nodup := by
  dsimp only [DynamicDJPTree.treeEdges]
  refine (List.nodup_finRange D.numSteps).map_on fun i _ j _ hij => ?_
  rcases Nat.lt_trichotomy i.val j.val with h | h | h
  · exact absurd hij (djp_edge_ne_of_lt D i j h)
  · exact Fin.ext h
  · exact absurd hij.symm (djp_edge_ne_of_lt D j i h)

/-! ## Public Round Finalization and Full-Round Specifications -/

private theorem partRoundFinish_safe_aux {w n : ℕ} (L : PartLayout w n) (s : Memory.State)
    (numComps cEdgeLen0 cLiftLen0 mcLen0 hitPrev size : ℕ) (u : Fin n) (tLenOuter : ℕ)
    (shOuter : SHHandle) (nc0 tLen' : ℕ) (h₀ : SHHandle)
    (cRes : PartCursor) (s₁ : Memory.State) (numCorr : ℕ) (s₂ s₃ s₄ : Memory.State)
    (h_cRes : (Memory.spec 0).clientResult s (partEmitComp
      ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, L.es.length, numComps + 1⟩,
        hitPrev, size, cEdgeLen0⟩) = cRes)
    (h_s1 : (Memory.spec 0).clientState s (partEmitComp
      ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, L.es.length, numComps + 1⟩,
        hitPrev, size, cEdgeLen0⟩) = s₁)
    (h_numCorr : (Memory.spec 0).clientResult s₁
      (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + L.es.length, 0, 2 * L.es.length)) =
      numCorr)
    (h_s2 : (Memory.spec 0).clientState s₁
      (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + L.es.length, 0, 2 * L.es.length)) =
      s₂)
    (h_s3 : (Memory.spec 0).clientState s₂
      (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, L.es.length⟩, numCorr, mcLen0⟩) = s₃)
    (h_s4 : (Memory.spec 0).clientState s₃
      (partMarkDeadLoop ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩) = s₄)
    (hce1 : cEdgeLen0 ≤ cRes.count) (hce_le_m : cRes.count ≤ L.es.length)
    (hnc : numComps < n) (hcl_le : cLiftLen0 + size ≤ 2 * n)
    (hsafe1 : partEmitCompSafe w
      ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, L.es.length, numComps + 1⟩,
        hitPrev, size, cEdgeLen0⟩ s)
    (hsafe2 : shCollectCorruptedSafe w
      (h₀, nc0, L.bufBase + 14 * n + L.es.length, 0, 2 * L.es.length) s₁)
    (hsafe3 : partEmitCorrLoopSafe w
      ⟨⟨L.edgeBase, L.bufBase, n, L.es.length⟩, numCorr, mcLen0⟩ s₂)
    (hsafe4 : partMarkDeadLoopSafe w ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩ s₃)
    (hsafe5 : partWriteRoundMetaSafe w ⟨L.bufBase, n, numComps, size, cRes.count - cEdgeLen0,
      L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0, L.bufBase + 4 * n + cLiftLen0⟩ s₄) :
    partRoundFinishSafe w ⟨L.toEnv,
      ⟨u.val, numComps, cEdgeLen0, cLiftLen0, mcLen0, tLenOuter, shOuter⟩, nc0,
      ⟨0, hitPrev, size, tLen', h₀⟩⟩ s := by
  have h16 := L.h16
  have hn_pos := L.hn_pos
  have hfit_u1 : Fits w (u.val + 1) := L.hfit_end.of_le (by have := u.isLt; omega)
  have hfit_nc1 : Fits w (numComps + 1) := L.hfit_end.of_le (by omega)
  have hfit_2m : Fits w (2 * L.es.length) := L.hfit_end.of_le (by omega)
  have hfit_buf : Fits w (L.bufBase + 14 * n + 14 * L.es.length) := L.hfit_end.of_le (by omega)
  have hfit_ce : Fits w (L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0) :=
    L.hfit_end.of_le (by omega)
  have hfit_cl : Fits w (L.bufBase + 4 * n + cLiftLen0) := L.hfit_end.of_le (by omega)
  rw [partRoundFinishSafe_def]
  simp only [PartLayout.toEnv, h_cRes, h_s1, h_numCorr, h_s2, h_s3, h_s4]
  exact And.intro h16 <| And.intro hfit_u1 <| And.intro hfit_nc1 <| And.intro hfit_2m <|
    And.intro hce1 <| And.intro hfit_buf <| And.intro hfit_ce <| And.intro hfit_cl <|
    And.intro hsafe1 <| And.intro hsafe2 <| And.intro hsafe3 <| And.intro hsafe4 hsafe5

private theorem partRoundFinish_exec_aux {w n : ℕ} (L : PartLayout w n) (s : Memory.State)
    (numComps cEdgeLen0 cLiftLen0 mcLen0 hitPrev size : ℕ) (u : Fin n) (tLenOuter : ℕ)
    (shOuter : SHHandle) (nc0 tLen' : ℕ) (h₀ : SHHandle)
    (cRes : PartCursor) (s₁ : Memory.State) (numCorr : ℕ) (s₂ : Memory.State)
    (mRes : PartCursor) (s₃ : Memory.State) (lRes : PartCursor) (s₄ s₅ : Memory.State)
    (h_cRes : (Memory.spec 0).clientResult s (partEmitComp
      ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, L.es.length, numComps + 1⟩,
        hitPrev, size, cEdgeLen0⟩) = cRes)
    (h_s1 : (Memory.spec 0).clientState s (partEmitComp
      ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, L.es.length, numComps + 1⟩,
        hitPrev, size, cEdgeLen0⟩) = s₁)
    (h_numCorr : (Memory.spec 0).clientResult s₁
      (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + L.es.length, 0, 2 * L.es.length)) =
      numCorr)
    (h_s2 : (Memory.spec 0).clientState s₁
      (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + L.es.length, 0, 2 * L.es.length)) =
      s₂)
    (h_mRes : (Memory.spec 0).clientResult s₂
      (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, L.es.length⟩, numCorr, mcLen0⟩) = mRes)
    (h_s3 : (Memory.spec 0).clientState s₂
      (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, L.es.length⟩, numCorr, mcLen0⟩) = s₃)
    (h_lRes : (Memory.spec 0).clientResult s₃
      (partMarkDeadLoop ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩) = lRes)
    (h_s4 : (Memory.spec 0).clientState s₃
      (partMarkDeadLoop ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩) = s₄)
    (h_s5 : (Memory.spec 0).clientState s₄ (partWriteRoundMeta
      ⟨L.bufBase, n, numComps, size, cRes.count - cEdgeLen0,
        L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0, L.bufBase + 4 * n + cLiftLen0⟩) =
      s₅)
    (hnext_eq : (⟨h₀.itemBase, h₀.nodeBase, 0, h₀.itemCount, h₀.nodeCount,
      h₀.rankThreshold⟩ : SHHandle) =
      ⟨L.itemBase, L.nodeBase, 0, h₀.itemCount, h₀.nodeCount, partRankThreshold⟩)
    (hvh1 : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partEmitComp
      ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, L.es.length, numComps + 1⟩,
        hitPrev, size, cEdgeLen0⟩)))
    (hvh2 : (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁
      (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + L.es.length, 0, 2 * L.es.length))))
    (hvh3 : (Memory.spec w).ValidHistory s₂ ((Memory.spec w).clientHistory s₂
      (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, L.es.length⟩, numCorr, mcLen0⟩)))
    (hvh4 : (Memory.spec w).ValidHistory s₃ ((Memory.spec w).clientHistory s₃
      (partMarkDeadLoop ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩)))
    (hvh5 : (Memory.spec w).ValidHistory s₄ ((Memory.spec w).clientHistory s₄
      (partWriteRoundMeta ⟨L.bufBase, n, numComps, size, cRes.count - cEdgeLen0,
        L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0, L.bufBase + 4 * n + cLiftLen0⟩))) :
    let m := L.es.length
    let d : PartRoundFinishArgs := ⟨L.toEnv,
      ⟨u.val, numComps, cEdgeLen0, cLiftLen0, mcLen0, tLenOuter, shOuter⟩, nc0,
      ⟨0, hitPrev, size, tLen', h₀⟩⟩
    let prog := partRoundFinish d
    let res_v : PartOuterState := ⟨u.val + 1, numComps + 1, cRes.count, lRes.count, mRes.count,
      tLen', ⟨L.itemBase, L.nodeBase, 0, h₀.itemCount, h₀.nodeCount, partRankThreshold⟩⟩
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = res_v ∧
    (Memory.spec 0).clientState s prog = s₅ ∧
    memoryCost prog s =
      memoryCost (partEmitComp ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, m,
        numComps + 1⟩, hitPrev, size, cEdgeLen0⟩) s +
      memoryCost (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + m, 0, 2 * m)) s₁ +
      memoryCost (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, m⟩, numCorr, mcLen0⟩) s₂ +
      memoryCost (partMarkDeadLoop ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩) s₃ +
      memoryCost (partWriteRoundMeta ⟨L.bufBase, n, numComps, size, cRes.count - cEdgeLen0,
        L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0, L.bufBase + 4 * n + cLiftLen0⟩) s₄ := by
  intro m d prog res_v
  have hprog : prog =
      (partEmitComp ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, m, numComps + 1⟩,
        hitPrev, size, cEdgeLen0⟩ >>= fun cRes' =>
        shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + m, 0, 2 * m) >>= fun numCorr' =>
          partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, m⟩, numCorr', mcLen0⟩ >>= fun mRes' =>
            partMarkDeadLoop ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩ >>= fun lRes' =>
              partWriteRoundMeta ⟨L.bufBase, n, numComps, size, cRes'.count - cEdgeLen0,
                L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0, L.bufBase + 4 * n + cLiftLen0⟩ >>=
                fun _ => pure ⟨u.val + 1, numComps + 1, cRes'.count, lRes'.count, mRes'.count,
                  tLen', ⟨h₀.itemBase, h₀.nodeBase, 0, h₀.itemCount, h₀.nodeCount,
                    h₀.rankThreshold⟩⟩) := partRoundFinish_def d
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hprog]; refine validHistory_bind_step hvh1 ?_; rw [h_s1]
    refine validHistory_bind_step hvh2 ?_; rw [h_numCorr, h_s2]
    refine validHistory_bind_step hvh3 ?_; rw [h_s3]
    refine validHistory_bind_step hvh4 ?_; rw [h_cRes, h_s4]
    exact validHistory_bind_step hvh5 (validHistory_pure w _ _)
  · rw [hprog, StateTransitionSpec.clientResult_bind, h_s1, StateTransitionSpec.clientResult_bind,
      h_numCorr, h_s2, StateTransitionSpec.clientResult_bind, h_s3, h_cRes,
      StateTransitionSpec.clientResult_bind, h_s4, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_pure, h_mRes, h_lRes, hnext_eq]
  · rw [hprog, StateTransitionSpec.clientState_bind, h_s1, StateTransitionSpec.clientState_bind,
      h_numCorr, h_s2, StateTransitionSpec.clientState_bind, h_s3, h_cRes,
      StateTransitionSpec.clientState_bind, h_s4, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure, h_s5]
  · rw [hprog, memoryCost_bind', h_s1, memoryCost_bind', h_numCorr, h_s2, memoryCost_bind',
      h_s3, h_cRes, memoryCost_bind', h_s4, memoryCost_bind', memoryCost_pure]; omega

private theorem partRoundFinish_body_aux {w n : ℕ} (L : PartLayout w n) (s₀ : Memory.State)
    (dead0 inCur0 edgeState0 : ℕ → ℕ) (ic0 nc0 tLen0 : ℕ) (u : Fin n)
    (numComps cEdgeLen0 cLiftLen0 mcLen0 tLenOuter : ℕ) (shOuter h₀ : SHHandle)
    (hitPrev size tLen' : ℕ) (s : Memory.State)
    (W : DjpWitness L s₀ dead0 inCur0 edgeState0 (numComps + 1) ic0 nc0 tLen0 u
      ⟨0, hitPrev, size, tLen', h₀⟩ s)
    (hnc : numComps < n) (hnc_le : nc0 ≤ 2 * ic0) (hcl_le : cLiftLen0 + size ≤ 2 * n)
    (cRes : PartCursor) (s₁ : Memory.State) (numCorr : ℕ) (s₂ : Memory.State)
    (mRes : PartCursor) (s₃ : Memory.State) (lRes : PartCursor) (s₄ s₅ : Memory.State)
    (h_cRes : (Memory.spec 0).clientResult s (partEmitComp
      ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, L.es.length, numComps + 1⟩,
        hitPrev, size, cEdgeLen0⟩) = cRes)
    (h_s1 : (Memory.spec 0).clientState s (partEmitComp
      ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, L.es.length, numComps + 1⟩,
        hitPrev, size, cEdgeLen0⟩) = s₁)
    (h_numCorr : (Memory.spec 0).clientResult s₁
      (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + L.es.length, 0, 2 * L.es.length)) =
      numCorr)
    (h_s2 : (Memory.spec 0).clientState s₁
      (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + L.es.length, 0, 2 * L.es.length)) =
      s₂)
    (h_mRes : (Memory.spec 0).clientResult s₂
      (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, L.es.length⟩, numCorr, mcLen0⟩) = mRes)
    (h_s3 : (Memory.spec 0).clientState s₂
      (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, L.es.length⟩, numCorr, mcLen0⟩) = s₃)
    (h_lRes : (Memory.spec 0).clientResult s₃
      (partMarkDeadLoop ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩) = lRes)
    (h_s4 : (Memory.spec 0).clientState s₃
      (partMarkDeadLoop ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩) = s₄)
    (h_s5 : (Memory.spec 0).clientState s₄ (partWriteRoundMeta
      ⟨L.bufBase, n, numComps, size, cRes.count - cEdgeLen0,
        L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0, L.bufBase + 4 * n + cLiftLen0⟩) =
      s₅)
    (hsz_w : size = W.D.numSteps + 1)
    (hsafe1 : partEmitCompSafe w
      ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, L.es.length, numComps + 1⟩,
        hitPrev, size, cEdgeLen0⟩ s)
    (hvh1 : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partEmitComp
      ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, L.es.length, numComps + 1⟩,
        hitPrev, size, cEdgeLen0⟩)))
    (hfr1 : s₁.frontier = s.frontier)
    (hmod1 : ∀ x, s₁.mem x ≠ s.mem x →
      (L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + L.es.length) ∨
      (L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 2 * L.es.length + 4 * cRes.count))
    (hce1 : cEdgeLen0 ≤ cRes.count)
    (hcost1 : memoryCost (partEmitComp
      ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, L.es.length, numComps + 1⟩,
        hitPrev, size, cEdgeLen0⟩) s ≤ 3 * (if hitPrev = 0 then size else size - 1) + 15 *
      (remDeg n L.offBase s.mem (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)) -
        remDeg n L.offBase s.mem ((Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)) ∪
          W.D.treeVerts W.D.numSteps)))
    (emittedIdx : List (Fin L.es.length)) (compLocal : List (IndexedEdge size))
    (hnd_emit : emittedIdx.Nodup) (hlen_comp : compLocal.length = cRes.count - cEdgeLen0)
    (hhold_comp :
      HoldsIndexedEdges (L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0) compLocal s₁.mem)
    (hmap_comp : compLocal.map (fun e => ⟨(djpVertsList W.D)[e.u.val]'(by
        rw [djpVertsList_length, ← hsz_w]; exact e.u.isLt),
      (djpVertsList W.D)[e.v.val]'(by rw [djpVertsList_length, ← hsz_w]; exact e.v.isLt),
      e.weight, e.id⟩) = emittedIdx.map (fun eIdx => L.es[eIdx.val]'eIdx.isLt))
    (hemit_iff : ∀ eIdx : Fin L.es.length, eIdx ∈ emittedIdx ↔
      edgeState0 eIdx.val = 0 ∧ (L.es[eIdx.val]'eIdx.isLt).u ∈ W.D.treeVerts W.D.numSteps ∧
        (L.es[eIdx.val]'eIdx.isLt).v ∈ W.D.treeVerts W.D.numSteps)
    (hsafe2 : shCollectCorruptedSafe w
      (h₀, nc0, L.bufBase + 14 * n + L.es.length, 0, 2 * L.es.length) s₁)
    (hvh2 : (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁
      (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + L.es.length, 0, 2 * L.es.length))))
    (hsafe3 : partEmitCorrLoopSafe w
      ⟨⟨L.edgeBase, L.bufBase, n, L.es.length⟩, numCorr, mcLen0⟩ s₂)
    (hvh3 : (Memory.spec w).ValidHistory s₂ ((Memory.spec w).clientHistory s₂
      (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, L.es.length⟩, numCorr, mcLen0⟩)))
    (hfr3 : s₃.frontier = s₁.frontier)
    (hsh_s3 : SHInv w ic0 nc0 (2 * L.es.length) (4 * L.es.length) h₀ W.roots W.created s₃)
    (hmc_ge : mcLen0 ≤ mRes.count) (hmc_diff : 16 * (mRes.count - mcLen0) ≤ h₀.itemCount - ic0)
    (hcost23 : memoryCost
        (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + L.es.length, 0, 2 * L.es.length)) s₁ +
      memoryCost
        (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, L.es.length⟩, numCorr, mcLen0⟩) s₂ ≤
      20 * (h₀.itemCount - ic0))
    (hmod23 : ∀ x, s₃.mem x ≠ s₁.mem x →
      (L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + 2 * L.es.length) ∨
      (L.bufBase + 14 * n + 6 * L.es.length + 4 * mcLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 6 * L.es.length + 4 * mRes.count))
    (corrEmitted : List (Fin L.es.length)) (hnd_corr : corrEmitted.Nodup)
    (hlen_corr : corrEmitted.length = mRes.count - mcLen0)
    (hhold_corr : HoldsIndexedEdges (L.bufBase + 14 * n + 6 * L.es.length + 4 * mcLen0)
      (corrEmitted.map fun eIdx => L.es[eIdx.val]'eIdx.isLt) s₃.mem)
    (hest3 : ∀ i < L.es.length, s₃.mem (L.bufBase + 14 * n + i) =
      if ∃ hlt : i < L.es.length, (⟨i, hlt⟩ : Fin L.es.length) ∈ corrEmitted then 2
      else if ∃ hlt : i < L.es.length, (⟨i, hlt⟩ : Fin L.es.length) ∈ emittedIdx then 1
      else edgeState0 i)
    (hclaim3 : cRes.count + mRes.count ≤
      (Finset.univ.filter (fun i : Fin L.es.length =>
        s₃.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card)
    (hcorr_es0 : ∀ eIdx ∈ corrEmitted,
      (if ∃ hlt : eIdx.val < L.es.length, (⟨eIdx.val, hlt⟩ : Fin L.es.length) ∈ emittedIdx then 1
        else edgeState0 eIdx.val) = 0)
    (hcorr_uncorr : ∀ eIdx : Fin L.es.length,
      (if ∃ hlt : eIdx.val < L.es.length, (⟨eIdx.val, hlt⟩ : Fin L.es.length) ∈ emittedIdx then 1
        else edgeState0 eIdx.val) = 0 →
      eIdx ∉ corrEmitted → ∀ p ∈ forestEntries W.roots, p.1.val = eIdx.val → p.2 ≤ p.1.origKey)
    (hsafe4 : partMarkDeadLoopSafe w ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩ s₃)
    (hvh4 : (Memory.spec w).ValidHistory s₃ ((Memory.spec w).clientHistory s₃
      (partMarkDeadLoop ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩)))
    (hfr4 : s₄.frontier = s₃.frontier)
    (hmod4 : ∀ x, s₄.mem x ≠ s₃.mem x →
      (L.bufBase ≤ x ∧ x < L.bufBase + n) ∨
      (L.bufBase + 4 * n + cLiftLen0 ≤ x ∧ x < L.bufBase + 4 * n + lRes.count))
    (hl_eq : lRes.count = cLiftLen0 + size) (hcost4 : memoryCost
      (partMarkDeadLoop ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩) s₃ ≤ 3 * size)
    (hlifts : ∀ k : Fin size, s₄.mem (L.bufBase + 4 * n + cLiftLen0 + k.val) =
      ((djpVertsList W.D)[k.val]'(by rw [djpVertsList_length, ← hsz_w]; exact k.isLt)).val)
    (hdead4' : ∀ x : Fin n, s₄.mem (L.bufBase + x.val) =
      if x ∈ W.D.treeVerts W.D.numSteps then 1 else dead0 x.val)
    (hmc_le_m : mRes.count ≤ L.es.length) (hce_le_m : cRes.count ≤ L.es.length)
    (hsafe5 : partWriteRoundMetaSafe w ⟨L.bufBase, n, numComps, size, cRes.count - cEdgeLen0,
      L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0, L.bufBase + 4 * n + cLiftLen0⟩ s₄)
    (hvh5 : (Memory.spec w).ValidHistory s₄ ((Memory.spec w).clientHistory s₄
      (partWriteRoundMeta ⟨L.bufBase, n, numComps, size, cRes.count - cEdgeLen0,
        L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0, L.bufBase + 4 * n + cLiftLen0⟩)))
    (hfr5 : s₅.frontier = s₄.frontier) (hwf5 : Memory.WellFormed w s₅)
    (hmod5 : ∀ x, s₅.mem x ≠ s₄.mem x →
      (L.bufBase + 6 * n + 3 * numComps ≤ x ∧ x < L.bufBase + 6 * n + 3 * (numComps + 1)) ∨
      x = L.bufBase + 9 * n + numComps)
    (hcost5 : memoryCost (partWriteRoundMeta ⟨L.bufBase, n, numComps, size,
      cRes.count - cEdgeLen0, L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0,
      L.bufBase + 4 * n + cLiftLen0⟩) s₄ = 4)
    (hm0 : s₅.mem (L.bufBase + 6 * n + 3 * numComps) = size)
    (hm1 : s₅.mem (L.bufBase + 6 * n + 3 * numComps + 1) = cRes.count - cEdgeLen0)
    (hm2 : s₅.mem (L.bufBase + 6 * n + 3 * numComps + 2) =
      L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0)
    (hm3 : s₅.mem (L.bufBase + 9 * n + numComps) = L.bufBase + 4 * n + cLiftLen0) :
    let m := L.es.length
    let d : PartRoundFinishArgs :=
      ⟨L.toEnv, ⟨u.val, numComps, cEdgeLen0, cLiftLen0, mcLen0, tLenOuter, shOuter⟩, nc0,
        ⟨0, hitPrev, size, tLen', h₀⟩⟩
    let prog := partRoundFinish d
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    let hNext : SHHandle :=
      ⟨L.itemBase, L.nodeBase, 0, h₀.itemCount, h₀.nodeCount, partRankThreshold⟩
    let V_i := W.D.treeVerts W.D.numSteps
    let deadSet := Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)
    let lift : Fin size → Fin n := fun k =>
      (djpVertsList W.D)[k.val]'(by rw [djpVertsList_length, ← W.hsize]; exact k.isLt)
    partRoundFinishSafe w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    res.u = u.val + 1 ∧ res.numComps = numComps + 1 ∧
    cEdgeLen0 ≤ res.cEdgeLen ∧ res.cLiftLen = cLiftLen0 + size ∧
    mcLen0 ≤ res.mcLen ∧ res.tLen = tLen' ∧ res.sh = hNext ∧
    s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
    (∀ x, s'.mem x ≠ s₀.mem x →
      InSHPool ic0 nc0 (2 * m) (4 * m)
        ⟨L.itemBase, L.nodeBase, 0, ic0, nc0, partRankThreshold⟩ x ∨
      (L.bufBase ≤ x ∧ x < L.bufBase + 4 * n) ∨
      (L.bufBase + 4 * n + cLiftLen0 ≤ x ∧ x < L.bufBase + 4 * n + (cLiftLen0 + size)) ∨
      (L.bufBase + 6 * n + 3 * numComps ≤ x ∧ x < L.bufBase + 6 * n + 3 * (numComps + 1)) ∨
      x = L.bufBase + 9 * n + numComps ∨
      (L.bufBase + 10 * n + 4 * tLen0 ≤ x ∧ x < L.bufBase + 10 * n + 4 * tLen') ∨
      (L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + 2 * m) ∨
      (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 2 * m + 4 * res.cEdgeLen) ∨
      (L.bufBase + 14 * n + 6 * m + 4 * mcLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 6 * m + 4 * res.mcLen)) ∧
    hNext.nodeCount ≤ 2 * hNext.itemCount ∧
    SHInv w hNext.itemCount hNext.nodeCount (2 * m) (4 * m) hNext [] (fun _ => 0) s' ∧
    memoryCost prog s ≤ 6 * size + 15 *
      (remDeg n L.offBase s.mem deadSet - remDeg n L.offBase s.mem (deadSet ∪ V_i)) +
      20 * (h₀.itemCount - ic0) + 4 ∧
    16 * (res.mcLen - mcLen0) ≤ h₀.itemCount - ic0 ∧
    (∀ x : Fin n, s'.mem (L.bufBase + x.val) = if x ∈ V_i then 1 else dead0 x.val) ∧
    (∀ k : Fin size, s'.mem (L.bufBase + 4 * n + cLiftLen0 + k.val) = (lift k).val) ∧
    s'.mem (L.bufBase + 6 * n + 3 * numComps) = size ∧
    s'.mem (L.bufBase + 6 * n + 3 * numComps + 1) = res.cEdgeLen - cEdgeLen0 ∧
    s'.mem (L.bufBase + 6 * n + 3 * numComps + 2) = L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0 ∧
    s'.mem (L.bufBase + 9 * n + numComps) = L.bufBase + 4 * n + cLiftLen0 ∧
    HoldsIndexedEdges (L.bufBase + 10 * n + 4 * tLen0) W.treeIndexed s'.mem ∧
    ∃ (emittedIdx corrEmitted : List (Fin m)) (compLocal : List (IndexedEdge size)),
      emittedIdx.Nodup ∧ corrEmitted.Nodup ∧
      (∀ eIdx : Fin m, eIdx ∈ emittedIdx → eIdx ∉ corrEmitted) ∧
      compLocal.length = res.cEdgeLen - cEdgeLen0 ∧
      corrEmitted.length = res.mcLen - mcLen0 ∧
      HoldsIndexedEdges (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0) compLocal s'.mem ∧
      compLocal.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) =
        emittedIdx.map (fun eIdx => L.es[eIdx.val]'eIdx.isLt) ∧
      HoldsIndexedEdges (L.bufBase + 14 * n + 6 * m + 4 * mcLen0)
        (corrEmitted.map fun eIdx => L.es[eIdx.val]'eIdx.isLt) s'.mem ∧
      (∀ eIdx : Fin m, eIdx ∈ emittedIdx ↔
        edgeState0 eIdx.val = 0 ∧ (L.es[eIdx.val]'eIdx.isLt).u ∈ V_i ∧
          (L.es[eIdx.val]'eIdx.isLt).v ∈ V_i) ∧
      (∀ i < m, s'.mem (L.bufBase + 14 * n + i) =
        if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ emittedIdx then 1
        else if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ corrEmitted then 2
        else edgeState0 i) ∧
      res.cEdgeLen + res.mcLen ≤
        (Finset.univ.filter (fun i : Fin m => s'.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card ∧
      (∀ x : Fin n, s'.mem (L.bufBase + n + x.val) = s.mem (L.bufBase + n + x.val)) ∧
      (hitPrev = 0 → size < L.maxsize → ∀ eIdx : Fin m, edgeState0 eIdx.val = 0 →
        ¬((L.es[eIdx.val]'eIdx.isLt).u ∈ V_i ↔ (L.es[eIdx.val]'eIdx.isLt).v ∉ V_i)) ∧
      (∀ eIdx ∈ corrEmitted, edgeState0 eIdx.val = 0) ∧
      (∀ eIdx : Fin m, edgeState0 eIdx.val = 0 → eIdx ∉ emittedIdx → eIdx ∉ corrEmitted →
        ∀ s_step : Fin W.D.numSteps,
          ((L.es[eIdx.val]'eIdx.isLt).u ∈ W.D.treeVerts s_step.val ↔
            (L.es[eIdx.val]'eIdx.isLt).v ∉ W.D.treeVerts s_step.val) →
          W.D.wPop s_step ≤ (L.es[eIdx.val]'eIdx.isLt).weight) := by
  let m := L.es.length
  let outer : PartOuterState := ⟨u.val, numComps, cEdgeLen0, cLiftLen0, mcLen0, tLenOuter, shOuter⟩
  let djp : PartDjpState := ⟨0, hitPrev, size, tLen', h₀⟩
  let d : PartRoundFinishArgs := ⟨L.toEnv, outer, nc0, djp⟩
  let V_i := W.D.treeVerts W.D.numSteps
  let deadSet : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)
  have hn_pos := L.hn_pos
  have hs5_agree_4 : ∀ x, ¬((L.bufBase + 6 * n + 3 * numComps ≤ x ∧
      x < L.bufBase + 6 * n + 3 * (numComps + 1)) ∨ x = L.bufBase + 9 * n + numComps) →
      s₅.mem x = s₄.mem x := fun x hx => by_contra fun hne => hx (hmod5 x hne)
  have hs4_agree_3 : ∀ x, ¬((L.bufBase ≤ x ∧ x < L.bufBase + n) ∨
      (L.bufBase + 4 * n + cLiftLen0 ≤ x ∧ x < L.bufBase + 4 * n + (cLiftLen0 + size))) →
      s₄.mem x = s₃.mem x := fun x hx =>
    by_contra fun hne => hx (by rcases hmod4 x hne with h | h; exacts [.inl h, .inr (by omega)])
  have hs3_agree_1 : ∀ x, ¬((L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + 2 * m) ∨
      (L.bufBase + 14 * n + 6 * m + 4 * mcLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 6 * m + 4 * mRes.count)) →
      s₃.mem x = s₁.mem x := fun x hx => by_contra fun hne => hx (hmod23 x hne)
  have hs1_agree_0 : ∀ x, ¬((L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + m) ∨
      (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 2 * m + 4 * cRes.count)) →
      s₁.mem x = s.mem x := fun x hx => by_contra fun hne => hx (hmod1 x hne)
  have hagree_s5_s2 : ∀ x, L.bufBase ≤ x → x < L.bufBase + 14 * n →
      ¬(L.bufBase ≤ x ∧ x < L.bufBase + n) →
      ¬(L.bufBase + 4 * n + cLiftLen0 ≤ x ∧ x < L.bufBase + 4 * n + (cLiftLen0 + size)) →
      ¬(L.bufBase + 6 * n + 3 * numComps ≤ x ∧ x < L.bufBase + 6 * n + 3 * (numComps + 1)) →
      x ≠ L.bufBase + 9 * n + numComps → s₅.mem x = s.mem x := fun x hx1 hx2 h1 h2 h3 h4 =>
    (hs5_agree_4 x (by tauto)).trans ((hs4_agree_3 x (by tauto)).trans
      ((hs3_agree_1 x (by omega)).trans (hs1_agree_0 x (by omega))))
  have hsh_next := shInv_next_round (partCongrSh_of_mod_ge L W.hib W.hnb hsh_s3 hwf5
    (hfr5.trans hfr4) fun x hx => by
      by_cases hx4 : s₅.mem x = s₄.mem x
      · rcases hmod4 x (hx4 ▸ hx) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      · rcases hmod5 x hx4 with ⟨h1, _⟩ | rfl <;> omega) hnc_le
  have hnext_eq : (⟨h₀.itemBase, h₀.nodeBase, 0, h₀.itemCount, h₀.nodeCount,
      h₀.rankThreshold⟩ : SHHandle) =
      ⟨L.itemBase, L.nodeBase, 0, h₀.itemCount, h₀.nodeCount, partRankThreshold⟩ := by
    rw [W.hib, W.hnb, W.hrt]
  rw [hnext_eq] at hsh_next
  have hdisj_ec : ∀ eIdx : Fin m, eIdx ∈ emittedIdx → eIdx ∉ corrEmitted := fun eIdx he hc => by
    have h1 := hcorr_es0 eIdx hc
    have hm' : ∃ hlt : eIdx.val < L.es.length,
        (⟨eIdx.val, hlt⟩ : Fin L.es.length) ∈ emittedIdx := ⟨eIdx.isLt, he⟩
    simp only [hm', ↓reduceIte] at h1; omega
  have hest_fn : ∀ i < m, s₅.mem (L.bufBase + 14 * n + i) =
      if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ emittedIdx then 1
      else if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ corrEmitted then 2
      else edgeState0 i := fun i hi => by
    dsimp only [m] at hi ⊢
    rw [hs5_agree_4 _ (by omega), hs4_agree_3 _ (by omega), hest3 i hi]
    by_cases h2 : ∃ hlt : i < L.es.length, (⟨i, hlt⟩ : Fin L.es.length) ∈ corrEmitted
    · have h1 : ¬∃ hlt : i < L.es.length, (⟨i, hlt⟩ : Fin L.es.length) ∈ emittedIdx :=
        fun ⟨hlt, hm⟩ => hdisj_ec ⟨i, hlt⟩ hm h2.choose_spec
      simp only [h2, h1, ↓reduceIte]
    · simp only [h2, ↓reduceIte]
  have hclaim_fn : cRes.count + mRes.count ≤
      (Finset.univ.filter (fun i : Fin m => s₅.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card := by
    have hfilt_eq : Finset.univ.filter (fun i : Fin m => s₅.mem (L.bufBase + 14 * n + i.val) ≠ 0) =
        Finset.univ.filter (fun i : Fin m => s₃.mem (L.bufBase + 14 * n + i.val) ≠ 0) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; dsimp only [m]
      rw [hest_fn i.val i.isLt, hest3 i.val i.isLt]
      split_ifs <;> first | exact Iff.rfl | decide
    rw [hfilt_eq]; exact hclaim3
  have hsafe : partRoundFinishSafe w d s := partRoundFinish_safe_aux L s numComps cEdgeLen0
    cLiftLen0 mcLen0 hitPrev size u tLenOuter shOuter nc0 tLen' h₀ cRes s₁ numCorr s₂ s₃ s₄
    h_cRes h_s1 h_numCorr h_s2 h_s3 h_s4 hce1 hce_le_m hnc hcl_le
    hsafe1 hsafe2 hsafe3 hsafe4 hsafe5
  have hexec := partRoundFinish_exec_aux L s numComps cEdgeLen0 cLiftLen0 mcLen0 hitPrev size u
    tLenOuter shOuter nc0 tLen' h₀ cRes s₁ numCorr s₂ mRes s₃ lRes s₄ s₅
    h_cRes h_s1 h_numCorr h_s2 h_mRes h_s3 h_lRes h_s4 h_s5 hnext_eq hvh1 hvh2 hvh3 hvh4 hvh5
  dsimp only at hexec
  let res_v : PartOuterState := ⟨u.val + 1, numComps + 1, cRes.count, lRes.count, mRes.count,
    tLen', ⟨L.itemBase, L.nodeBase, 0, h₀.itemCount, h₀.nodeCount, partRankThreshold⟩⟩
  rcases hexec with ⟨hvh, hres_eq, hst_eq, hcost_add⟩
  have hcost_eq : memoryCost (partRoundFinish d) s ≤
      6 * size + 15 * (remDeg n L.offBase s.mem deadSet -
        remDeg n L.offBase s.mem (deadSet ∪ V_i)) + 20 * (h₀.itemCount - ic0) + 4 := by
    dsimp only [deadSet, V_i, d, outer, djp] at ⊢
    have hlive_le : (if hitPrev = 0 then size else size - 1) ≤ size := by split_ifs <;> omega
    rw [hcost_add]; omega
  have hmod_all : ∀ x, s₅.mem x ≠ s₀.mem x →
      InSHPool ic0 nc0 (2 * m) (4 * m)
        ⟨L.itemBase, L.nodeBase, 0, ic0, nc0, partRankThreshold⟩ x ∨
      (L.bufBase ≤ x ∧ x < L.bufBase + 4 * n) ∨
      (L.bufBase + 4 * n + cLiftLen0 ≤ x ∧ x < L.bufBase + 4 * n + (cLiftLen0 + size)) ∨
      (L.bufBase + 6 * n + 3 * numComps ≤ x ∧ x < L.bufBase + 6 * n + 3 * (numComps + 1)) ∨
      x = L.bufBase + 9 * n + numComps ∨
      (L.bufBase + 10 * n + 4 * tLen0 ≤ x ∧ x < L.bufBase + 10 * n + 4 * tLen') ∨
      (L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + 2 * m) ∨
      (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 2 * m + 4 * cRes.count) ∨
      (L.bufBase + 14 * n + 6 * m + 4 * mcLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 6 * m + 4 * mRes.count) := fun x hx => by
    by_cases hx5 : s₅.mem x = s₄.mem x
    · by_cases hx4 : s₄.mem x = s₃.mem x
      · by_cases hx3 : s₃.mem x = s₁.mem x
        · by_cases hx1 : s₁.mem x = s.mem x
          · exact (W.hmod x (hx1 ▸ hx3 ▸ hx4 ▸ hx5 ▸ hx)).elim .inl fun h => h.elim
              (fun h => .inr (.inl ⟨by omega, h.2⟩))
              (fun h => .inr (.inr (.inr (.inr (.inr (.inl h))))))
          · rcases hmod1 x hx1 with h | h
            · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl (by omega)))))))
            · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))
        · rcases hmod23 x hx3 with h | h
          · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
          · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h)))))))
      · rcases hmod4 x hx4 with h | h
        · exact .inr (.inl ⟨h.1, by omega⟩)
        · rw [hl_eq] at h; exact .inr (.inr (.inl h))
    · rcases hmod5 x hx5 with h | rfl
      · exact .inr (.inr (.inr (.inl h)))
      · exact .inr (.inr (.inr (.inr (.inl rfl))))
  dsimp only
  dsimp only [d, outer, djp] at hsafe hvh hres_eq hst_eq
  refine ⟨hsafe, hvh, by rw [hres_eq], by rw [hres_eq], by rw [hres_eq]; exact hce1,
    by rw [hres_eq]; exact hl_eq, by rw [hres_eq]; exact hmc_ge, by rw [hres_eq],
    by rw [hres_eq], by rw [hst_eq]; exact hfr5.trans (hfr4.trans (hfr3.trans hfr1)),
    by rw [hst_eq]; exact hwf5, fun x hx => by
      rw [hst_eq] at hx; rw [hres_eq]; exact hmod_all x hx,
    hsh_next.1, by rw [hst_eq]; exact hsh_next.2,
    hcost_eq, by rw [hres_eq]; exact hmc_diff,
    fun x => by rw [hst_eq, hs5_agree_4 _ (by omega)]; exact hdead4' x,
    fun k => by rw [hst_eq, hs5_agree_4 _ (by omega)]; exact hlifts k,
    by rw [hst_eq]; exact hm0, by rw [hst_eq, hres_eq]; exact hm1,
    by rw [hst_eq]; exact hm2, by rw [hst_eq]; exact hm3,
    (by
      rw [hst_eq]
      exact W.htree_mem.congr fun x hx1 hx2 => by
        rw [W.htree_len] at hx2
        have := W.htlen; have := W.htlen_le
        exact hagree_s5_s2 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)),
    emittedIdx, corrEmitted, compLocal, hnd_emit, hnd_corr, hdisj_ec,
    by rw [hres_eq]; exact hlen_comp, by rw [hres_eq]; exact hlen_corr,
    (by
      rw [hst_eq]
      exact hhold_comp.congr fun x _ hx2 => by
        rw [hlen_comp] at hx2
        rw [hs5_agree_4 _ (by omega), hs4_agree_3 _ (by omega),
          hs3_agree_1 _ (by omega)]),
    hmap_comp,
    (by
      rw [hst_eq]
      exact hhold_corr.congr fun x _ hx2 => by
        rw [List.length_map, hlen_corr] at hx2
        rw [hs5_agree_4 _ (by omega), hs4_agree_3 _ (by omega)]),
    hemit_iff, fun i hi => by rw [hst_eq]; exact hest_fn i hi,
    by rw [hst_eq, hres_eq]; exact hclaim_fn,
    fun x => by
      rw [hst_eq]
      exact hagree_s5_s2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    fun hp hsz eIdx he0 => W.hempty_stop rfl hp hsz eIdx he0,
    fun eIdx hc => by
      have h1 := hcorr_es0 eIdx hc; split_ifs at h1; exact h1,
    fun eIdx he0 hne_em hne_corr s_step hcross => by
      have he1 : (if ∃ hlt : eIdx.val < m, (⟨eIdx.val, hlt⟩ : Fin m) ∈ emittedIdx then 1
          else edgeState0 eIdx.val) = 0 := by
        split_ifs with hm
        · exact absurd hm.choose_spec hne_em
        · exact he0
      rcases W.hcut_cov eIdx he0 (fun ⟨hu, hv⟩ => hne_em ((hemit_iff eIdx).mpr ⟨he0, hu, hv⟩))
        ⟨s_step, hcross⟩ with ⟨p, hp, hpe⟩
      have hle := hcorr_uncorr eIdx he1 hne_corr p hp hpe
      have hlt_p : p.1.val < L.es.length := hpe ▸ eIdx.isLt
      have hkw := W.hwpop_fut s_step p hp ⟨hlt_p, by simpa only [hpe] using hcross⟩
      have hprop := (W.hent_prop p hp).choose_spec
      have he_eq : (W.hent_prop p hp).choose = eIdx := Fin.ext (hprop.1.symm.trans hpe)
      rw [hprop.2.1, he_eq] at hle; omega⟩

/-- Specification of `partRoundFinish`: emits component edges `C_i`, collects/emits newly
corrupted edges `M_i`, records `lift_i` and dead vertices, writes round metadata, resets
`firstRoot := 0`, and bounds total emission/collection cost by
`6 * size + 15 * remDegDrop + 20 * (h₀.itemCount - ic0) + 4`. -/
theorem partRoundFinish_spec {w n : ℕ} (L : PartLayout w n) (s₀ : Memory.State)
    (dead0 inCur0 edgeState0 : ℕ → ℕ) (ic0 nc0 tLen0 : ℕ) (u : Fin n)
    (numComps cEdgeLen0 cLiftLen0 mcLen0 tLenOuter : ℕ) (shOuter h₀ : SHHandle)
    (hitPrev size tLen' : ℕ) (s : Memory.State)
    (W : DjpWitness L s₀ dead0 inCur0 edgeState0 (numComps + 1) ic0 nc0 tLen0 u
      ⟨0, hitPrev, size, tLen', h₀⟩ s)
    (hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem)
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem)
    (hdead₀ : ∀ x < n, s₀.mem (L.bufBase + x) = dead0 x)
    (hedge₀ : ∀ i < L.es.length, s₀.mem (L.bufBase + 14 * n + i) = edgeState0 i)
    (hincur₀_ne : ∀ x < n, inCur0 x ≠ numComps + 1)
    (hsimp : ∀ e : Fin L.es.length, (L.es[e.val]'e.isLt).u ≠ (L.es[e.val]'e.isLt).v)
    (hnc : numComps < n) (hnc_le : nc0 ≤ 2 * ic0) (hcl_le : cLiftLen0 + size ≤ 2 * n)
    (hclaimed : cEdgeLen0 + mcLen0 ≤
      (Finset.univ.filter (fun i : Fin L.es.length => edgeState0 i.val ≠ 0)).card) :
    let m := L.es.length
    let d : PartRoundFinishArgs :=
      ⟨L.toEnv, ⟨u.val, numComps, cEdgeLen0, cLiftLen0, mcLen0, tLenOuter, shOuter⟩, nc0,
        ⟨0, hitPrev, size, tLen', h₀⟩⟩
    let prog := partRoundFinish d
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    let hNext : SHHandle :=
      ⟨L.itemBase, L.nodeBase, 0, h₀.itemCount, h₀.nodeCount, partRankThreshold⟩
    let V_i := W.D.treeVerts W.D.numSteps
    let deadSet := Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)
    let lift : Fin size → Fin n := fun k =>
      (djpVertsList W.D)[k.val]'(by rw [djpVertsList_length, ← W.hsize]; exact k.isLt)
    partRoundFinishSafe w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    res.u = u.val + 1 ∧ res.numComps = numComps + 1 ∧
    cEdgeLen0 ≤ res.cEdgeLen ∧ res.cLiftLen = cLiftLen0 + size ∧
    mcLen0 ≤ res.mcLen ∧ res.tLen = tLen' ∧ res.sh = hNext ∧
    s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
    (∀ x, s'.mem x ≠ s₀.mem x →
      InSHPool ic0 nc0 (2 * m) (4 * m)
        ⟨L.itemBase, L.nodeBase, 0, ic0, nc0, partRankThreshold⟩ x ∨
      (L.bufBase ≤ x ∧ x < L.bufBase + 4 * n) ∨
      (L.bufBase + 4 * n + cLiftLen0 ≤ x ∧ x < L.bufBase + 4 * n + (cLiftLen0 + size)) ∨
      (L.bufBase + 6 * n + 3 * numComps ≤ x ∧ x < L.bufBase + 6 * n + 3 * (numComps + 1)) ∨
      x = L.bufBase + 9 * n + numComps ∨
      (L.bufBase + 10 * n + 4 * tLen0 ≤ x ∧ x < L.bufBase + 10 * n + 4 * tLen') ∨
      (L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + 2 * m) ∨
      (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 2 * m + 4 * res.cEdgeLen) ∨
      (L.bufBase + 14 * n + 6 * m + 4 * mcLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 6 * m + 4 * res.mcLen)) ∧
    hNext.nodeCount ≤ 2 * hNext.itemCount ∧
    SHInv w hNext.itemCount hNext.nodeCount (2 * m) (4 * m) hNext [] (fun _ => 0) s' ∧
    memoryCost prog s ≤ 6 * size + 15 *
      (remDeg n L.offBase s.mem deadSet - remDeg n L.offBase s.mem (deadSet ∪ V_i)) +
      20 * (h₀.itemCount - ic0) + 4 ∧
    16 * (res.mcLen - mcLen0) ≤ h₀.itemCount - ic0 ∧
    (∀ x : Fin n, s'.mem (L.bufBase + x.val) = if x ∈ V_i then 1 else dead0 x.val) ∧
    (∀ k : Fin size, s'.mem (L.bufBase + 4 * n + cLiftLen0 + k.val) = (lift k).val) ∧
    s'.mem (L.bufBase + 6 * n + 3 * numComps) = size ∧
    s'.mem (L.bufBase + 6 * n + 3 * numComps + 1) = res.cEdgeLen - cEdgeLen0 ∧
    s'.mem (L.bufBase + 6 * n + 3 * numComps + 2) = L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0 ∧
    s'.mem (L.bufBase + 9 * n + numComps) = L.bufBase + 4 * n + cLiftLen0 ∧
    HoldsIndexedEdges (L.bufBase + 10 * n + 4 * tLen0) W.treeIndexed s'.mem ∧
    ∃ (emittedIdx corrEmitted : List (Fin m)) (compLocal : List (IndexedEdge size)),
      emittedIdx.Nodup ∧ corrEmitted.Nodup ∧
      (∀ eIdx : Fin m, eIdx ∈ emittedIdx → eIdx ∉ corrEmitted) ∧
      compLocal.length = res.cEdgeLen - cEdgeLen0 ∧
      corrEmitted.length = res.mcLen - mcLen0 ∧
      HoldsIndexedEdges (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0) compLocal s'.mem ∧
      compLocal.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) =
        emittedIdx.map (fun eIdx => L.es[eIdx.val]'eIdx.isLt) ∧
      HoldsIndexedEdges (L.bufBase + 14 * n + 6 * m + 4 * mcLen0)
        (corrEmitted.map fun eIdx => L.es[eIdx.val]'eIdx.isLt) s'.mem ∧
      (∀ eIdx : Fin m, eIdx ∈ emittedIdx ↔
        edgeState0 eIdx.val = 0 ∧ (L.es[eIdx.val]'eIdx.isLt).u ∈ V_i ∧
          (L.es[eIdx.val]'eIdx.isLt).v ∈ V_i) ∧
      (∀ i < m, s'.mem (L.bufBase + 14 * n + i) =
        if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ emittedIdx then 1
        else if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ corrEmitted then 2
        else edgeState0 i) ∧
      res.cEdgeLen + res.mcLen ≤
        (Finset.univ.filter (fun i : Fin m => s'.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card ∧
      (∀ x : Fin n, s'.mem (L.bufBase + n + x.val) = s.mem (L.bufBase + n + x.val)) ∧
      (hitPrev = 0 → size < L.maxsize → ∀ eIdx : Fin m, edgeState0 eIdx.val = 0 →
        ¬((L.es[eIdx.val]'eIdx.isLt).u ∈ V_i ↔ (L.es[eIdx.val]'eIdx.isLt).v ∉ V_i)) ∧
      (∀ eIdx ∈ corrEmitted, edgeState0 eIdx.val = 0) ∧
      (∀ eIdx : Fin m, edgeState0 eIdx.val = 0 → eIdx ∉ emittedIdx → eIdx ∉ corrEmitted →
        ∀ s_step : Fin W.D.numSteps,
          ((L.es[eIdx.val]'eIdx.isLt).u ∈ W.D.treeVerts s_step.val ↔
            (L.es[eIdx.val]'eIdx.isLt).v ∉ W.D.treeVerts s_step.val) →
          W.D.wPop s_step ≤ (L.es[eIdx.val]'eIdx.isLt).weight) := by
  let m := L.es.length
  let V_i := W.D.treeVerts W.D.numSteps
  let lift : Fin size → Fin n := fun k =>
    (djpVertsList W.D)[k.val]'(by rw [djpVertsList_length, ← W.hsize]; exact k.isLt)
  have h16 := L.h16; have hn_pos := L.hn_pos
  have hsz_w : size = W.D.numSteps + 1 := W.hsize
  have hsz_le : size ≤ n := by
    have h1 := djpVerts_card W.D W.D.numSteps le_rfl
    have h2 : (W.D.treeVerts W.D.numSteps).card ≤ n := by
      simpa [Fintype.card_fin] using Finset.card_le_univ (W.D.treeVerts W.D.numSteps)
    rw [hsz_w, ← h1]; exact h2
  have hemit := partEmitComp_spec L s₀ dead0 inCur0 edgeState0 (numComps + 1) ic0 nc0 tLen0 u
    h₀ hitPrev size tLen' s W hcsr₀ hin₀ hedge₀ hincur₀_ne hsimp cEdgeLen0 mcLen0 hclaimed
  dsimp only at hemit
  generalize h_cRes : (Memory.spec 0).clientResult s (partEmitComp
    ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, m, numComps + 1⟩,
      hitPrev, size, cEdgeLen0⟩) = cRes at hemit
  generalize h_s1 : (Memory.spec 0).clientState s (partEmitComp
    ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, m, numComps + 1⟩,
      hitPrev, size, cEdgeLen0⟩) = s₁ at hemit
  rcases hemit with ⟨hsafe1, hvh1, hfr1, hwf1, hmod1, hce1, hcost1, emittedIdx, compLocal,
    hnd_emit, hlen_comp, hhold_comp, hmap_comp, hemit_iff, hest1, hclaim1⟩
  have hsh_s1 : SHInv w ic0 nc0 (2 * m) (4 * m) h₀ W.roots W.created s₁ :=
    partCongrSh_of_mod_ge L W.hib W.hnb W.hsh hwf1 hfr1 fun x hx => by
      rcases hmod1 x hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have hin_s1 : HoldsIndexedEdges L.edgeBase L.es s₁.mem :=
    (partCongrEdges_of_agree_buf L fun x hx => by
      by_contra hne; rcases hmod1 x hne with ⟨_, _⟩ | ⟨_, _⟩ <;> omega).1 (djpWitness_edges W hin₀)
  let edgeState1 : ℕ → ℕ := fun i =>
    if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ emittedIdx then 1 else edgeState0 i
  have hclaim1' : cRes.count + mcLen0 ≤
      (Finset.univ.filter (fun i : Fin m => edgeState1 i.val ≠ 0)).card := by
    have heq : Finset.univ.filter (fun i : Fin m => edgeState1 i.val ≠ 0) =
        Finset.univ.filter (fun i : Fin m => s₁.mem (L.bufBase + 14 * n + i.val) ≠ 0) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
      rw [hest1 i.val i.isLt]
    rw [heq]; exact hclaim1
  have hcorr := partRoundFinish_corr_spec L ic0 nc0 mcLen0 cRes.count h₀ W.roots W.created
    edgeState1 s₁ hsh_s1 (hfr1.trans W.hfr) W.hib W.hnb W.hrt hin_s1 hest1
    (fun p hp => let h := W.hent_prop p hp; ⟨h.choose, h.choose_spec.1⟩) hclaim1'
  dsimp only at hcorr
  generalize h_numCorr : (Memory.spec 0).clientResult s₁
    (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + m, 0, 2 * m)) = numCorr at hcorr
  generalize h_s2 : (Memory.spec 0).clientState s₁
    (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + m, 0, 2 * m)) = s₂ at hcorr
  generalize h_mRes : (Memory.spec 0).clientResult s₂
    (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, m⟩, numCorr, mcLen0⟩) = mRes at hcorr
  generalize h_s3 : (Memory.spec 0).clientState s₂
    (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, m⟩, numCorr, mcLen0⟩) = s₃ at hcorr
  rcases hcorr with ⟨hsafe2, hvh2, hsafe3, hvh3, hfr3, hwf3, hsh_s3, hmc_ge, hmc_diff, hcost23,
    hmod23, _, corrEmitted, hnd_corr, hlen_corr, hhold_corr, _, hest3, hclaim3,
    hcorr_es0, hcorr_uncorr⟩
  have hagree_s3_buf4n : ∀ x < L.bufBase + 4 * n, s₃.mem x = s.mem x := fun x hx => by
    have h31 : s₃.mem x = s₁.mem x := by
      by_contra hne; rcases hmod23 x hne with h | h <;> omega
    have h10 : s₁.mem x = s.mem x := by
      by_contra hne; rcases hmod1 x hne with h | h <;> omega
    exact h31.trans h10
  have hmark := partMarkDeadLoop_spec L size cLiftLen0 lift dead0 s₃ hwf3
    (hfr3.trans (hfr1.trans W.hfr)) hsz_le hcl_le
    (fun k => (hagree_s3_buf4n _ (by omega)).trans (W.hverts_mem k.val k.isLt))
    (fun x hx => (hagree_s3_buf4n _ (by omega)).trans (djpWitness_dead W hdead₀ x hx))
  dsimp only at hmark
  generalize h_lRes : (Memory.spec 0).clientResult s₃
    (partMarkDeadLoop ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩) = lRes at hmark
  generalize h_s4 : (Memory.spec 0).clientState s₃
    (partMarkDeadLoop ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩) = s₄ at hmark
  rcases hmark with ⟨hsafe4, hvh4, hfr4, hwf4, hmod4, hl_eq, hcost4, hlifts, hdead4⟩
  have hverts_mem_iff : ∀ x : Fin n, (∃ k : Fin size, lift k = x) ↔ x ∈ V_i := fun x => by
    constructor
    · rintro ⟨k, rfl⟩; rw [← mem_djpVertsList_iff]
      exact List.getElem_mem (by rw [djpVertsList_length, ← hsz_w]; exact k.isLt)
    · intro hx; rw [← mem_djpVertsList_iff] at hx; obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      exact ⟨⟨k, by rw [hsz_w, ← djpVertsList_length]; exact hk⟩, rfl⟩
  have hdead4' : ∀ x : Fin n, s₄.mem (L.bufBase + x.val) = if x ∈ V_i then 1 else dead0 x.val :=
    fun x => by rw [hdead4 x]; simp only [hverts_mem_iff x]
  have hmc_le_m : mRes.count ≤ m := by
    have h1 := Finset.card_le_univ (Finset.univ.filter (fun i : Fin m =>
      s₃.mem (L.bufBase + 14 * n + i.val) ≠ 0))
    rw [Fintype.card_fin] at h1; dsimp only [m] at *; omega
  have hce_le_m : cRes.count ≤ m := by
    have h1 := Finset.card_le_univ (Finset.univ.filter (fun i : Fin m =>
      s₁.mem (L.bufBase + 14 * n + i.val) ≠ 0))
    rw [Fintype.card_fin] at h1; dsimp only [m] at *; omega
  have hmeta := partWriteRoundMeta_spec L numComps size (cRes.count - cEdgeLen0)
    (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0) (L.bufBase + 4 * n + cLiftLen0) s₄ hwf4
    (hfr4.trans (hfr3.trans (hfr1.trans W.hfr))) hnc (L.hfit_end.of_le (by omega))
    (L.hfit_end.of_le (by omega)) (L.hfit_end.of_le (by omega)) (L.hfit_end.of_le (by omega))
  dsimp only at hmeta
  generalize h_s5 : (Memory.spec 0).clientState s₄ (partWriteRoundMeta
    ⟨L.bufBase, n, numComps, size, cRes.count - cEdgeLen0,
      L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0, L.bufBase + 4 * n + cLiftLen0⟩) = s₅ at hmeta
  rcases hmeta with ⟨hsafe5, hvh5, hfr5, hwf5, hmod5, hcost5, hm0, hm1, hm2, hm3⟩
  dsimp only [m] at *
  exact partRoundFinish_body_aux L s₀ dead0 inCur0 edgeState0 ic0 nc0 tLen0 u
    numComps cEdgeLen0 cLiftLen0 mcLen0 tLenOuter shOuter h₀ hitPrev size tLen' s
    W hnc hnc_le hcl_le cRes s₁ numCorr s₂ mRes s₃ lRes s₄ s₅
    h_cRes h_s1 h_numCorr h_s2 h_mRes h_s3 h_lRes h_s4 h_s5 hsz_w
    hsafe1 hvh1 hfr1 hmod1 hce1 hcost1 emittedIdx compLocal
    hnd_emit hlen_comp hhold_comp hmap_comp hemit_iff
    hsafe2 hvh2 hsafe3 hvh3 hfr3 hsh_s3 hmc_ge hmc_diff hcost23 hmod23
    corrEmitted hnd_corr hlen_corr hhold_corr hest3 hclaim3 hcorr_es0 hcorr_uncorr
    hsafe4 hvh4 hfr4 hmod4 hl_eq hcost4 hlifts hdead4' hmc_le_m hce_le_m
    hsafe5 hvh5 hfr5 hwf5 hmod5 hcost5 hm0 hm1 hm2 hm3

/-- Full specification of `partRunRound`: initializes DJP from live vertex `u`, runs `partDjpLoop`,
and finalizes emission via `partRoundFinish`, producing a valid `PartitionRoundWitness` and proving
`memoryCost prog s₀ + 2465 * remDeg' + 295 * (2 * m - ic') ≤ 2465 * remDeg + 295 * (2 * m - ic₀) +
6 * r.numVerts + 19`. -/
theorem partRunRound_spec {w n : ℕ} (L : PartLayout w n) (s₀ : Memory.State)
    (dead0 inCur0 edgeState0 : ℕ → ℕ) (numComps cEdgeLen0 cLiftLen0 mcLen0 tLen0 : ℕ)
    (u : Fin n) (h₀ : SHHandle)
    (hfr₀ : s₀.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hib₀ : h₀.itemBase = L.itemBase) (hnb₀ : h₀.nodeBase = L.nodeBase)
    (hrt₀ : h₀.rankThreshold = partRankThreshold)
    (hnc_le : h₀.nodeCount ≤ 2 * h₀.itemCount)
    (hsh₀ : SHInv w h₀.itemCount h₀.nodeCount (2 * L.es.length) (4 * L.es.length) h₀
      [] (fun _ => 0) s₀)
    (hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem)
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem)
    (hdead₀ : ∀ x < n, s₀.mem (L.bufBase + x) = dead0 x)
    (hincur₀ : ∀ x < n, s₀.mem (L.bufBase + n + x) = inCur0 x)
    (hincur₀_le : ∀ x < n, inCur0 x ≤ numComps)
    (hu_alive : dead0 u.val = 0)
    (hedge₀ : ∀ i < L.es.length, s₀.mem (L.bufBase + 14 * n + i) = edgeState0 i)
    (hsimp_g : IsSimple (edgeEnds (L.es.map IndexedEdge.toWeighted)))
    (hnc_dead : numComps ≤ (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)).card)
    (htLen_dead : tLen0 ≤ (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)).card)
    (hcl_dead : cLiftLen0 ≤
      (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)).card + numComps)
    (hclaimed : cEdgeLen0 + mcLen0 ≤
      (Finset.univ.filter (fun i : Fin L.es.length => edgeState0 i.val ≠ 0)).card)
    (hcap_rem₀ : h₀.itemCount + remDeg n L.offBase s₀.mem
      (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)) ≤ 2 * L.es.length) :
    let m := L.es.length
    let st0 : PartOuterState := ⟨u.val, numComps, cEdgeLen0, cLiftLen0, mcLen0, tLen0, h₀⟩
    let prog := partRunRound (L.toEnv, st0)
    let res := (Memory.spec 0).clientResult s₀ prog
    let s' := (Memory.spec 0).clientState s₀ prog
    let deadSet := Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)
    partRunRoundSafe w (L.toEnv, st0) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    res.u = u.val + 1 ∧ res.numComps = numComps + 1 ∧
    cEdgeLen0 ≤ res.cEdgeLen ∧ mcLen0 ≤ res.mcLen ∧
    s'.frontier = s₀.frontier ∧ Memory.WellFormed w s' ∧
    (∀ x, s'.mem x ≠ s₀.mem x →
      InSHPool 0 0 (2 * m) (4 * m)
        ⟨L.itemBase, L.nodeBase, 0, 0, 0, partRankThreshold⟩ x ∨
      (L.bufBase ≤ x ∧ x < L.bufBase + 4 * n) ∨
      (L.bufBase + 4 * n + cLiftLen0 ≤ x ∧ x < L.bufBase + 4 * n + res.cLiftLen) ∨
      (L.bufBase + 6 * n + 3 * numComps ≤ x ∧ x < L.bufBase + 6 * n + 3 * (numComps + 1)) ∨
      x = L.bufBase + 9 * n + numComps ∨
      (L.bufBase + 10 * n + 4 * tLen0 ≤ x ∧ x < L.bufBase + 10 * n + 4 * res.tLen) ∨
      (L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + 2 * m) ∨
      (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 2 * m + 4 * res.cEdgeLen) ∨
      (L.bufBase + 14 * n + 6 * m + 4 * mcLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 6 * m + 4 * res.mcLen)) ∧
    res.sh.itemBase = L.itemBase ∧ res.sh.nodeBase = L.nodeBase ∧ res.sh.firstRoot = 0 ∧
    res.sh.rankThreshold = partRankThreshold ∧
    h₀.itemCount ≤ res.sh.itemCount ∧ res.sh.nodeCount ≤ 2 * res.sh.itemCount ∧
    SHInv w res.sh.itemCount res.sh.nodeCount (2 * m) (4 * m) res.sh [] (fun _ => 0) s' ∧
    16 * (res.mcLen - mcLen0) ≤ res.sh.itemCount - h₀.itemCount ∧
    res.cEdgeLen + res.mcLen ≤
      (Finset.univ.filter (fun i : Fin m => s'.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card ∧
    ∃ (r : PartitionRoundWitness n) (emittedIdx corrEmitted : List (Fin m))
        (treeIndexed : List (IndexedEdge n)),
      let deadSet' := Finset.univ.filter (fun x : Fin n => s'.mem (L.bufBase + x.val) ≠ 0)
      res.cLiftLen = cLiftLen0 + r.numVerts ∧
      res.tLen = tLen0 + treeIndexed.length ∧
      treeIndexed.length = r.tree.numSteps ∧
      treeIndexed.map IndexedEdge.toWeighted = r.tree.treeEdges ∧
      (∀ e ∈ treeIndexed, ∃ eIdx : Fin m, e = L.es[eIdx.val] ∧ edgeState0 eIdx.val = 0) ∧
      HoldsIndexedEdges (L.bufBase + 10 * n + 4 * tLen0) treeIndexed s'.mem ∧
      emittedIdx.Nodup ∧ corrEmitted.Nodup ∧
      (∀ eIdx : Fin m, eIdx ∈ emittedIdx → eIdx ∉ corrEmitted) ∧
      r.compLocal.length = res.cEdgeLen - cEdgeLen0 ∧
      corrEmitted.length = res.mcLen - mcLen0 ∧
      r.corrEdges = corrEmitted.map (fun eIdx => L.es[eIdx.val]'eIdx.isLt) ∧
      HoldsIndexedEdges (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0) r.compLocal s'.mem ∧
      r.compGlobal = emittedIdx.map (fun eIdx => L.es[eIdx.val]'eIdx.isLt) ∧
      HoldsIndexedEdges (L.bufBase + 14 * n + 6 * m + 4 * mcLen0) r.corrEdges s'.mem ∧
      (∀ k : Fin r.numVerts, s'.mem (L.bufBase + 4 * n + cLiftLen0 + k.val) = (r.lift k).val) ∧
      s'.mem (L.bufBase + 6 * n + 3 * numComps) = r.numVerts ∧
      s'.mem (L.bufBase + 6 * n + 3 * numComps + 1) = r.compLocal.length ∧
      s'.mem (L.bufBase + 6 * n + 3 * numComps + 2) = L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0 ∧
      s'.mem (L.bufBase + 9 * n + numComps) = L.bufBase + 4 * n + cLiftLen0 ∧
      r.tree.root = u ∧ u ∈ r.verts ∧ r.verts.card = r.numVerts ∧
      1 ≤ r.numVerts ∧ r.numVerts ≤ L.maxsize ∧
      (1 ≤ r.compLocal.length → r.numVerts ≤ 2 * r.compLocal.length) ∧
      Function.Injective r.lift ∧
      IsSimple (edgeEnds (r.compLocal.map IndexedEdge.toWeighted)) ∧
      (∀ e ∈ r.compGlobal, e.u ∈ r.verts ∧ e.v ∈ r.verts) ∧
      r.tree.treeEdges.Subperm (r.compGlobal.map IndexedEdge.toWeighted) ∧
      (∀ x : Fin n, s'.mem (L.bufBase + x.val) = if x ∈ r.verts then 1 else dead0 x.val) ∧
      (∀ x : Fin n, x ∈ r.verts → s'.mem (L.bufBase + n + x.val) = numComps + 1) ∧
      (∀ x : Fin n, x ∉ r.verts → s'.mem (L.bufBase + n + x.val) = inCur0 x.val) ∧
      (∀ i < m, s'.mem (L.bufBase + 14 * n + i) =
        if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ emittedIdx then 1
        else if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ corrEmitted then 2
        else edgeState0 i) ∧
      (∀ eIdx : Fin m, eIdx ∈ emittedIdx ↔
        edgeState0 eIdx.val = 0 ∧ (L.es[eIdx.val]'eIdx.isLt).u ∈ r.verts ∧
          (L.es[eIdx.val]'eIdx.isLt).v ∈ r.verts) ∧
      (∀ eIdx ∈ corrEmitted, edgeState0 eIdx.val = 0) ∧
      res.tLen ≤ deadSet'.card ∧ res.cLiftLen ≤ deadSet'.card + (numComps + 1) ∧
      numComps + 1 ≤ deadSet'.card ∧
      res.sh.itemCount + remDeg n L.offBase s'.mem deadSet' ≤ 2 * m ∧
      (r.verts ∩ deadSet).card ≤ 1 ∧
      (L.maxsize ≤ r.verts.card ∨ (r.verts ∩ deadSet).Nonempty ∨
        (∀ eIdx : Fin m, edgeState0 eIdx.val = 0 →
          ¬((L.es[eIdx.val]'eIdx.isLt).u ∈ r.verts ↔
            (L.es[eIdx.val]'eIdx.isLt).v ∉ r.verts))) ∧
      (∀ eIdx : Fin m, edgeState0 eIdx.val = 0 → eIdx ∉ emittedIdx → eIdx ∉ corrEmitted →
        ∀ s_step : Fin r.tree.numSteps,
          ((L.es[eIdx.val]'eIdx.isLt).u ∈ r.tree.treeVerts s_step.val ↔
            (L.es[eIdx.val]'eIdx.isLt).v ∉ r.tree.treeVerts s_step.val) →
          r.tree.wPop s_step ≤ (L.es[eIdx.val]'eIdx.isLt).weight) ∧
      (∀ x ∈ r.verts, x ∈ deadSet →
        ∃ hpos : 0 < r.tree.numSteps,
          x = r.tree.vOut ⟨r.tree.numSteps - 1, Nat.sub_lt hpos Nat.one_pos⟩) ∧
      memoryCost prog s₀ + 2465 * remDeg n L.offBase s'.mem deadSet' +
        295 * (2 * m - res.sh.itemCount) ≤
        2465 * remDeg n L.offBase s₀.mem deadSet + 295 * (2 * m - h₀.itemCount) +
          6 * r.numVerts + 19 := by
  let m := L.es.length
  let st0 : PartOuterState := ⟨u.val, numComps, cEdgeLen0, cLiftLen0, mcLen0, tLen0, h₀⟩
  let deadSet : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)
  have h16 := L.h16; have hn_pos := L.hn_pos
  have hu_not_dead : u ∉ deadSet := by simp [deadSet, hu_alive]
  have hdead_lt_n : deadSet.card < n := by
    have hlt : Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ⊂
        (Finset.univ : Finset (Fin n)) :=
      Finset.ssubset_univ_iff.mpr fun heq => by
        have : u ∈ Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) := by
          rw [heq]; exact Finset.mem_univ _
        exact hu_not_dead this
    simpa [Fintype.card_fin] using Finset.card_lt_card hlt
  have hnc : numComps < n := lt_of_le_of_lt hnc_dead hdead_lt_n
  have hincur_ne : ∀ x < n, inCur0 x ≠ numComps + 1 := fun x hx h => by
    have := hincur₀_le x hx; omega
  have hcid_fit : Fits w (numComps + 1) := L.hfit_end.of_le (by omega)
  have hsimp_e : ∀ e : Fin m, (L.es[e.val]'e.isLt).u ≠ (L.es[e.val]'e.isLt).v := fun e => by
    have hdiag := ((isSimple_iff _).mp hsimp_g).1 ⟨e.val, by simp [m]⟩
    simpa [edgeEnds, IndexedEdge.toWeighted, Sym2.mk_isDiag_iff] using hdiag
  have hinit := partRoundInit_spec L dead0 inCur0 edgeState0 (numComps + 1) h₀.itemCount
    h₀.nodeCount tLen0 u h₀ s₀ hfr₀ hib₀ hnb₀ hrt₀ rfl hsh₀ hcsr₀ hin₀ hincur₀
    hincur_ne hcid_fit hu_alive hedge₀ hsimp_e htLen_dead hcap_rem₀
  dsimp only at hinit
  generalize h_h1 : (Memory.spec 0).clientResult s₀
    (partRoundInit ⟨L.toEnv, numComps + 1, u.val, h₀⟩) = h₁ at *
  generalize h_s1 : (Memory.spec 0).clientState s₀
    (partRoundInit ⟨L.toEnv, numComps + 1, u.val, h₀⟩) = s₁ at *
  rcases hinit with ⟨hsafe_in, hvh_in, _, _, W₀, hpot_in⟩
  have hloop := partDjpLoop_spec L s₀ dead0 inCur0 edgeState0 (numComps + 1) h₀.itemCount
    h₀.nodeCount tLen0 u hcsr₀ hin₀ hdead₀ hedge₀ hincur_ne hcid_fit hsimp_e h₁ s₁ W₀
  dsimp only at hloop
  generalize h_st1 : (Memory.spec 0).clientResult s₁
    (partDjpLoop ⟨L.toEnv, numComps + 1, tLen0, h₁⟩) = st1 at *
  generalize h_s2 : (Memory.spec 0).clientState s₁
    (partDjpLoop ⟨L.toEnv, numComps + 1, tLen0, h₁⟩) = s₂ at *
  rcases hloop with ⟨hsafe_lp, hvh_lp, hst1_0, _, _, W_lp, hpot_lp⟩
  have hst1_eq : (⟨0, st1.hitPrev, st1.size, st1.tLen, st1.sh⟩ : PartDjpState) = st1 := by
    cases st1; exact congrArg (PartDjpState.mk · _ _ _ _) hst1_0.symm
  let W' : DjpWitness L s₀ dead0 inCur0 edgeState0 (numComps + 1) h₀.itemCount h₀.nodeCount tLen0 u
      ⟨0, st1.hitPrev, st1.size, st1.tLen, st1.sh⟩ s₂ :=
    { W_lp with
      hstop_dead := fun x hx hd =>
        ⟨(W_lp.hstop_dead x hx hd).1, rfl, (W_lp.hstop_dead x hx hd).2.2.1,
          (W_lp.hstop_dead x hx hd).2.2.2⟩
      hhit_prev := fun h =>
        ⟨(W_lp.hhit_prev h).1, rfl, (W_lp.hhit_prev h).2.2.1, (W_lp.hhit_prev h).2.2.2⟩
      hcont_cov := fun h => absurd rfl h
      hempty_stop := fun _ => W_lp.hempty_stop hst1_0
      hcont_size := fun h => absurd rfl h }
  let hitPrev := st1.hitPrev; let size := st1.size; let tLen' := st1.tLen; let h_end := st1.sh
  let V_i := W'.D.treeVerts W'.D.numSteps
  have hsz_eq : size = W'.D.numSteps + 1 := W'.hsize
  have htl_eq : tLen' = tLen0 + W'.D.numSteps := W'.htlen
  have htl_dead' : tLen' ≤ deadSet.card + W'.D.numSteps := W'.htlen_dead
  have hcard_Vi : V_i.card = size := by
    dsimp only [V_i, size]; rw [djpVerts_card W'.D W'.D.numSteps le_rfl, ← hsz_eq]
  have hdead_inter : (V_i ∩ deadSet).card ≤ 1 := by
    by_cases hp0 : hitPrev = 0
    · have hdisj : V_i ∩ deadSet = ∅ := by
        ext x; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false, not_and, deadSet]
        intro hx hne; exact hne (W'.hno_hit hp0 x hx)
      rw [hdisj, Finset.card_empty]; exact Nat.zero_le 1
    · have hp1 := W'.hhit_prev hp0
      have hsub : V_i ∩ deadSet ⊆ {W'.D.vOut ⟨W'.D.numSteps - 1, by have := hp1.2.2.1; omega⟩} := by
        intro x hx; rw [Finset.mem_inter, Finset.mem_filter] at hx
        exact Finset.mem_singleton.mpr ((W'.hstop_dead x hx.1 hx.2.2).2.2.2 hp1.2.2.1)
      exact (Finset.card_le_card hsub).trans (Finset.card_singleton _).le
  have hu_in_Vi : u ∈ V_i := mem_djpVerts_mono W'.D.root W'.D.vOut (Nat.zero_le _)
    (Finset.mem_singleton.mpr W'.hroot.symm)
  have hdead_union_card : (deadSet ∪ V_i).card =
      deadSet.card + size - (if hitPrev = 0 then 0 else 1) := by
    have hcu := Finset.card_union_add_card_inter deadSet V_i; rw [Finset.inter_comm] at hcu
    by_cases hp0 : hitPrev = 0
    · have hdisj : V_i ∩ deadSet = ∅ := by
        ext x; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false, not_and, deadSet]
        intro hx hne; exact hne (W'.hno_hit hp0 x hx)
      rw [hdisj, Finset.card_empty] at hcu; simp [hp0]; omega
    · have hp1 := W'.hhit_prev hp0
      let x0 := W'.D.vOut ⟨W'.D.numSteps - 1, by have := hp1.2.2.1; omega⟩
      have hx0_in : x0 ∈ V_i := mem_djpVerts_mono W'.D.root W'.D.vOut
        (by have := hp1.2.2.1; omega : W'.D.numSteps - 1 + 1 ≤ W'.D.numSteps)
        (vOut_mem_djpVerts_succ W'.D.root W'.D.vOut
          ⟨W'.D.numSteps - 1, by have := hp1.2.2.1; omega⟩)
      have hx0_dead : x0 ∈ deadSet := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1.2.2.2 hp1.2.2.1⟩
      have hge1 : 1 ≤ (V_i ∩ deadSet).card := Finset.card_pos.mpr
        ⟨x0, Finset.mem_inter.mpr ⟨hx0_in, hx0_dead⟩⟩
      have heq1 : (V_i ∩ deadSet).card = 1 := le_antisymm hdead_inter hge1
      simp only [hp0, ↓reduceIte]; omega
  have hcl_le : cLiftLen0 + size ≤ 2 * n := by
    have hcb : (deadSet ∪ V_i).card ≤ n := by
      simpa [Fintype.card_fin] using Finset.card_le_univ (deadSet ∪ V_i)
    dsimp only [deadSet] at hdead_union_card hcl_dead hnc_dead hcb ⊢
    split_ifs at hdead_union_card <;> omega
  have hfin := partRoundFinish_spec L s₀ dead0 inCur0 edgeState0 h₀.itemCount h₀.nodeCount tLen0 u
    numComps cEdgeLen0 cLiftLen0 mcLen0 tLen0 h₀ h_end hitPrev size tLen' s₂ W' hcsr₀ hin₀ hdead₀
    hedge₀ hincur_ne hsimp_e hnc hnc_le hcl_le hclaimed
  dsimp only at hfin
  generalize h_res : (Memory.spec 0).clientResult s₂
    (partRoundFinish ⟨L.toEnv, st0, h₀.nodeCount, ⟨0, hitPrev, size, tLen', h_end⟩⟩) = res at *
  generalize h_s3 : (Memory.spec 0).clientState s₂
    (partRoundFinish ⟨L.toEnv, st0, h₀.nodeCount, ⟨0, hitPrev, size, tLen', h_end⟩⟩) = s₃ at *
  rcases hfin with ⟨hsafe_fn, hvh_fn, hres1, hres21, hce_le, hl_eq, hmc_ge, htl_res, hhn_res,
    hfr_fn, hwf_fn, hmod_fn, hnc_next, hsh_next, hcost_fn, hmc_diff, hdead_fn, hlifts_fn,
    hm0, hm1, hm2, hm3, htree_fn, emittedIdx, corrEmitted, compLocal, hnd_em, hnd_cr, hdisj_ec,
    hlen_cp, hlen_cr, hhold_cp, hmap_cp, hhold_cr, hemit_iff, hest_fn, hclaim_fn,
    hincur_fn, hempty_fn, hcorr_es0, huncorr_fn⟩
  have hprog_rr : partRunRound (L.toEnv, st0) =
      (partRoundInit ⟨L.toEnv, numComps + 1, u.val, h₀⟩ >>= fun h₁' =>
        partDjpLoop ⟨L.toEnv, numComps + 1, tLen0, h₁'⟩ >>= fun st1' =>
          partRoundFinish ⟨L.toEnv, st0, h₀.nodeCount, st1'⟩) := partRunRound_def _
  have hsafe : partRunRoundSafe w (L.toEnv, st0) s₀ := by
    rw [partRunRoundSafe_def]; dsimp only [st0]
    rw [h_h1, h_s1, h_st1, h_s2]
    refine ⟨h16, hcid_fit, hsafe_in, hsafe_lp, ?_⟩
    rw [← hst1_eq]; exact hsafe_fn
  have hvh : (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (partRunRound (L.toEnv, st0))) := by
    rw [hprog_rr]; refine validHistory_bind_step hvh_in ?_; rw [h_h1, h_s1]
    refine validHistory_bind_step hvh_lp ?_; rw [h_st1, h_s2, ← hst1_eq]
    exact hvh_fn
  have hres_eq : (Memory.spec 0).clientResult s₀ (partRunRound (L.toEnv, st0)) = res := by
    rw [hprog_rr, StateTransitionSpec.clientResult_bind, h_h1, h_s1,
      StateTransitionSpec.clientResult_bind, h_st1, h_s2, ← hst1_eq, h_res]
  have hst_eq : (Memory.spec 0).clientState s₀ (partRunRound (L.toEnv, st0)) = s₃ := by
    rw [hprog_rr, StateTransitionSpec.clientState_bind, h_h1, h_s1,
      StateTransitionSpec.clientState_bind, h_st1, h_s2, ← hst1_eq, h_s3]
  have hcost_eq : memoryCost (partRunRound (L.toEnv, st0)) s₀ =
      memoryCost (partRoundInit ⟨L.toEnv, numComps + 1, u.val, h₀⟩) s₀ +
      memoryCost (partDjpLoop ⟨L.toEnv, numComps + 1, tLen0, h₁⟩) s₁ +
      memoryCost (partRoundFinish ⟨L.toEnv, st0, h₀.nodeCount,
        ⟨0, hitPrev, size, tLen', h_end⟩⟩) s₂ := by
    rw [hprog_rr, memoryCost_bind', h_h1, h_s1, memoryCost_bind', h_st1, h_s2, ← hst1_eq, add_assoc]
  have hs3_agree_off : ∀ k ≤ n, s₃.mem (L.offBase + k) = s₀.mem (L.offBase + k) := fun k hk => by
    by_contra hne; rcases hmod_fn (L.offBase + k) hne with hp | h | h | h | h | h | h | h | h
    · have := L.inSHPool_lt_bufBase rfl rfl hp; have := L.csr_lt_itemBase; omega
    all_goals (have := L.csr_lt_itemBase; have := L.hit_nd; have := L.hnd_buf; omega)
  have hs2_agree_off : ∀ k ≤ n, s₂.mem (L.offBase + k) = s₀.mem (L.offBase + k) := fun k hk =>
    W'.agree_outside_mod
      (fun hp => by have := L.inSHPool_lt_bufBase rfl rfl hp; have := L.csr_lt_itemBase; omega)
      (fun _ => by have := L.csr_lt_itemBase; have := L.hit_nd; have := L.hnd_buf; omega)
      (fun _ => by have := L.csr_lt_itemBase; have := L.hit_nd; have := L.hnd_buf; omega)
  have hs3_fr : s₃.frontier = s₀.frontier := hfr_fn.trans (W'.hfr.trans hfr₀.symm)
  let lift : Fin size → Fin n := fun k =>
    (djpVertsList W'.D)[k.val]'(by rw [djpVertsList_length, ← hsz_eq]; exact k.isLt)
  have hlift_inj : Function.Injective lift := fun a b hab =>
    Fin.ext ((djpVertsList_nodup W'.D).getElem_inj_iff.mp hab)
  let r : PartitionRoundWitness n :=
    { tree := W'.D, numVerts := size, lift := lift, compLocal := compLocal,
      corrEdges := corrEmitted.map (fun eIdx => L.es[eIdx.val]'eIdx.isLt) }
  have hr_global_eq : r.compGlobal = emittedIdx.map (fun eIdx => L.es[eIdx.val]'eIdx.isLt) :=
    hmap_cp
  have hdeadSet' : Finset.univ.filter (fun x : Fin n => s₃.mem (L.bufBase + x.val) ≠ 0) =
      deadSet ∪ V_i := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hdead_fn x]
    by_cases hx : x ∈ V_i <;> simp [hx, V_i, deadSet]
  have hdead_lt : deadSet.card < (deadSet ∪ V_i).card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, fun heq =>
      hu_not_dead (heq ▸ Finset.mem_union_right _ hu_in_Vi)⟩)
  have htlen_le_dead' : tLen' ≤ (deadSet ∪ V_i).card := by
    by_cases hp0 : hitPrev = 0
    · simp only [hp0, ↓reduceIte, Nat.sub_zero] at hdead_union_card; omega
    · simp only [hp0, ↓reduceIte] at hdead_union_card; have := W'.hhit_prev hp0; omega
  have hcl_dead' : cLiftLen0 + size ≤ (deadSet ∪ V_i).card + (numComps + 1) := by
    dsimp only [deadSet] at hdead_union_card hcl_dead ⊢; split_ifs at hdead_union_card <;> omega
  have hrem_s3_eq : remDeg n L.offBase s₃.mem (deadSet ∪ V_i) =
      remDeg n L.offBase s₂.mem (deadSet ∪ V_i) :=
    remDeg_congr _ fun k hk => (hs3_agree_off k hk).trans (hs2_agree_off k hk).symm
  have hrem_s2_dead : remDeg n L.offBase s₂.mem deadSet = remDeg n L.offBase s₀.mem deadSet :=
    remDeg_congr _ hs2_agree_off
  have hcap_rem' : h_end.itemCount + remDeg n L.offBase s₃.mem (deadSet ∪ V_i) ≤ 2 * m := by
    rw [hrem_s3_eq]; exact W'.hcap_rem
  have hpool_sub : ∀ x, InSHPool h₀.itemCount h₀.nodeCount (2 * m) (4 * m)
      ⟨L.itemBase, L.nodeBase, 0, h₀.itemCount, h₀.nodeCount, partRankThreshold⟩ x →
      InSHPool 0 0 (2 * m) (4 * m) ⟨L.itemBase, L.nodeBase, 0, 0, 0, partRankThreshold⟩ x :=
    fun x hx => by
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [left; right] <;> dsimp only at h1 h2 ⊢ <;> omega
  have hcomp_simp : IsSimple (edgeEnds (r.compLocal.map IndexedEdge.toWeighted)) := by
    have hmap_cp' : r.compLocal.map (fun e => ⟨r.lift e.u, r.lift e.v, e.weight, e.id⟩) =
        emittedIdx.map (fun eIdx => L.es[eIdx.val]'eIdx.isLt) := hmap_cp
    refine compactVertices_isSimple hmap_cp' ?_
    rw [isSimple_iff] at hsimp_g ⊢
    refine ⟨fun i => ?_, fun i₁ i₂ hij => ?_⟩
    · have hi : i.val < emittedIdx.length := by simpa using i.isLt
      let eIdx := emittedIdx[i.val]'hi
      simpa [edgeEnds, List.getElem_map, IndexedEdge.toWeighted] using
        hsimp_g.1 ⟨eIdx.val, by simp [eIdx.isLt]⟩
    · have hi1 : i₁.val < emittedIdx.length := by simpa using i₁.isLt
      have hi2 : i₂.val < emittedIdx.length := by simpa using i₂.isLt
      let e1 := emittedIdx[i₁.val]'hi1; let e2 := emittedIdx[i₂.val]'hi2
      have hsame : edgeEnds (L.es.map IndexedEdge.toWeighted) ⟨e1.val, by simp [e1.isLt]⟩ =
          edgeEnds (L.es.map IndexedEdge.toWeighted) ⟨e2.val, by simp [e2.isLt]⟩ := by
        simpa [edgeEnds, List.getElem_map, IndexedEdge.toWeighted] using hij
      exact Fin.ext (hnd_em.getElem_inj_iff.mp (Fin.ext (by
        simpa using congrArg Fin.val (hsimp_g.2 hsame))))
  have htree_sub : r.tree.treeEdges.Subperm (r.compGlobal.map IndexedEdge.toWeighted) := by
    refine (djp_treeEdges_nodup W'.D).subperm fun ew hew => ?_
    rw [← W'.htree_w, List.mem_map] at hew; obtain ⟨ei, hei, rfl⟩ := hew
    obtain ⟨eIdx, hei_eq, he0⟩ := W'.htree_src ei hei
    obtain ⟨s_step, hs_mem⟩ : ∃ s_step : Fin W'.D.numSteps, W'.D.edge s_step =
        (L.es[eIdx.val]'eIdx.isLt).toWeighted := by
      have hm : ei.toWeighted ∈ W'.treeIndexed.map IndexedEdge.toWeighted :=
        List.mem_map.mpr ⟨ei, hei, rfl⟩
      rw [W'.htree_w] at hm; obtain ⟨s_step, _, hs_eq⟩ := List.mem_map.mp hm
      exact ⟨s_step, by rw [hs_eq, hei_eq]⟩
    have huv := W'.D.mem_treeVerts_of_edge s_step; rw [hs_mem] at huv
    have he_em : eIdx ∈ emittedIdx := (hemit_iff eIdx).mpr
      ⟨he0, mem_djpVerts_mono W'.D.root W'.D.vOut s_step.isLt huv.1,
        mem_djpVerts_mono W'.D.root W'.D.vOut s_step.isLt huv.2⟩
    rw [hr_global_eq]
    exact List.mem_map.mpr ⟨L.es[eIdx.val]'eIdx.isLt, List.mem_map.mpr ⟨eIdx, he_em, rfl⟩,
      congrArg IndexedEdge.toWeighted hei_eq.symm⟩
  have hcost_total :
      memoryCost (partRunRound (L.toEnv, st0)) s₀ +
        2465 * remDeg n L.offBase s₃.mem (deadSet ∪ V_i) + 295 * (2 * m - h_end.itemCount) ≤
      2465 * remDeg n L.offBase s₀.mem deadSet + 295 * (2 * m - h₀.itemCount) +
        6 * size + 19 := by
    have hphi_nn : (0 : ℚ) ≤ totalPhi partRankThreshold W'.roots :=
      totalPhi_nonneg partRankThreshold W'.roots
    have hrem_le : remDeg n L.offBase s₂.mem (deadSet ∪ V_i) ≤ remDeg n L.offBase s₀.mem deadSet :=
      hrem_s2_dead ▸ remDeg_anti Finset.subset_union_left
    have hcost_fn_q : (memoryCost (partRoundFinish ⟨L.toEnv, st0, h₀.nodeCount,
        ⟨0, hitPrev, size, tLen', h_end⟩⟩) s₂ : ℚ) ≤
        6 * (size : ℚ) + 15 * ((remDeg n L.offBase s₀.mem deadSet : ℚ) -
          (remDeg n L.offBase s₃.mem (deadSet ∪ V_i) : ℚ)) +
        20 * ((h_end.itemCount : ℚ) - (h₀.itemCount : ℚ)) + 4 := by
      have h1 : (remDeg n L.offBase s₂.mem deadSet -
          remDeg n L.offBase s₂.mem (deadSet ∪ V_i) : ℕ) =
          remDeg n L.offBase s₀.mem deadSet - remDeg n L.offBase s₃.mem (deadSet ∪ V_i) := by
        rw [hrem_s2_dead, hrem_s3_eq]
      have h2 := hcost_fn; rw [h1] at h2; have h2_q := Nat.cast_le (α := ℚ).mpr h2
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_sub (hrem_s3_eq ▸ hrem_le), Nat.cast_sub W'.hic_ge] at h2_q
      push_cast at h2_q ⊢; exact h2_q
    have hpot_diff : (memoryCost (partRoundInit ⟨L.toEnv, numComps + 1, u.val, h₀⟩) s₀ : ℚ) +
        (memoryCost (partDjpLoop ⟨L.toEnv, numComps + 1, tLen0, h₁⟩) s₁ : ℚ) +
        2450 * (remDeg n L.offBase s₃.mem (deadSet ∪ V_i) : ℚ) +
        275 * ((2 * m - h_end.itemCount : ℕ) : ℚ) ≤
        2450 * (remDeg n L.offBase s₀.mem deadSet : ℚ) +
        275 * ((2 * m - h₀.itemCount : ℕ) : ℚ) + 15 := by
      dsimp only [djpPot] at hpot_in hpot_lp
      have hrem0_eq : remDeg n L.offBase s₀.mem
          (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)) =
          remDeg n L.offBase s₀.mem deadSet := rfl
      have hset_lp : Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ∪
          W_lp.D.treeVerts W_lp.D.numSteps = deadSet ∪ V_i := rfl
      rw [hrem0_eq] at hpot_in; rw [hset_lp, ← hrem_s3_eq, hst1_0] at hpot_lp
      simp only [↓reduceIte, add_zero] at hpot_lp
      have hlen_nn : (0 : ℚ) ≤ ((forestItems W_lp.roots).length : ℚ) := Nat.cast_nonneg _
      have hphi_lp :
          totalPhi partRankThreshold W_lp.roots = totalPhi partRankThreshold W'.roots := rfl
      rw [hphi_lp] at hpot_lp; dsimp only [m] at hpot_in hpot_lp ⊢
      linarith only [hpot_in, hpot_lp, hphi_nn, hlen_nn]
    have htot_q : ((memoryCost (partRunRound (L.toEnv, st0)) s₀ +
        2465 * remDeg n L.offBase s₃.mem (deadSet ∪ V_i) +
        295 * (2 * m - h_end.itemCount) : ℕ) : ℚ) ≤
        ((2465 * remDeg n L.offBase s₀.mem deadSet + 295 * (2 * m - h₀.itemCount) +
          6 * size + 19 : ℕ) : ℚ) := by
      rw [hcost_eq]; push_cast
      rw [Nat.cast_sub W'.hic_le, Nat.cast_sub hsh₀.ic_max] at hpot_diff ⊢
      push_cast at hpot_diff ⊢; linarith only [hcost_fn_q, hpot_diff]
    exact_mod_cast htot_q
  have hmod_all : ∀ x, s₃.mem x ≠ s₀.mem x →
      InSHPool 0 0 (2 * m) (4 * m) ⟨L.itemBase, L.nodeBase, 0, 0, 0, partRankThreshold⟩ x ∨
      (L.bufBase ≤ x ∧ x < L.bufBase + 4 * n) ∨
      (L.bufBase + 4 * n + cLiftLen0 ≤ x ∧ x < L.bufBase + 4 * n + res.cLiftLen) ∨
      (L.bufBase + 6 * n + 3 * numComps ≤ x ∧ x < L.bufBase + 6 * n + 3 * (numComps + 1)) ∨
      x = L.bufBase + 9 * n + numComps ∨
      (L.bufBase + 10 * n + 4 * tLen0 ≤ x ∧ x < L.bufBase + 10 * n + 4 * res.tLen) ∨
      (L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + 2 * m) ∨
      (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 2 * m + 4 * res.cEdgeLen) ∨
      (L.bufBase + 14 * n + 6 * m + 4 * mcLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 6 * m + 4 * res.mcLen) := fun x hx => by
    rcases hmod_fn x hx with hp | h | h | h | h | h | h | h | h
    · exact .inl (hpool_sub x hp)
    · exact .inr (.inl h)
    · rw [hl_eq]; exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr (.inl h))))
    · rw [htl_res]; exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h)))))))
  have hstop_all : L.maxsize ≤ r.verts.card ∨ (r.verts ∩ deadSet).Nonempty ∨
      (∀ eIdx : Fin m, edgeState0 eIdx.val = 0 →
        ¬((L.es[eIdx.val]'eIdx.isLt).u ∈ r.verts ↔ (L.es[eIdx.val]'eIdx.isLt).v ∉ r.verts)) := by
    by_cases hsz : L.maxsize ≤ size
    · exact .inl (hcard_Vi ▸ hsz)
    · by_cases hp0 : hitPrev = 0
      · exact .inr (.inr (hempty_fn hp0 (by omega)))
      · have hp1 := W'.hhit_prev hp0
        refine .inr (.inl ⟨W'.D.vOut ⟨W'.D.numSteps - 1, by have := hp1.2.2.1; omega⟩,
          Finset.mem_inter.mpr ⟨?_,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1.2.2.2 hp1.2.2.1⟩⟩⟩)
        exact mem_djpVerts_mono W'.D.root W'.D.vOut
          (by have := hp1.2.2.1; omega : W'.D.numSteps - 1 + 1 ≤ W'.D.numSteps)
          (vOut_mem_djpVerts_succ W'.D.root W'.D.vOut
            ⟨W'.D.numSteps - 1, by have := hp1.2.2.1; omega⟩)
  dsimp only
  dsimp only [st0] at hsafe hvh hres_eq hst_eq
  refine ⟨hsafe, hvh, by rw [hres_eq]; exact hres1, by rw [hres_eq]; exact hres21,
    by rw [hres_eq]; exact hce_le, by rw [hres_eq]; exact hmc_ge,
    by rw [hst_eq]; exact hs3_fr, by rw [hst_eq]; exact hwf_fn,
    fun x hx => by rw [hst_eq] at hx; rw [hres_eq]; exact hmod_all x hx,
    by rw [hres_eq, hhn_res], by rw [hres_eq, hhn_res],
    by rw [hres_eq, hhn_res], by rw [hres_eq, hhn_res],
    by rw [hres_eq, hhn_res]; exact W'.hic_ge,
    by rw [hres_eq, hhn_res]; exact hnc_next,
    by rw [hst_eq, hres_eq, hhn_res]; exact hsh_next,
    by rw [hres_eq, hhn_res]; exact hmc_diff,
    by rw [hst_eq, hres_eq]; exact hclaim_fn,
    r, emittedIdx, corrEmitted, W'.treeIndexed,
    by rw [hres_eq]; exact hl_eq, by rw [hres_eq, htl_res, htl_eq, W'.htree_len],
    W'.htree_len, W'.htree_w, W'.htree_src, by rw [hst_eq]; exact htree_fn,
    hnd_em, hnd_cr, hdisj_ec, by rw [hres_eq]; exact hlen_cp, by rw [hres_eq]; exact hlen_cr,
    rfl, by rw [hst_eq]; exact hhold_cp, hr_global_eq, by rw [hst_eq]; exact hhold_cr,
    fun k => by rw [hst_eq]; exact hlifts_fn k, by rw [hst_eq]; exact hm0,
    by rw [hst_eq, hm1, ← hlen_cp], by rw [hst_eq]; exact hm2, by rw [hst_eq]; exact hm3,
    W'.hroot, hu_in_Vi, by
      dsimp only [r, PartitionRoundWitness.verts, size]
      exact (djpVerts_card _ _ le_rfl).trans W'.hsize.symm,
    by dsimp only [r, size]; rw [W'.hsize]; exact Nat.succ_pos _, W'.hsize_le,
    fun _ => by
      have h1' : r.tree.treeEdges.length = W'.D.numSteps := by
        dsimp only [r, DynamicDJPTree.treeEdges]; simp
      have h2' : (r.compGlobal.map IndexedEdge.toWeighted).length = compLocal.length := by
        rw [hr_global_eq, List.length_map, List.length_map]
        simpa using (congrArg List.length hmap_cp).symm
      have := htree_sub.length_le; dsimp only [r] at *; omega,
    hlift_inj, hcomp_simp, fun e he => by
      rw [hr_global_eq, List.mem_map] at he; obtain ⟨eIdx, he_in, rfl⟩ := he
      exact ((hemit_iff eIdx).mp he_in).2,
    htree_sub, fun x => by rw [hst_eq]; exact hdead_fn x,
    fun x hx => by rw [hst_eq, hincur_fn x]; exact (W'.hincur_in x hx).1,
    fun x hx => by rw [hst_eq, hincur_fn x]; exact W'.hincur_out x hx,
    fun i hi => by rw [hst_eq]; exact hest_fn i hi, hemit_iff, hcorr_es0,
    by rw [hst_eq, hres_eq, htl_res, hdeadSet']; exact htlen_le_dead',
    by rw [hst_eq, hres_eq, hl_eq, hdeadSet']; exact hcl_dead',
    by rw [hst_eq, hdeadSet']
       dsimp only [deadSet] at hdead_lt hnc_dead ⊢; have := hdead_lt; omega,
    by rw [hst_eq, hres_eq, hhn_res, hdeadSet']; exact hcap_rem',
    hdead_inter, hstop_all, huncorr_fn,
    fun x hx hx_dead => let hsd := W'.hstop_dead x hx (Finset.mem_filter.mp hx_dead).2
      ⟨hsd.2.2.1, hsd.2.2.2 hsd.2.2.1⟩,
    by rw [hst_eq, hres_eq, hhn_res, hdeadSet']; exact hcost_total⟩

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
