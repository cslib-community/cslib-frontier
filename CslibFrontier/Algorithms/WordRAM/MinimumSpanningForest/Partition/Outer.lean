/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.OuterRound
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Components
import CslibFrontier.Computability.WordRAM.Realization.LoopFrame

/-!
# Outer Loop and Top-Level `Partition` Specification

Steps toward Theorem 5.8 of [PettieRamachandran2002] (#8624), verifying the outer vertex-scan loop
(`partOuterStep` / `partRunOuterLoop`) using a pure `ℕ` amortized potential bound
(`iterate_potential_spec`), the remaining-edge loop (`partRunRemLoop`), and the full top-level
`partitionProg_spec` connecting `partSetup`, `partRunOuterLoop`, `partRunRemLoop`, and
`connectedComponentsProg` to the conglomerate-MSF and decision-tree depth guarantees in
`Partition.Bridges` (§3.1, p. 20; §3.2, pp. 21–22; §5.1, pp. 25–26).

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partitionProg_spec`: full specification of
  `partitionProg` establishing safety, framing below `s.frontier`, `O(m + n)` memory cost
  (`≤ 6000 * (m + n)`), `|M_C| ≤ m / 8`, edge-list partitioning, and the `PartitionRoundWitness`
  and conglomerate invariants consumed by `Partition.Bridges`.

## References

* [S. Pettie and V. Ramachandran, *An Optimal Minimum Spanning Tree
  Algorithm*][PettieRamachandran2002]
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest
open Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

private theorem list_take_sum_add_le {α : Type*} (f : α → ℕ) (xs : List α) (i : ℕ)
    (hi : i < xs.length) :
    ((xs.take i).map f).sum + f (xs[i]'hi) ≤ (xs.map f).sum := by
  induction xs generalizing i with
  | nil => cases hi
  | cons a rest ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      have := ih i' (by simpa using hi)
      omega

private structure OuterInvWitness {w n : ℕ} (L : PartLayout w n) (s₀ : Memory.State)
    (t : ℕ) (a : PartOuterState) (s : Memory.State) where
  rounds : List (PartitionRoundWitness n)
  emittedAll : List (Fin L.es.length)
  corrAll : List (Fin L.es.length)
  treeIndexedAll : List (IndexedEdge n)
  dead0 : ℕ → ℕ
  inCur0 : ℕ → ℕ
  edgeState0 : ℕ → ℕ
  ha_u : a.u = t
  ht_le : t ≤ n
  hrounds_len : rounds.length = a.numComps
  hfr : s.frontier = L.bufBase + (14 * n + 14 * L.es.length)
  hwf : Memory.WellFormed w s
  hmod : ∀ x, s.mem x ≠ s₀.mem x →
    InSHPool 0 0 (2 * L.es.length) (4 * L.es.length)
      ⟨L.itemBase, L.nodeBase, 0, 0, 0, partRankThreshold⟩ x ∨
    (L.bufBase ≤ x ∧ x < L.bufBase + (14 * n + 14 * L.es.length))
  hhib : a.sh.itemBase = L.itemBase
  hhnb : a.sh.nodeBase = L.nodeBase
  hhfr : a.sh.firstRoot = 0
  hhrt : a.sh.rankThreshold = partRankThreshold
  hhnc : a.sh.nodeCount ≤ 2 * a.sh.itemCount
  hsh : SHInv w a.sh.itemCount a.sh.nodeCount (2 * L.es.length) (4 * L.es.length) a.sh
    [] (fun _ => 0) s
  hdead_mem : ∀ x < n, s.mem (L.bufBase + x) = dead0 x
  hdead_cov : ∀ x < t, dead0 x ≠ 0
  hdead_iff : ∀ x : Fin n, dead0 x.val ≠ 0 ↔ ∃ r ∈ rounds, x ∈ r.verts
  hincur_mem : ∀ x < n, s.mem (L.bufBase + n + x) = inCur0 x
  hincur_le : ∀ x < n, inCur0 x ≤ a.numComps
  hedge_mem : ∀ i < L.es.length, s.mem (L.bufBase + 14 * n + i) = edgeState0 i
  hedge_vals : ∀ i : Fin L.es.length,
    (edgeState0 i.val = 1 ↔ i ∈ emittedAll) ∧
    (edgeState0 i.val = 2 ↔ i ∈ corrAll) ∧
    (edgeState0 i.val = 0 ∨ edgeState0 i.val = 1 ∨ edgeState0 i.val = 2)
  hem_nd : emittedAll.Nodup
  hcr_nd : corrAll.Nodup
  hdisj_ec : ∀ e, e ∈ emittedAll → e ∉ corrAll
  hcEdgeLen : a.cEdgeLen = (rounds.map fun r => r.compLocal.length).sum
  hcLiftLen : a.cLiftLen = (rounds.map PartitionRoundWitness.numVerts).sum
  hcl_dead : a.cLiftLen ≤
    (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)).card + a.numComps
  hnc_dead : a.numComps ≤ (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)).card
  hmcLen : a.mcLen = corrAll.length
  hmc_corr : corrAll.map (fun eIdx => L.es[eIdx.val]'eIdx.isLt) =
    rounds.flatMap PartitionRoundWitness.corrEdges
  hem_comp : emittedAll.map (fun eIdx => L.es[eIdx.val]'eIdx.isLt) =
    rounds.flatMap PartitionRoundWitness.compGlobal
  hmc_bound : 16 * a.mcLen ≤ a.sh.itemCount
  hmc_mem : HoldsIndexedEdges (L.bufBase + 14 * n + 6 * L.es.length)
    (rounds.flatMap PartitionRoundWitness.corrEdges) s.mem
  htLen : a.tLen = treeIndexedAll.length
  htLen_dead : a.tLen ≤ (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)).card
  htree_w : treeIndexedAll.map IndexedEdge.toWeighted =
    rounds.flatMap (fun r => r.tree.treeEdges)
  htree_mem : HoldsIndexedEdges (L.bufBase + 10 * n) treeIndexedAll s.mem
  hcap_rem : a.sh.itemCount + remDeg n L.offBase s.mem
    (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)) ≤ 2 * L.es.length
  hclaim_card : a.cEdgeLen + a.mcLen ≤
    (Finset.univ.filter (fun i : Fin L.es.length => edgeState0 i.val ≠ 0)).card
  hmeta : ∀ i (hi : i < rounds.length),
    let r := rounds[i]'hi
    let cEdgeBase := s.mem (L.bufBase + 6 * n + 3 * i + 2)
    let cLiftBase := s.mem (L.bufBase + 9 * n + i)
    s.mem (L.bufBase + 6 * n + 3 * i) = r.numVerts ∧
    s.mem (L.bufBase + 6 * n + 3 * i + 1) = r.compLocal.length ∧
    cEdgeBase = L.bufBase + 14 * n + 2 * L.es.length +
      4 * ((rounds.take i).map fun q => q.compLocal.length).sum ∧
    cLiftBase = L.bufBase + 4 * n +
      ((rounds.take i).map PartitionRoundWitness.numVerts).sum ∧
    HoldsIndexedEdges cEdgeBase r.compLocal s.mem ∧
    (∀ k : Fin r.numVerts, s.mem (cLiftBase + k.val) = (r.lift k).val) ∧
    r.verts.card = r.numVerts ∧ 1 ≤ r.numVerts ∧ r.numVerts ≤ L.maxsize ∧
    (1 ≤ r.compLocal.length → r.numVerts ≤ 2 * r.compLocal.length) ∧
    Function.Injective r.lift ∧
    IsSimple (edgeEnds (r.compLocal.map IndexedEdge.toWeighted)) ∧
    (∀ e ∈ r.compGlobal, e.u ∈ r.verts ∧ e.v ∈ r.verts) ∧
    r.tree.treeEdges.Subperm (r.compGlobal.map IndexedEdge.toWeighted) ∧
    (r.verts ∩ (Finset.univ.filter fun j : Fin rounds.length =>
      j.val < i).biUnion (fun j => (rounds[j.val]'j.isLt).verts)).card ≤ 1
  hstop : ∀ i : Fin rounds.length,
    L.maxsize ≤ (rounds[i.val]'i.isLt).verts.card ∨
    (∃ j : Fin rounds.length, j.val < i.val ∧
      ((rounds[i.val]'i.isLt).verts ∩ (rounds[j.val]'j.isLt).verts).Nonempty) ∨
    ((∀ j : Fin rounds.length, j ≠ i →
      ¬((rounds[i.val]'i.isLt).verts ∩ (rounds[j.val]'j.isLt).verts).Nonempty) ∧
      ∀ eIdx : Fin L.es.length, edgeState0 eIdx.val = 0 →
        (L.es[eIdx.val]'eIdx.isLt).u ∉ (rounds[i.val]'i.isLt).verts ∧
        (L.es[eIdx.val]'eIdx.isLt).v ∉ (rounds[i.val]'i.isLt).verts)
  huncorr : ∀ i : Fin rounds.length, ∀ eIdx : Fin L.es.length, edgeState0 eIdx.val = 0 →
    ¬((L.es[eIdx.val]'eIdx.isLt).u ∈ (rounds[i.val]'i.isLt).verts ∧
      (L.es[eIdx.val]'eIdx.isLt).v ∈ (rounds[i.val]'i.isLt).verts) ∧
    ∀ s_step : Fin (rounds[i.val]'i.isLt).tree.numSteps,
      ((L.es[eIdx.val]'eIdx.isLt).u ∈ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val ↔
        (L.es[eIdx.val]'eIdx.isLt).v ∉ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val) →
      (rounds[i.val]'i.isLt).tree.wPop s_step ≤ (L.es[eIdx.val]'eIdx.isLt).weight
  hstop_prev : ∀ i : Fin rounds.length, ∀ x ∈ (rounds[i.val]'i.isLt).verts,
    x ∈ (Finset.univ.filter fun j : Fin rounds.length =>
      j.val < i.val).biUnion (fun j => (rounds[j.val]'j.isLt).verts) →
    ∃ hpos : 0 < (rounds[i.val]'i.isLt).tree.numSteps,
      x = (rounds[i.val]'i.isLt).tree.vOut
        ⟨(rounds[i.val]'i.isLt).tree.numSteps - 1, Nat.sub_lt hpos Nat.one_pos⟩
  huncorr_tree : ∀ i j : Fin rounds.length, i.val < j.val →
    ∀ e ∈ (rounds[j.val]'j.isLt).tree.treeEdges,
      ¬(e.u ∈ (rounds[i.val]'i.isLt).verts ∧ e.v ∈ (rounds[i.val]'i.isLt).verts) ∧
      ∀ s_step : Fin (rounds[i.val]'i.isLt).tree.numSteps,
        (e.u ∈ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val ↔
          e.v ∉ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val) →
        (rounds[i.val]'i.isLt).tree.wPop s_step ≤ e.weight

private def outerPotFn {w n : ℕ} (L : PartLayout w n) (_k : ℕ) (a : PartOuterState)
    (s : Memory.State) : ℕ :=
  let deadSet := Finset.univ.filter (fun x : Fin n => s.mem (L.bufBase + x.val) ≠ 0)
  2465 * remDeg n L.offBase s.mem deadSet +
    295 * (2 * L.es.length - a.sh.itemCount) +
    6 * (2 * n - a.cLiftLen)

private theorem outerInv_agree_below_itemBase {w n : ℕ} {L : PartLayout w n}
    {s₀ : Memory.State} {t : ℕ} {a : PartOuterState} {s : Memory.State}
    (W : OuterInvWitness L s₀ t a s) : ∀ x < L.itemBase, s.mem x = s₀.mem x := fun x hx => by
  by_contra hne
  rcases W.hmod x hne with hp | h
  · exact absurd (L.inSHPool_lt_bufBase rfl rfl hp) (by omega)
  · have := L.hadj_it; have := L.hit_nd; have := L.hnd_buf; omega

private theorem outerInv_csr {w n : ℕ} {L : PartLayout w n} {s₀ : Memory.State}
    {t : ℕ} {a : PartOuterState} {s : Memory.State} (W : OuterInvWitness L s₀ t a s)
    (hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem) :
    HoldsUndirCSR L.offBase L.adjBase L.es s.mem :=
  (L.congr_below_itemBase (outerInv_agree_below_itemBase W)).2 hcsr₀

private theorem outerInv_edges {w n : ℕ} {L : PartLayout w n} {s₀ : Memory.State}
    {t : ℕ} {a : PartOuterState} {s : Memory.State} (W : OuterInvWitness L s₀ t a s)
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem) :
    HoldsIndexedEdges L.edgeBase L.es s.mem :=
  (L.congr_below_itemBase (outerInv_agree_below_itemBase W)).1 hin₀

private theorem partOuterStep_spec {w n : ℕ} (L : PartLayout w n) (s₀ : Memory.State)
    (hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem)
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem)
    (hsimp_g : IsSimple (edgeEnds (L.es.map IndexedEdge.toWeighted)))
    (t : ℕ) (ht : t < n) (a : PartOuterState) (s : Memory.State)
    (W : OuterInvWitness L s₀ t a s) :
    let m := L.es.length
    let env := L.toEnv
    let prog := partOuterStep (env, a)
    let a' := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    partOuterStepSafe w (env, a) s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    (∀ x, ¬(InSHPool 0 0 (2 * m) (4 * m)
        ⟨L.itemBase, L.nodeBase, 0, 0, 0, partRankThreshold⟩ x ∨
      (L.bufBase ≤ x ∧ x < L.bufBase + (14 * n + 14 * m))) → s'.mem x = s.mem x) ∧
    Nonempty (OuterInvWitness L s₀ (t + 1) a' s') ∧
      memoryCost prog s + outerPotFn L (t + 1) a' s' ≤ outerPotFn L t a s + 20 := by
  let m := L.es.length
  let env := L.toEnv
  let deadSet : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => W.dead0 x.val ≠ 0)
  have h16 := L.h16
  have hn_pos := L.hn_pos
  have ha1 : a.u = t := W.ha_u
  have hdead_lt : L.bufBase + a.u < s.frontier := by rw [W.hfr, ha1]; omega
  have ha1_fit : Fits w (a.u + 1) := L.hfit_end.of_le (by omega)
  have hdead_t : s.mem (L.bufBase + a.u) = W.dead0 t := ha1 ▸ W.hdead_mem t ht
  have hprog : partOuterStep (env, a) =
      (Memory.read (L.bufBase + a.u) >>= fun d =>
        if d ≠ 0 then
          pure ⟨a.u + 1, a.numComps, a.cEdgeLen, a.cLiftLen, a.mcLen, a.tLen, a.sh⟩
        else partRunRound (env, a)) := partOuterStep_def (env, a)
  by_cases hd0 : W.dead0 t = 0
  · have hcsr := outerInv_csr W hcsr₀
    have hin := outerInv_edges W hin₀
    have hrun := partRunRound_spec L s W.dead0 W.inCur0 W.edgeState0 a.numComps a.cEdgeLen
      a.cLiftLen a.mcLen a.tLen ⟨t, ht⟩ a.sh W.hfr W.hhib W.hhnb W.hhrt W.hhnc W.hsh
      hcsr hin W.hdead_mem W.hincur_mem W.hincur_le hd0 W.hedge_mem hsimp_g
      W.hnc_dead W.htLen_dead W.hcl_dead W.hclaim_card W.hcap_rem
    dsimp only at hrun
    have ha_eta : (⟨t, a.numComps, a.cEdgeLen, a.cLiftLen, a.mcLen, a.tLen, a.sh⟩ :
        PartOuterState) = a := by
      cases a; simpa using ha1.symm
    rw [ha_eta] at hrun
    generalize h_a' : (Memory.spec 0).clientResult s (partRunRound (L.toEnv, a)) = a' at hrun
    generalize h_s' : (Memory.spec 0).clientState s (partRunRound (L.toEnv, a)) = s' at hrun
    rcases hrun with ⟨hsafe_r, hvh_r, ha'1, ha'21, ha'ce, ha'mc, hs'_fr, hwf', hmod_r,
      hib', hnb', hfr', hrt', hic_ge', hnc', hsh', hmc_diff', hclaim',
      r, emittedIdx, corrEmitted, treeIndexed, hl_eq, htl_eq, htr_len, htr_w, htr_src, htr_mem,
      hnd_em, hnd_cr, hdisj_ec, hcp_len, hcr_len, hcr_eq, hcp_mem, hcg_eq, hcr_mem, hlifts,
      hm0, hm1, hm2, hm3, hr_root, hu_in_r, hr_card, hnv_pos, hnv_max, hnv_2c,
      hlift_inj, hcp_simp,
      hcg_verts, htr_sub, hdead_fn, hincur_in, hincur_out, hest_fn, hemit_iff, hcr_es0,
      htlen_dead', hcl_dead', hnc_dead', hcap_rem', hdead_inter, hstop_r, huncorr_r,
      hstop_prev_r, hcost_r⟩
    have hsafe : partOuterStepSafe w (env, a) s := by
      rw [partOuterStepSafe_def]
      exact ⟨h16, ha1_fit, hdead_lt, fun _ => hsafe_r⟩
    have hvh : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (partOuterStep (env, a))) := by
      rw [hprog]; refine validHistory_read_bind hdead_lt ?_
      rw [hdead_t, hd0]; simp only [ne_eq, not_true_eq_false, ↓reduceIte]; exact hvh_r
    have ha'_eq : (Memory.spec 0).clientResult s (partOuterStep (env, a)) = a' := by
      rw [hprog, clientResult_bind_read, hdead_t, hd0]
      simp only [ne_eq, not_true_eq_false, ↓reduceIte]; exact h_a'
    have hs'_eq : (Memory.spec 0).clientState s (partOuterStep (env, a)) = s' := by
      rw [hprog, clientState_bind_read, hdead_t, hd0]
      simp only [ne_eq, not_true_eq_false, ↓reduceIte]; exact h_s'
    have hcost_eq : memoryCost (partOuterStep (env, a)) s =
        1 + memoryCost (partRunRound (L.toEnv, a)) s := by
      rw [hprog, memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        hdead_t, hd0]
      simp only [ne_eq, not_true_eq_false, ↓reduceIte]; rfl
    have hdead_card_le : (Finset.univ.filter (fun x : Fin n =>
        s'.mem (L.bufBase + x.val) ≠ 0)).card ≤ n := by
      have hc := Finset.card_le_univ
        (Finset.univ.filter fun x : Fin n => s'.mem (L.bufBase + x.val) ≠ 0)
      simpa [Fintype.card_fin] using hc
    have hm_card_le : a'.cEdgeLen + a'.mcLen ≤ m := by
      have hfc := Finset.card_le_univ
        (Finset.univ.filter fun i : Fin m => s'.mem (L.bufBase + 14 * n + i.val) ≠ 0)
      rw [Fintype.card_fin] at hfc; dsimp only [m] at hfc ⊢; exact hclaim'.trans hfc
    have hcl_le_2n : a'.cLiftLen ≤ 2 * n := by omega
    have htl_le_n : a'.tLen ≤ n := by omega
    have hmod_step : ∀ x, ¬(InSHPool 0 0 (2 * m) (4 * m)
        ⟨L.itemBase, L.nodeBase, 0, 0, 0, partRankThreshold⟩ x ∨
        (L.bufBase ≤ x ∧ x < L.bufBase + (14 * n + 14 * m))) → s'.mem x = s.mem x := by
      intro x hx; by_contra hne
      rcases hmod_r x hne with h | h | h | h | h | h | h | h | h
      · exact hx (.inl h)
      · exact hx (.inr (by omega))
      · exact hx (.inr (by omega))
      · exact hx (.inr (by omega))
      · exact hx (.inr (by omega))
      · exact hx (.inr (by omega))
      · exact hx (.inr (by omega))
      · exact hx (.inr (by omega))
      · exact hx (.inr (by omega))
    have h_s'_agree : ∀ x,
        ((L.bufBase + 4 * n ≤ x ∧ x < L.bufBase + 4 * n + a.cLiftLen) ∨
         (L.bufBase + 6 * n ≤ x ∧ x < L.bufBase + 6 * n + 3 * a.numComps) ∨
         (L.bufBase + 9 * n ≤ x ∧ x < L.bufBase + 9 * n + a.numComps) ∨
         (L.bufBase + 10 * n ≤ x ∧ x < L.bufBase + 10 * n + 4 * a.tLen) ∨
         (L.bufBase + 14 * n + 2 * m ≤ x ∧ x < L.bufBase + 14 * n + 2 * m + 4 * a.cEdgeLen) ∨
         (L.bufBase + 14 * n + 6 * m ≤ x ∧ x < L.bufBase + 14 * n + 6 * m + 4 * a.mcLen)) →
        s'.mem x = s.mem x := by
      intro x hx; by_contra hne
      have hx_lo : L.bufBase + 4 * n ≤ x := by rcases hx with h | h | h | h | h | h <;> omega
      rcases hmod_r x hne with hp | h | h | h | h | h | h | h | h
      · rcases PartLayout.inSHPool_bounds hp with ⟨_, _⟩ | ⟨_, _⟩ <;> dsimp only at * <;>
          have := L.hit_nd <;> have := L.hnd_buf <;> omega
      · omega
      · rcases hx with h1 | h1 | h1 | h1 | h1 | h1 <;> omega
      · rcases hx with h1 | h1 | h1 | h1 | h1 | h1 <;> omega
      · rcases hx with h1 | h1 | h1 | h1 | h1 | h1 <;> omega
      · rcases hx with h1 | h1 | h1 | h1 | h1 | h1 <;> omega
      · rcases hx with h1 | h1 | h1 | h1 | h1 | h1 <;> omega
      · rcases hx with h1 | h1 | h1 | h1 | h1 | h1 <;> omega
      · rcases hx with h1 | h1 | h1 | h1 | h1 | h1 <;> omega
    let dead1 : ℕ → ℕ := fun x =>
      if hlt : x < n then if (⟨x, hlt⟩ : Fin n) ∈ r.verts then 1 else W.dead0 x else 0
    let inCur1 : ℕ → ℕ := fun x =>
      if hlt : x < n then if (⟨x, hlt⟩ : Fin n) ∈ r.verts then a.numComps + 1 else W.inCur0 x
      else 0
    let edgeState1 : ℕ → ℕ := fun i =>
      if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ emittedIdx then 1
      else if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ corrEmitted then 2
      else W.edgeState0 i
    have hed1_imp_0 : ∀ i, edgeState1 i = 0 → W.edgeState0 i = 0 := fun i hi => by
      dsimp only [edgeState1] at hi; split_ifs at hi; exact hi
    have hdeadSet1 : Finset.univ.filter (fun x : Fin n => dead1 x.val ≠ 0) =
        Finset.univ.filter (fun x : Fin n => s'.mem (L.bufBase + x.val) ≠ 0) := by
      ext x; simp [dead1, hdead_fn x]
    have hem_disj_all : ∀ e ∈ W.emittedAll, e ∉ emittedIdx := fun e he_all he_em => by
      have h1 := ((W.hedge_vals e).1).mpr he_all
      have h0 := ((hemit_iff e).mp he_em).1; omega
    have hcr_disj_all : ∀ e ∈ W.corrAll, e ∉ corrEmitted := fun e he_all he_cr => by
      have h2 := ((W.hedge_vals e).2.1).mpr he_all
      have h0 := hcr_es0 e he_cr; omega
    have hmc_len_all : (W.rounds.flatMap PartitionRoundWitness.corrEdges).length = a.mcLen := by
      have := congrArg List.length W.hmc_corr
      simpa [W.hmcLen] using this.symm
    have hdisj_of_noedge : ∀ V : Finset (Fin n),
        (⟨t, ht⟩ ∉ V) →
        (∀ eIdx : Fin m, W.edgeState0 eIdx.val = 0 →
          (L.es[eIdx.val]'eIdx.isLt).u ∉ V ∧ (L.es[eIdx.val]'eIdx.isLt).v ∉ V) →
        ¬(V ∩ r.verts).Nonempty := fun V hu_notV he_notV ⟨x, hx⟩ => by
      rw [Finset.mem_inter] at hx
      have hmem := (mem_djpVertsList_iff r.tree x).mpr hx.2
      obtain ⟨k, hk_lt, hkx⟩ := List.getElem_of_mem hmem
      rcases k with _ | k'
      · have h0 : (djpVertsList r.tree)[0]'hk_lt = r.tree.root := by simp [djpVertsList]
        rw [h0, hr_root] at hkx; subst hkx; exact hu_notV hx.1
      · let s_step : Fin r.tree.numSteps := ⟨k', by rw [djpVertsList_length] at hk_lt; omega⟩
        have hk_eq : (djpVertsList r.tree)[k' + 1]'hk_lt = r.tree.vOut s_step :=
          djpVertsList_getElem_succ r.tree s_step
        rw [hk_eq] at hkx
        have hmem_tr : r.tree.edge s_step ∈ r.tree.treeEdges := by
          dsimp only [DynamicDJPTree.treeEdges]
          exact List.mem_map.mpr ⟨s_step, List.mem_finRange _, rfl⟩
        rw [← htr_w, List.mem_map] at hmem_tr
        obtain ⟨ei, hei, hei_w⟩ := hmem_tr
        obtain ⟨eIdx, hei_eq, he0⟩ := htr_src ei hei
        have hno := he_notV eIdx he0
        rcases r.tree.ends_match s_step with ⟨_, hv⟩ | ⟨_, hu⟩
        · have hv' : (r.tree.edge s_step).v = r.tree.vOut s_step := hv
          rw [← hei_w, hei_eq] at hv'; dsimp only [IndexedEdge.toWeighted] at hv'
          exact hno.2 (by rw [hv', hkx]; exact hx.1)
        · have hu' : (r.tree.edge s_step).u = r.tree.vOut s_step := hu
          rw [← hei_w, hei_eq] at hu'; dsimp only [IndexedEdge.toWeighted] at hu'
          exact hno.1 (by rw [hu', hkx]; exact hx.1)
    have W' : OuterInvWitness L s₀ (t + 1) a' s' :=
      { rounds := W.rounds ++ [r]
        emittedAll := W.emittedAll ++ emittedIdx
        corrAll := W.corrAll ++ corrEmitted
        treeIndexedAll := W.treeIndexedAll ++ treeIndexed
        dead0 := dead1
        inCur0 := inCur1
        edgeState0 := edgeState1
        ha_u := ha'1
        ht_le := ht
        hrounds_len := by simp [W.hrounds_len, ha'21]
        hfr := hs'_fr.trans W.hfr
        hwf := hwf'
        hmod := fun x hne => by
          by_cases hxs : s'.mem x = s.mem x
          · exact W.hmod x (hxs ▸ hne)
          · by_contra hn; exact hxs (hmod_step x hn)
        hhib := hib'
        hhnb := hnb'
        hhfr := hfr'
        hhrt := hrt'
        hhnc := hnc'
        hsh := hsh'
        hdead_mem := fun x hx => by simpa [dead1, hx] using hdead_fn ⟨x, hx⟩
        hdead_cov := fun x hx => by
          dsimp only [dead1]
          rw [dite_eq_left_of_eq_true (eq_true (by omega))]
          split_ifs with hr
          · exact Nat.one_ne_zero
          · by_cases hxt : x < t
            · exact W.hdead_cov x hxt
            · have hxt_eq : x = t := by omega
              subst hxt_eq; exact absurd hu_in_r hr
        hdead_iff := fun x => by
          simp only [dead1, x.isLt, ↓reduceDIte, List.mem_append, List.mem_singleton]
          split_ifs with hx
          · simp only [ne_eq, one_ne_zero, not_false_eq_true, true_iff]
            exact ⟨r, .inr rfl, hx⟩
          · rw [W.hdead_iff x]
            constructor
            · rintro ⟨q, hq, hqx⟩; exact ⟨q, .inl hq, hqx⟩
            · rintro ⟨q, hq | rfl, hqx⟩
              · exact ⟨q, hq, hqx⟩
              · exact absurd hqx hx
        hincur_mem := fun x hx => by
          dsimp only [inCur1]; rw [dite_eq_left_of_eq_true (eq_true hx)]
          split_ifs with hr
          · exact hincur_in ⟨x, hx⟩ hr
          · exact hincur_out ⟨x, hx⟩ hr
        hincur_le := fun x hx => by
          dsimp only [inCur1]; rw [dite_eq_left_of_eq_true (eq_true hx), ha'21]
          split_ifs
          · exact le_rfl
          · exact (W.hincur_le x hx).trans (Nat.le_succ _)
        hedge_mem := hest_fn
        hedge_vals := fun i => by
          dsimp only [edgeState1]
          have hvi := W.hedge_vals i
          have hem_e : (∃ hlt : i.val < m, (⟨i.val, hlt⟩ : Fin m) ∈ emittedIdx) ↔
              i ∈ emittedIdx := ⟨fun ⟨_, h⟩ => h, fun h => ⟨i.isLt, h⟩⟩
          have hcr_e : (∃ hlt : i.val < m, (⟨i.val, hlt⟩ : Fin m) ∈ corrEmitted) ↔
              i ∈ corrEmitted := ⟨fun ⟨_, h⟩ => h, fun h => ⟨i.isLt, h⟩⟩
          refine ⟨?_, ?_, ?_⟩
          · simp only [List.mem_append, hem_e, hcr_e]
            split_ifs with h1 h2
            · simp [h1]
            · refine ⟨fun h => by omega, fun h => ?_⟩
              rcases h with ha | hb
              · exfalso; have := hvi.1.mpr ha; have := hcr_es0 i h2; omega
              · exact absurd hb h1
            · rw [hvi.1]; simp [h1]
          · simp only [List.mem_append, hem_e, hcr_e]
            split_ifs with h1 h2
            · refine ⟨fun h => by omega, fun h => ?_⟩
              rcases h with ha | hb
              · have h2 := (hvi.2.1).mpr ha; have h0 := ((hemit_iff i).mp h1).1; omega
              · exact absurd h1 (fun h_em => hdisj_ec i h_em hb)
            · simp [h2]
            · rw [hvi.2.1]; simp [h2]
          · split_ifs
            · exact .inr (.inl rfl)
            · exact .inr (.inr rfl)
            · exact hvi.2.2
        hem_nd := List.nodup_append.mpr ⟨W.hem_nd, hnd_em, fun e he1 e' he2 heq =>
          hem_disj_all e he1 (heq ▸ he2)⟩
        hcr_nd := List.nodup_append.mpr ⟨W.hcr_nd, hnd_cr, fun e he1 e' he2 heq =>
          hcr_disj_all e he1 (heq ▸ he2)⟩
        hdisj_ec := fun e he => by
          simp only [List.mem_append] at he ⊢
          rintro (h1 | h2)
          · rcases he with ha | hb
            · exact W.hdisj_ec e ha h1
            · have := ((W.hedge_vals e).2.1).mpr h1; have := ((hemit_iff e).mp hb).1; omega
          · rcases he with ha | hb
            · have := ((W.hedge_vals e).1).mpr ha; have := hcr_es0 e h2; omega
            · exact hdisj_ec e hb h2
        hcEdgeLen := by
          simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_cons,
            List.sum_nil, add_zero, ← W.hcEdgeLen]; omega
        hcLiftLen := by
          simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_cons,
            List.sum_nil, add_zero, ← W.hcLiftLen]; exact hl_eq
        hcl_dead := by rw [hdeadSet1, ha'21]; exact hcl_dead'
        hnc_dead := by rw [hdeadSet1, ha'21]; exact hnc_dead'
        hmcLen := by simp only [List.length_append, ← W.hmcLen, hcr_len]; omega
        hmc_corr := by
          simp only [List.map_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, W.hmc_corr, hcr_eq]
        hem_comp := by
          simp only [List.map_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, W.hem_comp, hcg_eq]
        hmc_bound := by have := W.hmc_bound; omega
        hmc_mem := by
          simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          refine holdsIndexedEdges_append ?_ (by rw [hmc_len_all]; exact hcr_mem)
          refine W.hmc_mem.congr fun x hx1 hx2 => h_s'_agree x ?_
          rw [hmc_len_all] at hx2; exact .inr (.inr (.inr (.inr (.inr ⟨hx1, hx2⟩))))
        htLen := by simp only [List.length_append, ← W.htLen, htl_eq]
        htLen_dead := hdeadSet1 ▸ htlen_dead'
        htree_w := by
          simp only [List.map_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, W.htree_w, htr_w]
        htree_mem := by
          refine holdsIndexedEdges_append ?_ (by rw [← W.htLen]; exact htr_mem)
          refine W.htree_mem.congr fun x hx1 hx2 => h_s'_agree x ?_
          rw [← W.htLen] at hx2; exact .inr (.inr (.inr (.inl ⟨hx1, hx2⟩)))
        hcap_rem := hdeadSet1 ▸ hcap_rem'
        hclaim_card := by
          have heq_f : Finset.univ.filter (fun i : Fin m => edgeState1 i.val ≠ 0) =
              Finset.univ.filter (fun i : Fin m => s'.mem (L.bufBase + 14 * n + i.val) ≠ 0) := by
            ext i; have hi : i.val < L.es.length := i.isLt
            simp [edgeState1, m, hest_fn i.val hi, hi]
          rw [heq_f]; exact hclaim'
        hmeta := fun i hi => by
          by_cases hi_old : i < W.rounds.length
          · have hmeta_old := W.hmeta i hi_old
            have hget : (W.rounds ++ [r])[i]'hi = W.rounds[i]'hi_old :=
              List.getElem_append_left hi_old
            have htake : (W.rounds ++ [r]).take i = W.rounds.take i :=
              List.take_append_of_le_length hi_old.le
            have hi_a : i < a.numComps := W.hrounds_len ▸ hi_old
            have hce_sum : ((W.rounds.take i).map fun q => q.compLocal.length).sum +
                (W.rounds[i]'hi_old).compLocal.length ≤ a.cEdgeLen := by
              rw [W.hcEdgeLen]
              exact list_take_sum_add_le (fun q => q.compLocal.length) W.rounds i hi_old
            have hcl_sum : ((W.rounds.take i).map PartitionRoundWitness.numVerts).sum +
                (W.rounds[i]'hi_old).numVerts ≤ a.cLiftLen := by
              rw [W.hcLiftLen]
              exact list_take_sum_add_le PartitionRoundWitness.numVerts W.rounds i hi_old
            have hs_c0 : s'.mem (L.bufBase + 6 * n + 3 * i) =
                s.mem (L.bufBase + 6 * n + 3 * i) :=
              h_s'_agree _ (.inr (.inl ⟨by omega, by omega⟩))
            have hs_c1 : s'.mem (L.bufBase + 6 * n + 3 * i + 1) =
                s.mem (L.bufBase + 6 * n + 3 * i + 1) :=
              h_s'_agree _ (.inr (.inl ⟨by omega, by omega⟩))
            have hs_c2 : s'.mem (L.bufBase + 6 * n + 3 * i + 2) =
                s.mem (L.bufBase + 6 * n + 3 * i + 2) :=
              h_s'_agree _ (.inr (.inl ⟨by omega, by omega⟩))
            have hs_cl : s'.mem (L.bufBase + 9 * n + i) = s.mem (L.bufBase + 9 * n + i) :=
              h_s'_agree _ (.inr (.inr (.inl ⟨by omega, by omega⟩)))
            dsimp only
            rw [hget, htake, hs_c0, hs_c1, hs_c2, hs_cl]
            rcases hmeta_old with ⟨hm_0, hm_1, hm_2, hm_3, hm_ce, hm_cl, hm_vc,
              hm_p1, hm_p2, hm_p3, hm_inj, hm_sp, hm_gv, hm_ts, hm_bi⟩
            refine ⟨hm_0, hm_1, hm_2, hm_3, ?_, fun k => ?_, hm_vc,
              hm_p1, hm_p2, hm_p3, hm_inj, hm_sp, hm_gv, hm_ts, ?_⟩
            · refine hm_ce.congr fun x hx1 hx2 => h_s'_agree x ?_
              rw [hm_2] at hx1 hx2; exact .inr (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩))))
            · have hk := k.isLt
              have hs_lk : s'.mem (s.mem (L.bufBase + 9 * n + i) + k.val) =
                  s.mem (s.mem (L.bufBase + 9 * n + i) + k.val) := by
                rw [hm_3]; exact h_s'_agree _ (.inl ⟨by omega, by omega⟩)
              exact hs_lk.trans (hm_cl k)
            · have hbi_eq : (Finset.univ.filter fun j : Fin (W.rounds ++ [r]).length =>
                  j.val < i).biUnion (fun j => ((W.rounds ++ [r])[j.val]'j.isLt).verts) =
                  (Finset.univ.filter fun j : Fin W.rounds.length =>
                  j.val < i).biUnion (fun j => (W.rounds[j.val]'j.isLt).verts) := by
                ext x
                simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · rintro ⟨j, hj, hxj⟩
                  have hj' : j.val < W.rounds.length := by omega
                  refine ⟨⟨j.val, hj'⟩, hj, ?_⟩; rwa [List.getElem_append_left hj'] at hxj
                · rintro ⟨j, hj, hxj⟩
                  have hj' : j.val < (W.rounds ++ [r]).length := by simp
                  refine ⟨⟨j.val, hj'⟩, hj, ?_⟩; rwa [List.getElem_append_left j.isLt]
              rw [hbi_eq]; exact hm_bi
          · have hi_eq : i = W.rounds.length := by simp at hi; omega
            subst hi_eq
            have hget : (W.rounds ++ [r])[W.rounds.length]'hi = r := by simp
            have htake : (W.rounds ++ [r]).take W.rounds.length = W.rounds := by simp
            dsimp only
            rw [hget, htake, W.hrounds_len, hm0, hm1, hm2, hm3, ← W.hcEdgeLen, ← W.hcLiftLen]
            refine ⟨rfl, rfl, rfl, rfl, hcp_mem, hlifts, hr_card, hnv_pos, hnv_max, hnv_2c,
              hlift_inj, hcp_simp, hcg_verts, htr_sub, ?_⟩
            have hbi_eq : (Finset.univ.filter fun j : Fin (W.rounds ++ [r]).length =>
                j.val < W.rounds.length).biUnion
                (fun j => ((W.rounds ++ [r])[j.val]'j.isLt).verts) = deadSet := by
              ext x
              simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, deadSet,
                W.hdead_iff]
              constructor
              · rintro ⟨j, hj, hxj⟩
                exact ⟨W.rounds[j.val]'hj, List.getElem_mem _, by
                  rwa [List.getElem_append_left hj] at hxj⟩
              · rintro ⟨q, hq, hxq⟩
                obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
                exact ⟨⟨j, by simp; omega⟩, hj, by rwa [List.getElem_append_left hj]⟩
            rw [← W.hrounds_len, hbi_eq]; exact hdead_inter
        hstop := fun i => by
          by_cases hi_old : i.val < W.rounds.length
          · have hget : (W.rounds ++ [r])[i.val]'i.isLt = W.rounds[i.val]'hi_old :=
              List.getElem_append_left hi_old
            rcases W.hstop ⟨i.val, hi_old⟩ with h1 | ⟨j, hj1, hj2⟩ | ⟨hisol, hed⟩
            · exact .inl (by simpa [hget] using h1)
            · have hj_lt : j.val < (W.rounds ++ [r]).length := by
                simp only [List.length_append, List.length_singleton]; have := j.isLt; omega
              refine .inr (.inl ⟨⟨j.val, hj_lt⟩, hj1, ?_⟩)
              simpa [hget, List.getElem_append_left j.isLt] using hj2
            · refine .inr (.inr ⟨fun j hne => ?_, fun eIdx he1 => by
                rw [hget]; exact hed eIdx (hed1_imp_0 eIdx.val he1)⟩)
              by_cases hj_old : j.val < W.rounds.length
              · have hne' : (⟨j.val, hj_old⟩ : Fin W.rounds.length) ≠ ⟨i.val, hi_old⟩ :=
                  fun h => hne (Fin.ext (congrArg (Fin.val : Fin W.rounds.length → ℕ) h))
                simpa [hget, List.getElem_append_left hj_old] using
                  hisol ⟨j.val, hj_old⟩ hne'
              · have hj_eq : j.val = W.rounds.length := by have := j.isLt; simp at *; omega
                have hget_j : (W.rounds ++ [r])[j.val]'j.isLt = r := by simp [hj_eq]
                rw [hget, hget_j]
                refine hdisj_of_noedge _ ?_ hed
                intro huV
                exact absurd ((W.hdead_iff ⟨t, ht⟩).mpr
                  ⟨W.rounds[i.val]'hi_old, List.getElem_mem _, huV⟩) (not_not.mpr hd0)
          · have hi_eq : i.val = W.rounds.length := by have := i.isLt; simp at *; omega
            have hget : (W.rounds ++ [r])[i.val]'i.isLt = r := by simp [hi_eq]
            by_cases hnon : (r.verts ∩ deadSet).Nonempty
            · obtain ⟨x, hx⟩ := hnon
              rw [Finset.mem_inter, Finset.mem_filter] at hx
              obtain ⟨q, hq, hxq⟩ := (W.hdead_iff x).mp hx.2.2
              obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
              refine .inr (.inl ⟨⟨j,
                by simp only [List.length_append, List.length_singleton]; omega⟩,
                by rw [hi_eq]; exact hj, ⟨x, ?_⟩⟩)
              rw [Finset.mem_inter, hget, List.getElem_append_left hj]; exact ⟨hx.1, hxq⟩
            · rcases hstop_r with hsz | hnon2 | hem
              · exact .inl (by simpa [hget] using hsz)
              · exact absurd hnon2 hnon
              · refine .inr (.inr ⟨fun j hne => ?_, fun eIdx he1 => ?_⟩)
                · have hj_old : j.val < W.rounds.length := by
                    have := j.isLt; simp only [List.length_append, List.length_singleton] at this
                    have : j.val ≠ i.val := fun h => hne (Fin.ext h)
                    omega
                  have hget_j : (W.rounds ++ [r])[j.val]'j.isLt = W.rounds[j.val]'hj_old :=
                    List.getElem_append_left hj_old
                  rw [hget, hget_j]
                  intro ⟨x, hx⟩
                  rw [Finset.mem_inter] at hx
                  exact hnon ⟨x, Finset.mem_inter.mpr ⟨hx.1, Finset.mem_filter.mpr
                    ⟨Finset.mem_univ _, (W.hdead_iff x).mpr
                      ⟨W.rounds[j.val]'hj_old, List.getElem_mem _, hx.2⟩⟩⟩⟩
                · have he0 := hed1_imp_0 eIdx.val he1
                  have hne_em : eIdx ∉ emittedIdx := fun h => by
                    dsimp only [edgeState1] at he1
                    have hm : ∃ hlt : eIdx.val < m, (⟨eIdx.val, hlt⟩ : Fin m) ∈ emittedIdx :=
                      ⟨eIdx.isLt, h⟩
                    simp only [hm, ↓reduceIte] at he1; omega
                  have hnot_int : ¬((L.es[eIdx.val]'eIdx.isLt).u ∈ r.verts ∧
                      (L.es[eIdx.val]'eIdx.isLt).v ∈ r.verts) := fun ⟨hu, hv⟩ =>
                    hne_em ((hemit_iff eIdx).mpr ⟨he0, hu, hv⟩)
                  have hiff := hem eIdx he0
                  rw [hget]
                  constructor
                  · intro hu
                    have hv : (L.es[eIdx.val]'eIdx.isLt).v ∈ r.verts := by
                      by_contra hnv; exact hiff (by simp [hu, hnv])
                    exact hnot_int ⟨hu, hv⟩
                  · intro hv
                    have hu : (L.es[eIdx.val]'eIdx.isLt).u ∈ r.verts := by
                      by_contra hnu; exact hiff (by simp [hnu, hv])
                    exact hnot_int ⟨hu, hv⟩
        huncorr := fun i eIdx he1 => by
          have he0 := hed1_imp_0 eIdx.val he1
          by_cases hi_old : i.val < W.rounds.length
          · have hget : (W.rounds ++ [r])[i.val]'i.isLt = W.rounds[i.val]'hi_old :=
              List.getElem_append_left hi_old
            rw [hget]; exact W.huncorr ⟨i.val, hi_old⟩ eIdx he0
          · have hi_eq : i.val = W.rounds.length := by have := i.isLt; simp at *; omega
            have hget : (W.rounds ++ [r])[i.val]'i.isLt = r := by simp [hi_eq]
            have hne_em : eIdx ∉ emittedIdx := fun h => by
              dsimp only [edgeState1] at he1
              have hm : ∃ hlt : eIdx.val < m, (⟨eIdx.val, hlt⟩ : Fin m) ∈ emittedIdx :=
                ⟨eIdx.isLt, h⟩
              simp only [hm, ↓reduceIte] at he1; omega
            have hne_cr : eIdx ∉ corrEmitted := fun h => by
              dsimp only [edgeState1] at he1
              have hno : ¬∃ hlt : eIdx.val < m, (⟨eIdx.val, hlt⟩ : Fin m) ∈ emittedIdx :=
                by rintro ⟨_, hm⟩; exact hne_em hm
              have hm : ∃ hlt : eIdx.val < m, (⟨eIdx.val, hlt⟩ : Fin m) ∈ corrEmitted :=
                ⟨eIdx.isLt, h⟩
              simp only [hno, hm, ↓reduceIte] at he1; omega
            rw [hget]
            exact ⟨fun ⟨hu, hv⟩ => hne_em ((hemit_iff eIdx).mpr ⟨he0, hu, hv⟩),
              huncorr_r eIdx he0 hne_em hne_cr⟩
        hstop_prev := fun i x hx hx_prev => by
          by_cases hi_old : i.val < W.rounds.length
          · have hget : (W.rounds ++ [r])[i.val]'i.isLt = W.rounds[i.val]'hi_old :=
              List.getElem_append_left hi_old
            have hbi_eq : (Finset.univ.filter fun j : Fin (W.rounds ++ [r]).length =>
                  j.val < i.val).biUnion (fun j => ((W.rounds ++ [r])[j.val]'j.isLt).verts) =
                (Finset.univ.filter fun j : Fin W.rounds.length =>
                  j.val < i.val).biUnion (fun j => (W.rounds[j.val]'j.isLt).verts) := by
              ext y
              simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨j, hj, hyj⟩
                have hj' : j.val < W.rounds.length := by omega
                exact ⟨⟨j.val, hj'⟩, hj, by rwa [List.getElem_append_left hj'] at hyj⟩
              · rintro ⟨j, hj, hyj⟩
                have hj' : j.val < (W.rounds ++ [r]).length := by simp
                exact ⟨⟨j.val, hj'⟩, hj, by rwa [List.getElem_append_left j.isLt]⟩
            rw [hbi_eq] at hx_prev; rw [hget] at hx ⊢
            exact W.hstop_prev ⟨i.val, hi_old⟩ x hx hx_prev
          · have hi_eq : i.val = W.rounds.length := by have := i.isLt; simp at *; omega
            have hget : (W.rounds ++ [r])[i.val]'i.isLt = r := by simp [hi_eq]
            have hx_dead : x ∈ deadSet := by
              rw [Finset.mem_biUnion] at hx_prev
              obtain ⟨j, hj, hxj⟩ := hx_prev
              rw [Finset.mem_filter] at hj
              have hj' : j.val < W.rounds.length := by omega
              rw [List.getElem_append_left hj'] at hxj
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (W.hdead_iff x).mpr
                ⟨W.rounds[j.val]'hj', List.getElem_mem _, hxj⟩⟩
            rw [hget] at hx ⊢; exact hstop_prev_r x hx hx_dead
        huncorr_tree := fun i j hij e he => by
          by_cases hj_old : j.val < W.rounds.length
          · have hi_old : i.val < W.rounds.length := by omega
            have hget_i : (W.rounds ++ [r])[i.val]'i.isLt = W.rounds[i.val]'hi_old :=
              List.getElem_append_left hi_old
            have hget_j : (W.rounds ++ [r])[j.val]'j.isLt = W.rounds[j.val]'hj_old :=
              List.getElem_append_left hj_old
            rw [hget_j] at he; rw [hget_i]
            exact W.huncorr_tree ⟨i.val, hi_old⟩ ⟨j.val, hj_old⟩ hij e he
          · have hj_eq : j.val = W.rounds.length := by have := j.isLt; simp at *; omega
            have hi_old : i.val < W.rounds.length := by omega
            have hget_i : (W.rounds ++ [r])[i.val]'i.isLt = W.rounds[i.val]'hi_old :=
              List.getElem_append_left hi_old
            have hget_j : (W.rounds ++ [r])[j.val]'j.isLt = r := by simp [hj_eq]
            rw [hget_j, ← htr_w, List.mem_map] at he
            obtain ⟨ei, hei, rfl⟩ := he
            obtain ⟨eIdx, hei_eq, he0⟩ := htr_src ei hei
            rw [hei_eq, hget_i]; exact W.huncorr ⟨i.val, hi_old⟩ eIdx he0 }
    have hpot_le : memoryCost (partOuterStep (env, a)) s + outerPotFn L (t + 1) a' s' ≤
        outerPotFn L t a s + 20 := by
      have hdeadSet' : Finset.univ.filter (fun x : Fin n => s'.mem (L.bufBase + x.val) ≠ 0) =
          deadSet ∪ r.verts := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hdead_fn x]
        by_cases hx : x ∈ r.verts <;> simp [hx, deadSet]
      have hdeadSet0 : Finset.univ.filter (fun x : Fin n => s.mem (L.bufBase + x.val) ≠ 0) =
          deadSet := by ext x; simp [deadSet, W.hdead_mem x.val x.isLt]
      have hle_2n0 : a.cLiftLen ≤ 2 * n := by
        have hc := Finset.card_le_univ
          (Finset.univ.filter fun x : Fin n => W.dead0 x.val ≠ 0)
        rw [Fintype.card_fin] at hc; have := W.hcl_dead; have := W.hnc_dead; omega
      have hle_2m0 : a.sh.itemCount ≤ 2 * m := W.hsh.ic_max
      have hle_2m1 : a'.sh.itemCount ≤ 2 * m := hsh'.ic_max
      dsimp only [outerPotFn]
      rw [hdeadSet'] at hcost_r
      rw [hdeadSet', hdeadSet0, hcost_eq]
      dsimp only [env, PartLayout.toEnv, deadSet] at hcost_r ⊢
      omega
    exact ⟨hsafe, hvh, hs'_eq ▸ hs'_fr, fun x hx => hs'_eq ▸ hmod_step x hx,
      by rw [ha'_eq, hs'_eq]; exact ⟨⟨W'⟩, hpot_le⟩⟩
  · have hsafe : partOuterStepSafe w (env, a) s := by
      rw [partOuterStepSafe_def]
      exact ⟨h16, ha1_fit, hdead_lt, fun hd => absurd (hdead_t ▸ hd) hd0⟩
    have hvh : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (partOuterStep (env, a))) := by
      rw [hprog]; refine validHistory_read_bind hdead_lt ?_
      rw [hdead_t]; simp only [ne_eq, hd0, not_false_eq_true, ↓reduceIte]
      exact validHistory_pure w s _
    let aNext : PartOuterState :=
      ⟨a.u + 1, a.numComps, a.cEdgeLen, a.cLiftLen, a.mcLen, a.tLen, a.sh⟩
    have ha'_eq : (Memory.spec 0).clientResult s (partOuterStep (env, a)) = aNext := by
      rw [hprog, clientResult_bind_read, hdead_t]
      simp only [ne_eq, hd0, not_false_eq_true, ↓reduceIte, StateTransitionSpec.clientResult_pure]
      rfl
    have hs'_eq : (Memory.spec 0).clientState s (partOuterStep (env, a)) = s := by
      rw [hprog, clientState_bind_read, hdead_t]
      simp only [ne_eq, hd0, not_false_eq_true, ↓reduceIte]; rfl
    have hcost_eq : memoryCost (partOuterStep (env, a)) s = 1 := by
      rw [hprog, memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, hdead_t]
      simp only [ne_eq, hd0, not_false_eq_true, ↓reduceIte, memoryCost_pure]
    have W' : OuterInvWitness L s₀ (t + 1) aNext s :=
      { W with
        ha_u := by dsimp only [aNext]; omega
        ht_le := ht
        hdead_cov := fun x hx => by
          by_cases hxt : x < t
          · exact W.hdead_cov x hxt
          · have hxt_eq : x = t := by omega
            subst hxt_eq; exact hd0 }
    have hpot_le : memoryCost (partOuterStep (env, a)) s + outerPotFn L (t + 1) aNext s ≤
        outerPotFn L t a s + 20 := by
      rw [hcost_eq]; dsimp only [outerPotFn, aNext]; omega
    exact ⟨hsafe, hvh, by rw [hs'_eq], fun x _ => by rw [hs'_eq],
      by rw [ha'_eq, hs'_eq]; exact ⟨⟨W'⟩, hpot_le⟩⟩

private theorem partRunOuterLoop_spec {w n : ℕ} (L : PartLayout w n) (s₀ : Memory.State)
    (h₀ : SHHandle) (hfr₀ : s₀.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hwf₀ : Memory.WellFormed w s₀)
    (hib₀ : h₀.itemBase = L.itemBase) (hnb₀ : h₀.nodeBase = L.nodeBase)
    (hfr0_eq : h₀.firstRoot = 0) (hrt₀ : h₀.rankThreshold = partRankThreshold)
    (hic₀ : h₀.itemCount = 0) (hnc₀ : h₀.nodeCount = 0)
    (hsh₀ : SHInv w 0 0 (2 * L.es.length) (4 * L.es.length) h₀ [] (fun _ => 0) s₀)
    (hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem)
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem)
    (hz1 : ∀ j < 2 * n, s₀.mem (L.bufBase + j) = 0)
    (hz2 : ∀ j < L.es.length, s₀.mem (L.bufBase + 14 * n + j) = 0)
    (hsimp_g : IsSimple (edgeEnds (L.es.map IndexedEdge.toWeighted))) :
    let m := L.es.length
    let d : PartSetupResult := ⟨L.toEnv, h₀⟩
    let prog := partRunOuterLoop d
    let res := (Memory.spec 0).clientResult s₀ prog
    let s' := (Memory.spec 0).clientState s₀ prog
    partRunOuterLoopSafe w d s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    s'.frontier = s₀.frontier ∧
    (∀ x, ¬(InSHPool 0 0 (2 * m) (4 * m)
        ⟨L.itemBase, L.nodeBase, 0, 0, 0, partRankThreshold⟩ x ∨
      (L.bufBase ≤ x ∧ x < L.bufBase + (14 * n + 14 * m))) → s'.mem x = s₀.mem x) ∧
    memoryCost prog s₀ ≤ 5520 * m + 32 * n ∧
    Nonempty (OuterInvWitness L s₀ n res s') := by
  let m := L.es.length
  let d : PartSetupResult := ⟨L.toEnv, h₀⟩
  have hn_pos := L.hn_pos
  have hrem0 : remDeg n L.offBase s₀.mem
      (Finset.univ.filter (fun x : Fin n => s₀.mem (L.bufBase + x.val) ≠ 0)) = 2 * m := by
    have h0 : Finset.univ.filter (fun x : Fin n => s₀.mem (L.bufBase + x.val) ≠ 0) = ∅ := by
      ext x; simp [hz1 x.val (by omega)]
    rw [h0]; exact remDeg_empty hcsr₀
  let st₀ : PartOuterState := ⟨0, 0, 0, 0, 0, 0, h₀⟩
  let W₀ : OuterInvWitness L s₀ 0 st₀ s₀ :=
    { rounds := []
      emittedAll := []
      corrAll := []
      treeIndexedAll := []
      dead0 := fun _ => 0
      inCur0 := fun _ => 0
      edgeState0 := fun _ => 0
      ha_u := rfl
      ht_le := Nat.zero_le n
      hrounds_len := rfl
      hfr := hfr₀
      hwf := hwf₀
      hmod := fun _ h => absurd rfl h
      hhib := hib₀
      hhnb := hnb₀
      hhfr := hfr0_eq
      hhrt := hrt₀
      hhnc := by rw [hnc₀, hic₀]
      hsh := by simpa [st₀, hic₀, hnc₀] using hsh₀
      hdead_mem := fun x hx => hz1 x (by omega)
      hdead_cov := fun x hx => absurd hx (Nat.not_lt_zero _)
      hdead_iff := fun x => by simp
      hincur_mem := fun x hx => by simpa [Nat.add_assoc] using hz1 (n + x) (by omega)
      hincur_le := fun _ _ => le_rfl
      hedge_mem := fun i hi => hz2 i hi
      hedge_vals := fun i => by simp
      hem_nd := List.nodup_nil
      hcr_nd := List.nodup_nil
      hdisj_ec := fun _ h => absurd h List.not_mem_nil
      hcEdgeLen := rfl
      hcLiftLen := rfl
      hcl_dead := Nat.zero_le _
      hnc_dead := Nat.zero_le _
      hmcLen := rfl
      hmc_corr := rfl
      hem_comp := rfl
      hmc_bound := by dsimp only [st₀]; simp
      hmc_mem := fun _ hi => by simp at hi
      htLen := rfl
      htLen_dead := Nat.zero_le _
      htree_w := rfl
      htree_mem := fun _ hi => by simp at hi
      hcap_rem := by
        have h0 : Finset.univ.filter (fun x : Fin n => (0 : ℕ) ≠ 0) = ∅ := by ext; simp
        rw [h0, hic₀, zero_add]
        have h0' : Finset.univ.filter (fun x : Fin n => s₀.mem (L.bufBase + x.val) ≠ 0) = ∅ := by
          ext x; simp [hz1 x.val (by omega)]
        rw [h0'] at hrem0; exact hrem0.le
      hclaim_card := Nat.zero_le _
      hmeta := fun _ hi => by simp at hi
      hstop := fun i => Fin.elim0 i
      huncorr := fun i => Fin.elim0 i
      hstop_prev := fun i => Fin.elim0 i
      huncorr_tree := fun i => Fin.elim0 i }
  have hpot₀ : outerPotFn L 0 st₀ s₀ = 5520 * m + 12 * n := by
    dsimp only [outerPotFn, st₀]
    rw [hrem0, hic₀]
    dsimp only [m]
    omega
  let modOuter : Set ℕ := {x | InSHPool 0 0 (2 * m) (4 * m)
    ⟨L.itemBase, L.nodeBase, 0, 0, 0, partRankThreshold⟩ x ∨
    (L.bufBase ≤ x ∧ x < L.bufBase + (14 * n + 14 * m))}
  have hit := iterate_potential_spec partOuterStep partOuterStepSafe w L.toEnv 20 n
    (fun k a s => Nonempty (OuterInvWitness L s₀ k a s)) (outerPotFn L) modOuter
    (fun k hk a s ⟨W⟩ => by
      have hstep := partOuterStep_spec L s₀ hcsr₀ hin₀ hsimp_g k hk a s W
      dsimp only at hstep
      rcases hstep with ⟨hsafe_s, hvh_s, hfr_s, hmod_s, ⟨W'⟩, hpot_s⟩
      exact ⟨hsafe_s, hvh_s, hpot_s, ⟨hfr_s.ge, fun x _ hx => hmod_s x hx⟩, ⟨W'⟩⟩)
    st₀ s₀ ⟨W₀⟩
  dsimp only at hit
  rcases hit with ⟨hsafe, hvh, hpot, hmod, ⟨W⟩⟩
  have hprog : partRunOuterLoop d = iterate partOuterStep L.toEnv n st₀ := partRunOuterLoop_def d
  rw [← hprog] at hvh hpot W
  have hsafe' : partRunOuterLoopSafe w d s₀ := by
    rw [partRunOuterLoopSafe_def]; exact ⟨L.h16, hsafe⟩
  have hmod' : ∀ x, ¬(InSHPool 0 0 (2 * m) (4 * m)
      ⟨L.itemBase, L.nodeBase, 0, 0, 0, partRankThreshold⟩ x ∨
      (L.bufBase ≤ x ∧ x < L.bufBase + (14 * n + 14 * m))) →
      ((Memory.spec 0).clientState s₀ (partRunOuterLoop d)).mem x = s₀.mem x := by
    intro x hx; by_contra hne; exact hx (W.hmod x hne)
  have hcost : memoryCost (partRunOuterLoop d) s₀ ≤ 5520 * m + 32 * n := by
    rw [hpot₀] at hpot; omega
  exact ⟨hsafe', hvh, W.hfr.trans hfr₀.symm, hmod', hcost, ⟨W⟩⟩

private theorem partRunRemLoop_spec {w n : ℕ} (L : PartLayout w n) (edgeState : ℕ → ℕ)
    (s₀ : Memory.State) (hwf₀ : Memory.WellFormed w s₀)
    (hfr₀ : s₀.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem)
    (hest₀ : ∀ i < L.es.length, s₀.mem (L.bufBase + 14 * n + i) = edgeState i) :
    let m := L.es.length
    let d : PartEdgeBufEnv := ⟨L.edgeBase, L.bufBase, n, m⟩
    let prog := partRunRemLoop d
    let res := (Memory.spec 0).clientResult s₀ prog
    let s' := (Memory.spec 0).clientState s₀ prog
    partRunRemLoopSafe w d s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    res.idx = m ∧ res.count ≤ m ∧
    s'.frontier = s₀.frontier ∧
    Memory.WellFormed w s' ∧
    (∀ x, ¬(L.bufBase + 14 * n + 10 * m ≤ x ∧ x < L.bufBase + 14 * n + 14 * m) →
      s'.mem x = s₀.mem x) ∧
    memoryCost prog s₀ ≤ 10 * m ∧
    ∃ remIdx : List (Fin m),
      remIdx.Nodup ∧
      remIdx.length = res.count ∧
      (∀ eIdx : Fin m, eIdx ∈ remIdx ↔ edgeState eIdx.val = 0) ∧
      HoldsIndexedEdges (L.bufBase + 14 * n + 10 * m)
        (remIdx.map fun eIdx => L.es[eIdx.val]'eIdx.isLt) s'.mem := by
  let m := L.es.length
  let d : PartEdgeBufEnv := ⟨L.edgeBase, L.bufBase, n, m⟩
  let modRem : Set ℕ :=
    {x | L.bufBase + 14 * n + 10 * m ≤ x ∧ x < L.bufBase + 14 * n + 14 * m}
  let invRem : ℕ → PartCursor → Memory.State → Prop := fun k a s =>
    a.idx = k ∧ a.count ≤ k ∧ s.frontier = s₀.frontier ∧ Memory.WellFormed w s ∧
    (∀ x, x ∉ modRem → s.mem x = s₀.mem x) ∧
    ∃ remIdx : List (Fin m),
      remIdx.Nodup ∧ remIdx.length = a.count ∧
      (∀ eIdx : Fin m, eIdx ∈ remIdx ↔ eIdx.val < k ∧ edgeState eIdx.val = 0) ∧
      HoldsIndexedEdges (L.bufBase + 14 * n + 10 * m)
        (remIdx.map fun eIdx => L.es[eIdx.val]'eIdx.isLt) s.mem
  have hit := iterate_potential_spec partEmitRemStep partEmitRemStepSafe w d 10 m
    invRem (fun _ _ _ => 0) modRem (fun k hk a s hi => by
      rcases hi with ⟨ha1, ha2, hfr, hwf, hmod, remIdx, hnd, hlen, hiff, hhold⟩
      have h16 := L.h16
      have hn_pos := L.hn_pos
      have hk1_fit : Fits w (a.idx + 1) := L.hfit_end.of_le (by omega)
      have ha2_fit : Fits w (a.count + 1) := L.hfit_end.of_le (by omega)
      have hbuf_fit : Fits w (L.bufBase + 14 * n + 14 * m) := L.hfit_end.of_le (by omega)
      have hst_lt : L.bufBase + 14 * n + a.idx < s.frontier := by rw [hfr, hfr₀]; omega
      have hst_agree : s.mem (L.bufBase + 14 * n + a.idx) = edgeState k :=
        (hmod _ (by change ¬(L.bufBase + 14 * n + 10 * m ≤ _ ∧ _); omega)).trans
          (ha1 ▸ hest₀ k hk)
      have hprog_step : partEmitRemStep (d, a) =
          (Memory.read (L.bufBase + 14 * n + a.idx) >>= fun st =>
            if st = 0 then
              partCopyIndexedEdge
                ⟨L.edgeBase, L.bufBase + 14 * n + 10 * m, a.idx, a.count⟩ >>= fun _ =>
                pure ⟨a.idx + 1, a.count + 1⟩
            else pure ⟨a.idx + 1, a.count⟩) := partEmitRemStep_def (d, a)
      by_cases hed0 : edgeState k = 0
      · have hsrc_lt : L.edgeBase + 4 * a.idx + 3 < s.frontier := by
          rw [hfr, hfr₀]; have := L.edge_lt_itemBase; have := L.hit_nd; have := L.hnd_buf; omega
        have hdst_lt : L.bufBase + 14 * n + 10 * m + 4 * a.count + 3 < s.frontier := by
          rw [hfr, hfr₀]; omega
        have hcp := partCopyIndexedEdge_spec h16 hwf hsrc_lt hdst_lt
        dsimp only at hcp
        rcases hcp with ⟨hsafe_cp, hvh_cp, hcost_cp, hfr_cp, hwf_cp, hmod_cp, hval_cp⟩
        generalize h_s' : (Memory.spec 0).clientState s
          (partCopyIndexedEdge ⟨L.edgeBase, L.bufBase + 14 * n + 10 * m, a.idx, a.count⟩) =
          s' at *
        have hsafe_s : partEmitRemStepSafe w (d, a) s := by
          rw [partEmitRemStepSafe_def]
          exact ⟨h16, hk1_fit, ha2_fit, hbuf_fit, hst_lt, fun _ => hsafe_cp⟩
        have hvh_s : (Memory.spec w).ValidHistory s
            ((Memory.spec w).clientHistory s (partEmitRemStep (d, a))) := by
          rw [hprog_step]; refine validHistory_read_bind hst_lt ?_
          rw [hst_agree, hed0]; simp only [↓reduceIte]
          exact validHistory_bind_step hvh_cp (validHistory_pure w _ _)
        have hres_s : (Memory.spec 0).clientResult s (partEmitRemStep (d, a)) =
            ⟨a.idx + 1, a.count + 1⟩ := by
          rw [hprog_step, clientResult_bind_read, hst_agree, hed0]; simp only [↓reduceIte]
          rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
        have hst_s : (Memory.spec 0).clientState s (partEmitRemStep (d, a)) = s' := by
          rw [hprog_step, clientState_bind_read, hst_agree, hed0]; simp only [↓reduceIte]
          rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure, h_s']
        have hcost_s : memoryCost (partEmitRemStep (d, a)) s ≤ 9 := by
          rw [hprog_step, memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
            hst_agree, hed0]
          simp only [↓reduceIte, memoryCost_bind', memoryCost_pure]; omega
        have hmod_step : ∀ x, x ∉ modRem → s'.mem x = s.mem x := fun x hx =>
          hmod_cp x fun h => hx (show L.bufBase + 14 * n + 10 * m ≤ x ∧
            x < L.bufBase + 14 * n + 14 * m by omega)
        have hmod_tot : ∀ x, x ∉ modRem → s'.mem x = s₀.mem x := fun x hx =>
          (hmod_step x hx).trans (hmod x hx)
        let kFin : Fin m := ⟨k, hk⟩
        have hk_not : kFin ∉ remIdx := fun hm => by
          have hlt := ((hiff kFin).mp hm).1; dsimp only [kFin] at hlt; omega
        have hnd' : (remIdx ++ [kFin]).Nodup :=
          List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, fun x hx y hy heq => by
            rw [List.mem_singleton] at hy; subst hy; exact hk_not (heq ▸ hx)⟩
        have hhold' : HoldsIndexedEdges (L.bufBase + 14 * n + 10 * m)
            ((remIdx ++ [kFin]).map fun eIdx => L.es[eIdx.val]'eIdx.isLt) s'.mem := by
          rw [List.map_append, List.map_singleton]
          refine holdsIndexedEdges_append ?_ ?_
          · refine hhold.congr fun x hx1 hx2 => ?_
            rw [List.length_map, hlen] at hx2; exact hmod_cp x (by omega)
          · intro i hi
            simp only [List.length_singleton] at hi
            have hi0 : i = 0 := by omega
            subst hi0
            have hin_s : HoldsIndexedEdges L.edgeBase L.es s.mem :=
              hin₀.congr fun x _ hx2 => hmod x (by
                change ¬(L.bufBase + 14 * n + 10 * m ≤ x ∧ x < L.bufBase + 14 * n + 14 * m)
                have := L.edge_lt_itemBase; have := L.hit_nd; have := L.hnd_buf; omega)
            have he_s := hin_s k hk
            rw [ha1] at hval_cp
            refine ⟨?_, ?_, ?_, ?_⟩
            · simpa [List.length_map, hlen, kFin] using hval_cp.1.trans he_s.1
            · simpa [List.length_map, hlen, kFin] using hval_cp.2.1.trans he_s.2.1
            · simpa [List.length_map, hlen, kFin] using hval_cp.2.2.1.trans he_s.2.2.1
            · simpa [List.length_map, hlen, kFin] using hval_cp.2.2.2.trans he_s.2.2.2
        have hiff' : ∀ eIdx : Fin m, eIdx ∈ remIdx ++ [kFin] ↔
            eIdx.val < k + 1 ∧ edgeState eIdx.val = 0 := by
          intro eIdx; simp only [List.mem_append, List.mem_singleton, hiff]
          constructor
          · rintro (⟨h1, h2⟩ | rfl)
            · exact ⟨by omega, h2⟩
            · dsimp only [kFin]; exact ⟨by omega, hed0⟩
          · rintro ⟨h1, h2⟩
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h1) with hlt | heq
            · exact .inl ⟨hlt, h2⟩
            · exact .inr (Fin.ext heq)
        refine ⟨hsafe_s, hvh_s, by omega,
          by rw [hst_s]; exact ⟨hfr_cp.ge, fun x _ hx => hmod_step x hx⟩,
          by rw [hres_s]; exact ⟨by dsimp only; omega, by dsimp only; omega,
            by rw [hst_s]; exact hfr_cp.trans hfr, by rw [hst_s]; exact hwf_cp,
            fun x hx => by rw [hst_s]; exact hmod_tot x hx,
            remIdx ++ [kFin], hnd', by simp [hlen], hiff',
            by rw [hst_s]; exact hhold'⟩⟩
      · have hsafe_s : partEmitRemStepSafe w (d, a) s := by
          rw [partEmitRemStepSafe_def]
          exact ⟨h16, hk1_fit, ha2_fit, hbuf_fit, hst_lt, fun h => absurd (hst_agree ▸ h) hed0⟩
        have hvh_s : (Memory.spec w).ValidHistory s
            ((Memory.spec w).clientHistory s (partEmitRemStep (d, a))) := by
          rw [hprog_step]; refine validHistory_read_bind hst_lt ?_
          rw [hst_agree]; simp only [hed0, ↓reduceIte]; exact validHistory_pure w _ _
        have hres_s : (Memory.spec 0).clientResult s (partEmitRemStep (d, a)) =
            ⟨a.idx + 1, a.count⟩ := by
          rw [hprog_step, clientResult_bind_read, hst_agree]
          simp only [hed0, ↓reduceIte]; exact StateTransitionSpec.clientResult_pure _ _
        have hst_s : (Memory.spec 0).clientState s (partEmitRemStep (d, a)) = s := by
          rw [hprog_step, clientState_bind_read, hst_agree]; simp only [hed0, ↓reduceIte]; rfl
        have hcost_s : memoryCost (partEmitRemStep (d, a)) s = 1 := by
          rw [hprog_step, memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
            hst_agree]
          simp only [hed0, ↓reduceIte, memoryCost_pure]
        have hiff' : ∀ eIdx : Fin m, eIdx ∈ remIdx ↔
            eIdx.val < k + 1 ∧ edgeState eIdx.val = 0 := by
          intro eIdx; rw [hiff]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
          · rintro ⟨h1, h2⟩
            have hne : eIdx.val ≠ k := fun h => hed0 (h ▸ h2); exact ⟨by omega, h2⟩
        refine ⟨hsafe_s, hvh_s, by omega, by rw [hst_s]; exact Memory.Modifies.refl modRem s,
          by rw [hres_s]; exact ⟨by dsimp only; omega, by dsimp only; omega,
            by rw [hst_s]; exact hfr, by rw [hst_s]; exact hwf,
            fun x hx => by rw [hst_s]; exact hmod x hx,
            remIdx, hnd, hlen, hiff', by rw [hst_s]; exact hhold⟩⟩)
    ⟨0, 0⟩ s₀ ⟨rfl, le_rfl, rfl, hwf₀, fun _ _ => rfl, [], List.nodup_nil, rfl,
      fun _ => by simp, fun _ hi => by simp at hi⟩
  dsimp only at hit
  rcases hit with ⟨hsafe, hvh, hpot, _, h1, h2, hfr, hwf, hmod, remIdx, hnd, hlen, hiff, hhold⟩
  have hprog : partRunRemLoop d = iterate partEmitRemStep d m ⟨0, 0⟩ := partRunRemLoop_def d
  rw [← hprog] at hvh hpot h1 h2 hfr hwf hmod hlen hhold
  have hcost : memoryCost (partRunRemLoop d) s₀ ≤ 10 * m := by omega
  exact ⟨by rw [partRunRemLoopSafe_def]; exact ⟨L.h16, hsafe⟩, hvh, h1, h2, hfr, hwf, hmod, hcost,
    remIdx, hnd, hlen, fun eIdx => by simpa [eIdx.isLt] using hiff eIdx, hhold⟩

/-- Full specification of `partitionProg` (step toward Theorem 5.8 of [PettieRamachandran2002]
#8624), specializing [PettieRamachandran2002] §3.2 (Fig. 2, p. 21) `Partition(G, t, ε)` with
target component size `t = maxsize` and fixed `ε = 1 / 16` (`partRankThreshold = 8`, yielding
at most `m / 8 = 2 * ε * m` corrupted edges), plus materialization of remaining edges and
conglomerate labels via `connectedComponentsProg`. Proves native safety (`partitionProgSafe`),
`ValidHistory`, `Memory.WellFormed`, frame preservation below `s.frontier`, `O(m + n)` cost
(`≤ 6000 * (m + n)`), `|M_C| ≤ m / 8`, `H_rem.Subperm es`, edge partition
`((rounds.flatMap compGlobal) ++ H_rem ++ (rounds.flatMap corrEdges)).Perm es`, conglomerate
labeling matching the DJP tree forest, and per-round structural invariants. -/
theorem partitionProg_spec {w n edgeBase maxsize : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s) (hmax_pos : 1 ≤ maxsize)
    (hin : HoldsIndexedEdges edgeBase es s.mem) (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + 1100 * (es.length + n + 1)))
    (hsimp : IsSimple (edgeEnds (es.map IndexedEdge.toWeighted))) :
    let prog := partitionProg ⟨n, es.length, edgeBase, maxsize⟩
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    partitionProgSafe w ⟨n, es.length, edgeBase, maxsize⟩ s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    Memory.WellFormed w s' ∧
    (∀ a < s.frontier, s'.mem a = s.mem a) ∧
    s.frontier ≤ s'.frontier ∧
    s'.frontier ≤ s.frontier + 72 * (es.length + n + 1) ∧
    memoryCost prog s ≤ 6000 * (es.length + n) ∧
    res.numComps ≤ n ∧
    res.mcLen ≤ es.length / 8 ∧
    res.hRemLen ≤ es.length ∧
    res.nConglom ≤ n ∧
    res.compMetaBase + 3 * res.numComps ≤ s'.frontier ∧
    res.liftMetaBase + res.numComps ≤ s'.frontier ∧
    res.mcBase + 4 * res.mcLen ≤ s'.frontier ∧
    res.hRemBase + 4 * res.hRemLen ≤ s'.frontier ∧
    res.conglomBase + n ≤ s'.frontier ∧
    (n ≠ 0 → s.frontier ≤ res.compMetaBase ∧ s.frontier ≤ res.liftMetaBase ∧
      s.frontier ≤ res.mcBase ∧ s.frontier ≤ res.hRemBase ∧ s.frontier ≤ res.conglomBase) ∧
    ∃ (rounds : List (PartitionRoundWitness n)) (H_rem : List (IndexedEdge n))
        (conglomFn : Fin n → Fin res.nConglom),
      rounds.length = res.numComps ∧
      H_rem.length = res.hRemLen ∧
      H_rem.Subperm es ∧
      ((rounds.flatMap PartitionRoundWitness.compGlobal) ++ H_rem ++
        (rounds.flatMap PartitionRoundWitness.corrEdges)).Perm es ∧
      (rounds.flatMap PartitionRoundWitness.corrEdges).length = res.mcLen ∧
      HoldsIndexedEdges res.mcBase (rounds.flatMap PartitionRoundWitness.corrEdges) s'.mem ∧
      HoldsIndexedEdges res.hRemBase H_rem s'.mem ∧
      (∀ u : Fin n, s'.mem (res.conglomBase + u.val) = (conglomFn u).val) ∧
      Function.Surjective conglomFn ∧
      (∀ x y : Fin n, conglomFn x = conglomFn y ↔
        (edgePartition (rounds.flatMap fun r => r.tree.treeEdges)).rel x y = true) ∧
      (∀ x : Fin n, ∃ r ∈ rounds, x ∈ r.verts) ∧
      (∀ i : Fin rounds.length,
        let r := rounds[i.val]'i.isLt
        let v_i := s'.mem (res.compMetaBase + 3 * i.val)
        let m_i := s'.mem (res.compMetaBase + 3 * i.val + 1)
        let cEdgeBase := s'.mem (res.compMetaBase + 3 * i.val + 2)
        let cLiftBase := s'.mem (res.liftMetaBase + i.val)
        v_i = r.numVerts ∧ m_i = r.compLocal.length ∧
        cEdgeBase + 4 * r.compLocal.length ≤ s'.frontier ∧
        cLiftBase + r.numVerts ≤ s'.frontier ∧
        (s.frontier ≤ cEdgeBase ∧ s.frontier ≤ cLiftBase) ∧
        HoldsIndexedEdges cEdgeBase r.compLocal s'.mem ∧
        (∀ k : Fin r.numVerts, s'.mem (cLiftBase + k.val) = (r.lift k).val) ∧
        r.verts.card = r.numVerts ∧ 1 ≤ r.numVerts ∧ r.numVerts ≤ maxsize ∧
        (1 ≤ r.compLocal.length → r.numVerts ≤ 2 * r.compLocal.length) ∧
        Function.Injective r.lift ∧
        IsSimple (edgeEnds (r.compLocal.map IndexedEdge.toWeighted)) ∧
        (∀ e ∈ r.compGlobal, e.u ∈ r.verts ∧ e.v ∈ r.verts) ∧
        r.tree.treeEdges.Subperm (r.compGlobal.map IndexedEdge.toWeighted) ∧
        (r.verts ∩ (Finset.univ.filter fun j : Fin rounds.length =>
          j.val < i.val).biUnion (fun j => (rounds[j.val]'j.isLt).verts)).card ≤ 1) ∧
      (∀ i : Fin rounds.length,
        maxsize ≤ (rounds[i.val]'i.isLt).verts.card ∨
        (∃ j : Fin rounds.length, j.val < i.val ∧
          ((rounds[i.val]'i.isLt).verts ∩ (rounds[j.val]'j.isLt).verts).Nonempty) ∨
        ((∀ j : Fin rounds.length, j ≠ i →
          ¬((rounds[i.val]'i.isLt).verts ∩ (rounds[j.val]'j.isLt).verts).Nonempty) ∧
          ∀ e ∈ H_rem, e.u ∉ (rounds[i.val]'i.isLt).verts ∧
            e.v ∉ (rounds[i.val]'i.isLt).verts)) ∧
      (∀ i : Fin rounds.length, ∀ e ∈ H_rem,
        ¬(e.u ∈ (rounds[i.val]'i.isLt).verts ∧ e.v ∈ (rounds[i.val]'i.isLt).verts) ∧
        ∀ s_step : Fin (rounds[i.val]'i.isLt).tree.numSteps,
          (e.u ∈ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val ↔
            e.v ∉ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val) →
          (rounds[i.val]'i.isLt).tree.wPop s_step ≤ e.weight) ∧
      (∀ i : Fin rounds.length, ∀ x ∈ (rounds[i.val]'i.isLt).verts,
        x ∈ (Finset.univ.filter fun j : Fin rounds.length =>
          j.val < i.val).biUnion (fun j => (rounds[j.val]'j.isLt).verts) →
        ∃ hpos : 0 < (rounds[i.val]'i.isLt).tree.numSteps,
          x = (rounds[i.val]'i.isLt).tree.vOut
            ⟨(rounds[i.val]'i.isLt).tree.numSteps - 1, Nat.sub_lt hpos Nat.one_pos⟩) ∧
      (∀ i j : Fin rounds.length, i.val < j.val →
        ∀ e ∈ (rounds[j.val]'j.isLt).tree.treeEdges,
          ∀ s_step : Fin (rounds[i.val]'i.isLt).tree.numSteps,
            (e.u ∈ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val ↔
              e.v ∉ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val) →
            (rounds[i.val]'i.isLt).tree.wPop s_step ≤ e.weight) := by
  by_cases hn0 : n = 0
  · subst hn0
    have hes_nil : es = [] := List.eq_nil_iff_forall_not_mem.mpr fun e _ => Fin.elim0 e.u
    have hprog : partitionProg ⟨0, es.length, edgeBase, maxsize⟩ =
        pure ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
      rw [partitionProg_def]; simp only [↓reduceIte]
    have hsafe0 : partitionProgSafe w ⟨0, es.length, edgeBase, maxsize⟩ s := by
      rw [partitionProgSafe_def]; exact ⟨h16, fun h => absurd rfl h⟩
    dsimp only
    rw [hprog, StateTransitionSpec.clientResult_pure, StateTransitionSpec.clientState_pure,
      memoryCost_pure]
    refine ⟨hsafe0, validHistory_pure w s _, hwf, fun _ _ => rfl, le_rfl,
      Nat.le_add_right _ _, Nat.zero_le _, le_rfl, Nat.zero_le _, Nat.zero_le _, le_rfl,
      Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
      fun h => absurd rfl h, [], [], Fin.elim0,
      rfl, rfl, List.nil_subperm, by simp [hes_nil], rfl,
      fun _ hi => by simp at hi, fun _ hi => by simp at hi,
      fun u => Fin.elim0 u, fun y => Fin.elim0 y, fun x => Fin.elim0 x, fun x => Fin.elim0 x,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  · have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn0
    let m := es.length
    have hsetup := partSetup_spec h16 hwf hn_pos hmax_pos hin hin_lt hfit
    dsimp only at hsetup
    generalize h_setup : (Memory.spec 0).clientResult s
      (partSetup ⟨n, m, edgeBase, maxsize⟩) = setup at *
    generalize h_s1 : (Memory.spec 0).clientState s
      (partSetup ⟨n, m, edgeBase, maxsize⟩) = s₁ at *
    rcases hsetup with ⟨hsafe1, hvh1, hcost1, _, _, _, _, hs_bb, hs_h,
      hs1_fr, hwf1, hfr1_mem, hin1, hcsr1, hsh1, hz1, hz2, L, hL_env, hL_es, hL_eb, hL_ms,
      hL_off, hL_adj, hL_it, hL_nd, hL_buf, _⟩
    subst hL_es; subst hL_eb; subst hL_ms
    have hbb_eq : setup.env.bufBase = L.bufBase := hL_buf.symm
    have hsh1' : SHInv w 0 0 (2 * L.es.length) (4 * L.es.length) setup.sh [] (fun _ => 0) s₁ :=
      hs_h ▸ hsh1
    have houter := partRunOuterLoop_spec L s₁ setup.sh (hbb_eq ▸ hs1_fr) hwf1
      hL_it.symm hL_nd.symm (by rw [hs_h]) (by rw [hs_h]) (by rw [hs_h]) (by rw [hs_h])
      hsh1' (hL_off ▸ hL_adj ▸ hcsr1) hin1
      (fun j hj => hbb_eq ▸ hz1 j hj) (fun j hj => hbb_eq ▸ hz2 j hj) hsimp
    dsimp only at houter
    have hsetup_eq : (⟨L.toEnv, setup.sh⟩ : PartSetupResult) = setup := by
      cases setup; simp only [PartSetupResult.mk.injEq] at hL_env ⊢; exact ⟨hL_env, trivial⟩
    rw [hsetup_eq] at houter
    generalize h_res : (Memory.spec 0).clientResult s₁ (partRunOuterLoop setup) = res at *
    generalize h_s2 : (Memory.spec 0).clientState s₁ (partRunOuterLoop setup) = s₂ at *
    rcases houter with ⟨hsafe2, hvh2, hs2_fr, hmod2, hcost2, ⟨W⟩⟩
    have hin2 : HoldsIndexedEdges L.edgeBase L.es s₂.mem := outerInv_edges W hin1
    have hrem := partRunRemLoop_spec L W.edgeState0 s₂ W.hwf W.hfr hin2 W.hedge_mem
    dsimp only at hrem
    generalize h_hRem : (Memory.spec 0).clientResult s₂
      (partRunRemLoop ⟨L.edgeBase, L.bufBase, n, L.es.length⟩) = hRem at *
    generalize h_s3 : (Memory.spec 0).clientState s₂
      (partRunRemLoop ⟨L.edgeBase, L.bufBase, n, L.es.length⟩) = s₃ at *
    rcases hrem with ⟨hsafe3, hvh3, _, hhRem2, hs3_fr, hwf3, hmod3, hcost3,
      remIdx, hnd_rem, hlen_rem, hiff_rem, hhold_rem⟩
    have hdead_le_n : (Finset.univ.filter fun x : Fin n => W.dead0 x.val ≠ 0).card ≤ n := by
      have := Finset.card_le_univ (Finset.univ.filter fun x : Fin n => W.dead0 x.val ≠ 0)
      simpa [Fintype.card_fin] using this
    have htl_le_n : W.treeIndexedAll.length ≤ n := by
      rw [← W.htLen]; exact W.htLen_dead.trans hdead_le_n
    have htree_s3 : HoldsIndexedEdges (L.bufBase + 10 * n) W.treeIndexedAll s₃.mem := by
      refine W.htree_mem.congr fun x hx1 hx2 => hmod3 x ?_; omega
    have hcc := @connectedComponentsProg_spec w n (L.bufBase + 10 * n) W.treeIndexedAll s₃
      h16 hwf3 htree_s3 (by rw [hs3_fr, W.hfr]; omega)
      (by rw [hs3_fr, W.hfr]; exact L.hfit_end.of_le (by omega))
    rw [← W.htLen] at hcc
    obtain ⟨hvh4, hcost4, hmod4, hcc_post⟩ := framedTriple_iff_realization.mp hcc
    generalize h_cc : (Memory.spec 0).clientResult s₃
      (connectedComponentsProg ⟨n, res.tLen, L.bufBase + 10 * n⟩) = cc at hcc_post
    generalize h_s4 : (Memory.spec 0).clientState s₃
      (connectedComponentsProg ⟨n, res.tLen, L.bufBase + 10 * n⟩) = s₄ at hvh4 hcost4 hmod4 hcc_post
    rcases hcc_post with ⟨hcc1, hcc2, hs4_fr, hwf4, hcc_lt, hcc_surj, hcc_rel, _⟩
    have hframe4 : ∀ a < s₃.frontier, s₄.mem a = s₃.mem a := fun a ha =>
      hmod4.mem_eq_of_not_mem ha (Set.notMem_empty a)
    let conglomFn : Fin n → Fin cc.numComps := fun u => ⟨s₄.mem (cc.compBase + u.val), hcc_lt u⟩
    have hconglom_mem : ∀ u : Fin n, s₄.mem (cc.compBase + u.val) = (conglomFn u).val :=
      fun _ => rfl
    have hconglom_surj : Function.Surjective conglomFn := fun c => by
      obtain ⟨u, hu⟩ := hcc_surj c; exact ⟨u, Fin.ext hu⟩
    have hconglom_rel : ∀ x y : Fin n, conglomFn x = conglomFn y ↔
        (edgePartition (W.treeIndexedAll.map IndexedEdge.toWeighted)).rel x y = true :=
      fun x y => by simpa [conglomFn, Fin.ext_iff] using hcc_rel x y
    have hprog : partitionProg ⟨n, L.es.length, L.edgeBase, L.maxsize⟩ =
        (partSetup ⟨n, L.es.length, L.edgeBase, L.maxsize⟩ >>= fun setup =>
          partRunOuterLoop setup >>= fun res =>
            partRunRemLoop ⟨L.edgeBase, setup.env.bufBase, n, L.es.length⟩ >>= fun hRem =>
              connectedComponentsProg ⟨n, res.tLen, setup.env.bufBase + 10 * n⟩ >>=
                fun cc =>
                  let b := setup.env.bufBase
                  pure ⟨res.numComps, b + 6 * n, b + 9 * n, b + 14 * n + 6 * L.es.length,
                    res.mcLen, b + 14 * n + 10 * L.es.length, hRem.count,
                    cc.compBase, cc.numComps⟩) := by
      rw [partitionProg_def]; simp [hn0]
    have hsafe : partitionProgSafe w ⟨n, L.es.length, L.edgeBase, L.maxsize⟩ s := by
      rw [partitionProgSafe_def]
      refine ⟨h16, fun _ => ?_⟩
      dsimp only
      rw [h_setup, h_s1, h_res, h_s2, hbb_eq, h_s3]
      have hres_tl : res.tLen ≤ n := W.htLen ▸ htl_le_n
      refine ⟨L.hfit_end.of_le (by omega), hsafe1, hsafe2, hsafe3,
        by rw [hs3_fr, W.hfr]; omega, L.hfit_end.of_le (by rw [hs3_fr, W.hfr]; omega), ?_⟩
      intro j hj
      have hj_t : j < W.treeIndexedAll.length := by rw [← W.htLen]; exact hj
      have hej := htree_s3 j hj_t
      exact ⟨hej.1 ▸ (W.treeIndexedAll[j]'hj_t).u.isLt,
        hej.2.1 ▸ (W.treeIndexedAll[j]'hj_t).v.isLt⟩
    have hvh : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        (partitionProg ⟨n, L.es.length, L.edgeBase, L.maxsize⟩)) := by
      rw [hprog]
      refine validHistory_bind_step hvh1 ?_
      rw [h_s1, h_setup]
      refine validHistory_bind_step hvh2 ?_
      rw [h_s2, h_res, hbb_eq]
      refine validHistory_bind_step hvh3 ?_
      rw [h_s3]
      exact validHistory_bind_step hvh4 (validHistory_pure w _ _)
    let outRes : PartitionResult :=
      ⟨res.numComps, L.bufBase + 6 * n, L.bufBase + 9 * n, L.bufBase + 14 * n + 6 * L.es.length,
        res.mcLen, L.bufBase + 14 * n + 10 * L.es.length, hRem.count, cc.compBase, cc.numComps⟩
    have hres_eq : (Memory.spec 0).clientResult s
        (partitionProg ⟨n, L.es.length, L.edgeBase, L.maxsize⟩) = outRes := by
      rw [hprog, StateTransitionSpec.clientResult_bind, h_s1, h_setup,
        StateTransitionSpec.clientResult_bind, h_s2, h_res, hbb_eq,
        StateTransitionSpec.clientResult_bind, h_s3, h_hRem,
        StateTransitionSpec.clientResult_bind, h_s4, h_cc, StateTransitionSpec.clientResult_pure]
    have hst_eq : (Memory.spec 0).clientState s
        (partitionProg ⟨n, L.es.length, L.edgeBase, L.maxsize⟩) = s₄ := by
      rw [hprog, StateTransitionSpec.clientState_bind, h_s1, h_setup,
        StateTransitionSpec.clientState_bind, h_s2, h_res, hbb_eq,
        StateTransitionSpec.clientState_bind, h_s3, h_hRem,
        StateTransitionSpec.clientState_bind, h_s4, h_cc, StateTransitionSpec.clientState_pure]
    have hcost_eq : memoryCost (partitionProg ⟨n, L.es.length, L.edgeBase, L.maxsize⟩) s =
        memoryCost (partSetup ⟨n, L.es.length, L.edgeBase, L.maxsize⟩) s +
        memoryCost (partRunOuterLoop setup) s₁ +
        memoryCost (partRunRemLoop ⟨L.edgeBase, L.bufBase, n, L.es.length⟩) s₂ +
        memoryCost (connectedComponentsProg ⟨n, res.tLen, L.bufBase + 10 * n⟩) s₃ := by
      rw [hprog, memoryCost_bind', h_s1, h_setup, memoryCost_bind', h_s2, h_res, hbb_eq,
        memoryCost_bind', h_s3, h_hRem, memoryCost_bind', h_s4, h_cc, memoryCost_pure, add_zero]
      omega
    have hcost_bound : memoryCost (partitionProg ⟨n, L.es.length, L.edgeBase, L.maxsize⟩) s ≤
        6000 * (L.es.length + n) := by
      have h1 : res.tLen ≤ n := W.htLen ▸ htl_le_n
      rw [hcost_eq]; omega
    have hframe_s4 : ∀ a < s.frontier, s₄.mem a = s.mem a := fun a ha => by
      have ha1 : a < s₁.frontier := by
        rw [hs1_fr, hbb_eq]; have := L.hoff_ge; have := L.hoff_adj
        have := L.hadj_it; have := L.hit_nd; have := L.hnd_buf; omega
      have ha2 : a < s₂.frontier := by rw [hs2_fr]; exact ha1
      have ha3 : a < s₃.frontier := by rw [hs3_fr]; exact ha2
      have h43 := hframe4 a ha3
      have h32 := hmod3 a (by rw [hs2_fr, hs1_fr, hbb_eq] at ha2; omega)
      have h21 := hmod2 a (by
        rintro (hp | h)
        · rcases PartLayout.inSHPool_bounds hp with ⟨h1, _⟩ | ⟨h1, _⟩ <;> dsimp only at h1 <;>
            have := L.hoff_ge <;> have := L.hoff_adj <;> have := L.hadj_it <;>
            have := L.hit_nd <;> omega
        · have := L.hoff_ge; have := L.hoff_adj; have := L.hadj_it
          have := L.hit_nd; have := L.hnd_buf; omega)
      exact h43.trans (h32.trans (h21.trans (hfr1_mem a ha)))
    have hs4_agree_buf : ∀ a < L.bufBase + (14 * n + 14 * L.es.length), s₄.mem a = s₃.mem a :=
      fun a ha => hframe4 a (by rw [hs3_fr, W.hfr]; exact ha)
    have hs3_agree_pre : ∀ a < L.bufBase + 14 * n + 10 * L.es.length, s₃.mem a = s₂.mem a :=
      fun a ha => hmod3 a (by omega)
    have hmc_len_le : res.mcLen ≤ L.es.length / 8 := by
      have := W.hmc_bound; have := W.hcap_rem; omega
    have hnc_le : res.numComps ≤ n := W.hnc_dead.trans hdead_le_n
    let H_rem : List (IndexedEdge n) := remIdx.map (fun eIdx => L.es[eIdx.val]'eIdx.isLt)
    have hperm_fin : (W.emittedAll ++ remIdx ++ W.corrAll).Perm (List.finRange L.es.length) := by
      have hdisj_er : ∀ e ∈ W.emittedAll, e ∉ remIdx := fun e he1 he2 => by
        have h1 := ((W.hedge_vals e).1).mpr he1; have h0 := (hiff_rem e).mp he2; omega
      have hdisj_rc : ∀ e ∈ remIdx, e ∉ W.corrAll := fun e he1 he2 => by
        have h0 := (hiff_rem e).mp he1; have h2 := ((W.hedge_vals e).2.1).mpr he2; omega
      have hnd_all : (W.emittedAll ++ remIdx ++ W.corrAll).Nodup := by
        refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨W.hem_nd, hnd_rem, fun e h1 _ h2 heq =>
          hdisj_er e h1 (heq ▸ h2)⟩, W.hcr_nd, fun e h1 _ h2 heq => ?_⟩
        rw [List.mem_append] at h1
        rcases h1 with h1a | h1b
        · exact W.hdisj_ec e h1a (heq ▸ h2)
        · exact hdisj_rc e h1b (heq ▸ h2)
      refine (List.perm_ext_iff_of_nodup hnd_all (List.nodup_finRange _)).mpr fun e => ?_
      simp only [List.mem_append, List.mem_finRange, iff_true]
      rcases (W.hedge_vals e).2.2 with h0 | h1 | h2
      · exact .inl (.inr ((hiff_rem e).mpr h0))
      · exact .inl (.inl ((W.hedge_vals e).1.mp h1))
      · exact .inr ((W.hedge_vals e).2.1.mp h2)
    have hperm_es : ((W.rounds.flatMap PartitionRoundWitness.compGlobal) ++ H_rem ++
        (W.rounds.flatMap PartitionRoundWitness.corrEdges)).Perm L.es := by
      have hm := hperm_fin.map (fun eIdx : Fin L.es.length => L.es[eIdx.val]'eIdx.isLt)
      simp only [List.map_append, W.hem_comp, W.hmc_corr] at hm
      have hfr_map : (List.finRange L.es.length).map
          (fun eIdx : Fin L.es.length => L.es[eIdx.val]'eIdx.isLt) = L.es :=
        List.ext_getElem (by simp) fun i hi1 hi2 => by simp
      simpa [H_rem, hfr_map] using hm
    have hsub_rem : H_rem.Subperm L.es := by
      have h1 : H_rem.Sublist ((W.rounds.flatMap PartitionRoundWitness.compGlobal) ++ H_rem) :=
        List.sublist_append_right _ _
      have h2 : ((W.rounds.flatMap PartitionRoundWitness.compGlobal) ++ H_rem).Sublist
          ((W.rounds.flatMap PartitionRoundWitness.compGlobal) ++ H_rem ++
            (W.rounds.flatMap PartitionRoundWitness.corrEdges)) :=
        List.sublist_append_left _ _
      exact (h1.trans h2).subperm.trans hperm_es.subperm
    have h_ex : ∃ (rounds : List (PartitionRoundWitness n)) (H_rem : List (IndexedEdge n))
        (conglomFn : Fin n → Fin outRes.nConglom),
        rounds.length = outRes.numComps ∧
        H_rem.length = outRes.hRemLen ∧
        H_rem.Subperm L.es ∧
        ((rounds.flatMap PartitionRoundWitness.compGlobal) ++ H_rem ++
          (rounds.flatMap PartitionRoundWitness.corrEdges)).Perm L.es ∧
        (rounds.flatMap PartitionRoundWitness.corrEdges).length = outRes.mcLen ∧
        HoldsIndexedEdges outRes.mcBase (rounds.flatMap PartitionRoundWitness.corrEdges) s₄.mem ∧
        HoldsIndexedEdges outRes.hRemBase H_rem s₄.mem ∧
        (∀ u : Fin n, s₄.mem (outRes.conglomBase + u.val) = (conglomFn u).val) ∧
        Function.Surjective conglomFn ∧
        (∀ x y : Fin n, conglomFn x = conglomFn y ↔
          (edgePartition (rounds.flatMap fun r => r.tree.treeEdges)).rel x y = true) ∧
        (∀ x : Fin n, ∃ r ∈ rounds, x ∈ r.verts) ∧
        (∀ i : Fin rounds.length,
          let r := rounds[i.val]'i.isLt
          let v_i := s₄.mem (outRes.compMetaBase + 3 * i.val)
          let m_i := s₄.mem (outRes.compMetaBase + 3 * i.val + 1)
          let cEdgeBase := s₄.mem (outRes.compMetaBase + 3 * i.val + 2)
          let cLiftBase := s₄.mem (outRes.liftMetaBase + i.val)
          v_i = r.numVerts ∧ m_i = r.compLocal.length ∧
          cEdgeBase + 4 * r.compLocal.length ≤ s₄.frontier ∧
          cLiftBase + r.numVerts ≤ s₄.frontier ∧
          (s.frontier ≤ cEdgeBase ∧ s.frontier ≤ cLiftBase) ∧
          HoldsIndexedEdges cEdgeBase r.compLocal s₄.mem ∧
          (∀ k : Fin r.numVerts, s₄.mem (cLiftBase + k.val) = (r.lift k).val) ∧
          r.verts.card = r.numVerts ∧ 1 ≤ r.numVerts ∧ r.numVerts ≤ L.maxsize ∧
          (1 ≤ r.compLocal.length → r.numVerts ≤ 2 * r.compLocal.length) ∧
          Function.Injective r.lift ∧
          IsSimple (edgeEnds (r.compLocal.map IndexedEdge.toWeighted)) ∧
          (∀ e ∈ r.compGlobal, e.u ∈ r.verts ∧ e.v ∈ r.verts) ∧
          r.tree.treeEdges.Subperm (r.compGlobal.map IndexedEdge.toWeighted) ∧
          (r.verts ∩ (Finset.univ.filter fun j : Fin rounds.length =>
            j.val < i.val).biUnion (fun j => (rounds[j.val]'j.isLt).verts)).card ≤ 1) ∧
        (∀ i : Fin rounds.length,
          L.maxsize ≤ (rounds[i.val]'i.isLt).verts.card ∨
          (∃ j : Fin rounds.length, j.val < i.val ∧
            ((rounds[i.val]'i.isLt).verts ∩ (rounds[j.val]'j.isLt).verts).Nonempty) ∨
          ((∀ j : Fin rounds.length, j ≠ i →
            ¬((rounds[i.val]'i.isLt).verts ∩ (rounds[j.val]'j.isLt).verts).Nonempty) ∧
            ∀ e ∈ H_rem, e.u ∉ (rounds[i.val]'i.isLt).verts ∧
              e.v ∉ (rounds[i.val]'i.isLt).verts)) ∧
        (∀ i : Fin rounds.length, ∀ e ∈ H_rem,
          ¬(e.u ∈ (rounds[i.val]'i.isLt).verts ∧ e.v ∈ (rounds[i.val]'i.isLt).verts) ∧
          ∀ s_step : Fin (rounds[i.val]'i.isLt).tree.numSteps,
            (e.u ∈ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val ↔
              e.v ∉ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val) →
            (rounds[i.val]'i.isLt).tree.wPop s_step ≤ e.weight) ∧
        (∀ i : Fin rounds.length, ∀ x ∈ (rounds[i.val]'i.isLt).verts,
          x ∈ (Finset.univ.filter fun j : Fin rounds.length =>
            j.val < i.val).biUnion (fun j => (rounds[j.val]'j.isLt).verts) →
          ∃ hpos : 0 < (rounds[i.val]'i.isLt).tree.numSteps,
            x = (rounds[i.val]'i.isLt).tree.vOut
              ⟨(rounds[i.val]'i.isLt).tree.numSteps - 1, Nat.sub_lt hpos Nat.one_pos⟩) ∧
        (∀ i j : Fin rounds.length, i.val < j.val →
          ∀ e ∈ (rounds[j.val]'j.isLt).tree.treeEdges,
            ∀ s_step : Fin (rounds[i.val]'i.isLt).tree.numSteps,
              (e.u ∈ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val ↔
                e.v ∉ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val) →
              (rounds[i.val]'i.isLt).tree.wPop s_step ≤ e.weight) := by
      refine ⟨W.rounds, H_rem, conglomFn, W.hrounds_len, by simpa [H_rem] using hlen_rem,
        hsub_rem, hperm_es,
        by have hlen := congrArg List.length W.hmc_corr
           simpa [outRes, W.hmcLen] using hlen.symm,
        by have hmc_le_m : (W.rounds.flatMap PartitionRoundWitness.corrEdges).length ≤
               L.es.length := by
             have hlen := congrArg List.length W.hmc_corr
             simp only [List.length_map, ← W.hmcLen] at hlen; omega
           exact W.hmc_mem.congr fun x hx1 hx2 =>
             (hs4_agree_buf x (by dsimp only [outRes] at hx1 hx2 ⊢; omega)).trans
               (hs3_agree_pre x (by dsimp only [outRes] at hx1 hx2 ⊢; omega)),
        hhold_rem.congr fun x hx1 hx2 =>
          hs4_agree_buf x (by
            dsimp only [outRes] at hx1 hx2 ⊢
            simp only [H_rem, List.length_map, hlen_rem] at hx2; omega),
        fun u => hconglom_mem u, hconglom_surj,
        fun x y => by rw [← W.htree_w]; exact hconglom_rel x y,
        fun x => (W.hdead_iff x).mp (W.hdead_cov x.val x.isLt),
        fun i => ?_, fun i => ?_, fun i e he => ?_, W.hstop_prev,
        fun i j hij e he => (W.huncorr_tree i j hij e he).2⟩
      · have hi : i.val < W.rounds.length := i.isLt
        have hmt := W.hmeta i.val hi
        rcases hmt with ⟨hm0, hm1, hm2, hm3, hce, hcl, hvc, hp1, hp2, hp3,
          hinj, hsp, hgv, hts, hbi⟩
        have hce_sum : ((W.rounds.take i.val).map fun q => q.compLocal.length).sum +
            (W.rounds[i.val]'hi).compLocal.length ≤ L.es.length := by
          have h1 := list_take_sum_add_le (fun q => q.compLocal.length) W.rounds i.val hi
          rw [← W.hcEdgeLen] at h1
          have hfc := Finset.card_le_univ
            (Finset.univ.filter fun j : Fin L.es.length => W.edgeState0 j.val ≠ 0)
          rw [Fintype.card_fin] at hfc
          have := W.hclaim_card; omega
        have hcl_sum : ((W.rounds.take i.val).map PartitionRoundWitness.numVerts).sum +
            (W.rounds[i.val]'hi).numVerts ≤ 2 * n := by
          have h1 := list_take_sum_add_le PartitionRoundWitness.numVerts W.rounds i.val hi
          rw [← W.hcLiftLen] at h1
          have := W.hcl_dead; omega
        have hmem_s42 : ∀ addr < L.bufBase + 14 * n, s₄.mem addr = s₂.mem addr := fun addr ha =>
          (hs4_agree_buf addr (by omega)).trans (hs3_agree_pre addr (by omega))
        have hi_n : i.val < n := by have := W.hrounds_len; omega
        have ha_c0 := hmem_s42 (L.bufBase + 6 * n + 3 * i.val) (by omega)
        have ha_c1 := hmem_s42 (L.bufBase + 6 * n + 3 * i.val + 1) (by omega)
        have ha_c2 := hmem_s42 (L.bufBase + 6 * n + 3 * i.val + 2) (by omega)
        have ha_cl := hmem_s42 (L.bufBase + 9 * n + i.val) (by omega)
        dsimp only [outRes]
        rw [ha_c0, ha_c1, ha_c2, ha_cl]
        have hs_le_buf : s.frontier ≤ L.bufBase := by
          have := L.hoff_ge; have := L.hoff_adj; have := L.hadj_it
          have := L.hit_nd; have := L.hnd_buf; omega
        refine ⟨hm0, hm1,
          by rw [hm2, hs4_fr, hs3_fr, W.hfr]; omega,
          by rw [hm3, hs4_fr, hs3_fr, W.hfr]; omega,
          ⟨by rw [hm2]; omega, by rw [hm3]; omega⟩,
          ?_, fun k => ?_, hvc, hp1, hp2, hp3, hinj, hsp, hgv, hts, hbi⟩
        · refine hce.congr fun x hx1 hx2 =>
            (hs4_agree_buf x (by omega)).trans (hs3_agree_pre x (by omega))
        · have hk := k.isLt; rw [hm3]
          exact ((hs4_agree_buf _ (by omega)).trans (hs3_agree_pre _ (by omega))).trans
            (hm3 ▸ hcl k)
      · rcases W.hstop i with h1 | h2 | ⟨h3a, h3b⟩
        · exact .inl h1
        · exact .inr (.inl h2)
        · refine .inr (.inr ⟨h3a, fun e he => ?_⟩)
          obtain ⟨eIdx, he_in, rfl⟩ := List.mem_map.mp he
          exact h3b eIdx ((hiff_rem eIdx).mp he_in)
      · obtain ⟨eIdx, he_in, rfl⟩ := List.mem_map.mp he
        exact W.huncorr i eIdx ((hiff_rem eIdx).mp he_in)
    have hs_le_buf : s.frontier ≤ L.bufBase := by
      have := L.hoff_ge; have := L.hoff_adj; have := L.hadj_it
      have := L.hit_nd; have := L.hnd_buf; omega
    have hs4_fr_ub : s₄.frontier ≤ s.frontier + 72 * (L.es.length + n + 1) := by
      have hbuf_eq : L.bufBase = s.frontier + (2 * n + 4 * L.es.length + 1) +
          (3 * (2 * L.es.length + 1) + 12 * (4 * L.es.length + 1)) := by
        rw [← hbb_eq]; exact hs_bb
      have hres_tl : res.tLen ≤ n := W.htLen ▸ htl_le_n
      rw [hs4_fr, hs3_fr, W.hfr, hbuf_eq]; omega
    have hmc_div : res.mcLen ≤ L.es.length := hmc_len_le.trans (Nat.div_le_self _ _)
    refine ⟨hsafe, hvh, by rw [hst_eq]; exact hwf4, hst_eq ▸ hframe_s4,
      by rw [hst_eq, hs4_fr, hs3_fr, W.hfr]; omega,
      by rw [hst_eq]; exact hs4_fr_ub,
      hcost_bound, by rw [hres_eq]; exact hnc_le, by rw [hres_eq]; exact hmc_len_le,
      by rw [hres_eq]; exact hhRem2, by rw [hres_eq]; exact hcc2,
      by rw [hres_eq, hst_eq, hs4_fr, hs3_fr, W.hfr]; dsimp only [outRes]; omega,
      by rw [hres_eq, hst_eq, hs4_fr, hs3_fr, W.hfr]; dsimp only [outRes]; omega,
      by rw [hres_eq, hst_eq, hs4_fr, hs3_fr, W.hfr]; dsimp only [outRes]; omega,
      by rw [hres_eq, hst_eq, hs4_fr, hs3_fr, W.hfr]; dsimp only [outRes]; omega,
      by rw [hres_eq, hst_eq, hs4_fr]; dsimp only [outRes]; rw [hcc1]; omega,
      fun _ => by
        rw [hres_eq]; dsimp only [outRes]
        refine ⟨by omega, by omega, by omega, by omega, ?_⟩
        rw [hcc1, hs3_fr, W.hfr]; omega,
      ?_⟩
    rw [hres_eq, hst_eq]
    exact h_ex

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
