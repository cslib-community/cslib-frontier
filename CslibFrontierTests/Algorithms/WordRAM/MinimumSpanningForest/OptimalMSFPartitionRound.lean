/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.PrecompSearch
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.PartitionRound
import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Foundations.Data.List.Subperm
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Tests for `OptimalMSF.PartitionRound` (`pr02LoopBodyProg`)

Exercises `PR02LoopEnv`, `PR02LoopState`, `pr02LoopBodyProg`, `pr02LoopBodyProgSafe`,
`realizes_pr02LoopBodyProg`, and `pr02LoopBodyProg_spec`:

* Concrete small-graph witnesses (`nCur ≤ 4`) exercise 3-stage Borůvka contraction and halting
  (`cont = 0`), including non-empty `selLen = 1` prefix preservation, sentinel preservation, and an
  unconditional end-to-end `precomputeDTProg_spec` -> `pr02LoopBodyProg_spec` -> `boundedWhile` ->
  `Program .standard` lowering witness at `r0 = 24` (`w = 2 ^ (4 * 24 ^ 4 + 16) + 2`).
* `boundedWhile_pr02LoopBody_spec` and `twoRoundOuterProg` verify multi-round composition
  (`st.cont = 1`) symbolically.
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSFPartitionRound

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest
open CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport

/-! ## Helpers for `MSFLiftInv` and Concrete Test Memory Layout -/

private theorem msfLiftInv_of_indexed {n : ℕ} (esCur : List (IndexedEdge n))
    (hids : ∀ j (hj : j < esCur.length), (esCur[j]'hj).id = j) :
    MSFLiftInv (esCur.map IndexedEdge.toWeighted) [] esCur := by
  have hlt : ∀ e ∈ esCur, e.id < (esCur.map IndexedEdge.toWeighted).length := fun e he => by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he; rw [hids j hj, List.length_map]; exact hj
  have hmap_id : esCur.map IndexedEdge.id = List.range esCur.length :=
    List.ext_getElem (by simp) fun j hj1 _ => by
      simp only [List.getElem_map, List.getElem_range]; exact hids j (by simpa using hj1)
  refine ⟨List.nodup_nil, hmap_id ▸ List.nodup_range, hlt,
    fun _ hi => absurd hi List.not_mem_nil, fun L hL_sub hL_msf => ⟨L.pmap
      (fun e he => ⟨e.id, hlt e (hL_sub.subset he)⟩) (fun _ h => h),
      by simp [List.map_pmap, List.pmap_eq_map], ?_⟩⟩
  have hmap_eq : (L.pmap (fun e he => (⟨e.id, hlt e (hL_sub.subset he)⟩ :
        Fin (esCur.map IndexedEdge.toWeighted).length)) (fun _ h => h)).map
      (fun i => (esCur.map IndexedEdge.toWeighted)[i.val]) = L.map IndexedEdge.toWeighted :=
    List.ext_getElem (by simp) fun k _ hk2 => by
      have hk2' : k < L.length := by simpa using hk2
      obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp (hL_sub.subset (List.getElem_mem hk2'))
      simp only [List.getElem_map, List.getElem_pmap]
      have hid : (L[k]'hk2').id = j := by rw [← heq]; exact hids j hj
      simp_rw [hid, heq]
  simpa only [List.nil_append] using hmap_eq ▸ hL_msf

private abbrev triMultiEs : List (IndexedEdge 4) :=
  [⟨0, 1, 5, 0⟩, ⟨1, 2, 3, 1⟩, ⟨0, 2, 7, 2⟩, ⟨2, 3, 2, 3⟩, ⟨0, 3, 9, 4⟩]

private def triSuf : List ℕ := encodeIndexedEdges triMultiEs ++ [99, 77, 0, 0, 0, 0, 0]
private theorem triSuf_len : triSuf.length = 27 := by decide
private theorem triSuf_lt : ∀ x ∈ triSuf, x < 100 := by decide

private theorem triMulti_msfLiftInv :
    MSFLiftInv (triMultiEs.map IndexedEdge.toWeighted) [] triMultiEs :=
  msfLiftInv_of_indexed triMultiEs fun j hj => by
    have hj5 : j < 5 := by simpa [triMultiEs] using hj
    interval_cases j <;> rfl

private def testWords (r0 : ℕ) (tp : List ℕ) : List ℕ :=
  ([r0, 9, 31 + tp.length, 1, 4, 5, 9 + tp.length, 0] ++ tp) ++ triSuf

private theorem testWords_len (r0 : ℕ) (tp : List ℕ) :
    (testWords r0 tp).length = 35 + tp.length := by
  rw [testWords, List.length_append, List.length_append, triSuf_len]
  simp only [List.length_cons, List.length_nil]; omega

private theorem testWords_layout (r0 : ℕ) (tp : List ℕ) :
    ∀ j : Fin 8, (testWords r0 tp).getD j.val 0 =
      appendWords (WordEncoding.encode (α := PR02LoopEnv))
        (WordEncoding.encode (α := PR02LoopState))
        (⟨r0, 9, 31 + tp.length⟩, ⟨1, 4, 5, 9 + tp.length, 0⟩) j := by
  intro j; fin_cases j <;> rfl

private theorem testWords_inputFits {w r0 B : ℕ} {tp : List ℕ}
    (h16 : Fits w 16) (hr0 : Fits w r0) (htp : ∀ v ∈ tp, Fits w v)
    (hB : Fits w (36 + tp.length + B)) (h100 : 100 ≤ 36 + tp.length + B) :
    InputFits w (testWords r0 tp) := by
  refine ⟨hB.of_le (by rw [testWords_len]; omega), fun v hv => ?_⟩
  simp only [testWords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | h2) | h3
  exacts [hr0, h16.of_le (by decide), hB.of_le (by omega), h16.of_le (by decide),
    h16.of_le (by decide), h16.of_le (by decide), hB.of_le (by omega), fits_zero w,
    htp v h2, hB.of_le ((triSuf_lt v h3).le.trans h100)]

private theorem testWords_mem_suf (r0 : ℕ) (tp : List ℕ) (k : ℕ) (hk : k < 27)
    (a : ℕ) (ha : a = 9 + tp.length + k) :
    (Memory.State.init (testWords r0 tp)).mem a = triSuf[k]'(triSuf_len ▸ hk) := by
  subst ha; let pre := [r0, 9, 31 + tp.length, 1, 4, 5, 9 + tp.length, 0] ++ tp
  change (if 9 + tp.length + k = 0 then (pre ++ triSuf).length
    else (pre ++ triSuf).getD (9 + tp.length + k - 1) 0) = triSuf[k]'(triSuf_len ▸ hk)
  rw [ite_eq_right (by omega), show 9 + tp.length + k - 1 = pre.length + k by simp [pre]; omega,
    List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem (triSuf_len ▸ hk), Option.getD_some]

private theorem testWords_holds (r0 : ℕ) (tp : List ℕ) :
    HoldsIndexedEdges (9 + tp.length) triMultiEs (Memory.State.init (testWords r0 tp)).mem := by
  intro j hj; have hj5 : j < 5 := by simpa [triMultiEs] using hj
  have hm (off : ℕ) (ho : off < 4) := testWords_mem_suf r0 tp (4 * j + off) (by omega)
    (9 + tp.length + 4 * j + off) (by omega)
  interval_cases j <;>
    exact ⟨hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)⟩

private theorem testWords_sentinels {r0 : ℕ} {tp : List ℕ} {s' : Memory.State}
    (hmod : Memory.Modifies (Set.Ico (31 + tp.length) (31 + tp.length + 5))
      (Memory.State.init (testWords r0 tp)) s') :
    s'.mem (29 + tp.length) = 99 ∧ s'.mem (30 + tp.length) = 77 :=
  have hfr : (Memory.State.init (testWords r0 tp)).frontier = 36 + tp.length := by
    change (testWords r0 tp).length + 1 = 36 + tp.length; rw [testWords_len]; omega
  ⟨(hmod.2 _ (by omega) (by simp only [Set.mem_Ico]; omega)).trans
      (testWords_mem_suf r0 tp 20 (by decide) _ (by omega)),
    (hmod.2 _ (by omega) (by simp only [Set.mem_Ico]; omega)).trans
      (testWords_mem_suf r0 tp 21 (by decide) _ (by omega))⟩

/-! ## 1. Concrete Borůvka Exit and `pr02LoopBodyProg_spec` Halting Checks -/

private theorem triMulti_concrete_boruvka_exit {w : ℕ} (hw : Fits w 500) :
    let s₀ := Memory.State.init (testWords 24 [])
    let res := (Memory.spec 0).clientResult s₀ (boruvkaThreeStageProg ⟨4, 5, 9, 31, 0⟩)
    let s₁ := (Memory.spec 0).clientState s₀ (boruvkaThreeStageProg ⟨4, 5, 9, 31, 0⟩)
    res.numVertices = 0 ∧ res.numEdges = 0 ∧ s₁.mem 29 = 99 ∧ s₁.mem 30 = 77 ∧
    ∃ accIds : List (Fin 5), accIds.length = res.selOff ∧
      (∀ j (hj : j < accIds.length), s₁.mem (31 + j) = accIds[j].val) ∧
      IsMinSpanningForest (triMultiEs.map IndexedEdge.toWeighted)
        (accIds.map fun i => (triMultiEs.map IndexedEdge.toWeighted)[i.val]) := by
  intro s₀ res s₁
  have hwf : Memory.WellFormed w s₀ := Memory.wellFormed_init
    (testWords_inputFits (B := 464) (hw.of_le (by decide)) (hw.of_le (by decide))
      (fun _ h => absurd h List.not_mem_nil) hw (by decide))
    (hw.of_le (by rw [testWords_len]; decide))
  have hb3 := boruvkaThreeStageProg_spec (w := w) (n := 4) (nCur := 4) (edgeBase := 9)
    (selBase := 31) (es := triMultiEs.map IndexedEdge.toWeighted) (accIds := [])
    (esCur := triMultiEs) (s := s₀) (hw.of_le (by decide)) hwf (testWords_holds 24 [])
    (by decide) (fun _ hj => absurd hj (Nat.not_lt_zero _)) (by decide) triMulti_msfLiftInv
    (hw.of_le (by decide))
  rcases framedTriple_iff_realization.mp hb3 with ⟨_, _, hmod, hn8, _, _, _, _, _, _,
    acc1, es', hes'_len, _, _, hacc1_len, hacc1_mem, hinv1⟩
  have hnv0 : res.numVertices = 0 := by change 8 * res.numVertices ≤ 4 at hn8; omega
  have hesemp : es' = [] := by
    cases es' with | nil => rfl | cons e _ => exact Fin.elim0 (hnv0 ▸ e.u)
  obtain ⟨h29, h30⟩ := testWords_sentinels (r0 := 24) (tp := [])
    (hmod.mono fun x hx => by simp only [Set.mem_Ico, List.length_nil, add_zero] at hx ⊢; exact hx)
  obtain ⟨remIds, hrem_val, hrem_msf⟩ := hinv1.2.2.2.2 es' (List.Subperm.refl _)
    (by rw [hesemp, List.map_nil]; exact isMinSpanningForest_nil)
  rw [show remIds = [] by simpa [hesemp] using congrArg List.length hrem_val,
    List.append_nil] at hrem_msf
  exact ⟨hnv0, by change es'.length = res.numEdges at hes'_len; rw [← hes'_len, hesemp]; rfl,
    h29, h30, acc1, hacc1_len, hacc1_mem, hrem_msf⟩

private theorem empty_loopBody_spec_exit {w r0 tableBase tableFrontier n₀ : ℕ}
    (h16 : Fits w 16) (hr0_ge : 24 ≤ r0) (hr0_log : max 1 (Nat.iterLog 3 n₀) ≤ r0)
    (s₀ : Memory.State) (htf : tableFrontier ≤ s₀.frontier)
    (hwf : Memory.WellFormed w s₀) (htab : HoldsDTTable r0 tableBase s₀.mem)
    (htib : DTTableInBounds r0 tableBase tableFrontier s₀.mem) (hfit : Fits w (s₀.frontier + 100)) :
    let env : PR02LoopEnv := ⟨r0, tableBase, tableFrontier⟩
    let st : PR02LoopState := ⟨1, 0, 0, s₀.frontier, 0⟩
    pr02LoopBodyProgSafe w (env, st) s₀ ∧
    ((Memory.spec 0).clientResult s₀ (pr02LoopBodyProg (env, st))).cont = 0 ∧
    memoryCost (pr02LoopBodyProg (env, st)) s₀ ≤ 30 * optDepthMN 0 0 + 110 := by
  intro env st
  have hinv := msfLiftInv_of_indexed ([] : List (IndexedEdge 0))
    fun _ h => absurd h (Nat.not_lt_zero _)
  obtain ⟨hsafe, hft⟩ := pr02LoopBodyProg_spec (w := w) (n_orig := 0) (n₀ := n₀) (r0 := r0)
    (tableFrontier := tableFrontier) (nCur := 0) (es := []) (env := env) (st := st) (accIds := [])
    (esCur := []) (s := s₀) h16 hwf rfl hr0_ge hr0_log rfl rfl (Nat.zero_le _) (by simp) htab htib
    htf le_rfl (by simpa only [env, List.length_nil, add_zero] using htf)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (by simp [st]) rfl
    (fun _ h => absurd h (Nat.not_lt_zero _)) hinv
    (by simpa only [List.length_nil, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] using hfit)
  obtain ⟨_, _, _, _, _, hcont, _, hcont1, _, _, _, _, _, hc, _⟩ :=
    framedTriple_iff_realization.mp hft
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at hc
  exact ⟨hsafe, hcont.elim id fun h1 => False.elim <| by obtain ⟨hm, _⟩ := hcont1 h1; simp at hm,
    le_trans (Nat.le_add_right _ _) hc⟩

/-! ## 2. `pr02LoopBodyProg_spec` Sentinel and Non-empty Prefix Preservation -/

private theorem triMulti_loopBody_spec_facts {w r0 n₀ : ℕ} {tp : List ℕ}
    (h16 : Fits w 16) (hr0_ge : 24 ≤ r0) (hr0_log : max 1 (Nat.iterLog 3 n₀) ≤ r0)
    (hn₀ : 4 ≤ n₀) (htp_fits : ∀ v ∈ tp, Fits w v) (hr0_fit : Fits w r0)
    (htab : HoldsDTTable r0 9 (Memory.State.init (testWords r0 tp)).mem)
    (htib : DTTableInBounds r0 9 (9 + tp.length) (Memory.State.init (testWords r0 tp)).mem)
    (hfit : Fits w (36 + tp.length + 1200 * 5 + 750 * 4 + 2 * 5 * r0 + 100)) :
    let env : PR02LoopEnv := ⟨r0, 9, 31 + tp.length⟩
    let st : PR02LoopState := ⟨1, 4, 5, 9 + tp.length, 0⟩
    let s₀ := Memory.State.init (testWords r0 tp); let p := pr02LoopBodyProg (env, st)
    let st' := (Memory.spec 0).clientResult s₀ p; let s' := (Memory.spec 0).clientState s₀ p
    pr02LoopBodyProgSafe w (env, st) s₀ ∧ (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ p) ∧
    (st'.cont = 0 ∨ st'.numVerts = 0 ∧ st'.numEdges = 0) ∧
    (∀ a < 9 + tp.length, s'.mem a = s₀.mem a) ∧
    s'.mem (29 + tp.length) = 99 ∧ s'.mem (30 + tp.length) = 77 ∧
    memoryCost p s₀ ≤ 20000 * 5 + 5000 * 4 + 30 * optDepthMN 5 4 + 110 ∧
    ∃ accIds' : List (Fin 5), ∃ esNext : List (IndexedEdge st'.numVerts),
      esNext.length = st'.numEdges ∧ accIds'.length = st'.selLen ∧
      MSFLiftInv (triMultiEs.map IndexedEdge.toWeighted) accIds' esNext := by
  intro env st s₀ p st' s'
  have hfr : s₀.frontier = 36 + tp.length := by
    change (testWords r0 tp).length + 1 = 36 + tp.length; rw [testWords_len]; omega
  have hwf : Memory.WellFormed w s₀ := Memory.wellFormed_init
    (testWords_inputFits (B := 64) h16 hr0_fit htp_fits (hfit.of_le (by omega)) (by omega))
    (hfit.of_le (by rw [testWords_len]; omega))
  obtain ⟨hsafe, hft⟩ := pr02LoopBodyProg_spec (w := w) (n_orig := 4) (n₀ := n₀) (r0 := r0)
    (tableFrontier := 9 + tp.length) (nCur := 4) (es := triMultiEs.map IndexedEdge.toWeighted)
    (env := env) (st := st) (accIds := []) (esCur := triMultiEs) (s := s₀) h16 hwf rfl hr0_ge
    hr0_log rfl rfl hn₀ (by decide) htab htib (by omega) (by dsimp only [env]; omega)
    (by dsimp only [env]; simp only [List.length_map, List.length_cons, List.length_nil]; omega)
    (testWords_holds r0 tp)
    (by dsimp only [st]; simp only [List.length_cons, List.length_nil]; omega) rfl
    (fun _ hj => absurd hj (Nat.not_lt_zero _)) triMulti_msfLiftInv (by rw [hfr]; exact hfit)
  obtain ⟨hvh, _, hmod, _, _, hcont_or, _, hcont1, _, _, _, _, htf_pres, hcost_le,
    accIds', esNext, hnext_len, _, _, hacc'_len, _, hinv'⟩ := framedTriple_iff_realization.mp hft
  obtain ⟨h29, h30⟩ := testWords_sentinels hmod
  refine ⟨hsafe, hvh, ?_, htf_pres, h29, h30, le_trans (Nat.le_add_right _ _) hcost_le,
    accIds', esNext, hnext_len, hacc'_len, hinv'⟩
  rcases hcont_or with h0 | h1; · exact Or.inl h0
  · obtain ⟨_, h8v, _⟩ := hcont1 h1; have hnv0 : st'.numVerts = 0 := by dsimp only [st', p]; omega
    exact Or.inr ⟨hnv0, by cases esNext with | nil => simpa using hnext_len.symm | cons e _ =>
      exact Fin.elim0 (hnv0 ▸ e.u)⟩

private theorem singleton_bridge_nonzero_selLen_spec {w r0 tableBase tableFrontier n₀ selBuf : ℕ}
    (h16 : Fits w 16) (hr0_ge : 24 ≤ r0) (hr0_log : max 1 (Nat.iterLog 3 n₀) ≤ r0)
    (htf_le : tableFrontier ≤ selBuf) (s₀ : Memory.State) (hwf : Memory.WellFormed w s₀)
    (htf : tableFrontier ≤ s₀.frontier) (hsel_fr : selBuf + 1 ≤ s₀.frontier)
    (hmem0 : s₀.mem selBuf = 0) (htab : HoldsDTTable r0 tableBase s₀.mem)
    (htib : DTTableInBounds r0 tableBase tableFrontier s₀.mem) (hfit : Fits w (s₀.frontier + 100)) :
    let e : WeightedEdge 2 ℕ := ⟨0, 1, 2⟩; let env : PR02LoopEnv := ⟨r0, tableBase, selBuf⟩
    let st : PR02LoopState := ⟨1, 0, 0, s₀.frontier, 1⟩; let p := pr02LoopBodyProg (env, st)
    let st' := (Memory.spec 0).clientResult s₀ p; let s' := (Memory.spec 0).clientState s₀ p
    pr02LoopBodyProgSafe w (env, st) s₀ ∧ s'.mem selBuf = 0 ∧
    (∀ a < tableFrontier, s'.mem a = s₀.mem a) ∧ st'.selLen ≤ 1 ∧
    memoryCost p s₀ ≤ 30 * optDepthMN 0 0 + 110 ∧ ∃ accIds' : List (Fin 1),
      accIds'.length = st'.selLen ∧
      MSFLiftInv [e] accIds' ([] : List (IndexedEdge st'.numVerts)) := by
  intro e env st p st' s'
  have hinv : MSFLiftInv [e] [⟨0, by decide⟩] ([] : List (IndexedEdge 0)) := by
    have hf : (DisjointSet.Partition.discrete 2).rel e.u e.v = false := by decide
    refine ⟨by simp, List.nodup_nil, fun _ h => absurd h List.not_mem_nil,
      fun _ _ _ h => absurd h List.not_mem_nil, fun L hL _ => ⟨[], by
        rw [List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hL.length_le)]; rfl,
        ⟨⟨List.Subperm.refl _, isAcyclicFrom_cons.mpr ⟨hf, isAcyclicFrom_nil _⟩, rfl⟩,
          fun F' hF' => ?_⟩⟩⟩
    cases F' with
    | nil =>
      have h := congrArg (fun p : DisjointSet.Partition 2 => p.rel e.u e.v) hF'.2.2
      rw [show (edgePartition ([] : List (WeightedEdge 2 ℕ))).rel e.u e.v = false from hf,
        show (edgePartition [e]).rel e.u e.v = true by simp [edgePartition]] at h; cases h
    | cons f rest =>
      have hlen := hF'.1.length_le; simp only [List.length_cons, List.length_nil] at hlen
      obtain rfl : rest = [] := List.length_eq_zero_iff.mp (by omega)
      obtain rfl : f = e := List.mem_singleton.mp (hF'.1.subset List.mem_cons_self); exact le_rfl
  obtain ⟨hsafe, hft⟩ := pr02LoopBodyProg_spec (w := w) (n_orig := 2) (n₀ := n₀) (r0 := r0)
    (tableFrontier := tableFrontier) (nCur := 0) (es := [e]) (env := env) (st := st)
    (accIds := [⟨0, by decide⟩]) (esCur := []) (s := s₀) h16 hwf rfl hr0_ge hr0_log rfl rfl
    (Nat.zero_le _) le_rfl htab htib htf htf_le hsel_fr (fun _ hi => absurd hi (Nat.not_lt_zero _))
    (by simp [st]) rfl (fun j hj => by cases j with | zero => exact hmem0 | succ => simp at hj)
    hinv (by simpa only [List.length_nil, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] using hfit)
  obtain ⟨_, _, hmod, _, _, _, _, _, _, hne_le, _, _, htf_pres, hc,
    accIds', esNext, _, _, _, hacc'_len, _, hinv'⟩ := framedTriple_iff_realization.mp hft
  have hsum := hinv'.sum_le; simp only [List.length_singleton] at hsum
  have hne0 : esNext.length = 0 := by simp only [List.length_nil] at hne_le; omega
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at hc
  refine ⟨hsafe, ?_, htf_pres, hacc'_len ▸ (by omega : accIds'.length ≤ 1),
    le_trans (Nat.le_add_right _ _) hc, accIds', hacc'_len,
    (List.eq_nil_of_length_eq_zero hne0) ▸ hinv'⟩
  rw [hmod.2 selBuf (by omega) (by dsimp only [env, st]; simp only [Set.mem_Ico]; omega)]
  exact hmem0

/-! ## 3. Multi-Round `boundedWhile_potential_spec` Loop over `pr02LoopBodyProg_spec` -/

private theorem boundedWhile_pr02LoopBody_spec {w n_orig n₀ r0 tableFrontier nCur fuel eb sl : ℕ}
    {es : List (WeightedEdge n_orig ℕ)} {env : PR02LoopEnv} {accIds₀ : List (Fin es.length)}
    {esCur₀ : List (IndexedEdge nCur)} {s₀ : Memory.State} (h16 : Fits w 16)
    (hwf₀ : Memory.WellFormed w s₀) (hr0_env : env.r0 = r0) (hr0_ge : 24 ≤ r0)
    (hr0_log : max 1 (Nat.iterLog 3 n₀) ≤ r0) (hn_le_n0 : nCur ≤ n₀)
    (hn_le_2m : nCur ≤ 2 * esCur₀.length) (hfuel : esCur₀.length + 1 ≤ fuel)
    (htab₀ : HoldsDTTable r0 env.tableBase s₀.mem)
    (htib₀ : DTTableInBounds r0 env.tableBase tableFrontier s₀.mem)
    (htf₀ : tableFrontier ≤ s₀.frontier) (htf_sel : tableFrontier ≤ env.selBuf)
    (hsel_fr₀ : env.selBuf + es.length ≤ s₀.frontier) (hholds₀ : HoldsIndexedEdges eb esCur₀ s₀.mem)
    (hedges_fr₀ : eb + 4 * esCur₀.length ≤ s₀.frontier) (hacc_len₀ : accIds₀.length = sl)
    (hacc_mem₀ : ∀ j (hj : j < accIds₀.length), s₀.mem (env.selBuf + j) = accIds₀[j].val)
    (hinv₀ : MSFLiftInv es accIds₀ esCur₀) (hfit₀ : Fits w (s₀.frontier + 1200 * esCur₀.length +
      750 * nCur + 2 * esCur₀.length * r0 + 100)) :
    let st₀ : PR02LoopState := ⟨1, nCur, esCur₀.length, eb, sl⟩
    let prog := boundedWhile (fun _ (st : PR02LoopState) => st.cont = 1) pr02LoopBodyProg
      env fuel st₀
    let st' := (Memory.spec 0).clientResult s₀ prog; let s' := (Memory.spec 0).clientState s₀ prog
    whileSafe (fun _ (st : PR02LoopState) => st.cont = 1) pr02LoopBodyProg
      (fun w x s => pr02LoopBodyProgSafe w x s) w env fuel st₀ s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧ st'.cont ≠ 1 ∧
    Memory.Modifies (Set.Ico env.selBuf (env.selBuf + es.length)) s₀ s' ∧
    HoldsDTTable r0 env.tableBase s'.mem ∧ DTTableInBounds r0 env.tableBase tableFrontier s'.mem ∧
    memoryCost prog s₀ ≤
      20000 * esCur₀.length + 5000 * nCur + 30 * optDepthMN esCur₀.length nCur + 110 ∧
    ∃ (accIds' : List (Fin es.length)) (esFinal : List (IndexedEdge st'.numVerts)),
      esFinal.length = st'.numEdges ∧ accIds'.length = st'.selLen ∧
      MSFLiftInv es accIds' esFinal := by
  intro st₀ prog st' s'
  let cap := s₀.frontier + 1200 * esCur₀.length + 750 * nCur + 2 * esCur₀.length * r0 + 100
  let I : PR02LoopState → Memory.State → Prop := fun st s =>
    Memory.WellFormed w s ∧ tableFrontier ≤ s.frontier ∧ env.selBuf + es.length ≤ s.frontier ∧
    HoldsDTTable r0 env.tableBase s.mem ∧ DTTableInBounds r0 env.tableBase tableFrontier s.mem ∧
    s.frontier + (if st.cont = 1 then
      1200 * st.numEdges + 750 * st.numVerts + 2 * st.numEdges * r0 + 100 else 0) ≤ cap ∧
    ∃ esCur : List (IndexedEdge st.numVerts), ∃ accIds : List (Fin es.length),
      st.numVerts ≤ n₀ ∧ (st.cont = 1 → st.numVerts ≤ 2 * esCur.length) ∧
      st.numEdges = esCur.length ∧ HoldsIndexedEdges st.edgeBase esCur s.mem ∧
      st.edgeBase + 4 * esCur.length ≤ s.frontier ∧ accIds.length = st.selLen ∧
      (∀ j (hj : j < accIds.length), s.mem (env.selBuf + j) = accIds[j].val) ∧
      MSFLiftInv es accIds esCur
  let rank : PR02LoopState → Memory.State → ℕ := fun st _ =>
    if st.cont = 1 then st.numEdges + 1 else 0
  let pot : PR02LoopState → Memory.State → ℕ := fun st _ => if st.cont = 1 then
    20000 * st.numEdges + 5000 * st.numVerts + 30 * optDepthMN st.numEdges st.numVerts + 110 else 0
  have hbw := boundedWhile_potential_spec (fun _ (st : PR02LoopState) => st.cont = 1)
    pr02LoopBodyProg (fun w x s => pr02LoopBodyProgSafe w x s) w env 0 I rank pot
    (Set.Ico env.selBuf (env.selBuf + es.length))
    (fun st _ _ hr => if hc : st.cont = 1 then by simp only [rank, hc, ↓reduceIte] at hr; omega
      else hc)
    (fun st s hI hg => by
      rcases hI with ⟨hwf, htf, hsel, htab, htib, hcap, esCur, accIds, hn0, hn2m, hm_eq',
        hholds, hedges, hacc_len, hacc_mem, hinv⟩
      have hfit_step : Fits w (s.frontier + 1200 * esCur.length + 750 * st.numVerts +
          2 * esCur.length * r0 + 100) := by
        dsimp only [cap] at hcap; simp only [hg, ↓reduceIte] at hcap
        exact hfit₀.of_le (by rw [← hm_eq']; omega)
      obtain ⟨hsafe, hft⟩ := pr02LoopBodyProg_spec (w := w) (n_orig := n_orig) (n₀ := n₀)
        (r0 := r0) (tableFrontier := tableFrontier) (nCur := st.numVerts) (es := es) (env := env)
        (st := st) (accIds := accIds) (esCur := esCur) (s := s) h16 hwf hr0_env hr0_ge hr0_log
        rfl hm_eq' hn0 (hn2m hg) htab htib htf htf_sel hsel hholds (hm_eq' ▸ hedges) hacc_len
        hacc_mem hinv hfit_step
      obtain ⟨hvh, _, hmod, hs'_ge, hcap', _, _, hcont1, hnv_n0, _, heb', hwf', htf_pres,
        hpot_step, accIds', esNext, hnext_len, hnext_holds, _, hacc'_len, hacc'_mem, hinv'⟩ :=
        framedTriple_iff_realization.mp hft
      refine ⟨hsafe, hvh, ?_, hmod.mono (fun x hx => by simp only [Set.mem_Ico] at hx ⊢; omega),
        ?_, ?_⟩
      · dsimp only [pot]; simp only [hg, ↓reduceIte, add_zero]; exact hm_eq' ▸ hpot_step
      · refine ⟨hwf', htf.trans hs'_ge, hsel.trans hs'_ge, htab.congr htib htf_pres,
          htib.mono le_rfl htf_pres, ?_, esNext, accIds', hnv_n0,
          fun hc1 => hnext_len ▸ (hcont1 hc1).2.2.2.1, hnext_len.symm, hnext_holds,
          hnext_len ▸ heb', hacc'_len, hacc'_mem, hinv'⟩
        dsimp only [cap] at hcap ⊢; simp only [hg, ↓reduceIte] at hcap
        rw [← hm_eq'] at hcap'; omega
      · dsimp only [rank]; simp only [hg, ↓reduceIte]
        by_cases hc1 : ((Memory.spec 0).clientResult s (pr02LoopBodyProg (env, st))).cont = 1
        · simp only [hc1, ↓reduceIte]; obtain ⟨_, _, h2m, _⟩ := hcont1 hc1; omega
        · simp only [hc1, ↓reduceIte]; omega)
    fuel st₀ s₀ ⟨hwf₀, htf₀, hsel_fr₀, htab₀, htib₀,
      by dsimp only [cap, st₀]; simp only [↓reduceIte]; omega, esCur₀, accIds₀, hn_le_n0,
      fun _ => hn_le_2m, rfl, hholds₀, hedges_fr₀, hacc_len₀, hacc_mem₀, hinv₀⟩
    (by dsimp only [rank, st₀]; simp only [↓reduceIte]; exact hfuel)
  rcases hbw with ⟨hsafe_bw, hvh_bw, hng_bw, ⟨_, _, _, htab_bw, htib_bw, _, esFinal, accIds',
    _, _, hm_bw, _, _, hacc_bw, _, hinv_bw⟩, hmod_bw, hcost_bw⟩
  dsimp only [pot, st₀] at hcost_bw; simp only [↓reduceIte, Nat.zero_mul, add_zero] at hcost_bw
  exact ⟨hsafe_bw, hvh_bw, hng_bw, hmod_bw, htab_bw, htib_bw,
    le_trans (Nat.le_add_right _ _) hcost_bw, accIds', esFinal, hm_bw.symm, hacc_bw, hinv_bw⟩

/-! ## 4. Composite `realize` Pipeline and Width-Blind `Program .standard` Witnesses -/

private def twoRoundOuterProg (p : PR02LoopEnv × PR02LoopState) : Memory.Prog PR02LoopState := do
  let st₁ ← pr02LoopBodyProg p; if st₁.cont = 1 then pr02LoopBodyProg (p.1, st₁) else pure st₁

private def twoRoundOuterProgSafe (w : ℕ) (p : PR02LoopEnv × PR02LoopState)
    (s : Memory.State) : Prop :=
  Fits w 16 ∧ pr02LoopBodyProgSafe w p s ∧
  let st₁ := (Memory.spec 0).clientResult s (pr02LoopBodyProg p)
  (st₁.cont = 1 → pr02LoopBodyProgSafe w (p.1, st₁)
    ((Memory.spec 0).clientState s (pr02LoopBodyProg p)))

private theorem realizes_twoRoundOuterProg : Realizes .exact twoRoundOuterProg
    (appendWords (WordEncoding.encode (α := PR02LoopEnv))
      (WordEncoding.encode (α := PR02LoopState)))
    (WordEncoding.encode (α := PR02LoopState)) twoRoundOuterProgSafe (fun _ _ => 0) := by
  unfold twoRoundOuterProg; realize [realizes_pr02LoopBodyProg]
  all_goals
    have hfront := hmem.frontier_fits
    first | exact h.2.1 | exact h.2.2 (by assumption) | (have h16 := h.1; fits)

private theorem exists_standard_loopBody_multiwidth :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ _frontier : Fin r, ∃ out : Fin 5 → Fin r, ∀ w r0 n₀ : ℕ, ∀ tp : List ℕ,
        Fits w 16 → 24 ≤ r0 → max 1 (Nat.iterLog 3 n₀) ≤ r0 → 4 ≤ n₀ →
        (∀ v ∈ tp, Fits w v) → Fits w r0 →
        HoldsDTTable r0 9 (Memory.State.init (testWords r0 tp)).mem →
        DTTableInBounds r0 9 (9 + tp.length) (Memory.State.init (testWords r0 tp)).mem →
        Fits w (36 + tp.length + 1200 * 5 + 750 * 4 + 2 * 5 * r0 + 100) →
        ∃ y n, Runs w prog (State.init (testWords r0 tp)) ⟨pc, y⟩ n ∧
          (step w prog ⟨pc, y⟩ = .halt 0 ∨ y.regs (out 1) = 0 ∧ y.regs (out 2) = 0) ∧
          n + 1 ≤ C * (memoryCost (pr02LoopBodyProg
            (⟨r0, 9, 31 + tp.length⟩, ⟨1, 4, 5, 9 + tp.length, 0⟩))
            (Memory.State.init (testWords r0 tp)) + 1) + 1 := by
  obtain ⟨r, C, pc, prog, hnw, _frontier, out, hrun⟩ :=
    realizes_pr02LoopBodyProg.exists_standard_basis_init_program_state_from_words (0 : Fin 5)
  refine ⟨r, C, pc, stripRand prog, not_readsWidth_stripRand hnw, isRandFree_stripRand prog,
    _frontier, out, fun w r0 n₀ tp h16 hr0 hlog hn0 htp hr0f htab htib hfit => ?_⟩
  obtain ⟨hsafe, hvh, hexit, _⟩ :=
    triMulti_loopBody_spec_facts h16 hr0 hlog hn0 htp hr0f htab htib hfit
  let inp : PR02LoopEnv × PR02LoopState := (⟨r0, 9, 31 + tp.length⟩, ⟨1, 4, 5, 9 + tp.length, 0⟩)
  obtain ⟨y, n, hruns, hhalt, _, hregs, hsteps⟩ := hrun w inp (testWords r0 tp)
    (testWords_layout r0 tp) (by change 8 ≤ (testWords r0 tp).length; rw [testWords_len]; omega)
    (hfit.of_le (by rw [testWords_len]; omega))
    (testWords_inputFits (B := 64) h16 hr0f htp (hfit.of_le (by omega)) (by omega)) hsafe hvh
  have hres_w := clientResult_width (p := pr02LoopBodyProg inp)
    (s := Memory.State.init (testWords r0 tp)) w
  refine ⟨y, n, runs_stripRand hruns, ?_, by simpa using hsteps⟩
  rcases hexit with hc0 | ⟨hv0, he0⟩
  · left; exact step_stripRand_of_halt (by rw [hhalt, hres_w]; exact congrArg _ hc0)
  · right; exact ⟨by rw [hregs 1, hres_w]; exact hv0, by rw [hregs 2, hres_w]; exact he0⟩

private theorem exists_standard_twoRound_pipeline :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ _frontier : Fin r, ∃ out : Fin 5 → Fin r,
      ∀ w d words s₀, s₀ = Memory.State.init words → (∀ j : Fin 8, words.getD j.val 0 =
        appendWords (WordEncoding.encode (α := PR02LoopEnv))
          (WordEncoding.encode (α := PR02LoopState)) d j) →
        8 ≤ words.length → Fits w (words.length + 1) → InputFits w words →
        twoRoundOuterProgSafe w d s₀ → (Memory.spec w).ValidHistory s₀
          ((Memory.spec w).clientHistory s₀ (twoRoundOuterProg d)) →
        ∃ y n, Runs w prog (State.init words) ⟨pc, y⟩ n ∧
          y.regs (out 0) = ((Memory.spec w).clientResult s₀ (twoRoundOuterProg d)).cont ∧
          n + 1 ≤ C * (memoryCost (twoRoundOuterProg d) s₀ + 1) + 1 := by
  obtain ⟨r, C, pc, prog, hnw, _frontier, out, hrun⟩ :=
    realizes_twoRoundOuterProg.exists_standard_basis_init_program_state_from_words (0 : Fin 5)
  refine ⟨r, C, pc, stripRand prog, not_readsWidth_stripRand hnw, isRandFree_stripRand prog,
    _frontier, out, fun w d words s₀ hs₀ hl hlen hf hinf hsafe hvh => ?_⟩
  subst hs₀; obtain ⟨y, n, hruns, _, _, hregs, hsteps⟩ := hrun w d words hl hlen hf hinf hsafe hvh
  exact ⟨y, n, runs_stripRand hruns, hregs 0, by simpa using hsteps⟩

/-! ## 5. Unconditional Concrete End-to-End Witness (`r0 = 24`) -/

private def e2eTriWords : List ℕ := encodeIndexedEdges triMultiEs ++ [99, 77]
private theorem e2eTriWords_len : e2eTriWords.length = 22 := by decide
private theorem e2eTriWords_lt : ∀ x ∈ e2eTriWords, x < 100 := by decide

private theorem e2eTri_init_mem (k : ℕ) (hk : k < 22) :
    (Memory.State.init e2eTriWords).mem (1 + k) = e2eTriWords[k]'(e2eTriWords_len ▸ hk) := by
  rw [Nat.add_comm 1 k]; change e2eTriWords.getD k 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (e2eTriWords_len ▸ hk),
    Option.getD_some]

private theorem e2eTri_init_holds :
    HoldsIndexedEdges 1 triMultiEs (Memory.State.init e2eTriWords).mem := by
  intro j hj; have hj5 : j < 5 := by simpa [triMultiEs] using hj
  have hm (off : ℕ) (ho : off < 4) := e2eTri_init_mem (4 * j + off) (by omega)
  interval_cases j <;>
    exact ⟨hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)⟩

private theorem dtPrecompCost_of_two_le {r0 : ℕ} (hr : 2 ≤ r0) :
    dtPrecompCost r0 = 2 ^ (2 ^ (4 * r0 ^ 4 + 16)) := by
  have hnot1 : ¬(r0 ≤ 1) := by omega
  dsimp only [dtPrecompCost]; simp only [hnot1, ↓reduceIte]

private theorem add_lt_pow_succ {s k w : ℕ} (hs : s < 2 ^ k) (hw : w = k + 1) :
    s + 2 ^ k < 2 ^ w := by
  rw [hw, Nat.pow_succ', two_mul]; exact Nat.add_lt_add_right hs _

private theorem e2eTri_fits_60k_aux {w k : ℕ} (hk : 16 ≤ k) (hw : w = 2 ^ k + 2) :
    Fits w (60000 + 2 ^ (2 ^ k)) := by
  have hpow_ge : 2 ^ 16 ≤ 2 ^ (2 ^ k) :=
    (Nat.pow_le_pow_right (by decide) hk).trans Nat.lt_two_pow_self.le
  have h1 : 60000 + 2 ^ (2 ^ k) < 2 ^ (2 ^ k + 1) :=
    add_lt_pow_succ ((by decide : 60000 < 2 ^ 16).trans_le hpow_ge) rfl
  have h2 : 2 ^ (2 ^ k + 1) < 2 ^ w := by
    rw [hw]; exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  exact h1.trans h2

private theorem e2eTri_fits_60k {w : ℕ} (hw : w = 2 ^ (4 * 24 ^ 4 + 16) + 2) :
    Fits w (60000 + dtPrecompCost 24) := by
  rw [dtPrecompCost_of_two_le (by decide : 2 ≤ 24)]
  exact e2eTri_fits_60k_aux (k := 4 * 24 ^ 4 + 16) (Nat.le_add_left 16 _) hw

private theorem triMulti_msf_of_lift {m : ℕ} {accIds : List (Fin 5)}
    {esFinal : List (IndexedEdge m)}
    (hinv : MSFLiftInv (triMultiEs.map IndexedEdge.toWeighted) accIds esFinal) :
    ∃ remIds : List (Fin 5), IsMinSpanningForest (triMultiEs.map IndexedEdge.toWeighted)
      ((accIds ++ remIds).map fun i => (triMultiEs.map IndexedEdge.toWeighted)[i.val]) := by
  have hkmsf := kruskalEdges_isMinSpanningForest (esFinal.map IndexedEdge.toWeighted)
  obtain ⟨L, hL_sub, hL_eq⟩ := hkmsf.1.1.exists_map
  obtain ⟨remIds, _, hmsf⟩ := hinv.2.2.2.2 L hL_sub (hL_eq ▸ hkmsf)
  exact ⟨remIds, hmsf⟩

private def e2eTriMultiProg (_ : Unit) : Memory.Prog PR02LoopState := do
  let tb ← precomputeDTProg 24
  let selBuf ← Memory.allocDirty 5
  boundedWhile (fun _ (st : PR02LoopState) => 0 < st.cont) pr02LoopBodyProg
    ⟨24, tb, selBuf⟩ 2 ⟨1, 4, 5, 1, 0⟩

private def e2eTriMultiProgSafe (w : ℕ) (_ : Unit) (s : Memory.State) : Prop :=
  Fits w 24 ∧ precomputeDTProgSafe w 24 s ∧
  let tb := (Memory.spec 0).clientResult s (precomputeDTProg 24)
  let s₁ := (Memory.spec 0).clientState s (precomputeDTProg 24)
  Fits w (s₁.frontier + 5) ∧
  let s₂ : Memory.State := ⟨s₁.mem, s₁.frontier + 5⟩
  whileSafe (fun _ (st : PR02LoopState) => 0 < st.cont) pr02LoopBodyProg
    pr02LoopBodyProgSafe w ⟨24, tb, s₁.frontier⟩ 2 ⟨1, 4, 5, 1, 0⟩ s₂

private theorem realizes_e2eTriMultiProg : Realizes .exact e2eTriMultiProg
    WordEncoding.encode WordEncoding.encode e2eTriMultiProgSafe (fun _ _ => 2) := by
  unfold e2eTriMultiProg; realize [realizes_precomputeDTProg, realizes_pr02LoopBodyProg]
  all_goals
    have hfront := hmem.frontier_fits
    have h16 : Fits w 16 := h.1.of_le (by decide)
    have hf := h.2.2.1
    first
    | exact h.1 | exact h.2.1
    | exact whileWork_le (fun (_ : PR02LoopEnv) (st : PR02LoopState) => 0 < st.cont)
        pr02LoopBodyProg (fun _ _ => le_rfl) _ 2 _ _
    | fits
    | (intro _; dsimp only [e2eTriMultiProgSafe] at h
       refine whileSafe_imp (fun (_ : PR02LoopEnv) (st : PR02LoopState) => 0 < st.cont)
         (fun (_ : PR02LoopEnv) (st : PR02LoopState) => 0 < st.cont) (fun _ => Iff.rfl)
         (fun _ => rfl) ?_ h.2.2.2; exact fun _ _ _ hs => ⟨h.1, hs⟩)

private theorem e2eTriMulti_spec {w : ℕ} (hw : w = 2 ^ (4 * 24 ^ 4 + 16) + 2) :
    let s₀ := Memory.State.init e2eTriWords
    let tb := (Memory.spec 0).clientResult s₀ (precomputeDTProg 24)
    let s₁ := (Memory.spec 0).clientState s₀ (precomputeDTProg 24)
    let s₂ : Memory.State := ⟨s₁.mem, s₁.frontier + 5⟩
    let env : PR02LoopEnv := ⟨24, tb, s₁.frontier⟩
    let st₀ : PR02LoopState := ⟨1, 4, 5, 1, 0⟩
    let step1 := pr02LoopBodyProg (env, st₀)
    pr02LoopBodyProgSafe w (env, st₀) s₂ ∧
    (Memory.spec w).ValidHistory s₂ ((Memory.spec w).clientHistory s₂ step1) ∧
    ((Memory.spec 0).clientState s₂ step1).mem 21 = 99 ∧
    ((Memory.spec 0).clientState s₂ step1).mem 22 = 77 ∧
    e2eTriMultiProgSafe w () s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (e2eTriMultiProg ())) ∧
    ((Memory.spec 0).clientResult s₀ (e2eTriMultiProg ())).cont = 0 ∧
    ((Memory.spec 0).clientState s₀ (e2eTriMultiProg ())).mem 21 = 99 ∧
    ((Memory.spec 0).clientState s₀ (e2eTriMultiProg ())).mem 22 = 77 ∧
    ∃ (accIds' remIds : List (Fin 5)),
      accIds'.length = ((Memory.spec 0).clientResult s₀ (e2eTriMultiProg ())).selLen ∧
      (∀ j (hj : j < accIds'.length),
        ((Memory.spec 0).clientState s₀ (e2eTriMultiProg ())).mem (s₁.frontier + j) =
          accIds'[j].val) ∧
      IsMinSpanningForest (triMultiEs.map IndexedEdge.toWeighted)
        ((accIds' ++ remIds).map fun i => (triMultiEs.map IndexedEdge.toWeighted)[i.val]) := by
  intro s₀
  have hfr₀ : s₀.frontier = 23 := by change e2eTriWords.length + 1 = 23; rw [e2eTriWords_len]
  have h60k : Fits w (60000 + dtPrecompCost 24) := e2eTri_fits_60k hw
  clear hw
  have h16 : Fits w 16 := h60k.of_le ((by decide : 16 ≤ 60000).trans (Nat.le_add_right _ _))
  have h24 : Fits w 24 := h60k.of_le ((by decide : 24 ≤ 60000).trans (Nat.le_add_right _ _))
  have hinf : InputFits w e2eTriWords :=
    ⟨h60k.of_le ((by rw [e2eTriWords_len]; decide : e2eTriWords.length ≤ 60000).trans
      (Nat.le_add_right _ _)),
    fun v hv => h60k.of_le
      (((e2eTriWords_lt v hv).le.trans (by decide : 100 ≤ 60000)).trans (Nat.le_add_right _ _))⟩
  have hwf₀ : Memory.WellFormed w s₀ :=
    Memory.wellFormed_init hinf
      (h60k.of_le ((by rw [hfr₀]; decide : s₀.frontier ≤ 60000).trans (Nat.le_add_right _ _)))
  have hsafe_pre : precomputeDTProgSafe w 24 s₀ := by
    rw [precomputeDTProgSafe_iff, hfr₀]
    exact h60k.of_le (Nat.add_le_add_right (by decide) _)
  have hpre := precomputeDTProg_spec hwf₀ hsafe_pre
  have hpre_r := framedTriple_iff_realization.mp hpre
  set tb := (Memory.spec 0).clientResult s₀ (precomputeDTProg 24)
  set s₁ := (Memory.spec 0).clientState s₀ (precomputeDTProg 24)
  rcases hpre_r with ⟨hv₁, _, hmod₁, hwf₁, hs₁_fr, htab₁, htib₁⟩
  have hs₁_ge : s₀.frontier ≤ s₁.frontier := hmod₁.1
  let s₂ : Memory.State := ⟨s₁.mem, s₁.frontier + 5⟩
  have hfit_alloc : Fits w (s₁.frontier + 5) := h60k.of_le (by rw [hfr₀] at hs₁_fr; omega)
  have hwf₂ : Memory.WellFormed w s₂ := ⟨hfit_alloc, hwf₁.mem_fits⟩
  have hs₂_21 : s₂.mem 21 = 99 :=
    (hmod₁.2 21 (by rw [hfr₀]; decide) (Set.notMem_empty _)).trans (e2eTri_init_mem 20 (by decide))
  have hs₂_22 : s₂.mem 22 = 77 :=
    (hmod₁.2 22 (by rw [hfr₀]; decide) (Set.notMem_empty _)).trans (e2eTri_init_mem 21 (by decide))
  have hholds₂ : HoldsIndexedEdges 1 triMultiEs s₂.mem :=
    e2eTri_init_holds.congr fun a _ ha =>
      hmod₁.2 a (by rw [hfr₀]; have : triMultiEs.length = 5 := rfl; omega) (Set.notMem_empty _)
  let env : PR02LoopEnv := ⟨24, tb, s₁.frontier⟩
  let st₀ : PR02LoopState := ⟨1, 4, 5, 1, 0⟩
  have htri_len : triMultiEs.length = 5 := rfl
  have htri_wlen : (triMultiEs.map IndexedEdge.toWeighted).length = 5 := rfl
  have hfit_step1 : Fits w (s₂.frontier + 1200 * 5 + 750 * 4 + 2 * 5 * 24 + 100) :=
    h60k.of_le (by dsimp only [s₂]; rw [hfr₀] at hs₁_fr; omega)
  have hstep1 := pr02LoopBodyProg_spec (w := w) (n_orig := 4) (n₀ := 4) (r0 := 24)
    (tableFrontier := s₁.frontier) (nCur := 4) (es := triMultiEs.map IndexedEdge.toWeighted)
    (env := env) (st := st₀) (accIds := []) (esCur := triMultiEs) (s := s₂)
    h16 hwf₂ rfl le_rfl (by decide) rfl htri_len le_rfl (by simp [htri_len]) htab₁ htib₁
    (by dsimp only [s₂]; omega) le_rfl (by dsimp only [env, s₂]; rw [htri_wlen])
    hholds₂ (by dsimp only [st₀, s₂]; rw [hfr₀] at hs₁_ge; omega) rfl
    (fun _ hj => absurd hj (Nat.not_lt_zero _)) triMulti_msfLiftInv
    (by rw [htri_len]; exact hfit_step1)
  obtain ⟨hsafe1, hft1⟩ := hstep1
  obtain ⟨hv_step1, _, hmod_step1, _⟩ := framedTriple_iff_realization.mp hft1
  have hs1'_21 : ((Memory.spec 0).clientState s₂ (pr02LoopBodyProg (env, st₀))).mem 21 = 99 := by
    rw [hmod_step1.2 21 (by dsimp only [s₂]; rw [hfr₀] at hs₁_ge; omega)
      (by dsimp only [env, st₀]; simp only [Set.mem_Ico]; rw [hfr₀] at hs₁_ge; omega)]
    exact hs₂_21
  have hs1'_22 : ((Memory.spec 0).clientState s₂ (pr02LoopBodyProg (env, st₀))).mem 22 = 77 := by
    rw [hmod_step1.2 22 (by dsimp only [s₂]; rw [hfr₀] at hs₁_ge; omega)
      (by dsimp only [env, st₀]; simp only [Set.mem_Ico]; rw [hfr₀] at hs₁_ge; omega)]
    exact hs₂_22
  let cap := s₂.frontier + 1200 * 5 + 750 * 4 + 2 * 5 * 24 + 100
  let I : PR02LoopState → Memory.State → Prop := fun st s =>
    Memory.WellFormed w s ∧ s₁.frontier ≤ s.frontier ∧ s₁.frontier + 5 ≤ s.frontier ∧
    HoldsDTTable 24 tb s.mem ∧ DTTableInBounds 24 tb s₁.frontier s.mem ∧
    s.frontier + (if st.cont = 1 then
      1200 * st.numEdges + 750 * st.numVerts + 2 * st.numEdges * 24 + 100 else 0) ≤ cap ∧
    (st.cont = 0 ∨ st.cont = 1) ∧
    ∃ esCur : List (IndexedEdge st.numVerts),
      ∃ accIds : List (Fin (triMultiEs.map IndexedEdge.toWeighted).length),
      st.numVerts ≤ 4 ∧ (st.cont = 1 → st.numVerts ≤ 2 * esCur.length) ∧
      st.numEdges = esCur.length ∧ HoldsIndexedEdges st.edgeBase esCur s.mem ∧
      st.edgeBase + 4 * esCur.length ≤ s.frontier ∧ accIds.length = st.selLen ∧
      (∀ j (hj : j < accIds.length), s.mem (s₁.frontier + j) = accIds[j].val) ∧
      MSFLiftInv (triMultiEs.map IndexedEdge.toWeighted) accIds esCur
  let rank : PR02LoopState → Memory.State → ℕ := fun st _ =>
    if 0 < st.cont then (if st.numEdges = 0 then 1 else 2) else 0
  let pot : PR02LoopState → Memory.State → ℕ := fun st _ => if 0 < st.cont then
    20000 * st.numEdges + 5000 * st.numVerts + 30 * optDepthMN st.numEdges st.numVerts + 110 else 0
  let guard : PR02LoopEnv → PR02LoopState → Prop := fun _ st => 0 < st.cont
  have hbw := boundedWhile_potential_spec guard pr02LoopBodyProg
    (fun w x s => pr02LoopBodyProgSafe w x s) w env 0 I rank pot
    (Set.Ico s₁.frontier (s₁.frontier + 5))
    (fun st _ _ hr => by
      dsimp only [rank, guard] at hr ⊢; split_ifs at hr with hg; exact hg)
    (fun st s hI hg => by
      rcases hI with ⟨hwf, hsf, hsel, htab, htib, hcap, h01, esCur, accIds, hnv4, hn2m, hm_eq,
        hholds, hedges, hacc_len, hacc_mem, hinv⟩
      have hc1 : st.cont = 1 := h01.elim (fun h0 => by omega) id
      have hfit_st : Fits w (s.frontier + 1200 * esCur.length + 750 * st.numVerts +
          2 * esCur.length * 24 + 100) := by
        dsimp only [cap] at hcap; simp only [hc1, ↓reduceIte] at hcap
        exact hfit_step1.of_le (by rw [← hm_eq]; omega)
      obtain ⟨hsafe, hft⟩ := pr02LoopBodyProg_spec (w := w) (n_orig := 4) (n₀ := 4) (r0 := 24)
        (tableFrontier := s₁.frontier) (nCur := st.numVerts)
        (es := triMultiEs.map IndexedEdge.toWeighted) (env := env) (st := st) (accIds := accIds)
        (esCur := esCur) (s := s) h16 hwf rfl le_rfl (by decide) rfl hm_eq hnv4 (hn2m hc1) htab
        htib hsf le_rfl (by dsimp only [env]; rw [htri_wlen]; exact hsel) hholds
        (hm_eq ▸ hedges) hacc_len hacc_mem hinv hfit_st
      obtain ⟨hvh, _, hmod, hs'_ge, hcap', h01', _, hcont1, hnv_n0, _, heb', hwf', htf_pres,
        hpot_step, accIds', esNext, hnext_len, hnext_holds, _, hacc'_len, hacc'_mem, hinv'⟩ :=
        framedTriple_iff_realization.mp hft
      refine ⟨hsafe, hvh, ?_, hmod.mono (fun x hx => by
          dsimp only [env] at hx; simp only [Set.mem_Ico] at hx ⊢; rw [htri_wlen] at hx; omega),
        ?_, ?_⟩
      · dsimp only [pot, guard] at hg ⊢; simp only [hg, ↓reduceIte, add_zero]
        by_cases hgt : 0 < ((Memory.spec 0).clientResult s (pr02LoopBodyProg (env, st))).cont
        · have hc1' : ((Memory.spec 0).clientResult s (pr02LoopBodyProg (env, st))).cont = 1 :=
            h01'.elim (fun h0 => by omega) id
          simp only [hgt, ↓reduceIte]
          simp only [hc1', ↓reduceIte] at hpot_step; exact hm_eq ▸ hpot_step
        · simp only [hgt, ↓reduceIte, add_zero]
          have h0' : ((Memory.spec 0).clientResult s (pr02LoopBodyProg (env, st))).cont = 0 := by
            omega
          simp only [h0', Nat.zero_ne_one, ↓reduceIte, add_zero] at hpot_step
          exact hm_eq ▸ hpot_step
      · refine ⟨hwf', hsf.trans hs'_ge, hsel.trans hs'_ge, htab.congr htib htf_pres,
          htib.mono le_rfl htf_pres, ?_, h01', esNext, accIds', hnv_n0,
          fun hc => hnext_len ▸ (hcont1 hc).2.2.2.1, hnext_len.symm, hnext_holds,
          hnext_len ▸ heb', hacc'_len, hacc'_mem, hinv'⟩
        dsimp only [cap] at hcap ⊢; simp only [hc1, ↓reduceIte] at hcap
        rw [← hm_eq] at hcap'; omega
      · dsimp only [rank, guard] at hg ⊢; simp only [hg, ↓reduceIte]
        by_cases hm0 : st.numEdges = 0
        · have hesc0 : esCur.length = 0 := hm_eq ▸ hm0
          by_cases hgt : 0 < ((Memory.spec 0).clientResult s (pr02LoopBodyProg (env, st))).cont
          · have hc1' : ((Memory.spec 0).clientResult s (pr02LoopBodyProg (env, st))).cont = 1 :=
              h01'.elim (fun h0 => by omega) id
            obtain ⟨hm1, _⟩ := hcont1 hc1'; omega
          · simp [hm0, hgt]
        · by_cases hgt : 0 < ((Memory.spec 0).clientResult s (pr02LoopBodyProg (env, st))).cont
          · have hc1' : ((Memory.spec 0).clientResult s (pr02LoopBodyProg (env, st))).cont = 1 :=
              h01'.elim (fun h0 => by omega) id
            obtain ⟨_, h8v, _⟩ := hcont1 hc1'
            have hnv0 : ((Memory.spec 0).clientResult s (pr02LoopBodyProg (env, st))).numVerts =
                0 := by omega
            have hesemp : esNext = [] := by
              cases esNext with | nil => rfl | cons e _ => exact Fin.elim0 (hnv0 ▸ e.u)
            have hne0 : ((Memory.spec 0).clientResult s (pr02LoopBodyProg (env, st))).numEdges =
                0 := by rw [← hnext_len, hesemp]; rfl
            simp [hm0, hgt, hne0]
          · simp [hm0, hgt])
    2 st₀ s₂ ⟨hwf₂, by dsimp only [s₂]; omega, by dsimp only [s₂]; omega, htab₁, htib₁,
      by dsimp only [cap, st₀]; simp only [↓reduceIte]; omega, Or.inr rfl, triMultiEs, [],
      by decide, fun _ => by dsimp only [st₀]; rw [htri_len]; decide, htri_len, hholds₂,
      by dsimp only [st₀, s₂]; rw [hfr₀] at hs₁_ge; omega, rfl,
      fun _ hj => absurd hj (Nat.not_lt_zero _), triMulti_msfLiftInv⟩
    (by dsimp only [rank, st₀]; simp)
  rcases hbw with ⟨hsafe_bw, hvh_bw, hng_bw, hI_bw, hmod_bw, _⟩
  rcases hI_bw with ⟨_, _, _, _, _, _, h01_end, esFinal, accIds', _, _, _, _, _,
    hacc'_len, hacc'_mem, hinv'⟩
  have he2e_eq : e2eTriMultiProg () = (precomputeDTProg 24 >>= fun tb' =>
      Memory.allocDirty 5 >>= fun selBuf' =>
        boundedWhile guard pr02LoopBodyProg ⟨24, tb', selBuf'⟩ 2 st₀) := rfl
  have hsafe_e2e : e2eTriMultiProgSafe w () s₀ :=
    ⟨h24, hsafe_pre, by change Fits w (s₁.frontier + 5); exact hfit_alloc, by
      change whileSafe guard pr02LoopBodyProg pr02LoopBodyProgSafe w env 2 st₀ s₂
      exact hsafe_bw⟩
  have hvh_e2e : (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (e2eTriMultiProg ())) := by
    rw [he2e_eq]; refine validHistory_bind_step hv₁ ?_
    change (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁
      (Memory.allocDirty 5 >>= fun selBuf' =>
        boundedWhile guard pr02LoopBodyProg ⟨24, tb, selBuf'⟩ 2 st₀))
    refine validHistory_allocDirty_bind hfit_alloc ?_
    exact hvh_bw
  have hres_e2e : (Memory.spec 0).clientResult s₀ (e2eTriMultiProg ()) =
      (Memory.spec 0).clientResult s₂ (boundedWhile guard pr02LoopBodyProg env 2 st₀) := by
    rw [he2e_eq, StateTransitionSpec.clientResult_bind]
    change (Memory.spec 0).clientResult s₁ (Memory.allocDirty 5 >>= fun selBuf' =>
      boundedWhile guard pr02LoopBodyProg ⟨24, tb, selBuf'⟩ 2 st₀) = _
    rw [clientResult_bind_allocDirty]
  have hst_e2e : (Memory.spec 0).clientState s₀ (e2eTriMultiProg ()) =
      (Memory.spec 0).clientState s₂ (boundedWhile guard pr02LoopBodyProg env 2 st₀) := by
    rw [he2e_eq, StateTransitionSpec.clientState_bind]
    change (Memory.spec 0).clientState s₁ (Memory.allocDirty 5 >>= fun selBuf' =>
      boundedWhile guard pr02LoopBodyProg ⟨24, tb, selBuf'⟩ 2 st₀) = _
    rw [clientState_bind_allocDirty]
  have hcont0_bw : ((Memory.spec 0).clientResult s₂
      (boundedWhile guard pr02LoopBodyProg env 2 st₀)).cont = 0 := by
    dsimp only [guard] at hng_bw; exact Nat.eq_zero_of_not_pos hng_bw
  have hbw_21 : ((Memory.spec 0).clientState s₂
      (boundedWhile guard pr02LoopBodyProg env 2 st₀)).mem 21 = 99 := by
    rw [hmod_bw.2 21 (by dsimp only [s₂]; rw [hfr₀] at hs₁_ge; omega)
      (by simp only [Set.mem_Ico]; rw [hfr₀] at hs₁_ge; omega)]; exact hs₂_21
  have hbw_22 : ((Memory.spec 0).clientState s₂
      (boundedWhile guard pr02LoopBodyProg env 2 st₀)).mem 22 = 77 := by
    rw [hmod_bw.2 22 (by dsimp only [s₂]; rw [hfr₀] at hs₁_ge; omega)
      (by simp only [Set.mem_Ico]; rw [hfr₀] at hs₁_ge; omega)]; exact hs₂_22
  obtain ⟨remIds, hmsf⟩ := triMulti_msf_of_lift hinv'
  exact ⟨hsafe1, hv_step1, hs1'_21, hs1'_22, hsafe_e2e, hvh_e2e,
    hres_e2e ▸ hcont0_bw, hst_e2e ▸ hbw_21, hst_e2e ▸ hbw_22,
    accIds', remIds, hres_e2e ▸ hacc'_len, fun j hj => hst_e2e ▸ hacc'_mem j hj, hmsf⟩

private theorem exists_standard_e2e_triMulti :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ frontier : Fin r, ∃ _out : Fin 5 → Fin r,
      ∀ w : ℕ, w = 2 ^ (4 * 24 ^ 4 + 16) + 2 →
        ∃ y n, Runs w prog (State.init e2eTriWords) ⟨pc, y⟩ n ∧
          step w prog ⟨pc, y⟩ = .halt 0 ∧
          (memoryState frontier y).mem 21 = 99 ∧
          (memoryState frontier y).mem 22 = 77 ∧
          n + 1 ≤ C * (memoryCost (e2eTriMultiProg ())
            (Memory.State.init e2eTriWords) + 1) + 1 := by
  obtain ⟨r, C, pc, prog, hnw, frontier, out, hrun⟩ :=
    realizes_e2eTriMultiProg.exists_standard_basis_init_program_state_from_words (0 : Fin 5)
  refine ⟨r, 3 * C, pc, stripRand prog, not_readsWidth_stripRand hnw, isRandFree_stripRand prog,
    frontier, out, fun w hw => ?_⟩
  have h60k : Fits w (60000 + dtPrecompCost 24) := e2eTri_fits_60k hw
  obtain ⟨_, _, _, _, hsafe, hvh, hcont0, h21, h22, _⟩ := e2eTriMulti_spec hw
  clear hw
  have hinf : InputFits w e2eTriWords :=
    ⟨h60k.of_le ((by rw [e2eTriWords_len]; decide : e2eTriWords.length ≤ 60000).trans
      (Nat.le_add_right _ _)),
    fun v hv => h60k.of_le
      (((e2eTriWords_lt v hv).le.trans (by decide : 100 ≤ 60000)).trans (Nat.le_add_right _ _))⟩
  obtain ⟨y, n, hruns, hhalt, hmem_st, _, hsteps⟩ := hrun w () e2eTriWords
    (fun j => Fin.elim0 j) (by rw [e2eTriWords_len]; decide)
    (h60k.of_le ((by rw [e2eTriWords_len]; decide : e2eTriWords.length + 1 ≤ 60000).trans
      (Nat.le_add_right _ _))) hinf hsafe hvh
  have hres_w := clientResult_width (p := e2eTriMultiProg ()) (s := Memory.State.init e2eTriWords) w
  have hst_w := clientState_width (p := e2eTriMultiProg ()) (s := Memory.State.init e2eTriWords) w
  have hmul : C * (memoryCost (e2eTriMultiProg ()) (Memory.State.init e2eTriWords) + 2 + 1) ≤
      3 * C * (memoryCost (e2eTriMultiProg ()) (Memory.State.init e2eTriWords) + 1) := by
    rw [Nat.mul_comm 3 C, Nat.mul_assoc]; exact Nat.mul_le_mul_left C (by omega)
  refine ⟨y, n, runs_stripRand hruns,
    step_stripRand_of_halt (by rw [hhalt, hres_w]; exact congrArg _ hcont0),
    by rw [hmem_st, hst_w]; exact h21, by rw [hmem_st, hst_w]; exact h22,
    le_trans hsteps (Nat.add_le_add_right hmul 1)⟩

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSFPartitionRound
