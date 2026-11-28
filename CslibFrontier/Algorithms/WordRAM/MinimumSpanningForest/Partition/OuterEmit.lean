/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.OuterOps
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.DjpLoop
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Collect
import CslibFrontier.DataStructure.Memory.Frame

/-!
# Post-DJP Component Emission, Corrupted Edges, and Metadata for `Partition`

Steps toward Theorem 5.8 of [PettieRamachandran2002] (#8624), verifying post-DJP edge emission
(`partEmitComp_spec`), corrupted-edge collection and emission (`partRoundFinish_corr_spec`),
dead-vertex and lift-array marking (`partMarkDeadLoop_spec`), and round metadata writes
(`partWriteRoundMeta_spec`) (§3.1, p. 20; §3.2, pp. 21–22; §5.1, pp. 25–26).

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partEmitComp_spec`: verifies CSR component-edge
  emission and active/dead edge marking via potential reduction on `remDeg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partRoundFinish_corr_spec`: verifies corrupted
  Soft-Heap item collection and `M_C` edge emission with `16 * ΔmcLen ≤ ΔitemCount`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partMarkDeadLoop_spec`,
  `partWriteRoundMeta_spec`: verifies dead-vertex marking, lift emission, and round metadata.

## References

* [S. Pettie and V. Ramachandran, *An Optimal Minimum Spanning Tree
  Algorithm*][PettieRamachandran2002]
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest
open Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

/-! ## Shared Framing, List, and Card Helpers -/

private theorem edge_lt_bufBase {w n : ℕ} (L : PartLayout w n) :
    L.edgeBase + 4 * L.es.length ≤ L.bufBase := by
  have h1 := L.edge_lt_itemBase; have h2 := L.hit_nd; have h3 := L.hnd_buf; omega

private theorem csr_lt_bufBase {w n : ℕ} (L : PartLayout w n) :
    L.offBase + n + 1 ≤ L.adjBase ∧ L.adjBase + 4 * L.es.length ≤ L.bufBase := by
  have h1 := L.csr_lt_itemBase; have h2 := L.hit_nd; have h3 := L.hnd_buf; exact ⟨h1.1, by omega⟩

/-- Preserves indexed-edge and CSR layout predicates under memory agreement below `L.bufBase`. -/
theorem partCongrEdges_of_agree_buf {w n : ℕ} (L : PartLayout w n) {m₁ m₂ : ℕ → ℕ}
    (hagree : ∀ x < L.bufBase, m₂ x = m₁ x) :
    (HoldsIndexedEdges L.edgeBase L.es m₁ → HoldsIndexedEdges L.edgeBase L.es m₂) ∧
    (HoldsUndirCSR L.offBase L.adjBase L.es m₁ → HoldsUndirCSR L.offBase L.adjBase L.es m₂) :=
  L.congr_below_itemBase fun x hx =>
    hagree x (by have h2 := L.hit_nd; have h3 := L.hnd_buf; omega)

/-- Preserves `SHInv` when all memory writes lie at or above `L.bufBase`. -/
theorem partCongrSh_of_mod_ge {w n ic nc : ℕ} (L : PartLayout w n) {h : SHHandle}
    (hib : h.itemBase = L.itemBase) (hnb : h.nodeBase = L.nodeBase)
    {roots : List SHTree} {created : ℕ → ℕ} {s s' : Memory.State}
    (hsh : SHInv w ic nc (2 * L.es.length) (4 * L.es.length) h roots created s)
    (hwf' : Memory.WellFormed w s') (hfr' : s'.frontier = s.frontier)
    (hmod : ∀ x, s'.mem x ≠ s.mem x → L.bufBase ≤ x) :
    SHInv w ic nc (2 * L.es.length) (4 * L.es.length) h roots created s' :=
  hsh.congr_outside hwf' hfr' fun a ha => by_contra fun hne =>
    absurd (L.inSHPool_lt_bufBase hib hnb ha) (by have := hmod a hne; omega)

private theorem finList_of_natList {m : ℕ} (l : List ℕ) (hlt : ∀ x ∈ l, x < m) :
    ∃ fl : List (Fin m), fl.map Fin.val = l :=
  ⟨l.pmap Fin.mk hlt, by simp [List.map_pmap]⟩

private theorem filter_ne_zero_card_lt {m : ℕ} (f : Fin m → ℕ) (e : Fin m) (he : f e = 0) :
    (Finset.univ.filter fun i : Fin m => f i ≠ 0).card < m := by
  have hlt : Finset.univ.filter (fun i : Fin m => f i ≠ 0) ⊂ (Finset.univ : Finset (Fin m)) :=
    Finset.ssubset_univ_iff.mpr fun heq => by
      have : e ∈ Finset.univ.filter (fun i : Fin m => f i ≠ 0) := by
        rw [heq]; exact Finset.mem_univ _
      exact (Finset.mem_filter.mp this).2 he
  simpa [Fintype.card_fin] using Finset.card_lt_card hlt

private theorem card_filter_ne_zero_add_one {m : ℕ} (f g : Fin m → ℕ) (e : Fin m)
    (hf0 : f e = 0) (hg_ne : g e ≠ 0) (hg_eq : ∀ i : Fin m, i ≠ e → g i = f i) :
    (Finset.univ.filter fun i : Fin m => f i ≠ 0).card + 1 ≤
      (Finset.univ.filter fun i : Fin m => g i ≠ 0).card := by
  have he_not : e ∉ Finset.univ.filter fun i : Fin m => f i ≠ 0 := by simp [hf0]
  have hsub : insert e (Finset.univ.filter fun i : Fin m => f i ≠ 0) ⊆
      Finset.univ.filter fun i : Fin m => g i ≠ 0 := by
    intro i hi
    rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi_old
    · exact hg_ne
    · have hne : i ≠ e := fun h => he_not (h ▸ hi_old)
      rw [hg_eq i hne]; exact (Finset.mem_filter.mp hi_old).2
  simpa [Finset.card_insert_of_notMem he_not] using Finset.card_le_card hsub

/-! ## Local Edge Emission and CSR Component Scan -/

private theorem partWriteLocalEdge_spec {w n size edgeBase localBase dstBase eIdx cEdgeLen : ℕ}
    {es : List (IndexedEdge n)} {lift : Fin size → Fin n} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s) (hin : HoldsIndexedEdges edgeBase es s.mem)
    (he_lt : eIdx < es.length) (hc_fit : Fits w (cEdgeLen + 1))
    (he_mem : edgeBase + 4 * eIdx + 3 < s.frontier)
    (hd_mem : dstBase + 4 * cEdgeLen + 3 < s.frontier)
    (hlu_lt : localBase + (es[eIdx]).u.val < s.frontier)
    (hlv_lt : localBase + (es[eIdx]).v.val < s.frontier)
    (hlu : ∃ lu : Fin size, s.mem (localBase + (es[eIdx]).u.val) = lu.val ∧
      lift lu = (es[eIdx]).u)
    (hlv : ∃ lv : Fin size, s.mem (localBase + (es[eIdx]).v.val) = lv.val ∧
      lift lv = (es[eIdx]).v) :
    let d : PartWriteLocalEdgeArgs := ⟨edgeBase, localBase, dstBase, eIdx, cEdgeLen⟩
    let prog := partWriteLocalEdge d
    partWriteLocalEdgeSafe w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    memoryCost prog s ≤ 10 ∧
    (Memory.spec 0).clientResult s prog = cEdgeLen + 1 ∧
    ((Memory.spec 0).clientState s prog).frontier = s.frontier ∧
    Memory.WellFormed w ((Memory.spec 0).clientState s prog) ∧
    (∀ x, ¬(dstBase + 4 * cEdgeLen ≤ x ∧ x < dstBase + 4 * cEdgeLen + 4) →
      ((Memory.spec 0).clientState s prog).mem x = s.mem x) ∧
    ∃ le : IndexedEdge size,
      ⟨lift le.u, lift le.v, le.weight, le.id⟩ = es[eIdx] ∧
      HoldsIndexedEdges (dstBase + 4 * cEdgeLen) [le]
        ((Memory.spec 0).clientState s prog).mem := by
  obtain ⟨lu, hlu_eq, hlu_lift⟩ := hlu; obtain ⟨lv, hlv_eq, hlv_lift⟩ := hlv
  obtain ⟨hu, hv, hw, hid⟩ := hin eIdx he_lt
  obtain ⟨-, hvh_w, hc_w, hfr_w, -, hmod_w, hw0, hw1, hw2, hw3⟩ := partWriteStride4_spec
    (dst := dstBase) (idx := cEdgeLen) h16 hwf
    (hwf.mem_fits (localBase + s.mem (edgeBase + 4 * eIdx)))
    (hwf.mem_fits (localBase + s.mem (edgeBase + 4 * eIdx + 1)))
    (hwf.mem_fits (edgeBase + 4 * eIdx + 2)) (hwf.mem_fits (edgeBase + 4 * eIdx + 3)) hd_mem
  have hft_w := FramedTriple.of_realization
    (S := {x | dstBase + 4 * cEdgeLen ≤ x ∧ x < dstBase + 4 * cEdgeLen + 4}) hvh_w hfr_w
    fun x hx => by_contra fun h => hx (hmod_w x h)
  obtain ⟨hvh, hc, hfr', hS, hres, h0, h1, h2, h3⟩ :=
    FramedTriple.realization_of_frontier_eq (w := w) (s := s) (c := 10)
    (p := partWriteLocalEdge ⟨edgeBase, localBase, dstBase, eIdx, cEdgeLen⟩)
    (S := {x | dstBase + 4 * cEdgeLen ≤ x ∧ x < dstBase + 4 * cEdgeLen + 4})
    (Q := fun r t => r = cEdgeLen + 1 ∧ t.mem (dstBase + 4 * cEdgeLen) = lu.val ∧
      t.mem (dstBase + 4 * cEdgeLen + 1) = lv.val ∧
      t.mem (dstBase + 4 * cEdgeLen + 2) = (es[eIdx]).weight ∧
      t.mem (dstBase + 4 * cEdgeLen + 3) = (es[eIdx]).id) (by
    rw [partWriteLocalEdge_def]; framed_triple
    · exact ⟨hfr_w, rfl, hw0.trans (by rw [hu, hlu_eq]), hw1.trans (by rw [hv, hlv_eq]),
        hw2.trans hw, hw3.trans hid⟩)
  refine ⟨by rw [partWriteLocalEdgeSafe_def]; exact ⟨h16, hc_fit, he_mem, hu ▸ hlu_lt,
      hv ▸ hlv_lt, hd_mem⟩, hvh, hc, hres, hfr', wellFormed_clientState hwf hvh,
    fun x hx => by_contra fun h => hx (hS x h), ⟨lu, lv, (es[eIdx]).weight, (es[eIdx]).id⟩,
    by simp [hlu_lift, hlv_lift], fun i hi => ?_⟩
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  simpa using ⟨h0, h1, h2, h3⟩

private theorem partMaybeEmitLocal_spec {w n size : ℕ} (L : PartLayout w n)
    {lift : Fin size → Fin n} {s t : Memory.State} (cid nb eIdx cEdgeLen : ℕ)
    (hs_fr : s.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hin : HoldsIndexedEdges L.edgeBase L.es s.mem)
    (ht_fr : t.frontier = s.frontier) (ht_wf : Memory.WellFormed w t)
    (ht_agree_buf14 : ∀ x < L.bufBase + 14 * n, t.mem x = s.mem x)
    (he_lt : eIdx < L.es.length) (hnb_lt : nb < n)
    (hc_emit : t.mem (L.bufBase + 14 * n + eIdx) = 0 → t.mem (L.bufBase + n + nb) = cid →
      cEdgeLen + 1 ≤ L.es.length ∧
      (∃ lu : Fin size, s.mem (L.bufBase + 2 * n + (L.es[eIdx]).u.val) = lu.val ∧
        lift lu = (L.es[eIdx]).u) ∧
      (∃ lv : Fin size, s.mem (L.bufBase + 2 * n + (L.es[eIdx]).v.val) = lv.val ∧
        lift lv = (L.es[eIdx]).v)) :
    let m := L.es.length
    let d : PartMaybeEmitLocalArgs := ⟨L.edgeBase, L.bufBase, n, m, cid, nb, eIdx, cEdgeLen⟩
    let prog := partMaybeEmitLocal d
    let res := (Memory.spec 0).clientResult t prog
    let t' := (Memory.spec 0).clientState t prog
    partMaybeEmitLocalSafe w d t ∧
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t prog) ∧
    memoryCost prog t ≤ 13 ∧ t'.frontier = t.frontier ∧ Memory.WellFormed w t' ∧
    (∀ _cond : t.mem (L.bufBase + 14 * n + eIdx) = 0 ∧ t.mem (L.bufBase + n + nb) = cid,
      res = cEdgeLen + 1 ∧
      (∀ x, ¬(x = L.bufBase + 14 * n + eIdx ∨
        (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen ≤ x ∧
          x < L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen + 4)) → t'.mem x = t.mem x) ∧
      t'.mem (L.bufBase + 14 * n + eIdx) = 1 ∧
      ∃ le : IndexedEdge size,
        ⟨lift le.u, lift le.v, le.weight, le.id⟩ = L.es[eIdx] ∧
        HoldsIndexedEdges (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen) [le] t'.mem) ∧
    (¬(t.mem (L.bufBase + 14 * n + eIdx) = 0 ∧ t.mem (L.bufBase + n + nb) = cid) →
      res = cEdgeLen ∧ t' = t) := by
  let m := L.es.length
  let d : PartMaybeEmitLocalArgs := ⟨L.edgeBase, L.bufBase, n, m, cid, nb, eIdx, cEdgeLen⟩
  have h16 := L.h16; have hn_pos := L.hn_pos; have hed_buf := edge_lt_bufBase L
  have hbuf_lt1 : L.bufBase + 14 * n + eIdx < t.frontier := by rw [ht_fr, hs_fr]; omega
  have hbuf_lt2 : L.bufBase + n + nb < t.frontier := by rw [ht_fr, hs_fr]; omega
  have hbuf_fit : Fits w (L.bufBase + 14 * n + 14 * m) := L.hfit_end.of_le (by omega)
  have hprog : partMaybeEmitLocal d =
      (Memory.read (L.bufBase + 14 * n + eIdx) >>= fun st =>
        Memory.read (L.bufBase + n + nb) >>= fun inNb =>
          if st = 0 ∧ inNb = cid then
            Memory.write (L.bufBase + 14 * n + eIdx) 1 >>= fun _ =>
              partWriteLocalEdge ⟨L.edgeBase, L.bufBase + 2 * n,
                L.bufBase + 14 * n + 2 * m, eIdx, cEdgeLen⟩
          else pure cEdgeLen) := partMaybeEmitLocal_def _
  by_cases hcond : t.mem (L.bufBase + 14 * n + eIdx) = 0 ∧ t.mem (L.bufBase + n + nb) = cid
  · obtain ⟨hc_le, hlu, hlv⟩ := hc_emit hcond.1 hcond.2
    let t₁ : Memory.State := ⟨Function.update t.mem (L.bufBase + 14 * n + eIdx) 1, t.frontier⟩
    have ht1_wf : Memory.WellFormed w t₁ := ⟨ht_wf.frontier_fits, fun a => by
      by_cases ha : a = L.bufBase + 14 * n + eIdx
      · subst ha; simpa [t₁] using h16.of_le (by omega)
      · simpa [t₁, ha] using ht_wf.mem_fits a⟩
    have ht1_below : ∀ x < L.bufBase + 14 * n, t₁.mem x = s.mem x := fun x hx => by
      dsimp only [t₁]; rw [Function.update_of_ne (by omega)]; exact ht_agree_buf14 x hx
    have hin_t1 := (partCongrEdges_of_agree_buf L fun x hx => ht1_below x (by omega)).1 hin
    have hwl := partWriteLocalEdge_spec (w := w) (size := size) (edgeBase := L.edgeBase)
      (localBase := L.bufBase + 2 * n) (dstBase := L.bufBase + 14 * n + 2 * m)
      (eIdx := eIdx) (cEdgeLen := cEdgeLen) (es := L.es) (lift := lift) (s := t₁)
      h16 ht1_wf hin_t1 he_lt (L.hfit_end.of_le (by omega))
      (by dsimp only [t₁]; rw [ht_fr, hs_fr]; omega) (by dsimp only [t₁]; rw [ht_fr, hs_fr]; omega)
      (by dsimp only [t₁]; rw [ht_fr, hs_fr]; omega) (by dsimp only [t₁]; rw [ht_fr, hs_fr]; omega)
      ⟨hlu.choose, (ht1_below _ (by omega)).trans hlu.choose_spec.1, hlu.choose_spec.2⟩
      ⟨hlv.choose, (ht1_below _ (by omega)).trans hlv.choose_spec.1, hlv.choose_spec.2⟩
    rcases hwl with ⟨hsafe_wl, hvh_wl, hc_wl, hres_wl, hfr_wl, -, hmod_wl, le, hle_eq, hle_hold⟩
    let S : Set ℕ := {x | x = L.bufBase + 14 * n + eIdx ∨
      (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen ≤ x ∧
        x < L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen + 4)}
    have hft_wl := FramedTriple.of_realization (S := S) hvh_wl hfr_wl fun x hx =>
      .inr (by_contra fun h => hx (hmod_wl x h))
    obtain ⟨hvh, hcost, hfr', hS, hres, hst⟩ :=
      FramedTriple.realization_of_frontier_eq (w := w) (s := t) (c := 13)
      (p := partMaybeEmitLocal d)
      (S := S) (Q := fun r t' => r = cEdgeLen + 1 ∧ t' = (Memory.spec 0).clientState t₁
        (partWriteLocalEdge ⟨L.edgeBase, L.bufBase + 2 * n, L.bufBase + 14 * n + 2 * m, eIdx,
          cEdgeLen⟩)) (by
      rw [hprog]; framed_triple)
    refine ⟨(by rw [partMaybeEmitLocalSafe_def]; exact ⟨h16, hbuf_fit, hbuf_lt1, hbuf_lt2,
        fun _ _ => hsafe_wl⟩), hvh, hcost, hfr', wellFormed_clientState ht_wf hvh,
      fun _ => ⟨hres, fun x hx => by_contra fun h => hx (hS x h), ?_, le, hle_eq, hst ▸ hle_hold⟩,
      fun h => absurd hcond h⟩
    rw [hst, hmod_wl _ (by omega)]; dsimp only [t₁]; rw [Function.update_self]
  · obtain ⟨hvh, hcost, -, -, hres, hst⟩ :=
      FramedTriple.realization_of_frontier_eq (w := w) (s := t) (c := 13)
      (p := partMaybeEmitLocal d)
      (S := ∅) (Q := fun r t' => r = cEdgeLen ∧ t' = t) (by
      rw [hprog]; refine FramedTriple.read_bind (c := 12) hbuf_lt1 ?_
      refine FramedTriple.read_bind (c := 11) hbuf_lt2 ?_
      simp only [hcond, ↓reduceIte]; exact FramedTriple.pure ⟨rfl, rfl, rfl⟩)
    exact ⟨(by rw [partMaybeEmitLocalSafe_def]; exact ⟨h16, hbuf_fit, hbuf_lt1, hbuf_lt2,
        fun h1 h2 => absurd ⟨h1, h2⟩ hcond⟩), hvh, hcost, by rw [hst], by rw [hst]; exact ht_wf,
      fun h => absurd h hcond, fun _ => ⟨hres, hst⟩⟩

private abbrev EmitCompInv {w n size : ℕ} (L : PartLayout w n) (s : Memory.State)
    (V_i : Finset (Fin n)) (lift : Fin size → Fin n) (edgeState0 : ℕ → ℕ)
    (cEdgeLen0 mcLen0 : ℕ) (cov : List (Fin L.es.length) → Prop)
    (a : PartCursor) (st : Memory.State) : Prop :=
  cEdgeLen0 ≤ a.count ∧ st.frontier = s.frontier ∧ Memory.WellFormed w st ∧
  (∀ x, ¬((L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + L.es.length) ∨
    (L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0 ≤ x ∧
      x < L.bufBase + 14 * n + 2 * L.es.length + 4 * a.count)) → st.mem x = s.mem x) ∧
  ∃ (emitted : List (Fin L.es.length)) (comp : List (IndexedEdge size)),
    emitted.Nodup ∧ comp.length = a.count - cEdgeLen0 ∧
    HoldsIndexedEdges (L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0) comp st.mem ∧
    comp.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) =
      emitted.map (fun eIdx => (L.es[eIdx.val]'eIdx.isLt)) ∧
    (∀ eIdx ∈ emitted,
      edgeState0 eIdx.val = 0 ∧ (L.es[eIdx.val]'eIdx.isLt).u ∈ V_i ∧
        (L.es[eIdx.val]'eIdx.isLt).v ∈ V_i) ∧
    cov emitted ∧
    (∀ i < L.es.length, st.mem (L.bufBase + 14 * n + i) =
      if ∃ hlt : i < L.es.length, (⟨i, hlt⟩ : Fin L.es.length) ∈ emitted then 1
      else edgeState0 i) ∧
    a.count + mcLen0 ≤
      (Finset.univ.filter (fun i : Fin L.es.length =>
        st.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card

private theorem partEmitEdgeLoop_spec {w n size : ℕ} (L : PartLayout w n)
    (s st : Memory.State) (V_i : Finset (Fin n)) (lift : Fin size → Fin n)
    (edgeState0 : ℕ → ℕ) (cid cEdgeLen0 mcLen0 k startJ endJ : ℕ) (uk : Fin n) (a2 : ℕ)
    (hs_fr : s.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hcsr : HoldsUndirCSR L.offBase L.adjBase L.es s.mem)
    (hin : HoldsIndexedEdges L.edgeBase L.es s.mem)
    (hincur_in : ∀ x : Fin n, x ∈ V_i → s.mem (L.bufBase + n + x.val) = cid)
    (hincur_out : ∀ x : Fin n, x ∉ V_i → s.mem (L.bufBase + n + x.val) ≠ cid)
    (huk_in : uk ∈ V_i) (hstart_eq : startJ = s.mem (L.offBase + uk.val))
    (hend_eq : endJ = s.mem (L.offBase + uk.val + 1))
    (hle_j : startJ ≤ endJ) (hend_le : endJ ≤ 2 * L.es.length)
    (hedge_local_fit : ∀ (eIdx : Fin L.es.length),
      (L.es[eIdx.val]'eIdx.isLt).u ∈ V_i → (L.es[eIdx.val]'eIdx.isLt).v ∈ V_i →
      (∃ lu : Fin size, s.mem (L.bufBase + 2 * n + (L.es[eIdx.val]'eIdx.isLt).u.val) = lu.val ∧
        lift lu = (L.es[eIdx.val]'eIdx.isLt).u) ∧
      (∃ lv : Fin size, s.mem (L.bufBase + 2 * n + (L.es[eIdx.val]'eIdx.isLt).v.val) = lv.val ∧
        lift lv = (L.es[eIdx.val]'eIdx.isLt).v))
    (hcEdge : cEdgeLen0 ≤ a2) (hst_fr : st.frontier = s.frontier) (hst_wf : Memory.WellFormed w st)
    (hst_mod : ∀ x, ¬((L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + L.es.length) ∨
      (L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 2 * L.es.length + 4 * a2)) → st.mem x = s.mem x)
    (emitted0 : List (Fin L.es.length)) (comp0 : List (IndexedEdge size))
    (hnd0 : emitted0.Nodup) (hlen0 : comp0.length = a2 - cEdgeLen0)
    (hhold0 : HoldsIndexedEdges (L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0)
      comp0 st.mem)
    (hmap0 : comp0.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) =
      emitted0.map (fun eIdx => (L.es[eIdx.val]'eIdx.isLt)))
    (hemit_sub0 : ∀ eIdx ∈ emitted0,
      edgeState0 eIdx.val = 0 ∧ (L.es[eIdx.val]'eIdx.isLt).u ∈ V_i ∧
        (L.es[eIdx.val]'eIdx.isLt).v ∈ V_i)
    (hemit_cov0 : ∀ eIdx : Fin L.es.length, edgeState0 eIdx.val = 0 →
      (L.es[eIdx.val]'eIdx.isLt).u ∈ V_i → (L.es[eIdx.val]'eIdx.isLt).v ∈ V_i →
      (∃ r < k, s.mem (L.bufBase + 3 * n + r) = (L.es[eIdx.val]'eIdx.isLt).u.val ∨
        s.mem (L.bufBase + 3 * n + r) = (L.es[eIdx.val]'eIdx.isLt).v.val) →
      eIdx ∈ emitted0)
    (hest0 : ∀ i < L.es.length, st.mem (L.bufBase + 14 * n + i) =
      if ∃ hlt : i < L.es.length, (⟨i, hlt⟩ : Fin L.es.length) ∈ emitted0 then 1 else
        edgeState0 i)
    (hclaim0 : a2 + mcLen0 ≤
      (Finset.univ.filter (fun i : Fin L.es.length =>
        st.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card) :
    let m := L.es.length
    let edgeStepD : PartAdjEnv := ⟨L.adjBase, L.edgeBase, L.bufBase, n, m, cid⟩
    let prog := iterate partEmitEdgeStep edgeStepD (endJ - startJ) ⟨startJ, a2⟩
    let b' := (Memory.spec 0).clientResult st prog
    let t' := (Memory.spec 0).clientState st prog
    iterationSafe partEmitEdgeStep partEmitEdgeStepSafe w edgeStepD (endJ - startJ)
      ⟨startJ, a2⟩ st ∧
    (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st prog) ∧
    memoryCost prog st ≤ 15 * (endJ - startJ) ∧
    t'.frontier = st.frontier ∧
    (∀ x, ¬((L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + m) ∨
      (L.bufBase + 14 * n + 2 * m ≤ x ∧ x < L.bufBase + 14 * n + 6 * m)) →
      t'.mem x = st.mem x) ∧
    cEdgeLen0 ≤ b'.count ∧ t'.frontier = s.frontier ∧ Memory.WellFormed w t' ∧
    (∀ x, ¬((L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + m) ∨
      (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 2 * m + 4 * b'.count)) → t'.mem x = s.mem x) ∧
    ∃ (emitted' : List (Fin m)) (comp' : List (IndexedEdge size)),
      emitted'.Nodup ∧ comp'.length = b'.count - cEdgeLen0 ∧
      HoldsIndexedEdges (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0) comp' t'.mem ∧
      comp'.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) =
        emitted'.map (fun eIdx => (L.es[eIdx.val]'eIdx.isLt)) ∧
      (∀ eIdx ∈ emitted',
        edgeState0 eIdx.val = 0 ∧ (L.es[eIdx.val]'eIdx.isLt).u ∈ V_i ∧
          (L.es[eIdx.val]'eIdx.isLt).v ∈ V_i) ∧
      (∀ eIdx : Fin m, edgeState0 eIdx.val = 0 →
        (L.es[eIdx.val]'eIdx.isLt).u ∈ V_i → (L.es[eIdx.val]'eIdx.isLt).v ∈ V_i →
        ((∃ r < k, s.mem (L.bufBase + 3 * n + r) = (L.es[eIdx.val]'eIdx.isLt).u.val ∨
            s.mem (L.bufBase + 3 * n + r) = (L.es[eIdx.val]'eIdx.isLt).v.val) ∨
          uk = (L.es[eIdx.val]'eIdx.isLt).u ∨ uk = (L.es[eIdx.val]'eIdx.isLt).v) →
        eIdx ∈ emitted') ∧
      (∀ i < m, t'.mem (L.bufBase + 14 * n + i) =
        if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ emitted' then 1 else edgeState0 i) ∧
      b'.count + mcLen0 ≤
        (Finset.univ.filter (fun i : Fin m => t'.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card := by
  let m := L.es.length
  let edgeStepD : PartAdjEnv := ⟨L.adjBase, L.edgeBase, L.bufBase, n, m, cid⟩
  have h16 := L.h16; have hcsr_buf := (csr_lt_bufBase L).2; have hn_pos := L.hn_pos
  let S : Set ℕ :=
    Set.Ico (L.bufBase + 14 * n) (L.bufBase + 14 * n + m) ∪
    Set.Ico (L.bufBase + 14 * n + 2 * m) (L.bufBase + 14 * n + 6 * m)
  let Inv (step : ℕ) (b : PartCursor) (t : Memory.State) : Prop :=
    b.idx = startJ + step ∧ EmitCompInv L s V_i lift edgeState0 cEdgeLen0 mcLen0 (fun emitted =>
      ∀ eIdx : Fin m, edgeState0 eIdx.val = 0 →
        (L.es[eIdx.val]'eIdx.isLt).u ∈ V_i → (L.es[eIdx.val]'eIdx.isLt).v ∈ V_i →
        ((∃ r < k, s.mem (L.bufBase + 3 * n + r) = (L.es[eIdx.val]'eIdx.isLt).u.val ∨
            s.mem (L.bufBase + 3 * n + r) = (L.es[eIdx.val]'eIdx.isLt).v.val) ∨
          ∃ q < step, s.mem (L.adjBase + 2 * (startJ + q) + 1) = eIdx.val) →
        eIdx ∈ emitted) b t
  have hinv0 : Inv 0 ⟨startJ, a2⟩ st :=
    ⟨rfl, hcEdge, hst_fr, hst_wf, hst_mod, emitted0, comp0, hnd0, hlen0, hhold0, hmap0,
      hemit_sub0, fun eIdx he hu hv hcond => hcond.elim (hemit_cov0 eIdx he hu hv)
        (fun ⟨_, hq, _⟩ => absurd hq (Nat.not_lt_zero _)), hest0, hclaim0⟩
  have hstep : ∀ step < endJ - startJ, ∀ b t, Inv step b t →
      partEmitEdgeStepSafe w (edgeStepD, b) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (partEmitEdgeStep (edgeStepD, b))) ∧
      let b' := (Memory.spec 0).clientResult t (partEmitEdgeStep (edgeStepD, b))
      let t' := (Memory.spec 0).clientState t (partEmitEdgeStep (edgeStepD, b))
      memoryCost (partEmitEdgeStep (edgeStepD, b)) t + 0 ≤ 0 + 15 ∧
      Memory.Modifies S t t' ∧ Inv (step + 1) b' t' := by
    intro step hstep b t hbinv
    rcases hbinv with ⟨hb1, hbce_le, ht_fr, ht_wf, ht_mod, emitted, comp,
      hnd, hlen, hhold, hmap, hemit_sub, hemit_cov, hest, hclaim⟩
    have hpair_mem : (s.mem (L.adjBase + 2 * b.idx), s.mem (L.adjBase + 2 * b.idx + 1)) ∈
        (List.range (s.mem (L.offBase + uk.val + 1) - s.mem (L.offBase + uk.val))).map
          (fun r => let p := s.mem (L.offBase + uk.val) + r
            (s.mem (L.adjBase + 2 * p), s.mem (L.adjBase + 2 * p + 1))) := by
      refine List.mem_map.mpr
        ⟨step, List.mem_range.mpr (by rw [← hstart_eq, ← hend_eq]; exact hstep), ?_⟩
      dsimp only; rw [← hstart_eq, ← hb1]
    rw [hcsr.mem_slice_iff] at hpair_mem
    rcases hpair_mem with ⟨eFin, heFin_id, heFin_ends⟩
    let nb := s.mem (L.adjBase + 2 * b.idx)
    have hnb_lt : nb < n := by
      dsimp only [nb]; rcases heFin_ends with ⟨_, hv⟩ | ⟨_, hu⟩
      · rw [← hv]; exact (L.es[eFin.val]'eFin.isLt).v.isLt
      · rw [← hu]; exact (L.es[eFin.val]'eFin.isLt).u.isLt
    have ht_below : ∀ x < L.bufBase + 14 * n, t.mem x = s.mem x := fun x hx => ht_mod x (by omega)
    have hadj0_eq : t.mem (L.adjBase + 2 * b.idx) = nb := ht_below _ (by omega)
    have hadj1_eq : t.mem (L.adjBase + 2 * b.idx + 1) = eFin.val :=
      (ht_below _ (by omega)).trans heFin_id.symm
    have hadj_lt : L.adjBase + 2 * b.idx + 1 < t.frontier := by rw [ht_fr, hs_fr]; omega
    have hme_emit : t.mem (L.bufBase + 14 * n + eFin.val) = 0 → t.mem (L.bufBase + n + nb) = cid →
        b.count + 1 ≤ m ∧
        (∃ lu : Fin size, s.mem (L.bufBase + 2 * n + (L.es[eFin.val]'eFin.isLt).u.val) = lu.val ∧
          lift lu = (L.es[eFin.val]'eFin.isLt).u) ∧
        (∃ lv : Fin size, s.mem (L.bufBase + 2 * n + (L.es[eFin.val]'eFin.isLt).v.val) =
          lv.val ∧ lift lv = (L.es[eFin.val]'eFin.isLt).v) := by
      intro hst0 hnb_c
      have hfilt_le : (Finset.univ.filter (fun i : Fin m =>
          t.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card < m :=
        filter_ne_zero_card_lt (fun i : Fin m => t.mem (L.bufBase + 14 * n + i.val)) eFin hst0
      have hnb_in : (⟨nb, hnb_lt⟩ : Fin n) ∈ V_i := by
        by_contra hnot
        exact hincur_out ⟨nb, hnb_lt⟩ hnot ((ht_below _ (by omega)).symm.trans hnb_c)
      have hboth : (L.es[eFin.val]'eFin.isLt).u ∈ V_i ∧ (L.es[eFin.val]'eFin.isLt).v ∈ V_i := by
        rcases heFin_ends with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · exact ⟨hu ▸ huk_in, (Fin.ext hv.symm : (⟨nb, hnb_lt⟩ : Fin n) = _) ▸ hnb_in⟩
        · exact ⟨(Fin.ext hu.symm : (⟨nb, hnb_lt⟩ : Fin n) = _) ▸ hnb_in, hv ▸ huk_in⟩
      exact ⟨by dsimp only [m] at hfilt_le hclaim ⊢; omega, hedge_local_fit eFin hboth.1 hboth.2⟩
    have hme := partMaybeEmitLocal_spec L cid nb eFin.val b.count hs_fr hin ht_fr ht_wf ht_below
      eFin.isLt hnb_lt hme_emit
    dsimp only at hme
    rcases hme with ⟨hsafe_me, hvh_me, hcost_me, hfr_me, hwf_me, hme_true, hme_false⟩
    have hprog_step : partEmitEdgeStep (edgeStepD, b) =
        (Memory.read (L.adjBase + 2 * b.idx) >>= fun nb' =>
          Memory.read (L.adjBase + 2 * b.idx + 1) >>= fun e' =>
            partMaybeEmitLocal ⟨L.edgeBase, L.bufBase, n, m, cid, nb', e', b.count⟩ >>= fun c' =>
              pure ⟨b.idx + 1, c'⟩) := partEmitEdgeStep_def _
    have hsafe_step : partEmitEdgeStepSafe w (edgeStepD, b) t := by
      rw [partEmitEdgeStepSafe_def]
      refine ⟨h16, L.hfit_end.of_le (by dsimp only [m]; omega), hadj_lt, ?_⟩
      simpa [edgeStepD, hadj0_eq, hadj1_eq, nb] using hsafe_me
    have hvh_step : (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (partEmitEdgeStep (edgeStepD, b))) := by
      rw [hprog_step]; refine validHistory_read_bind (by omega) (validHistory_read_bind hadj_lt ?_)
      rw [hadj0_eq, hadj1_eq]; exact validHistory_bind_step hvh_me (validHistory_pure w _ _)
    have hcost_step : memoryCost (partEmitEdgeStep (edgeStepD, b)) t ≤ 15 := by
      rw [hprog_step, memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, hadj0_eq, hadj1_eq,
        memoryCost_bind', memoryCost_pure]
      dsimp only [m] at hcost_me ⊢; omega
    have hres_step : (Memory.spec 0).clientResult t (partEmitEdgeStep (edgeStepD, b)) =
        ⟨b.idx + 1, (Memory.spec 0).clientResult t
          (partMaybeEmitLocal ⟨L.edgeBase, L.bufBase, n, m, cid, nb, eFin.val, b.count⟩)⟩ := by
      rw [hprog_step, clientResult_bind_read, clientResult_bind_read, hadj0_eq, hadj1_eq,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    have hst_step : (Memory.spec 0).clientState t (partEmitEdgeStep (edgeStepD, b)) =
        (Memory.spec 0).clientState t
          (partMaybeEmitLocal ⟨L.edgeBase, L.bufBase, n, m, cid, nb, eFin.val, b.count⟩) := by
      rw [hprog_step, clientState_bind_read, clientState_bind_read, hadj0_eq, hadj1_eq,
        StateTransitionSpec.clientState_bind]; rfl
    have hnb_in_iff : t.mem (L.bufBase + n + nb) = cid ↔ (⟨nb, hnb_lt⟩ : Fin n) ∈ V_i := by
      rw [ht_below _ (by omega)]
      exact ⟨fun hc => by_contra fun hn => hincur_out ⟨nb, hnb_lt⟩ hn hc,
        fun hm => hincur_in ⟨nb, hnb_lt⟩ hm⟩
    have hboth_in_iff : t.mem (L.bufBase + n + nb) = cid ↔
        (L.es[eFin.val]'eFin.isLt).u ∈ V_i ∧ (L.es[eFin.val]'eFin.isLt).v ∈ V_i := by
      rw [hnb_in_iff]; rcases heFin_ends with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · exact ⟨fun h => ⟨hu ▸ huk_in, (Fin.ext hv.symm : (⟨nb, hnb_lt⟩ : Fin n) = _) ▸ h⟩,
          fun h => (Fin.ext hv.symm : (⟨nb, hnb_lt⟩ : Fin n) = _) ▸ h.2⟩
      · exact ⟨fun h => ⟨(Fin.ext hu.symm : (⟨nb, hnb_lt⟩ : Fin n) = _) ▸ h, hv ▸ huk_in⟩,
          fun h => (Fin.ext hu.symm : (⟨nb, hnb_lt⟩ : Fin n) = _) ▸ h.1⟩
    by_cases hcond : t.mem (L.bufBase + 14 * n + eFin.val) = 0 ∧ t.mem (L.bufBase + n + nb) = cid
    · obtain ⟨hres_me, hmod_me, hset_me, le_new, hle_eq, hle_hold⟩ := hme_true hcond
      have hcond_s : edgeState0 eFin.val = 0 ∧ (L.es[eFin.val]'eFin.isLt).u ∈ V_i ∧
          (L.es[eFin.val]'eFin.isLt).v ∈ V_i := by
        refine ⟨?_, hboth_in_iff.mp hcond.2⟩
        have he_st := hest eFin.val eFin.isLt; rw [hcond.1] at he_st
        split_ifs at he_st; exact he_st.symm
      have he_not_mem : eFin ∉ emitted := fun hm => by
        have h1 := hest eFin.val eFin.isLt
        have hm' : ∃ hlt : eFin.val < L.es.length,
            (⟨eFin.val, hlt⟩ : Fin L.es.length) ∈ emitted := ⟨eFin.isLt, hm⟩
        simp only [hm', ↓reduceIte] at h1; omega
      have hcard_lt : b.count + 1 ≤ m := (hme_emit hcond.1 hcond.2).1
      set t₂ := (Memory.spec 0).clientState t
        (partMaybeEmitLocal ⟨L.edgeBase, L.bufBase, n, m, cid, nb, eFin.val, b.count⟩)
      refine ⟨hsafe_step, hvh_step, by omega,
        ⟨le_of_eq (hst_step ▸ hfr_me).symm, fun x _ hx => ?_⟩, ?_⟩
      · rw [hst_step]; exact hmod_me x fun h => hx (by
          rcases h with rfl | ⟨h1, h2⟩
          · left; exact ⟨Nat.le_add_right _ _, by omega⟩
          · right; exact ⟨by omega, by omega⟩)
      · rw [hres_step, hres_me, hst_step]; dsimp only [Inv, EmitCompInv, m] at *
        refine ⟨by omega, by omega, hfr_me.trans ht_fr, hwf_me, fun x hx => ?_,
          emitted ++ [eFin], comp ++ [le_new],
          List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, fun _ ha _ hb heq => by
            subst heq; rw [List.mem_singleton.mp hb] at ha; exact he_not_mem ha⟩,
          by rw [List.length_append, List.length_singleton, hlen, Nat.sub_add_comm hbce_le],
          ?_, by simp [hmap, hle_eq], ?_, ?_, ?_, ?_⟩
        · exact (hmod_me x fun h =>
              hx (by rcases h with rfl | h; exacts [.inl (by omega), .inr (by omega)])).trans
            (ht_mod x fun h => hx (by rcases h with h | h; exacts [.inl h, .inr (by omega)]))
        · refine holdsIndexedEdges_append
            (hhold.congr fun x _ hx2 => hmod_me x (by rw [hlen] at hx2; omega)) ?_
          have haddr : L.bufBase + 14 * n + 2 * L.es.length + 4 * cEdgeLen0 +
              4 * (b.count - cEdgeLen0) =
              L.bufBase + 14 * n + 2 * L.es.length + 4 * b.count := by
            rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_of_le hbce_le]
          simpa [hlen, haddr] using hle_hold
        · intro e' he'
          rcases List.mem_append.mp he' with he' | he'
          · exact hemit_sub e' he'
          · rw [List.mem_singleton.mp he']; exact hcond_s
        · intro e' he0 hu' hv' hcov'
          by_cases hee : e' = eFin
          · subst hee; simp
          · refine List.mem_append_left _ (hemit_cov e' he0 hu' hv' ?_)
            rcases hcov' with h | ⟨q, hq, hqe⟩
            · exact .inl h
            · refine .inr ⟨q, ?_, hqe⟩
              by_contra hnq; have hqq : q = step := by omega
              subst hqq; rw [← hb1, ← heFin_id] at hqe; exact hee (Fin.ext hqe.symm)
        · intro i hi
          by_cases hie : i = eFin.val
          · subst hie; rw [hset_me]
            split_ifs with hm_e
            · rfl
            · exact absurd ⟨hi, by simp⟩ hm_e
          · have hne_f : (⟨i, hi⟩ : Fin L.es.length) ≠ eFin := fun h => hie (congrArg Fin.val h)
            rw [hmod_me _ (by omega), hest i hi]
            simp only [List.mem_append, List.mem_singleton, hne_f, or_false]
        · have hc := card_filter_ne_zero_add_one
              (fun i : Fin L.es.length => t.mem (L.bufBase + 14 * n + i.val))
              (fun i : Fin L.es.length => t₂.mem (L.bufBase + 14 * n + i.val))
              eFin hcond.1 (by rw [hset_me]; omega) fun i hne =>
            hmod_me _ (by have := Fin.val_ne_of_ne hne; omega)
          dsimp only [t₂] at hc ⊢; omega
    · obtain ⟨hres_me, hst_me⟩ := hme_false hcond
      refine ⟨hsafe_step, hvh_step, by omega,
        ⟨by rw [hst_step, hst_me], fun _ _ _ => by rw [hst_step, hst_me]⟩, ?_⟩
      rw [hres_step, hres_me, hst_step, hst_me]
      refine ⟨by dsimp only; omega, hbce_le, ht_fr, ht_wf, ht_mod, emitted, comp, hnd, hlen, hhold,
        hmap, hemit_sub, fun e' he0 hu' hv' hcov' => ?_, hest, hclaim⟩
      rcases hcov' with h | ⟨q, hq, hqe⟩
      · exact hemit_cov e' he0 hu' hv' (.inl h)
      · by_cases hqs : q < step
        · exact hemit_cov e' he0 hu' hv' (.inr ⟨q, hqs, hqe⟩)
        · have hqq : q = step := by omega
          subst hqq; rw [← hb1, ← heFin_id] at hqe
          have he_eq : e' = eFin := Fin.ext hqe.symm; subst he_eq
          have hnb_c : t.mem (L.bufBase + n + nb) = cid := hboth_in_iff.mpr ⟨hu', hv'⟩
          have hst_ne : t.mem (L.bufBase + 14 * n + e'.val) ≠ 0 := fun h0 => hcond ⟨h0, hnb_c⟩
          have h1 := hest e'.val e'.isLt
          split_ifs at h1 with hm
          · exact (Fin.ext rfl : (⟨e'.val, hm.choose⟩ : Fin L.es.length) = e') ▸ hm.choose_spec
          · exact absurd (h1.trans he0) hst_ne
  obtain ⟨hsafe_it, hvh_it, hcost_it, hmod_it, hinv_end⟩ :=
    iterate_potential_spec partEmitEdgeStep partEmitEdgeStepSafe w edgeStepD 15 (endJ - startJ)
      Inv (fun _ _ _ => 0) S hstep ⟨startJ, a2⟩ st hinv0
  rcases hinv_end with ⟨_, hce_le', ht_fr', ht_wf', ht_mod', emitted', comp',
    hnd', hlen', hhold', hmap', hemit_sub', hemit_cov', hest', hclaim'⟩
  have hfr_it : ((Memory.spec 0).clientState st
      (iterate partEmitEdgeStep edgeStepD (endJ - startJ) ⟨startJ, a2⟩)).frontier = st.frontier :=
    ht_fr'.trans hst_fr.symm
  refine ⟨hsafe_it, hvh_it, by simpa only [add_zero, zero_add] using hcost_it, hfr_it, fun x hx =>
    mem_eq_of_modifies_frontier hvh_it hmod_it hfr_it x fun hxS => hx (by
      rcases hxS with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [left; right] <;> exact ⟨h1, h2⟩),
    hce_le', ht_fr', ht_wf', ht_mod', emitted', comp', hnd', hlen', hhold', hmap', hemit_sub',
    fun eIdx he0 hu hv hcov => hemit_cov' eIdx he0 hu hv ?_, hest', hclaim'⟩
  rcases hcov with h | hu_eq | hv_eq
  · exact .inl h
  · obtain ⟨q, hq1, hq2⟩ := List.mem_map.mp ((hcsr.mem_slice_iff uk
        (L.es[eIdx.val]'eIdx.isLt).v.val eIdx.val).mpr ⟨eIdx, rfl, .inl ⟨hu_eq.symm, rfl⟩⟩)
    rw [List.mem_range] at hq1
    exact .inr ⟨q, by rw [hstart_eq, hend_eq]; exact hq1,
      by simpa [hstart_eq] using congrArg Prod.snd hq2⟩
  · obtain ⟨q, hq1, hq2⟩ := List.mem_map.mp ((hcsr.mem_slice_iff uk
        (L.es[eIdx.val]'eIdx.isLt).u.val eIdx.val).mpr ⟨eIdx, rfl, .inr ⟨hv_eq.symm, rfl⟩⟩)
    rw [List.mem_range] at hq1
    exact .inr ⟨q, by rw [hstart_eq, hend_eq]; exact hq1,
      by simpa [hstart_eq] using congrArg Prod.snd hq2⟩

private theorem remDeg_sub_tree_eq {n : ℕ} (offBase bufBase size liveCount : ℕ)
    (mem : ℕ → ℕ) (V_i : Finset (Fin n)) (dead0 : ℕ → ℕ) (lift : Fin size → Fin n)
    (hlift_inj : Function.Injective lift) (hlive_le : liveCount ≤ size)
    (hverts_mem : ∀ k : Fin size, mem (bufBase + 3 * n + k.val) = (lift k).val)
    (hlive_verts : ∀ t < liveCount, ∃ x : Fin n,
      mem (bufBase + 3 * n + t) = x.val ∧ x ∈ V_i ∧ dead0 x.val = 0)
    (hverts_in_live : ∀ x ∈ V_i, dead0 x.val = 0 →
      ∃ t < liveCount, mem (bufBase + 3 * n + t) = x.val) :
    ∑ t ∈ Finset.range liveCount,
      (mem (offBase + mem (bufBase + 3 * n + t) + 1) - mem (offBase + mem (bufBase + 3 * n + t))) =
    remDeg n offBase mem (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)) -
      remDeg n offBase mem (Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0) ∪ V_i) := by
  let deadSet : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)
  let liveFin : Finset (Fin n) := V_i.filter (fun x => dead0 x.val = 0)
  have hbij : ∑ t ∈ Finset.range liveCount,
        (mem (offBase + mem (bufBase + 3 * n + t) + 1) -
          mem (offBase + mem (bufBase + 3 * n + t))) =
      ∑ x ∈ liveFin, (mem (offBase + x.val + 1) - mem (offBase + x.val)) := by
    refine Finset.sum_bij (fun t ht => lift ⟨t, lt_of_lt_of_le (Finset.mem_range.mp ht) hlive_le⟩)
      (fun t ht => by
        obtain ⟨x, hx_eq, hx_in, hx_dz⟩ := hlive_verts t (Finset.mem_range.mp ht)
        have hxe : lift ⟨t, lt_of_lt_of_le (Finset.mem_range.mp ht) hlive_le⟩ = x :=
          Fin.ext ((hverts_mem ⟨t,
            lt_of_lt_of_le (Finset.mem_range.mp ht) hlive_le⟩).symm.trans hx_eq)
        exact hxe ▸ Finset.mem_filter.mpr ⟨hx_in, hx_dz⟩)
      (fun _ _ _ _ heq => congrArg Fin.val (hlift_inj heq))
      (fun x hx => by
        rw [Finset.mem_filter] at hx; obtain ⟨t, ht_lt, htv⟩ := hverts_in_live x hx.1 hx.2
        exact ⟨t, Finset.mem_range.mpr ht_lt, Fin.ext (by rw [← hverts_mem ⟨t, _⟩, htv])⟩)
      (fun t ht => by rw [← hverts_mem ⟨t, lt_of_lt_of_le (Finset.mem_range.mp ht) hlive_le⟩])
  have hunion : deadSet ∪ V_i = deadSet ∪ liveFin := by
    ext x; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      deadSet, liveFin]; tauto
  have hdisj_dl : Disjoint deadSet liveFin := Finset.disjoint_left.mpr fun x hx1 hx2 =>
    (Finset.mem_filter.mp hx1).2 (Finset.mem_filter.mp hx2).2
  have hrem_split : ∀ (lf : Finset (Fin n)), Disjoint deadSet lf →
      remDeg n offBase mem (deadSet ∪ lf) +
        ∑ x ∈ lf, (mem (offBase + x.val + 1) - mem (offBase + x.val)) =
        remDeg n offBase mem deadSet := by
    intro lf hdisj_lf; induction lf using Finset.induction_on with
    | empty => simp
    | insert a sf ha ih =>
      have ha_u : a ∉ deadSet ∪ sf := fun hm =>
        (Finset.mem_union.mp hm).elim (fun hd => Finset.disjoint_left.mp hdisj_lf hd
          (Finset.mem_insert_self a sf)) ha
      rw [Finset.sum_insert ha, Finset.union_insert]
      have hins := remDeg_insert (offBase := offBase) (mem := mem) ha_u
      have ih' := ih (Finset.disjoint_of_subset_right (Finset.subset_insert a sf) hdisj_lf)
      omega
  have h := hrem_split liveFin hdisj_dl; rw [← hbij, ← hunion] at h
  dsimp only [deadSet] at h; omega

/-- Specification of CSR component-edge emission (`partEmitComp`). -/
theorem partEmitComp_spec {w n : ℕ} (L : PartLayout w n) (s₀ : Memory.State)
    (dead0 inCur0 edgeState0 : ℕ → ℕ) (cid ic0 nc0 tLen0 : ℕ) (u : Fin n)
    (h₀ : SHHandle) (hitPrev size tLen' : ℕ) (s : Memory.State)
    (W : DjpWitness L s₀ dead0 inCur0 edgeState0 cid ic0 nc0 tLen0 u
      ⟨0, hitPrev, size, tLen', h₀⟩ s)
    (hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem)
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem)
    (hedge₀ : ∀ i < L.es.length, s₀.mem (L.bufBase + 14 * n + i) = edgeState0 i)
    (hincur₀_ne : ∀ x < n, inCur0 x ≠ cid)
    (hsimp : ∀ e : Fin L.es.length, (L.es[e.val]'e.isLt).u ≠ (L.es[e.val]'e.isLt).v)
    (cEdgeLen0 mcLen0 : ℕ)
    (hclaimed : cEdgeLen0 + mcLen0 ≤
      (Finset.univ.filter (fun i : Fin L.es.length => edgeState0 i.val ≠ 0)).card) :
    let m := L.es.length
    let d : PartEmitCompArgs :=
      ⟨⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, m, cid⟩, hitPrev, size, cEdgeLen0⟩
    let prog := partEmitComp d
    let cRes := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    let liveCount := if hitPrev = 0 then size else size - 1
    let V_i := W.D.treeVerts W.D.numSteps
    let deadSet := Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)
    let lift : Fin size → Fin n := fun k =>
      (djpVertsList W.D)[k.val]'(by rw [djpVertsList_length, ← W.hsize]; exact k.isLt)
    partEmitCompSafe w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
    (∀ x, s'.mem x ≠ s.mem x →
      (L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + m) ∨
      (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 2 * m + 4 * cRes.count)) ∧
    cEdgeLen0 ≤ cRes.count ∧
    memoryCost prog s ≤ 3 * liveCount + 15 *
      (remDeg n L.offBase s.mem deadSet - remDeg n L.offBase s.mem (deadSet ∪ V_i)) ∧
    ∃ (emittedIdx : List (Fin m)) (compLocal : List (IndexedEdge size)),
      emittedIdx.Nodup ∧ compLocal.length = cRes.count - cEdgeLen0 ∧
      HoldsIndexedEdges (L.bufBase + 14 * n + 2 * m + 4 * cEdgeLen0) compLocal s'.mem ∧
      compLocal.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) =
        emittedIdx.map (fun eIdx => (L.es[eIdx.val]'eIdx.isLt)) ∧
      (∀ eIdx : Fin m, eIdx ∈ emittedIdx ↔
        edgeState0 eIdx.val = 0 ∧ (L.es[eIdx.val]'eIdx.isLt).u ∈ V_i ∧
          (L.es[eIdx.val]'eIdx.isLt).v ∈ V_i) ∧
      (∀ i < m, s'.mem (L.bufBase + 14 * n + i) =
        if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ emittedIdx then 1 else edgeState0 i) ∧
      cRes.count + mcLen0 ≤
        (Finset.univ.filter (fun i : Fin m => s'.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card := by
  let m := L.es.length
  let vertStepD : PartEmitVertEnv := ⟨L.offBase, L.adjBase, L.edgeBase, L.bufBase, n, m, cid⟩
  let edgeStepD : PartAdjEnv := ⟨L.adjBase, L.edgeBase, L.bufBase, n, m, cid⟩
  let V_i := W.D.treeVerts W.D.numSteps
  let deadSet : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => dead0 x.val ≠ 0)
  let liveCount : ℕ := if hitPrev = 0 then size else size - 1
  let lift : Fin size → Fin n := fun k =>
    (djpVertsList W.D)[k.val]'(by rw [djpVertsList_length, ← W.hsize]; exact k.isLt)
  have h16 := L.h16; have hn_pos := L.hn_pos; have hwf := W.hsh.wf
  have hcsr_buf := csr_lt_bufBase L; have hcsr1 := hcsr_buf.1; have hcsr2 := hcsr_buf.2
  have hcsr := djpWitness_csr W hcsr₀; have hin := djpWitness_edges W hin₀
  have hsz : size = W.D.numSteps + 1 := W.hsize
  have hhit_sub : hitPrev ≠ 0 → 1 ≤ size := fun hne => by
    have := (W.hhit_prev hne).2.2.1; omega
  have hlive_le : liveCount ≤ size := by dsimp only [liveCount]; split_ifs <;> omega
  have hverts_in_Vi : ∀ k : Fin size, lift k ∈ V_i := fun k => by
    dsimp only [lift, V_i]; rw [← mem_djpVertsList_iff]
    exact List.getElem_mem (by rw [djpVertsList_length, ← hsz]; exact k.isLt)
  have hverts_mem : ∀ k : Fin size, s.mem (L.bufBase + 3 * n + k.val) = (lift k).val := fun k =>
    W.hverts_mem k.val k.isLt
  have hlift_inj : Function.Injective lift := fun a b hab =>
    Fin.ext ((djpVertsList_nodup W.D).getElem_inj_iff.mp hab)
  have hlive_verts : ∀ t < liveCount, ∃ x : Fin n,
      s.mem (L.bufBase + 3 * n + t) = x.val ∧ x ∈ V_i ∧ dead0 x.val = 0 := fun t ht => by
    have ht_sz : t < size := lt_of_lt_of_le ht hlive_le
    refine ⟨lift ⟨t, ht_sz⟩, hverts_mem ⟨t, ht_sz⟩, hverts_in_Vi ⟨t, ht_sz⟩, ?_⟩
    by_cases hp0 : hitPrev = 0
    · exact W.hno_hit hp0 _ (hverts_in_Vi ⟨t, ht_sz⟩)
    · have hp1 := W.hhit_prev hp0; have h1 : 1 ≤ W.D.numSteps := hp1.2.2.1
      by_contra hdz
      have hsd := W.hstop_dead _ (hverts_in_Vi ⟨t, ht_sz⟩) hdz
      have hveq : (djpVertsList W.D)[t]'(by rw [djpVertsList_length, ← hsz]; exact ht_sz) =
          W.D.vOut ⟨W.D.numSteps - 1, by omega⟩ := hsd.2.2.2 h1
      have hlast : (djpVertsList W.D)[W.D.numSteps]'(by rw [djpVertsList_length]; omega) =
          W.D.vOut ⟨W.D.numSteps - 1, by omega⟩ := by
        simpa [Nat.sub_add_cancel h1] using
          djpVertsList_getElem_succ W.D ⟨W.D.numSteps - 1, by omega⟩
      have hidx := (djpVertsList_nodup W.D).getElem_inj_iff.mp (hveq.trans hlast.symm)
      simp only [liveCount, hp0, ↓reduceIte] at ht; omega
  have hverts_in_live : ∀ x ∈ V_i, dead0 x.val = 0 →
      ∃ t < liveCount, s.mem (L.bufBase + 3 * n + t) = x.val := fun x hx hdz => by
    obtain ⟨_, k, hk_sz, hk_m, _⟩ := W.hincur_in x hx
    by_cases hp0 : hitPrev = 0
    · exact ⟨k, by simp [liveCount, hp0, hk_sz], hk_m⟩
    · refine ⟨k, ?_, hk_m⟩
      dsimp only at hk_sz
      have hp1 := W.hhit_prev hp0; simp only [liveCount, hp0, ↓reduceIte]
      by_contra hge
      have hk_last : k = size - 1 := by omega
      have hlast : s.mem (L.bufBase + 3 * n + (size - 1)) =
          (W.D.vOut ⟨W.D.numSteps - 1, by have := hp1.2.2.1; omega⟩).val := by
        rw [W.hverts_mem (size - 1) (by dsimp only; omega)]
        simpa [show W.D.numSteps - 1 + 1 = size - 1 by omega] using
          congrArg Fin.val (djpVertsList_getElem_succ W.D ⟨W.D.numSteps - 1, by
            have := hp1.2.2.1; omega⟩)
      have hx_eq : x = W.D.vOut ⟨W.D.numSteps - 1, by have := hp1.2.2.1; omega⟩ :=
        Fin.ext (by rw [← hlast, ← hk_last, hk_m])
      exact hp1.2.2.2 hp1.2.2.1 (hx_eq ▸ hdz)
  have hedge_local_fit : ∀ (eIdx : Fin m),
      (L.es[eIdx.val]'eIdx.isLt).u ∈ V_i → (L.es[eIdx.val]'eIdx.isLt).v ∈ V_i →
      (∃ lu : Fin size, s.mem (L.bufBase + 2 * n + (L.es[eIdx.val]'eIdx.isLt).u.val) = lu.val ∧
        lift lu = (L.es[eIdx.val]'eIdx.isLt).u) ∧
      (∃ lv : Fin size, s.mem (L.bufBase + 2 * n + (L.es[eIdx.val]'eIdx.isLt).v.val) = lv.val ∧
        lift lv = (L.es[eIdx.val]'eIdx.isLt).v) := fun eIdx hu_in hv_in => by
    obtain ⟨_, ku, hku1, hku2, hku3⟩ := W.hincur_in (L.es[eIdx.val]'eIdx.isLt).u hu_in
    obtain ⟨_, kv, hkv1, hkv2, hkv3⟩ := W.hincur_in (L.es[eIdx.val]'eIdx.isLt).v hv_in
    exact ⟨⟨⟨ku, hku1⟩, hku3, Fin.ext (by rw [← W.hverts_mem ku hku1, hku2])⟩,
      ⟨⟨kv, hkv1⟩, hkv3, Fin.ext (by rw [← W.hverts_mem kv hkv1, hkv2])⟩⟩
  have hincur_in : ∀ x : Fin n, x ∈ V_i → s.mem (L.bufBase + n + x.val) = cid := fun x hx =>
    (W.hincur_in x hx).1
  have hincur_out : ∀ x : Fin n, x ∉ V_i → s.mem (L.bufBase + n + x.val) ≠ cid := fun x hx => by
    rw [W.hincur_out x hx]; exact hincur₀_ne x.val x.isLt
  have hsz_le_n : size ≤ n := by
    have h1 := djpVerts_card W.D W.D.numSteps le_rfl
    have h2 : (W.D.treeVerts W.D.numSteps).card ≤ n := by
      simpa [Fintype.card_fin] using Finset.card_le_univ (W.D.treeVerts W.D.numSteps)
    rw [hsz, ← h1]; exact h2
  let S : Set ℕ :=
    Set.Ico (L.bufBase + 14 * n) (L.bufBase + 14 * n + m) ∪
    Set.Ico (L.bufBase + 14 * n + 2 * m) (L.bufBase + 14 * n + 6 * m)
  let degAt (k : ℕ) : ℕ :=
    s.mem (L.offBase + s.mem (L.bufBase + 3 * n + k) + 1) -
      s.mem (L.offBase + s.mem (L.bufBase + 3 * n + k))
  let OuterInv (k : ℕ) (a : PartCursor) (st : Memory.State) : Prop :=
    a.idx = k ∧ EmitCompInv L s V_i lift edgeState0 cEdgeLen0 mcLen0 (fun emittedIdx =>
      ∀ eIdx : Fin m, edgeState0 eIdx.val = 0 →
        (L.es[eIdx.val]'eIdx.isLt).u ∈ V_i → (L.es[eIdx.val]'eIdx.isLt).v ∈ V_i →
        (∃ r < k, s.mem (L.bufBase + 3 * n + r) = (L.es[eIdx.val]'eIdx.isLt).u.val ∨
          s.mem (L.bufBase + 3 * n + r) = (L.es[eIdx.val]'eIdx.isLt).v.val) →
        eIdx ∈ emittedIdx) a st
  have houter0 : OuterInv 0 ⟨0, cEdgeLen0⟩ s := by
    refine ⟨rfl, le_rfl, rfl, hwf, fun _ _ => rfl, [], [], List.nodup_nil, by simp,
      fun _ h => by simp at h, rfl, fun _ h => (by cases h),
      fun _ _ _ _ ⟨_, hr, _⟩ => by omega,
      fun i hi => by simp [djpWitness_edgeState W hedge₀ i hi], ?_⟩
    convert hclaimed using 2; ext i; simp [djpWitness_edgeState W hedge₀ i.val i.isLt]
  have hstep : ∀ k < liveCount, ∀ a st, OuterInv k a st → Memory.Modifies S s st →
      partEmitVertStepSafe w (vertStepD, a) st ∧ Memory.FramedTriple w st
        (partEmitVertStep (vertStepD, a)) (15 * degAt k + 3) S (OuterInv (k + 1)) := by
    intro k hk a st hinv _
    rcases hinv with ⟨ha1, hce_le, hst_fr, hst_wf, hst_mod, emitted0, comp0, hnd0, hlen0,
      hhold0, hmap0, hemit_sub0, hemit_cov0, hest0, hclaim0⟩
    have ha1_eq : a.idx = k := ha1
    have hcv_lt : L.bufBase + 3 * n + k < st.frontier := by rw [hst_fr, W.hfr]; omega
    obtain ⟨uk, huk_eq, huk_in, _⟩ := hlive_verts k hk
    have hst_below : ∀ x < L.bufBase + 14 * n, st.mem x = s.mem x := fun x hx =>
      hst_mod x (by omega)
    have huk_st : st.mem (L.bufBase + 3 * n + k) = uk.val := (hst_below _ (by omega)).trans huk_eq
    have hoff_lt : L.offBase + st.mem (L.bufBase + 3 * n + k) + 1 < st.frontier := by
      rw [huk_st, hst_fr, W.hfr]; omega
    let startJ := s.mem (L.offBase + uk.val); let endJ := s.mem (L.offBase + uk.val + 1)
    have hstart_st : st.mem (L.offBase + st.mem (L.bufBase + 3 * n + k)) = startJ := by
      rw [huk_st]; exact hst_below _ (by omega)
    have hend_st : st.mem (L.offBase + st.mem (L.bufBase + 3 * n + k) + 1) = endJ := by
      rw [huk_st]; exact hst_below _ (by omega)
    have hit := partEmitEdgeLoop_spec L s st V_i lift edgeState0 cid cEdgeLen0 mcLen0 k startJ endJ
      uk a.count W.hfr hcsr hin hincur_in hincur_out huk_in rfl rfl (hcsr.off_mono uk)
      (by simpa [endJ, Nat.add_assoc] using hcsr.offset_le_end (uk.val + 1) uk.isLt)
      hedge_local_fit hce_le hst_fr hst_wf hst_mod emitted0 comp0 hnd0 hlen0 hhold0
      hmap0 hemit_sub0 hemit_cov0 hest0 hclaim0
    dsimp only at hit
    rcases hit with ⟨hsafe_it, hvh_it, hcost_it, hfr_it, hmod_it_st, hce_le', hfr_s', hwf', hmod',
      emitted', comp', hnd', hlen', hhold', hmap', hemit_sub', hemit_cov', hest', hclaim'⟩
    have hprog_v : partEmitVertStep (vertStepD, a) =
        (Memory.read (L.bufBase + 3 * n + a.idx) >>= fun u' =>
          Memory.read (L.offBase + u') >>= fun sJ =>
            Memory.read (L.offBase + u' + 1) >>= fun eJ =>
              iterate partEmitEdgeStep edgeStepD (eJ - sJ) ⟨sJ, a.count⟩ >>= fun res =>
                pure ⟨a.idx + 1, res.count⟩) := partEmitVertStep_def _
    have hk_lt_n : k < n := by omega
    have hsafe_v : partEmitVertStepSafe w (vertStepD, a) st := by
      rw [partEmitVertStepSafe_def]; dsimp only [vertStepD]
      refine ⟨h16, L.hfit_end.of_le (by omega), ha1_eq ▸ hcv_lt, ha1_eq ▸ hoff_lt, ?_, ?_⟩
      · rw [ha1_eq, hstart_st, hend_st]; exact hcsr.off_mono uk
      · rw [ha1_eq, hstart_st, hend_st]; exact hsafe_it
    have hdeg_k : degAt k = endJ - startJ := by simp [degAt, huk_eq, startJ, endJ]
    have hft_it := FramedTriple.of_realization (S := S) hvh_it hfr_it fun x hx =>
      by_contra fun hxS => hx (hmod_it_st x hxS)
    refine ⟨hsafe_v, ?_⟩
    rw [hprog_v]
    refine FramedTriple.read_bind (c := 15 * degAt k + 2) (ha1_eq ▸ hcv_lt) ?_
    rw [ha1_eq, huk_st]
    refine FramedTriple.read_bind (c := 15 * degAt k + 1) (by rw [hst_fr, W.hfr]; omega) ?_
    refine FramedTriple.read_bind (c := 15 * degAt k) (by rw [hst_fr, W.hfr]; omega) ?_
    rw [hst_below _ (by omega : L.offBase + uk.val < L.bufBase + 14 * n),
      hst_below _ (by omega : L.offBase + uk.val + 1 < L.bufBase + 14 * n)]
    framed_triple
    · refine ⟨rfl, hce_le', hfr_s', hwf', hmod', emitted', comp',
        hnd', hlen', hhold', hmap', hemit_sub', fun eIdx he0 hu hv hcov => ?_, hest', hclaim'⟩
      refine hemit_cov' eIdx he0 hu hv ?_
      rcases hcov with ⟨r, hr, hru⟩
      · by_cases hrk : r < k
        · exact .inl ⟨r, hrk, hru.elim .inl .inr⟩
        · have hr_eq : r = k := by omega
          subst hr_eq; exact hru.elim (fun h => .inr (.inl (Fin.ext (huk_eq.symm.trans h))))
            (fun h => .inr (.inr (Fin.ext (huk_eq.symm.trans h))))
  obtain ⟨hsafe_o, hft_o⟩ := FramedTriple.iterate_sum (fun k => 15 * degAt k + 3)
    (Q := fun a t => t.frontier = s.frontier ∧ OuterInv liveCount a t) OuterInv houter0 hstep
    fun _ _ h _ => ⟨h.2.2.1, h⟩
  obtain ⟨hvh_o, hcost_o, -, -, -, hce_le_o, hfr_o, hwf_o, hmod_o, emittedIdx, compLocal,
    hnd_o, hlen_o, hhold_o, hmap_o, hemit_sub_o, hemit_cov_o, hest_o, hclaim_o⟩ :=
    FramedTriple.realization_of_frontier_eq hft_o
  have hrem_sub := remDeg_sub_tree_eq L.offBase L.bufBase size liveCount s.mem V_i dead0 lift
    hlift_inj hlive_le hverts_mem hlive_verts hverts_in_live
  have hcost_bound : memoryCost (iterate partEmitVertStep vertStepD liveCount ⟨0, cEdgeLen0⟩) s ≤
      3 * liveCount + 15 * (remDeg n L.offBase s.mem deadSet -
        remDeg n L.offBase s.mem (deadSet ∪ V_i)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      smul_eq_mul] at hcost_o
    dsimp only [degAt] at hcost_o; dsimp only [deadSet]; rw [hrem_sub] at hcost_o; omega
  let d : PartEmitCompArgs := ⟨vertStepD, hitPrev, size, cEdgeLen0⟩
  have hprog_eq : partEmitComp d = iterate partEmitVertStep vertStepD liveCount ⟨0, cEdgeLen0⟩ := by
    rw [partEmitComp_def]; dsimp only [d, liveCount]; split_ifs <;> rfl
  have hsafe_eq : partEmitCompSafe w d s := by
    rw [partEmitCompSafe_def]; refine ⟨h16, hhit_sub, ?_⟩; simpa [d, liveCount] using hsafe_o
  have hemit_iff : ∀ eIdx : Fin m, eIdx ∈ emittedIdx ↔
      edgeState0 eIdx.val = 0 ∧ (L.es[eIdx.val]'eIdx.isLt).u ∈ V_i ∧
        (L.es[eIdx.val]'eIdx.isLt).v ∈ V_i := fun eIdx => by
    refine ⟨hemit_sub_o eIdx, fun ⟨he0, hu_in, hv_in⟩ => ?_⟩
    by_cases hp0 : hitPrev = 0
    · obtain ⟨t, ht_lt, ht_m⟩ := hverts_in_live _ hu_in (W.hno_hit hp0 _ hu_in)
      exact hemit_cov_o eIdx he0 hu_in hv_in ⟨t, ht_lt, .inl ht_m⟩
    · have hp1 := W.hhit_prev hp0
      have h_alive : dead0 (L.es[eIdx.val]'eIdx.isLt).u.val = 0 ∨
          dead0 (L.es[eIdx.val]'eIdx.isLt).v.val = 0 := by
        by_contra hnot; push Not at hnot
        exact hsimp eIdx (((W.hstop_dead _ hu_in hnot.1).2.2.2 hp1.2.2.1).trans
          ((W.hstop_dead _ hv_in hnot.2).2.2.2 hp1.2.2.1).symm)
      rcases h_alive with hu_a | hv_a
      · obtain ⟨t, ht_lt, ht_m⟩ := hverts_in_live _ hu_in hu_a
        exact hemit_cov_o eIdx he0 hu_in hv_in ⟨t, ht_lt, .inl ht_m⟩
      · obtain ⟨t, ht_lt, ht_m⟩ := hverts_in_live _ hv_in hv_a
        exact hemit_cov_o eIdx he0 hu_in hv_in ⟨t, ht_lt, .inr ht_m⟩
  refine ⟨hsafe_eq, by rw [hprog_eq]; exact hvh_o, by rw [hprog_eq]; exact hfr_o,
    by rw [hprog_eq]; exact hwf_o,
    fun x hx => by
      rw [hprog_eq] at hx ⊢; by_contra hn; exact hx (hmod_o x hn),
    by rw [hprog_eq]; exact hce_le_o, by rw [hprog_eq]; exact hcost_bound,
    emittedIdx, compLocal, hnd_o, by rw [hprog_eq]; exact hlen_o, by rw [hprog_eq]; exact hhold_o,
    hmap_o, hemit_iff, fun i hi => by rw [hprog_eq]; exact hest_o i hi,
    by rw [hprog_eq]; exact hclaim_o⟩

/-! ## Corrupted-Edge Emission, Dead-Vertex Marking, and Round Metadata -/

private theorem partEmitCorrLoop_spec {w n : ℕ} (L : PartLayout w n)
    (numCorr mcLen0 cEdgeLen : ℕ) (corrIds : List (Fin L.es.length))
    (edgeState1 : ℕ → ℕ) (s : Memory.State)
    (hwf : Memory.WellFormed w s) (hfr : s.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hin : HoldsIndexedEdges L.edgeBase L.es s.mem) (hcorr_len : corrIds.length = numCorr)
    (hcorr_mem : ∀ t (ht : t < numCorr),
      s.mem (L.bufBase + 14 * n + L.es.length + t) = (corrIds[t]'(hcorr_len.symm ▸ ht)).val)
    (hest1 : ∀ i < L.es.length, s.mem (L.bufBase + 14 * n + i) = edgeState1 i)
    (hclaim : cEdgeLen + mcLen0 ≤
      (Finset.univ.filter (fun i : Fin L.es.length => edgeState1 i.val ≠ 0)).card)
    (hnum_le : numCorr ≤ L.es.length) :
    let m := L.es.length
    let d : PartEmitCorrLoopArgs := ⟨⟨L.edgeBase, L.bufBase, n, m⟩, numCorr, mcLen0⟩
    let prog := partEmitCorrLoop d
    let mRes := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    partEmitCorrLoopSafe w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
    (∀ x, s'.mem x ≠ s.mem x →
      (L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + m) ∨
      (L.bufBase + 14 * n + 6 * m + 4 * mcLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 6 * m + 4 * mRes.count)) ∧
    mcLen0 ≤ mRes.count ∧ mRes.count ≤ mcLen0 + numCorr ∧ memoryCost prog s ≤ 11 * numCorr ∧
    ∃ corrEmitted : List (Fin m),
      corrEmitted.Nodup ∧ corrEmitted.length = mRes.count - mcLen0 ∧
      HoldsIndexedEdges (L.bufBase + 14 * n + 6 * m + 4 * mcLen0)
        (corrEmitted.map fun eIdx => L.es[eIdx.val]'eIdx.isLt) s'.mem ∧
      (∀ eIdx : Fin m, eIdx ∈ corrEmitted ↔ eIdx ∈ corrIds ∧ edgeState1 eIdx.val = 0) ∧
      (∀ i < m, s'.mem (L.bufBase + 14 * n + i) =
        if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ corrEmitted then 2 else edgeState1 i) ∧
      cEdgeLen + mRes.count ≤
        (Finset.univ.filter (fun i : Fin m => s'.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card := by
  let m := L.es.length
  let stepD : PartEdgeBufEnv := ⟨L.edgeBase, L.bufBase, n, m⟩
  have h16 := L.h16; have hn_pos := L.hn_pos; have hed_buf := edge_lt_bufBase L
  let S : Set ℕ :=
    Set.Ico (L.bufBase + 14 * n) (L.bufBase + 14 * n + m) ∪
    Set.Ico (L.bufBase + 14 * n + 6 * m + 4 * mcLen0) (L.bufBase + 14 * n + 10 * m)
  let Inv (t : ℕ) (a : PartCursor) (st : Memory.State) : Prop :=
    a.idx = t ∧ mcLen0 ≤ a.count ∧ a.count ≤ mcLen0 + t ∧
    st.frontier = s.frontier ∧ Memory.WellFormed w st ∧
    (∀ x, ¬((L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + m) ∨
      (L.bufBase + 14 * n + 6 * m + 4 * mcLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 6 * m + 4 * a.count)) → st.mem x = s.mem x) ∧
    ∃ corrEmitted : List (Fin m),
      corrEmitted.Nodup ∧ corrEmitted.length = a.count - mcLen0 ∧
      HoldsIndexedEdges (L.bufBase + 14 * n + 6 * m + 4 * mcLen0)
        (corrEmitted.map fun eIdx => L.es[eIdx.val]'eIdx.isLt) st.mem ∧
      (∀ eIdx ∈ corrEmitted, eIdx ∈ corrIds ∧ edgeState1 eIdx.val = 0) ∧
      (∀ r (hr : r < numCorr), r < t →
        let eIdx := corrIds[r]'(hcorr_len.symm ▸ hr)
        edgeState1 eIdx.val = 0 → eIdx ∈ corrEmitted) ∧
      (∀ i < m, st.mem (L.bufBase + 14 * n + i) =
        if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ corrEmitted then 2 else edgeState1 i) ∧
      cEdgeLen + a.count ≤
        (Finset.univ.filter (fun i : Fin m => st.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card
  have hinv0 : Inv 0 ⟨0, mcLen0⟩ s := by
    refine ⟨rfl, le_rfl, le_rfl, rfl, hwf, fun _ _ => rfl, [], List.nodup_nil, by simp,
      fun _ h => by simp at h, fun _ h => (by cases h), fun _ _ hr => by omega,
      fun i hi => by simp [hest1 i hi], ?_⟩
    convert hclaim using 2; ext i; simp [hest1 i.val i.isLt]
  have hstep : ∀ t < numCorr, ∀ a st, Inv t a st → Memory.Modifies S s st →
      partEmitCorrStepSafe w (stepD, a) st ∧
      Memory.FramedTriple w st (partEmitCorrStep (stepD, a)) 11 S (Inv (t + 1)) := by
    intro t ht a st hinv _
    rcases hinv with ⟨ha1, ha2_ge, ha2_le, hst_fr, hst_wf, hst_mod, corrEmitted, hnd_ce, hlen_ce,
      hhold_ce, hce_sub, hce_cov, hst_es, hclaim_st⟩
    let eFin : Fin m := corrIds[t]'(hcorr_len.symm ▸ ht)
    have hcb_lt : L.bufBase + 14 * n + m + a.idx < st.frontier := by rw [hst_fr, hfr]; omega
    have hst_agree_corr : st.mem (L.bufBase + 14 * n + m + a.idx) = eFin.val := by
      rw [hst_mod _ (by omega), ha1]; exact hcorr_mem t ht
    have hst_lt : L.bufBase + 14 * n + eFin.val < st.frontier := by rw [hst_fr, hfr]; omega
    have ht1_fit : Fits w (a.idx + 1) := L.hfit_end.of_le (by omega)
    have hbuf_fit : Fits w (L.bufBase + 14 * n + 14 * m) := L.hfit_end.of_le (by omega)
    have hcard_le_m : (Finset.univ.filter (fun i : Fin m =>
        st.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card ≤ m := by
      simpa using Finset.card_le_univ
        (Finset.univ.filter (fun i : Fin m => st.mem (L.bufBase + 14 * n + i.val) ≠ 0))
    have hmc1_fit : Fits w (a.count + 1) := L.hfit_end.of_le (by dsimp only [m] at *; omega)
    have hprog_s : partEmitCorrStep (stepD, a) =
        (Memory.read (L.bufBase + 14 * n + m + a.idx) >>= fun eIdx =>
          Memory.read (L.bufBase + 14 * n + eIdx) >>= fun stv =>
            if stv = 0 then
              Memory.write (L.bufBase + 14 * n + eIdx) 2 >>= fun _ =>
                partCopyIndexedEdge ⟨L.edgeBase, L.bufBase + 14 * n + 6 * m, eIdx, a.count⟩ >>=
                  fun _ => pure ⟨a.idx + 1, a.count + 1⟩
            else pure ⟨a.idx + 1, a.count⟩) := partEmitCorrStep_def _
    by_cases hst0 : st.mem (L.bufBase + 14 * n + eFin.val) = 0
    · have hfilt_lt : (Finset.univ.filter (fun i : Fin m =>
          st.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card < m :=
        filter_ne_zero_card_lt (fun i : Fin m => st.mem (L.bufBase + 14 * n + i.val)) eFin hst0
      have hmc_lt_m : a.count < m := by dsimp only [m] at *; omega
      let st₁ : Memory.State :=
        ⟨Function.update st.mem (L.bufBase + 14 * n + eFin.val) 2, st.frontier⟩
      have hwf₁ : Memory.WellFormed w st₁ := ⟨hst_wf.frontier_fits, fun x => by
        by_cases hx : x = L.bufBase + 14 * n + eFin.val
        · subst hx; simpa [st₁] using h16.of_le (by omega)
        · simpa [st₁, hx] using hst_wf.mem_fits x⟩
      have hcp := partCopyIndexedEdge_spec (srcBase := L.edgeBase)
        (dstBase := L.bufBase + 14 * n + 6 * m) (srcIdx := eFin.val) (dstIdx := a.count)
        (s := st₁) h16 hwf₁ (by dsimp only [st₁]; rw [hst_fr, hfr]; omega)
        (by dsimp only [st₁]; rw [hst_fr, hfr]; dsimp only [m] at *; omega)
      rcases hcp with ⟨hsafe_cp, hvh_cp, hcost_cp, hfr_cp, hwf_cp, hmod_cp, hv0, hv1, hv2, hv3⟩
      set st₂ := (Memory.spec 0).clientState st₁
        (partCopyIndexedEdge ⟨L.edgeBase, L.bufBase + 14 * n + 6 * m, eFin.val, a.count⟩)
      have hsafe_s : partEmitCorrStepSafe w (stepD, a) st := by
        rw [partEmitCorrStepSafe_def]
        refine ⟨h16, ht1_fit, hmc1_fit, hbuf_fit, hcb_lt,
          by simpa [stepD, hst_agree_corr] using hst_lt, fun _ => ?_⟩
        simpa [stepD, hst_agree_corr] using hsafe_cp
      have hin_st1 : HoldsIndexedEdges L.edgeBase L.es st₁.mem :=
        (partCongrEdges_of_agree_buf L fun x hx => by
          dsimp only [st₁]; rw [Function.update_of_ne (by omega)]; exact hst_mod x (by omega)).1 hin
      have hmod_step : ∀ x, ¬((L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + m) ∨
          (L.bufBase + 14 * n + 6 * m + 4 * a.count ≤ x ∧
            x < L.bufBase + 14 * n + 6 * m + 4 * a.count + 4)) →
          st₂.mem x = st.mem x := fun x hx => by
        rw [hmod_cp x (fun h => hx (.inr h))]; dsimp only [st₁]
        have := eFin.isLt; dsimp only [m] at *
        rw [Function.update_of_ne]
        intro h; exact hx (.inl ⟨by omega, by omega⟩)
      have he_not_ce : eFin ∉ corrEmitted := fun hm => by
        have h1 := hst_es eFin.val eFin.isLt
        have hm' : ∃ hlt : eFin.val < m, (⟨eFin.val, hlt⟩ : Fin m) ∈ corrEmitted := ⟨eFin.isLt, hm⟩
        simp only [hm', ↓reduceIte] at h1; omega
      have he1_z : edgeState1 eFin.val = 0 := by
        have h1 := hst_es eFin.val eFin.isLt; rw [hst0] at h1
        split_ifs at h1; exact h1.symm
      obtain ⟨hu, hv, hw, hid⟩ := hin_st1 eFin.val eFin.isLt
      have hhold_new : HoldsIndexedEdges (L.bufBase + 14 * n + 6 * m + 4 * mcLen0)
          ((corrEmitted ++ [eFin]).map fun i => L.es[i.val]'i.isLt) st₂.mem := by
        rw [List.map_append, List.map_singleton]
        refine holdsIndexedEdges_append (hhold_ce.congr fun x _ hx2 => by
          rw [List.length_map, hlen_ce] at hx2; exact hmod_cp x (by omega) |>.trans (by
            dsimp only [st₁]; rw [Function.update_of_ne (by omega)])) fun i hi => ?_
        have hi0 : i = 0 := Nat.lt_one_iff.mp hi; subst hi0; dsimp only [m] at *
        rw [List.length_map, hlen_ce,
          show L.bufBase + 14 * n + 6 * L.es.length + 4 * mcLen0 +
            4 * (a.count - mcLen0) + 4 * 0 =
            L.bufBase + 14 * n + 6 * L.es.length + 4 * a.count by omega]
        exact ⟨hv0.trans hu, hv1.trans hv, hv2.trans hw, hv3.trans hid⟩
      have hft_cp := FramedTriple.of_realization (S := S) hvh_cp hfr_cp fun x hx =>
        by_contra fun hxS => hx (hmod_cp x fun h => hxS (by
          simp only [S, Set.mem_union, Set.mem_Ico]; omega))
      refine ⟨hsafe_s, ?_⟩
      rw [hprog_s]
      refine FramedTriple.read_bind (c := 10) hcb_lt ?_
      rw [hst_agree_corr]
      refine FramedTriple.read_bind (c := 9) hst_lt ?_
      simp only [hst0, ↓reduceIte]
      framed_triple
      · change Inv (t + 1) ⟨a.idx + 1, a.count + 1⟩ st₂
        dsimp only [Inv, m] at *
        refine ⟨by omega, by omega, by omega, hfr_cp.trans hst_fr, hwf_cp, fun x hx => ?_,
          corrEmitted ++ [eFin],
          List.nodup_append.mpr ⟨hnd_ce, List.nodup_singleton _, fun _ ha _ hb heq => by
            subst heq; rw [List.mem_singleton.mp hb] at ha; exact he_not_ce ha⟩,
          by simp [hlen_ce]; omega, hhold_new,
          fun e' he' => ?_, fun r hr hrt he0 => ?_, fun i hi => ?_, ?_⟩
        · exact (hmod_step x fun h =>
              hx (by rcases h with h | h; exacts [.inl h, .inr (by omega)])).trans
            (hst_mod x fun h => hx (by rcases h with h | h; exacts [.inl h, .inr (by omega)]))
        · rcases List.mem_append.mp he' with he' | he'
          · exact hce_sub e' he'
          · rw [List.mem_singleton.mp he']; exact ⟨List.getElem_mem _, he1_z⟩
        · by_cases hrt' : r < t
          · exact List.mem_append_left _ (hce_cov r hr hrt' he0)
          · have hrt_eq : r = t := by omega
            subst hrt_eq; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        · by_cases hie : i = eFin.val
          · subst hie
            rw [hmod_cp (L.bufBase + 14 * n + eFin.val) (by omega)]; dsimp only [st₁]
            rw [Function.update_self]
            split_ifs with hm'
            · rfl
            · exact absurd ⟨hi, by simp⟩ hm'
          · have hne_f : (⟨i, hi⟩ : Fin L.es.length) ≠ eFin := fun h => hie (congrArg Fin.val h)
            rw [hmod_cp _ (by omega)]; dsimp only [st₁]
            rw [Function.update_of_ne (by omega), hst_es i hi]
            simp only [List.mem_append, List.mem_singleton, hne_f, or_false]
        · have hc := card_filter_ne_zero_add_one
              (fun i : Fin L.es.length => st.mem (L.bufBase + 14 * n + i.val))
              (fun i : Fin L.es.length => st₂.mem (L.bufBase + 14 * n + i.val))
              eFin hst0
              (by rw [hmod_cp _ (by omega)]; dsimp only [st₁]; rw [Function.update_self]; omega)
              fun i hne => by
            have := Fin.val_ne_of_ne hne
            rw [hmod_cp _ (by omega)]; dsimp only [st₁]; rw [Function.update_of_ne (by omega)]
          dsimp only [st₂] at hc ⊢; omega
    · have hsafe_s : partEmitCorrStepSafe w (stepD, a) st := by
        rw [partEmitCorrStepSafe_def]
        exact ⟨h16, ht1_fit, hmc1_fit, hbuf_fit, hcb_lt,
          by simpa [stepD, hst_agree_corr] using hst_lt,
          fun h0 => absurd h0 (by simpa [stepD, hst_agree_corr] using hst0)⟩
      refine ⟨hsafe_s, ?_⟩
      rw [hprog_s]
      refine FramedTriple.read_bind (c := 10) hcb_lt ?_
      rw [hst_agree_corr]
      refine FramedTriple.read_bind (c := 9) hst_lt ?_
      simp only [hst0, ↓reduceIte]
      refine FramedTriple.pure ?_
      refine ⟨by dsimp only; omega, ha2_ge, by dsimp only; omega, hst_fr, hst_wf, hst_mod,
        corrEmitted, hnd_ce, hlen_ce, hhold_ce, hce_sub, fun r hr hrt he0 => ?_, hst_es, hclaim_st⟩
      by_cases hrt' : r < t
      · exact hce_cov r hr hrt' he0
      · have hrt_eq : r = t := by omega
        have he_eq : eFin = corrIds[r]'(hcorr_len.symm ▸ hr) := Fin.ext (by simp [eFin, hrt_eq])
        rw [← he_eq] at he0
        have h1 := hst_es eFin.val eFin.isLt
        split_ifs at h1 with hm
        · exact he_eq ▸ hm.choose_spec
        · exact absurd (h1.trans he0) hst0
  obtain ⟨hsafe_it, hft⟩ := FramedTriple.iterate
    (Q := fun a t => t.frontier = s.frontier ∧ Inv numCorr a t) Inv hinv0 hstep
    fun _ _ h _ => ⟨h.2.2.2.1, h⟩
  obtain ⟨hvh_it, hcost_it, -, -, -, hmc_ge, hmc_le, hfr', hwf', hmod', corrEmitted, hnd_ce,
    hlen_ce, hhold_ce, hce_sub, hce_cov, hest', hclaim'⟩ :=
    FramedTriple.realization_of_frontier_eq hft
  let d : PartEmitCorrLoopArgs := ⟨stepD, numCorr, mcLen0⟩
  have hprog : partEmitCorrLoop d = iterate partEmitCorrStep stepD numCorr ⟨0, mcLen0⟩ :=
    partEmitCorrLoop_def d
  dsimp only [m] at *
  refine ⟨by rw [partEmitCorrLoopSafe_def]; exact ⟨h16, hsafe_it⟩, by rw [hprog]; exact hvh_it,
    by rw [hprog]; exact hfr', by rw [hprog]; exact hwf', fun x hx => by
      rw [hprog] at hx ⊢; by_contra hnot; exact hx (hmod' x hnot),
    by rw [hprog]; exact hmc_ge, by rw [hprog]; exact hmc_le, by rw [hprog]; exact hcost_it,
    corrEmitted, hnd_ce, by rw [hprog]; exact hlen_ce, by rw [hprog]; exact hhold_ce,
    fun eIdx => ⟨fun hm => hce_sub eIdx hm, fun ⟨hm, he0⟩ => by
      obtain ⟨r, hr, hget⟩ := List.getElem_of_mem hm
      exact (Fin.ext (congrArg Fin.val hget)) ▸
        hce_cov r (by omega) (by omega) (by simpa [hget] using he0)⟩,
    fun i hi => by rw [hprog]; exact hest' i hi, by rw [hprog]; exact hclaim'⟩

/-- Specification of dead-vertex and lift-array marking (`partMarkDeadLoop`). -/
theorem partMarkDeadLoop_spec {w n : ℕ} (L : PartLayout w n)
    (size cLiftLen0 : ℕ) (lift : Fin size → Fin n) (dead0 : ℕ → ℕ) (s : Memory.State)
    (hwf : Memory.WellFormed w s) (hfr : s.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hsz_le : size ≤ n) (hcl_le : cLiftLen0 + size ≤ 2 * n)
    (hverts : ∀ k : Fin size, s.mem (L.bufBase + 3 * n + k.val) = (lift k).val)
    (hdead : ∀ x < n, s.mem (L.bufBase + x) = dead0 x) :
    let d : PartMarkDeadLoopArgs := ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩
    let prog := partMarkDeadLoop d
    let lRes := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    partMarkDeadLoopSafe w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
    (∀ x, s'.mem x ≠ s.mem x →
      (L.bufBase ≤ x ∧ x < L.bufBase + n) ∨
      (L.bufBase + 4 * n + cLiftLen0 ≤ x ∧ x < L.bufBase + 4 * n + lRes.count)) ∧
    lRes.count = cLiftLen0 + size ∧ memoryCost prog s ≤ 3 * size ∧
    (∀ k : Fin size, s'.mem (L.bufBase + 4 * n + cLiftLen0 + k.val) = (lift k).val) ∧
    (∀ x : Fin n, s'.mem (L.bufBase + x.val) =
      if ∃ k : Fin size, lift k = x then 1 else dead0 x.val) := by
  have h16 := L.h16; have hfit := L.hfit_end
  obtain ⟨hsafe, hft⟩ := Memory.FramedTriple.iterate (w := w) (s := s) (body := partMarkDeadStep)
    (safe := partMarkDeadStepSafe) (d := ⟨L.bufBase, n⟩) (n := size) (a₀ := ⟨0, cLiftLen0⟩) (c := 3)
    (S := {x | (L.bufBase ≤ x ∧ x < L.bufBase + n) ∨
      (L.bufBase + 4 * n + cLiftLen0 ≤ x ∧ x < L.bufBase + 4 * n + (cLiftLen0 + size))})
    (Q := fun a t => t.frontier = s.frontier ∧ a.count = cLiftLen0 + size ∧
      (∀ k : Fin size, t.mem (L.bufBase + 4 * n + cLiftLen0 + k.val) = (lift k).val) ∧
      ∀ x : Fin n, t.mem (L.bufBase + x.val) =
        if ∃ k : Fin size, lift k = x then 1 else dead0 x.val)
    (fun t a st => a.idx = t ∧ a.count = cLiftLen0 + t ∧ st.frontier = s.frontier ∧
      (∀ k : Fin size, k.val < t → st.mem (L.bufBase + 4 * n + cLiftLen0 + k.val) = (lift k).val) ∧
      ∀ x : Fin n, st.mem (L.bufBase + x.val) =
        if ∃ k : Fin size, k.val < t ∧ lift k = x then 1 else dead0 x.val)
    ⟨rfl, rfl, rfl, fun _ h => by omega, fun x => by simp [hdead x.val x.isLt]⟩
    (fun t ht a st ⟨ha1, ha2, hst_fr, hcl_vals, hdead_vals⟩ ⟨_, hframe⟩ => by
      let kFin : Fin size := ⟨t, ht⟩; let vk : Fin n := lift kFin; have hvk := vk.isLt
      have hv_eq : st.mem (L.bufBase + 3 * n + a.idx) = vk.val :=
        (hframe _ (by omega) (by region_omega)).trans (ha1 ▸ hverts kFin)
      have hvfit : Fits w (st.mem (L.bufBase + 3 * n + a.idx)) := hv_eq ▸ hfit.of_le (by omega)
      refine ⟨by rw [partMarkDeadStepSafe_def]; dsimp only; exact ⟨h16, by fits, by fits, by omega,
        by omega, by omega⟩, ?_⟩
      rw [partMarkDeadStep_def]; framed_triple
      simp only [hv_eq]
      refine ⟨by omega, by omega, hst_fr, fun k hk => ?_, fun x => ?_⟩
      · by_cases hkt : k.val = t
        · simp (disch := omega) only [Function.update_apply, ite_eq_left, ite_eq_right]
          exact congrArg (fun k => (lift k).val) (Fin.ext hkt.symm : kFin = k)
        · simp (disch := omega) only [Function.update_apply, ite_eq_right]
          exact hcl_vals k (by omega)
      · by_cases hxv : x = vk
        · subst hxv
          simp only [Function.update_apply, ↓reduceIte]
          rw [ite_eq_left ⟨kFin, by simp [kFin], rfl⟩]
        · simp (disch := (have := Fin.val_ne_of_ne hxv; omega)) only [Function.update_apply,
            ite_eq_right]
          rw [hdead_vals x]
          refine if_congr ⟨fun ⟨k, hk1, hkx⟩ => ⟨k, by omega, hkx⟩, fun ⟨k, hk1, hkx⟩ =>
            ⟨k, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk1) fun hkt => hxv ?_, hkx⟩⟩ rfl rfl
          exact hkx.symm.trans (congrArg lift (Fin.ext hkt)))
    fun a t h _ => ⟨h.2.2.1, h.2.1, fun k => h.2.2.2.1 k k.isLt, fun x => by
      simpa using h.2.2.2.2 x⟩
  rw [← partMarkDeadLoop_def ⟨⟨L.bufBase, n⟩, size, cLiftLen0⟩] at hft
  obtain ⟨hv, hc, hfr', hS, hcnt, hcl', hdead'⟩ := FramedTriple.realization_of_frontier_eq hft
  exact ⟨by rw [partMarkDeadLoopSafe_def]; exact ⟨h16, hsafe⟩, hv, hfr',
    wellFormed_clientState hwf hv, fun x hx => by rw [hcnt]; exact hS x hx, hcnt, hc, hcl', hdead'⟩

/-- Specification of round metadata writes (`partWriteRoundMeta`). -/
theorem partWriteRoundMeta_spec {w n : ℕ} (L : PartLayout w n)
    (numComps size cLen cEdgeBase cLiftBase : ℕ) (s : Memory.State)
    (hwf : Memory.WellFormed w s) (hfr : s.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hnc : numComps < n) (hsz_fit : Fits w size) (hcl_fit : Fits w cLen)
    (hce_fit : Fits w cEdgeBase) (hclf_fit : Fits w cLiftBase) :
    let d : PartWriteRoundMetaArgs := ⟨L.bufBase, n, numComps, size, cLen, cEdgeBase, cLiftBase⟩
    let prog := partWriteRoundMeta d
    let s' := (Memory.spec 0).clientState s prog
    partWriteRoundMetaSafe w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
    (∀ x, s'.mem x ≠ s.mem x →
      (L.bufBase + 6 * n + 3 * numComps ≤ x ∧ x < L.bufBase + 6 * n + 3 * (numComps + 1)) ∨
      x = L.bufBase + 9 * n + numComps) ∧
    memoryCost prog s = 4 ∧
    s'.mem (L.bufBase + 6 * n + 3 * numComps) = size ∧
    s'.mem (L.bufBase + 6 * n + 3 * numComps + 1) = cLen ∧
    s'.mem (L.bufBase + 6 * n + 3 * numComps + 2) = cEdgeBase ∧
    s'.mem (L.bufBase + 9 * n + numComps) = cLiftBase := by
  have h16 := L.h16
  obtain ⟨hv, -, hfr', hS, h0, h1, h2, h3⟩ :=
    FramedTriple.realization_of_frontier_eq (w := w) (s := s) (c := 4)
    (p := partWriteRoundMeta ⟨L.bufBase, n, numComps, size, cLen, cEdgeBase, cLiftBase⟩)
    (S := {x | (L.bufBase + 6 * n + 3 * numComps ≤ x ∧ x < L.bufBase + 6 * n + 3 * (numComps + 1)) ∨
      x = L.bufBase + 9 * n + numComps})
    (Q := fun _ t => t.mem (L.bufBase + 6 * n + 3 * numComps) = size ∧
      t.mem (L.bufBase + 6 * n + 3 * numComps + 1) = cLen ∧
      t.mem (L.bufBase + 6 * n + 3 * numComps + 2) = cEdgeBase ∧
      t.mem (L.bufBase + 9 * n + numComps) = cLiftBase) (by
    rw [partWriteRoundMeta_def]; framed_triple
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
      simp (disch := omega) only [Function.update_apply, ite_eq_right, ↓reduceIte])
  refine ⟨by rw [partWriteRoundMetaSafe_def]; dsimp only; exact ⟨h16, by omega, by omega⟩, hv, hfr',
    wellFormed_clientState hwf hv, hS, ?_, h0, h1, h2, h3⟩
  simp [partWriteRoundMeta_def, memoryCost_bind', memoryCost_write, client_simps]

/-- Specification of corrupted-item collection and `M_C` edge emission in `partRoundFinish`. -/
theorem partRoundFinish_corr_spec {w n : ℕ} (L : PartLayout w n)
    (ic0 nc0 mcLen0 cEdgeLen : ℕ) (h₀ : SHHandle) (roots : List SHTree)
    (created : ℕ → ℕ) (edgeState1 : ℕ → ℕ) (s₁ : Memory.State)
    (hsh₁ : SHInv w ic0 nc0 (2 * L.es.length) (4 * L.es.length) h₀ roots created s₁)
    (hfr₁ : s₁.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hib₀ : h₀.itemBase = L.itemBase) (hnb₀ : h₀.nodeBase = L.nodeBase)
    (hrt₀ : h₀.rankThreshold = partRankThreshold)
    (hin₁ : HoldsIndexedEdges L.edgeBase L.es s₁.mem)
    (hest₁ : ∀ i < L.es.length, s₁.mem (L.bufBase + 14 * n + i) = edgeState1 i)
    (hent_id : ∀ p ∈ forestEntries roots, ∃ eIdx : Fin L.es.length, p.1.val = eIdx.val)
    (hclaim : cEdgeLen + mcLen0 ≤
      (Finset.univ.filter (fun i : Fin L.es.length => edgeState1 i.val ≠ 0)).card) :
    let m := L.es.length
    let pCorr := shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + m, 0, 2 * m)
    let numCorr := (Memory.spec 0).clientResult s₁ pCorr
    let s₂ := (Memory.spec 0).clientState s₁ pCorr
    let pMc := partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, m⟩, numCorr, mcLen0⟩
    let mRes := (Memory.spec 0).clientResult s₂ pMc
    let s₃ := (Memory.spec 0).clientState s₂ pMc
    shCollectCorruptedSafe w (h₀, nc0, L.bufBase + 14 * n + m, 0, 2 * m) s₁ ∧
    (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ pCorr) ∧
    partEmitCorrLoopSafe w ⟨⟨L.edgeBase, L.bufBase, n, m⟩, numCorr, mcLen0⟩ s₂ ∧
    (Memory.spec w).ValidHistory s₂ ((Memory.spec w).clientHistory s₂ pMc) ∧
    s₃.frontier = s₁.frontier ∧ Memory.WellFormed w s₃ ∧
    SHInv w ic0 nc0 (2 * m) (4 * m) h₀ roots created s₃ ∧
    mcLen0 ≤ mRes.count ∧ 16 * (mRes.count - mcLen0) ≤ h₀.itemCount - ic0 ∧
    memoryCost pCorr s₁ + memoryCost pMc s₂ ≤ 20 * (h₀.itemCount - ic0) ∧
    (∀ x, s₃.mem x ≠ s₁.mem x →
      (L.bufBase + 14 * n ≤ x ∧ x < L.bufBase + 14 * n + 2 * m) ∨
      (L.bufBase + 14 * n + 6 * m + 4 * mcLen0 ≤ x ∧
        x < L.bufBase + 14 * n + 6 * m + 4 * mRes.count)) ∧
    ∃ (corrIds corrEmitted : List (Fin m)),
      corrEmitted.Nodup ∧ corrEmitted.length = mRes.count - mcLen0 ∧
      HoldsIndexedEdges (L.bufBase + 14 * n + 6 * m + 4 * mcLen0)
        (corrEmitted.map fun eIdx => L.es[eIdx.val]'eIdx.isLt) s₃.mem ∧
      (∀ eIdx : Fin m, eIdx ∈ corrEmitted ↔ eIdx ∈ corrIds ∧ edgeState1 eIdx.val = 0) ∧
      (∀ i < m, s₃.mem (L.bufBase + 14 * n + i) =
        if ∃ hlt : i < m, (⟨i, hlt⟩ : Fin m) ∈ corrEmitted then 2 else edgeState1 i) ∧
      cEdgeLen + mRes.count ≤
        (Finset.univ.filter (fun i : Fin m => s₃.mem (L.bufBase + 14 * n + i.val) ≠ 0)).card ∧
      (∀ eIdx ∈ corrEmitted, edgeState1 eIdx.val = 0) ∧
      (∀ eIdx : Fin m, edgeState1 eIdx.val = 0 → eIdx ∉ corrEmitted →
        ∀ p ∈ forestEntries roots, p.1.val = eIdx.val → p.2 ≤ p.1.origKey) := by
  let m := L.es.length
  let corrPairs := (forestEntries roots).filter (fun p => decide (p.1.origKey < p.2))
  have hcorr_pow := shInv_corrupted_le hsh₁; rw [hrt₀] at hcorr_pow
  have hcorr_le16 : 16 * corrPairs.length ≤ h₀.itemCount - ic0 := by
    dsimp only [corrPairs, partRankThreshold] at hcorr_pow ⊢; omega
  have hic_le := hsh₁.ic_max; have hcorr_le_m : corrPairs.length ≤ m := by omega
  have hcorr := shCollectCorrupted_spec (w := w) (ic₀ := ic0) (nc₀ := nc0)
    (maxItems := 2 * m) (maxNodes := 4 * m)
    (outBase := L.bufBase + 14 * n + m) (outCount := 0) (outCap := m) (fuel := 2 * m)
    hsh₁ (by omega) (by simpa using hcorr_le_m) (by rw [hfr₁]; omega)
    (L.hfit_end.of_le (by omega)) fun a ha1 _ hp => by
      have := L.inSHPool_lt_bufBase hib₀ hnb₀ hp; omega
  dsimp only at hcorr
  generalize h_numCorr : (Memory.spec 0).clientResult s₁
    (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + m, 0, 2 * m)) = numCorr at *
  generalize h_s2 : (Memory.spec 0).clientState s₁
    (shCollectCorrupted (h₀, nc0, L.bufBase + 14 * n + m, 0, 2 * m)) = s₂ at *
  rcases hcorr with ⟨hvh2, hsafe2, hncorr_eq, hfr2, hmod2, hsh_s2, hperm2, hcost2⟩
  have hcorr_len_eq : numCorr = corrPairs.length := by simpa using hncorr_eq
  let corrVals := (List.range numCorr).map (fun i => s₂.mem (L.bufBase + 14 * n + m + i))
  have hvals_perm : corrVals.Perm (corrPairs.map fun p => p.1.val) := by
    simpa [corrVals, Nat.sub_zero, Nat.add_zero] using hperm2
  have hvals_lt : ∀ x ∈ corrVals, x < m := fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (hvals_perm.subset hx)
    obtain ⟨eIdx, he_id⟩ := hent_id p (List.mem_filter.mp hp).1
    exact he_id ▸ eIdx.isLt
  obtain ⟨corrIds, hcorr_map⟩ := finList_of_natList corrVals hvals_lt
  have hcorrIds_len : corrIds.length = numCorr := by
    have := congrArg List.length hcorr_map; simpa [corrVals] using this
  have hcorr_mem : ∀ t (ht : t < numCorr),
      s₂.mem (L.bufBase + 14 * n + m + t) = (corrIds[t]'(hcorrIds_len.symm ▸ ht)).val := by
    intro t ht
    have h1 : corrVals[t]'(by simp [corrVals, ht]) = s₂.mem (L.bufBase + 14 * n + m + t) := by
      simp [corrVals]
    have h2 : (corrIds.map Fin.val)[t]'(by simp [hcorrIds_len, ht]) =
        (corrIds[t]'(hcorrIds_len.symm ▸ ht)).val := by simp
    rw [← h1, ← h2]; congr 1; exact hcorr_map.symm
  have hs2_agree : ∀ x, ¬(L.bufBase + 14 * n + m ≤ x ∧ x < L.bufBase + 14 * n + m + numCorr) →
      s₂.mem x = s₁.mem x := fun x hx => by_contra fun hne => hx (by simpa using hmod2 x hne)
  have hin_s2 : HoldsIndexedEdges L.edgeBase L.es s₂.mem :=
    (partCongrEdges_of_agree_buf L fun x hx => hs2_agree x (by omega)).1 hin₁
  have hest_s2 : ∀ i < m, s₂.mem (L.bufBase + 14 * n + i) = edgeState1 i := fun i hi =>
    (hs2_agree _ (by omega)).trans (hest₁ i hi)
  have hemitCorr := partEmitCorrLoop_spec L numCorr mcLen0 cEdgeLen corrIds edgeState1 s₂
    hsh_s2.wf (hfr2.trans hfr₁) hin_s2 hcorrIds_len hcorr_mem hest_s2 hclaim (by omega)
  dsimp only at hemitCorr
  generalize h_mRes : (Memory.spec 0).clientResult s₂
    (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, m⟩, numCorr, mcLen0⟩) = mRes at *
  generalize h_s3 : (Memory.spec 0).clientState s₂
    (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, m⟩, numCorr, mcLen0⟩) = s₃ at *
  rcases hemitCorr with ⟨hsafe3, hvh3, hfr3, hwf3, hmod3, hmc_ge, hmc_le, hcost3,
    corrEmitted, hnd_corr, hlen_corr, hhold_corr, hcorr_iff, hest3, hclaim3⟩
  dsimp only [m] at *
  have hdiff_le : mRes.count - mcLen0 ≤ corrPairs.length := by rw [← hcorr_len_eq]; omega
  have h16_sub : 16 * (mRes.count - mcLen0) ≤ h₀.itemCount - ic0 :=
    (Nat.mul_le_mul_left 16 hdiff_le).trans hcorr_le16
  have hcost_mc : memoryCost (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, L.es.length⟩,
      numCorr, mcLen0⟩) s₂ ≤ 11 * corrPairs.length := by
    rw [← hcorr_len_eq]; exact hcost3
  have hcost_sum : memoryCost (shCollectCorrupted
      (h₀, nc0, L.bufBase + 14 * n + L.es.length, 0, 2 * L.es.length)) s₁ +
      memoryCost (partEmitCorrLoop ⟨⟨L.edgeBase, L.bufBase, n, L.es.length⟩,
        numCorr, mcLen0⟩) s₂ ≤ 20 * (h₀.itemCount - ic0) := by omega
  have hsh_s3 : SHInv w ic0 nc0 (2 * L.es.length) (4 * L.es.length) h₀ roots created s₃ :=
    partCongrSh_of_mod_ge L hib₀ hnb₀ hsh_s2 hwf3 hfr3 fun x hx => by
      rcases hmod3 x hx with h | h <;> omega
  rw [h_numCorr, h_s2, h_mRes, h_s3]
  refine ⟨hsafe2, hvh2, hsafe3, hvh3, hfr3.trans hfr2, hwf3, hsh_s3, hmc_ge, h16_sub, hcost_sum,
    fun x hx => ?_, corrIds, corrEmitted, hnd_corr, hlen_corr, hhold_corr, hcorr_iff, hest3,
    hclaim3, fun eIdx he => ((hcorr_iff eIdx).mp he).2, ?_⟩
  · by_cases hx2 : s₃.mem x = s₂.mem x
    · left; have := hmod2 x (hx2 ▸ hx); omega
    · rcases hmod3 x hx2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [left; right] <;> [omega; exact ⟨h1, h2⟩]
  · intro eIdx he1 hnot_ce p hp he_eq; by_contra hlt
    have hp_cp : p ∈ corrPairs := List.mem_filter.mpr ⟨hp, decide_eq_true (Nat.lt_of_not_ge hlt)⟩
    have hmem_v : eIdx.val ∈ corrVals := hvals_perm.mem_iff.mpr (List.mem_map.mpr ⟨p, hp_cp, he_eq⟩)
    rw [← hcorr_map, List.mem_map] at hmem_v; obtain ⟨e', he', he'_eq⟩ := hmem_v
    have he_ids : e' = eIdx := Fin.ext he'_eq; subst he_ids
    exact hnot_ce ((hcorr_iff e').mpr ⟨he', he1⟩)

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
