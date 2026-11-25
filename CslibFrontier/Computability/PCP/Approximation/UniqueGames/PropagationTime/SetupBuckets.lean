/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime.Layout
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Phase 1–2 symbolic execution: header setup, `slots` scan, and incidence-list construction

This internal module defines and certifies `setupCode` (header loading, `slots g` scan over input
edges, and workspace base-address computation) and `bucketsLoop` (reverse-order linked
incidence-list construction matching `buckets (slots g) g.edges = adj g`).

## Main definitions

* `Cslib.Complexity.UniqueGames.Propagation.setupCode`: header, `slots`, and layout setup code.
* `Cslib.Complexity.UniqueGames.Propagation.bucketsLoop`: incidence-list construction loop.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.slotsSetup_spec`: `ExecWithin` specification for
  `setupCode` establishing `ConstRegs` and `InputAt` with zeroed workspace above `headBase g`.
* `Cslib.Complexity.UniqueGames.Propagation.bucketsLoop_spec`: `ExecWithin` specification for
  `bucketsLoop` establishing `BucketsAt g` while preserving zeroed workspace from `visBase g` up.
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded Cslib.WordRAM Cslib.WordRAM.Block Reg

private def initSetupCode : Code .standard 34 := ram[
  rZero ← #0;
  rOne ← #1;
  rTwo ← #2;
  rL ← *rOne;
  rStride ← rL + rTwo;
  rN ← *rTwo;
  rTmp1 ← #3;
  rE ← *rTmp1;
  rEdgeBase ← #4;
  rOuterIdx ← rZero ]

private def slotsBody : Code .standard 34 := ram[
  rTmp1 ← rOuterIdx * rStride;
  rTmp1 ← rEdgeBase + rTmp1;
  rSrc ← *rTmp1;
  rTmp2 ← rTmp1 + rOne;
  rDst ← *rTmp2;
  rTmp3 ← rSrc + rOne;
  if rN < rTmp3 then [ rN ← rTmp3 ] else [ rN ← rN ];
  rTmp3 ← rDst + rOne;
  if rN < rTmp3 then [ rN ← rTmp3 ] else [ rN ← rN ];
  rOuterIdx ← rOuterIdx + rOne ]

private def slotsLoop : Code .standard 34 :=
  .loop (.lt rOuterIdx rE) slotsBody

private def layoutSetupA : Code .standard 34 := ram[
  rHeadBase ← *rZero;
  rHeadBase ← rHeadBase + rOne;
  rNodeBase ← rHeadBase + rN;
  rTmp1 ← #4;
  rTmp1 ← rTmp1 * rE;
  rVisBase ← rNodeBase + rTmp1;
  rTabBase ← rVisBase + rN ]

private def layoutSetupB : Code .standard 34 := ram[
  rTmp1 ← rN * rL;
  rCandBase ← rTabBase + rTmp1;
  rInvBase ← rCandBase + rL;
  rStackBase ← rInvBase + rL;
  rCompBase ← rStackBase + rN;
  outBase ← rCompBase + rN;
  rNodeFree ← rNodeBase;
  rOuterIdx ← rZero ]

private def layoutSetupCode : Code .standard 34 := ram[
  ⟪layoutSetupA⟫;
  ⟪layoutSetupB⟫ ]

/-- Phase 1 setup block: initialize constants, scan edges for `slots g`, and compute layout
bases. -/
def setupCode : Code .standard 34 := ram[
  ⟪initSetupCode⟫;
  ⟪slotsLoop⟫;
  ⟪layoutSetupCode⟫ ]

private def prependToSlot (slotReg : Fin 34) : Code .standard 34 := ram[
  rTmp3 ← rHeadBase + slotReg;
  rTmp4 ← *rTmp3;
  *rNodeFree ← rEdgeIdx;
  rTmp5 ← rNodeFree + rOne;
  *rTmp5 ← rTmp4;
  *rTmp3 ← rNodeFree;
  rNodeFree ← rNodeFree + rTwo ]

private def bucketsHead : Code .standard 34 := ram[
  rEdgeIdx ← rE - rOne;
  rEdgeIdx ← rEdgeIdx - rOuterIdx;
  rTmp1 ← rEdgeIdx * rStride;
  rTmp1 ← rEdgeBase + rTmp1;
  rSrc ← *rTmp1;
  rTmp2 ← rTmp1 + rOne;
  rDst ← *rTmp2 ]

private def bucketsBody : Code .standard 34 := ram[
  ⟪bucketsHead⟫;
  ⟪prependToSlot rSrc⟫;
  if rSrc = rDst then [ rOuterIdx ← rOuterIdx ] else [ ⟪prependToSlot rDst⟫ ];
  rOuterIdx ← rOuterIdx + rOne ]

/-- Phase 2 loop building per-slot linked incidence lists in `[headBase g, visBase g)`. -/
def bucketsLoop : Code .standard 34 :=
  .loop (.lt rOuterIdx rE) bucketsBody

private def slotsPrefix {C : Type} (g : Graph C) (k : ℕ) : ℕ :=
  (g.edges.take k).foldl (fun n e => max n (max e.src e.dst + 1)) g.vertices

private theorem slotsPrefix_succ {C : Type} (g : Graph C) {k : ℕ} (hk : k < g.edges.length) :
    slotsPrefix g (k + 1) =
      max (slotsPrefix g k) (max g.edges[k].src g.edges[k].dst + 1) := by
  rw [slotsPrefix, List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rfl

private theorem initSetup_spec {L w : ℕ} (g : Graph (Fin L → Fin L))
    (hinp : InputAt g (Data.init (encode g) : Data 34).mem) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w initSetupCode (Data.init (encode g)) y 10 ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧ y.regs rTwo = 2 ∧ y.regs rL = L ∧
      y.regs rStride = L + 2 ∧ y.regs rN = g.vertices ∧ y.regs rE = g.edges.length ∧
      y.regs rEdgeBase = 4 ∧ y.regs rOuterIdx = 0 ∧
      y.mem = (Data.init (encode g) : Data 34).mem := by
  have hfit_hb : Fits w (headBase g + L + 2) := fits_top hw (by wram_omega)
  have : Fits w 4 := hfit_hb.of_le (by wram_omega)
  have : Fits w 3 := hfit_hb.of_le (by wram_omega)
  have : Fits w 2 := hfit_hb.of_le (by wram_omega)
  have : Fits w 1 := hfit_hb.of_le (by wram_omega)
  have : Fits w (L + 2) := hfit_hb.of_le (by wram_omega)
  unfold initSetupCode
  wram_exec [Data.init_regs, hinp.mem1, hinp.mem2, hinp.mem3]
  wram_simp

private theorem layoutSetupA_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (x : Data 34)
    (hz0 : x.regs rZero = 0) (hz1 : x.regs rOne = 1) (hz2 : x.regs rTwo = 2)
    (hzL : x.regs rL = L) (hzSt : x.regs rStride = L + 2) (hzN : x.regs rN = slots g)
    (hzE : x.regs rE = g.edges.length) (hzEB : x.regs rEdgeBase = 4)
    (hm0 : x.mem 0 = 3 + g.edges.length * (L + 2)) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w layoutSetupA x y 7 ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧ y.regs rTwo = 2 ∧ y.regs rL = L ∧
      y.regs rStride = L + 2 ∧ y.regs rN = slots g ∧ y.regs rE = g.edges.length ∧
      y.regs rEdgeBase = 4 ∧ y.regs rHeadBase = headBase g ∧ y.regs rNodeBase = nodeBase g ∧
      y.regs rVisBase = visBase g ∧ y.regs rTabBase = tabBase g ∧ y.mem = x.mem := by
  have : Fits w 4 := fits_top hw (by wram_omega)
  have : Fits w (3 + g.edges.length * (L + 2) + 1) := fits_top hw (by wram_omega)
  have : Fits w (3 + g.edges.length * (L + 2) + 1 + slots g) := fits_top hw (by wram_omega)
  have : Fits w (4 * g.edges.length) := fits_top hw (by wram_omega)
  have : Fits w (3 + g.edges.length * (L + 2) + 1 + slots g + 4 * g.edges.length) :=
    fits_top hw (by wram_omega)
  have : Fits w (3 + g.edges.length * (L + 2) + 1 + slots g + 4 * g.edges.length + slots g) :=
    fits_top hw (by wram_omega)
  unfold layoutSetupA
  wram_exec [hz0, hz1, hzN, hzE, hm0]
  refine ⟨by wram_simp [hz0], by wram_simp [hz1], by wram_simp [hz2], by wram_simp [hzL],
    by wram_simp [hzSt], by wram_simp [hzN], by wram_simp [hzE], by wram_simp [hzEB],
    by wram_simp; wram_omega, by wram_simp; wram_omega,
    by wram_simp; wram_omega, by wram_simp; wram_omega, by wram_simp⟩

private theorem layoutSetupB_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (x : Data 34)
    (hz0 : x.regs rZero = 0) (hz1 : x.regs rOne = 1) (hz2 : x.regs rTwo = 2)
    (hzL : x.regs rL = L) (hzSt : x.regs rStride = L + 2) (hzN : x.regs rN = slots g)
    (hzE : x.regs rE = g.edges.length) (hzEB : x.regs rEdgeBase = 4)
    (hzHB : x.regs rHeadBase = headBase g) (hzNB : x.regs rNodeBase = nodeBase g)
    (hzVB : x.regs rVisBase = visBase g) (hzTB : x.regs rTabBase = tabBase g)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w layoutSetupB x y 8 ∧
      ConstRegs g y ∧ y.regs rNodeFree = nodeBase g ∧ y.regs rOuterIdx = 0 ∧ y.mem = x.mem := by
  have : Fits w (slots g * L) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + slots g * L) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + slots g * L + L) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + slots g * L + L + L) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + slots g * L + L + L + slots g) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + slots g * L + L + L + slots g + slots g) := fits_top hw (by wram_omega)
  unfold layoutSetupB
  wram_exec [hz0, hzL, hzN, hzNB, hzTB]
  refine ⟨?_, by wram_simp, by wram_simp, by wram_simp⟩
  apply ConstRegs.mk <;>
    wram_simp [hz0, hz1, hz2, hzL, hzSt, hzN, hzE, hzEB, hzHB, hzNB, hzVB, hzTB]

/-- Specification for `setupCode`. -/
theorem slotsSetup_spec {L w : ℕ} (g : Graph (Fin L → Fin L))
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w setupCode
        (Data.init (encode g)) y (16 * g.edges.length + 30) ∧
      ConstRegs g y ∧ InputAt g y.mem ∧ y.regs rNodeFree = nodeBase g ∧
      y.regs rOuterIdx = 0 ∧ ∀ a, headBase g ≤ a → y.mem a = 0 := by
  have hwb := outBaseAddr_lt_wordBound g
  have hewb := edges_lt_wordBound g
  obtain ⟨hinp, hzero_above⟩ := inputAt_init g
  let Pslots (k : ℕ) (x : Data 34) : Prop :=
    x.regs rZero = 0 ∧ x.regs rOne = 1 ∧ x.regs rTwo = 2 ∧ x.regs rL = L ∧
    x.regs rStride = L + 2 ∧ x.regs rN = slotsPrefix g k ∧ x.regs rE = g.edges.length ∧
    x.regs rEdgeBase = 4 ∧ x.mem = (Data.init (encode g) : Data 34).mem
  obtain ⟨x1, hx1, hz0, hz1, hz2, hzL, hzSt, hzN0, hzE, hzEB, hzIdx0, hx1m⟩ :=
    initSetup_spec (w := w) g hinp hw
  obtain ⟨x2, hx2, ⟨hz0', hz1', hz2', hzL', hzSt', hzN', hzE', hzEB', hx2m⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rOuterIdx) (limit := rE) (body := slotsBody)
      (N := g.edges.length) (T := 14) Pslots
      (fun y hy => hy.2.2.2.2.2.2.1)
      (fun y hy hlt => by
        obtain ⟨h0, h1, h2, hL, hSt, hN, hE, hEB, hmem⟩ := hy
        set k := y.regs rOuterIdx
        have hk_reg : y.regs rOuterIdx = k := rfl
        have hsrc_mem : y.mem (4 + k * (L + 2)) = g.edges[k].src := by
          rw [hmem]; exact hinp.edge_src k hlt
        have hdst_mem : y.mem (4 + k * (L + 2) + 1) = g.edges[k].dst := by
          rw [hmem]; exact hinp.edge_dst k hlt
        have hs_lt : g.edges[k].src < slots g := src_lt_slots (List.getElem_mem hlt)
        have hd_lt : g.edges[k].dst < slots g := dst_lt_slots (List.getElem_mem hlt)
        have hed := edge_end_le_wordBound hlt
        have : Fits w (k * (L + 2)) := hw.of_le (by omega)
        have : Fits w (4 + k * (L + 2)) := hw.of_le (by omega)
        have : Fits w (4 + k * (L + 2) + 1) := hw.of_le (by omega)
        have : Fits w (g.edges[k].src + 1) := hw.of_le (by omega)
        have : Fits w (g.edges[k].dst + 1) := hw.of_le (by omega)
        have : Fits w (k + 1) := hw.of_le (by omega)
        unfold slotsBody
        wram_exec [h0, h1, h2, hL, hSt, hN, hE, hEB, hk_reg, hsrc_mem, hdst_mem]
        all_goals
          refine ⟨⟨by wram_simp [h0], by wram_simp [h1], by wram_simp [h2], by wram_simp [hL],
            by wram_simp [hSt], ?_, by wram_simp [hE], by wram_simp [hEB],
            by wram_simp [hmem]⟩, by wram_simp⟩
          wram_simp [hN]
          rw [slotsPrefix_succ g hlt]
          omega)
      (by rw [hzIdx0]; exact Nat.zero_le _)
      (by rw [hzIdx0]; exact ⟨hz0, hz1, hz2, hzL, hzSt, hzN0, hzE, hzEB, hx1m⟩)
  rw [hzIdx0, Nat.sub_zero] at hx2
  have hzN_eq : x2.regs rN = slots g := by
    rw [hzN']; simp only [slotsPrefix, List.take_length, slots]
  have hx2_mem0 : x2.mem 0 = 3 + g.edges.length * (L + 2) := by rw [hx2m]; exact hinp.mem0
  obtain ⟨x3, hx3, ha0, ha1, ha2, haL, haSt, haN, haE, haEB, haHB, haNB, haVB, haTB, hx3m⟩ :=
    layoutSetupA_spec (w := w) g x2 hz0' hz1' hz2' hzL' hzSt' hzN_eq hzE' hzEB' hx2_mem0 hw
  obtain ⟨x4, hx4, hc4, hnf4, hidx4, hx4m⟩ :=
    layoutSetupB_spec (w := w) g x3 ha0 ha1 ha2 haL haSt haN haE haEB haHB haNB haVB haTB hw
  have hmem4 : x4.mem = (Data.init (encode g) : Data 34).mem := hx4m.trans (hx3m.trans hx2m)
  exact ⟨x4, (hx1.seq (hx2.seq (hx3.seq hx4))).mono (by omega), hc4, hmem4 ▸ hinp, hnf4, hidx4,
    fun a ha => by rw [hmem4]; exact hzero_above a ha⟩

private theorem prepend_adjChain {L : ℕ} {g : Graph (Fin L → Fin L)} {mem : ℕ → ℕ}
    {top u j : ℕ} {bs : List (List (Edge (Fin L → Fin L)))}
    (hlen : bs.length = slots g) (hu : u < slots g) (hj : j < g.edges.length)
    (htop_lo : nodeBase g ≤ top)
    (hbs : ∀ v < slots g, AdjChain g mem top (mem (headBase g + v)) (bs.getD v [])) :
    let mem' := Function.update (Function.update (Function.update mem top j)
      (top + 1) (mem (headBase g + u))) (headBase g + u) top
    ∀ v < slots g,
      AdjChain g mem' (top + 2) (mem' (headBase g + v))
        ((bs.set u (g.edges[j] :: bs.getD u [])).getD v []) := by
  intro mem' v hv
  have hfr : ∀ a, nodeBase g ≤ a → a < top → mem' a = mem a := by
    intro a ha1 ha2
    simp only [mem', Function.update_of_ne (by simp only [nodeBase] at ha1; omega :
        a ≠ headBase g + u),
      Function.update_of_ne (by omega : a ≠ top + 1),
      Function.update_of_ne (by omega : a ≠ top)]
  by_cases hvu : v = u
  · subst hvu
    rw [List.getD_set_self (hlen ▸ hu)]
    have hhd : mem' (headBase g + v) = top := Function.update_self _ _ _
    have hp0 : mem' top = j := by
      simp only [mem', Function.update_of_ne (by simp only [nodeBase] at htop_lo; omega :
          top ≠ headBase g + v),
        Function.update_of_ne (by omega : top ≠ top + 1), Function.update_self]
    have hp1 : mem' (top + 1) = mem (headBase g + v) := by
      simp only [mem', Function.update_of_ne (by simp only [nodeBase] at htop_lo; omega :
          top + 1 ≠ headBase g + v), Function.update_self]
    rw [hhd]
    refine .cons hj htop_lo (le_refl _) hp0 ?_
    rw [hp1]
    exact (hbs v hv).frame (by omega) hfr
  · rw [List.getD_set_ne (Ne.symm hvu)]
    have hhd : mem' (headBase g + v) = mem (headBase g + v) := by
      simp only [mem', Function.update_of_ne (by omega : headBase g + v ≠ headBase g + u),
        Function.update_of_ne (by simp only [nodeBase] at htop_lo; omega :
          headBase g + v ≠ top + 1),
        Function.update_of_ne (by simp only [nodeBase] at htop_lo; omega : headBase g + v ≠ top)]
    rw [hhd]
    exact (hbs v hv).frame (by omega) hfr

private theorem prependToSlot_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (slotReg : Fin 34)
    (x : Data 34) (bs : List (List (Edge (Fin L → Fin L)))) (u j : ℕ)
    (hsr : slotReg = rSrc ∨ slotReg = rDst)
    (hc : ConstRegs g x) (hinp : InputAt g x.mem)
    (hslot : x.regs slotReg = u) (hj_reg : x.regs rEdgeIdx = j)
    (hlen : bs.length = slots g) (hu : u < slots g) (hj : j < g.edges.length)
    (hlo : nodeBase g ≤ x.regs rNodeFree) (hhi : x.regs rNodeFree + 2 ≤ visBase g)
    (hbs : ∀ v < slots g,
      AdjChain g x.mem (x.regs rNodeFree) (x.mem (headBase g + v)) (bs.getD v []))
    (hzero : ∀ a, visBase g ≤ a → x.mem a = 0) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w (prependToSlot slotReg) x y 7 ∧
      ConstRegs g y ∧ InputAt g y.mem ∧
      y.regs rNodeFree = x.regs rNodeFree + 2 ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      y.regs rEdgeIdx = j ∧ y.regs rSrc = x.regs rSrc ∧ y.regs rDst = x.regs rDst ∧
      (∀ v < slots g,
        AdjChain g y.mem (y.regs rNodeFree) (y.mem (headBase g + v))
          ((bs.set u (g.edges[j] :: bs.getD u [])).getD v [])) ∧
      ∀ a, visBase g ≤ a → y.mem a = 0 := by
  have hprep := prepend_adjChain hlen hu hj hlo hbs
  have : Fits w (headBase g + u) := fits_top hw (by wram_omega)
  have : Fits w (x.regs rNodeFree + 1) := fits_top hw (by wram_omega)
  have : Fits w (x.regs rNodeFree + 2) := fits_top hw (by wram_omega)
  have hfr_inp : ∀ a < headBase g,
      Function.update (Function.update (Function.update x.mem (x.regs rNodeFree) j)
        (x.regs rNodeFree + 1) (x.mem (headBase g + u))) (headBase g + u) (x.regs rNodeFree) a =
        x.mem a := fun a ha => by
    simp only [Function.update_of_ne (by omega : a ≠ headBase g + u),
      Function.update_of_ne (by simp only [nodeBase] at hlo; omega : a ≠ x.regs rNodeFree + 1),
      Function.update_of_ne (by simp only [nodeBase] at hlo; omega : a ≠ x.regs rNodeFree)]
  have hfr_zero : ∀ a, visBase g ≤ a →
      Function.update (Function.update (Function.update x.mem (x.regs rNodeFree) j)
        (x.regs rNodeFree + 1) (x.mem (headBase g + u))) (headBase g + u) (x.regs rNodeFree) a =
        0 :=
    fun a ha => by
      simp only [Function.update_of_ne (by simp only [visBase, nodeBase] at ha; omega :
          a ≠ headBase g + u),
        Function.update_of_ne (by omega : a ≠ x.regs rNodeFree + 1),
        Function.update_of_ne (by omega : a ≠ x.regs rNodeFree)]
      exact hzero a ha
  rcases hsr with rfl | rfl <;>
  · unfold prependToSlot
    wram_exec [hc.one, hc.two, hc.headB, hslot, hj_reg]
    refine ⟨by wram_simp [hc], by wram_simp; exact hinp.frame hfr_inp,
      by wram_simp, by wram_simp, by wram_simp [hj_reg], by wram_simp, by wram_simp,
      ?_, ?_⟩
    · simp only [Data.write_mem, Data.set_mem]; wram_simp; exact hprep
    · simp only [Data.write_mem, Data.set_mem]; exact hfr_zero

/-- Specification for `bucketsLoop`. -/
theorem bucketsLoop_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) {x : Data 34}
    (hc : ConstRegs g x) (hinp : InputAt g x.mem)
    (hnf : x.regs rNodeFree = nodeBase g) (hidx : x.regs rOuterIdx = 0)
    (hzero : ∀ a, headBase g ≤ a → x.mem a = 0) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w bucketsLoop x y (g.edges.length * 28 + 2) ∧
      ConstRegs g y ∧ InputAt g y.mem ∧ BucketsAt g y.mem ∧
      ∀ a, visBase g ≤ a → y.mem a = 0 := by
  have hwb := outBaseAddr_lt_wordBound g
  have hewb := edges_lt_wordBound g
  let bsAt (k : ℕ) := buckets (slots g) (g.edges.drop (g.edges.length - k))
  have hbs_len : ∀ k ≤ g.edges.length, (bsAt k).length = slots g := fun k _ =>
    (buckets_spec (slots g) _ fun e he => by
      have hm := List.mem_of_mem_drop he
      exact ⟨src_lt_slots hm, dst_lt_slots hm⟩).1
  let P (k : ℕ) (y : Data 34) : Prop :=
    ConstRegs g y ∧ InputAt g y.mem ∧
    nodeBase g ≤ y.regs rNodeFree ∧ y.regs rNodeFree ≤ nodeBase g + 4 * k ∧
    (∀ u < slots g,
      AdjChain g y.mem (y.regs rNodeFree) (y.mem (headBase g + u)) ((bsAt k).getD u [])) ∧
    ∀ a, visBase g ≤ a → y.mem a = 0
  have hp0 : P 0 x := by
    refine ⟨hc, hinp, by omega, by omega, fun u hu => ?_, fun a ha =>
      hzero a (by simp only [visBase, nodeBase] at ha; omega)⟩
    have hnil : (bsAt 0).getD u [] = [] := by
      change (buckets (slots g) (g.edges.drop (g.edges.length - 0))).getD u [] = []
      rw [Nat.sub_zero, List.drop_length]
      exact List.getD_replicate _ hu
    rw [hnil, hzero (headBase g + u) (Nat.le_add_right _ _)]
    exact .nil
  obtain ⟨y, hy, ⟨hyC, hyInp, hyLo, hyHi, hyAdj, hyZero⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rOuterIdx) (limit := rE) (body := bucketsBody)
      (N := g.edges.length) (T := 26) P
      (fun y hy => hy.1.regE)
      (fun y hy hlt => by
        obtain ⟨hyC, hyInp, hyLo, hyHi, hyAdj, hyZero⟩ := hy
        set k := y.regs rOuterIdx
        have hk_reg : y.regs rOuterIdx = k := rfl
        set j := g.edges.length - 1 - k
        have hj : j < g.edges.length := by omega
        have hdrop : g.edges.drop (g.edges.length - (k + 1)) =
            g.edges[j] :: g.edges.drop (g.edges.length - k) := by
          rw [show g.edges.length - (k + 1) = j by omega,
            show g.edges.length - k = j + 1 by omega]
          exact List.drop_eq_getElem_cons hj
        have hbs_next : bsAt (k + 1) = insertEdge (bsAt k) g.edges[j] := by
          simp only [bsAt, hdrop, buckets, List.foldr_cons]
        have hs_lt : g.edges[j].src < slots g := src_lt_slots (List.getElem_mem hj)
        have hd_lt : g.edges[j].dst < slots g := dst_lt_slots (List.getElem_mem hj)
        have hsrc_mem := hyInp.edge_src j hj
        have hdst_mem := hyInp.edge_dst j hj
        have hlen_k : (bsAt k).length = slots g := hbs_len k (by omega)
        have hed := edge_end_le_wordBound hj
        have hed_k := edge_end_le_wordBound hlt
        have : Fits w (j * (L + 2)) := hw.of_le (by omega)
        have : Fits w (4 + j * (L + 2)) := hw.of_le (by omega)
        have : Fits w (4 + j * (L + 2) + 1) := hw.of_le (by omega)
        have : Fits w (k + 1) := hw.of_le (by omega)
        have hsub : g.edges.length - 1 - k = j := rfl
        obtain ⟨y1, hy1, hy1C, hy1J, hy1Src, hy1Dst, hy1NF, hy1Idx, hy1m⟩ :
            ∃ y1, ExecWithin w bucketsHead y y1 7 ∧
              ConstRegs g y1 ∧ y1.regs rEdgeIdx = j ∧ y1.regs rSrc = g.edges[j].src ∧
              y1.regs rDst = g.edges[j].dst ∧ y1.regs rNodeFree = y.regs rNodeFree ∧
              y1.regs rOuterIdx = k ∧ y1.mem = y.mem := by
          unfold bucketsHead
          wram_exec [hyC.one, hyC.stride, hyC.regE, hyC.edgeB, hk_reg, hsub, hsrc_mem, hdst_mem]
          exact ⟨by wram_simp [hyC], by wram_simp, by wram_simp, by wram_simp, by wram_simp,
            by wram_simp [hk_reg], by wram_simp⟩
        obtain ⟨z1, hz1, hz1C, hz1Inp, hz1NF, hz1Idx, hz1J, hz1Src, hz1Dst, hz1Adj, hz1Zero⟩ :=
          prependToSlot_spec (w := w) g rSrc y1 (bsAt k) g.edges[j].src j (Or.inl rfl)
            hy1C (hy1m ▸ hyInp) hy1Src hy1J hlen_k hs_lt hj
            (by omega) (by simp only [visBase]; omega)
            (by rw [hy1NF, hy1m]; exact hyAdj) (by rw [hy1m]; exact hyZero) hw
        by_cases hsd : g.edges[j].src = g.edges[j].dst
        · obtain ⟨z2, hz2, hz2C, hz2NF, hz2Idx, hz2m⟩ :
              ∃ z2, ExecWithin w
                (ram[ if rSrc = rDst then [ rOuterIdx ← rOuterIdx ] else [ ⟪prependToSlot rDst⟫ ];
                      rOuterIdx ← rOuterIdx + rOne ] : Code .standard 34) z1 z2 4 ∧
                ConstRegs g z2 ∧ z2.regs rNodeFree = z1.regs rNodeFree ∧
                z2.regs rOuterIdx = k + 1 ∧ z2.mem = z1.mem := by
            wram_exec [hz1Src, hy1Src, hz1Dst, hy1Dst, hsd, hz1Idx, hy1Idx, hz1C.one]
            exact ⟨by wram_simp [hz1C], by wram_simp, by wram_simp, by wram_simp⟩
          refine ⟨z2, (hy1.seq (hz1.seq hz2)).mono (by omega), ⟨hz2C, hz2m ▸ hz1Inp,
            by rw [hz2NF, hz1NF, hy1NF]; omega,
            by rw [hz2NF, hz1NF, hy1NF]; omega,
            fun u hu => ?_, by rw [hz2m]; exact hz1Zero⟩, hz2Idx⟩
          rw [hbs_next, hz2NF, hz2m]
          simp only [insertEdge, hsd, ↓reduceIte]
          simpa only [hsd] using hz1Adj u hu
        · have hlen_k1 : ((bsAt k).set g.edges[j].src
              (g.edges[j] :: (bsAt k).getD g.edges[j].src [])).length = slots g := by
            rw [List.length_set, hlen_k]
          obtain ⟨z2, hz2, hz2C, hz2Inp, hz2NF, hz2Idx, _, _, _, hz2Adj, hz2Zero⟩ :=
            prependToSlot_spec (w := w) g rDst z1
              ((bsAt k).set g.edges[j].src (g.edges[j] :: (bsAt k).getD g.edges[j].src []))
              g.edges[j].dst j (Or.inr rfl)
              hz1C hz1Inp (hz1Dst.trans hy1Dst) hz1J hlen_k1 hd_lt hj
              (by rw [hz1NF, hy1NF]; omega)
              (by rw [hz1NF, hy1NF]; simp only [visBase]; omega) hz1Adj hz1Zero hw
          have hbr : ExecWithin w
              (ram[ if rSrc = rDst then [ rOuterIdx ← rOuterIdx ] else [ ⟪prependToSlot rDst⟫ ] ] :
                Code .standard 34)
              z1 z2 9 :=
            ExecWithin.branch_neg
              (by simp only [Cond.holds_eq, hz1Src, hy1Src, hz1Dst, hy1Dst, hsd, not_false_eq_true])
              hz2
          obtain ⟨z3, hz3, hz3C, hz3NF, hz3Idx, hz3m⟩ :
              ∃ z3, ExecWithin w
                (ram[ rOuterIdx ← rOuterIdx + rOne ] : Code .standard 34) z2 z3 1 ∧
                ConstRegs g z3 ∧ z3.regs rNodeFree = z2.regs rNodeFree ∧
                z3.regs rOuterIdx = k + 1 ∧ z3.mem = z2.mem := by
            wram_exec [hz2Idx, hz1Idx, hy1Idx, hz2C.one]
            exact ⟨by wram_simp [hz2C], by wram_simp, by wram_simp, by wram_simp⟩
          refine ⟨z3, (hy1.seq (hz1.seq (hbr.seq hz3))).mono (by omega), ⟨hz3C, hz3m ▸ hz2Inp,
            by rw [hz3NF, hz2NF, hz1NF, hy1NF]; omega,
            by rw [hz3NF, hz2NF, hz1NF, hy1NF]; omega,
            fun u hu => ?_, by rw [hz3m]; exact hz2Zero⟩, hz3Idx⟩
          simp only [hbs_next, insertEdge, hsd, ↓reduceIte, hz3NF, hz3m]
          simpa only [List.getD_set_ne hsd] using hz2Adj u hu)
      (by rw [hidx]; exact Nat.zero_le _)
      (by rwa [hidx])
  rw [hidx, Nat.sub_zero] at hy
  refine ⟨y, hy, hyC, hyInp, fun u hu => ?_, hyZero⟩
  simpa only [bsAt, Nat.sub_self, List.drop_zero, buckets_getD] using
    (hyAdj u hu).frame (by simp only [visBase]; omega) fun _ _ _ => rfl

end Cslib.Complexity.UniqueGames.Propagation
