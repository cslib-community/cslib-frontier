/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime.Layout
import CslibFrontier.Computability.WordRAM.CountingLoop

/-!
# Phase 4 symbolic execution: solution extraction, edge checking, and output header

This internal module defines and certifies `extractCode` (writing `labelling (List.finRange L) g`
into `outBaseAddr g + 2 .. outBaseAddr g + 2 + slots g`), `checkCode` (testing every input edge
against the extracted labelling), and `finishCode` (writing the length-prefixed `encodeSolution`
header and decision register `Reg.ok`).

## Main definitions

* `Cslib.Complexity.UniqueGames.Propagation.extractCode`: labelling extraction loop.
* `Cslib.Complexity.UniqueGames.Propagation.checkCode`: edge-constraint verification loop.
* `Cslib.Complexity.UniqueGames.Propagation.finishCode`: output-header finalization block.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.extractCode_spec`: `ExecWithin` specification for
  `extractCode` in `slots g * 12 + 3` instructions.
* `Cslib.Complexity.UniqueGames.Propagation.checkCode_spec`: `ExecWithin` specification for
  `checkCode` matching `check g (labelling (List.finRange L) g)` in `|g.edges| * 19 + 4`
  instructions.
* `Cslib.Complexity.UniqueGames.Propagation.finishCode_spec`: `ExecWithin` specification for
  `finishCode` establishing `outputList = encodeSolution (slots g) (solve (List.finRange L) g)` and
  `Reg.ok = (solve (List.finRange L) g).isSome.toNat`.
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded Cslib.WordRAM Cslib.WordRAM.Block Reg

private def extractBody : Code .standard 34 := ram[
  rTmp1 ← rVisBase + rOuterIdx;
  rTmp1 ← *rTmp1;
  if rTmp1 = rOne then [
    rTmp2 ← rOuterIdx * rL;
    rTmp2 ← rTabBase + rTmp2;
    rTmp2 ← *rTmp2
  ] else [
    rTmp2 ← rZero ];
  rTmp3 ← outBase + rTwo;
  rTmp3 ← rTmp3 + rOuterIdx;
  *rTmp3 ← rTmp2;
  rOuterIdx ← rOuterIdx + rOne ]

/-- Extract `labelling (List.finRange L) g` into `outBase + 2 .. outBase + 2 + slots g`. -/
def extractCode : Code .standard 34 := ram[
  rOuterIdx ← rZero;
  ⟪.loop (.lt rOuterIdx rN) extractBody⟫ ]

private def checkBody : Code .standard 34 := ram[
  rTmp1 ← rOuterIdx * rStride;
  rEdgeIdx ← rEdgeBase + rTmp1;
  rSrc ← *rEdgeIdx;
  rTmp1 ← rEdgeIdx + rOne;
  rDst ← *rTmp1;
  rTmp2 ← outBase + rTwo;
  rTmp3 ← rTmp2 + rSrc;
  rTmp3 ← *rTmp3;
  rTmp4 ← rTmp2 + rDst;
  rTmp4 ← *rTmp4;
  rTmp5 ← rTmp3 + rTwo;
  rTmp5 ← rEdgeIdx + rTmp5;
  rTmp5 ← *rTmp5;
  if rTmp5 = rTmp4 then [ rOuterIdx ← rOuterIdx ] else [ ok ← rZero ];
  rOuterIdx ← rOuterIdx + rOne ]

private def checkInit : Code .standard 34 := ram[
  ok ← rOne;
  rOuterIdx ← rZero ]

/-- Verify that every input edge is satisfied by the extracted labelling, setting `Reg.ok`. -/
def checkCode : Code .standard 34 := ram[
  ⟪checkInit⟫;
  ⟪.loop (.lt rOuterIdx rE) checkBody⟫ ]

/-- Write the length-prefixed `encodeSolution` header at `Reg.outBase` from `Reg.ok`. -/
def finishCode : Code .standard 34 := ram[
  rTmp1 ← outBase + rOne;
  if ok = rOne then [
    rTmp2 ← rN + rOne;
    *outBase ← rTmp2;
    *rTmp1 ← rOne
  ] else [
    *outBase ← rOne;
    *rTmp1 ← rZero ] ]

/-- Specification for `extractCode`. -/
theorem extractCode_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L)) (x : Data 34)
    (hT : TableStateAt g (run (List.finRange L) g) x) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w extractCode x y (slots g * 12 + 3) ∧
      ConstRegs g y ∧ InputAt g y.mem ∧
      HoldsList (outBaseAddr g + 2)
        ((List.range (slots g)).map fun v => (labelling (List.finRange L) g v).val) y.mem := by
  obtain ⟨x0, hx0, hT0, hidx0⟩ :
      ∃ x0, ExecWithin w (ram[ rOuterIdx ← rZero ] : Code .standard 34) x x0 1 ∧
        TableStateAt g (run (List.finRange L) g) x0 ∧ x0.regs rOuterIdx = 0 := by
    wram_exec [hT.consts.zero]
    exact ⟨hT.of_eq (by wram_simp [hT.consts]) (by wram_simp), by wram_simp⟩
  let labVal (v : ℕ) : ℕ := (labelling (List.finRange L) g v).val
  let P (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧
    (∀ v < k, z.mem (outBaseAddr g + 2 + v) = labVal v) ∧
    ∀ addr, ¬ (outBaseAddr g + 2 ≤ addr ∧ addr < outBaseAddr g + 2 + k) → z.mem addr = x0.mem addr
  obtain ⟨y, hy, ⟨hyC, hyOut, hyFr⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rOuterIdx) (limit := rN) (body := extractBody)
      (N := slots g) (T := 10) P
      (fun z hz => hz.1.regN)
      (fun z hz hv => by
        obtain ⟨hzC, hzOut, hzFr⟩ := hz
        set v := z.regs rOuterIdx
        have hv_reg : z.regs rOuterIdx = v := rfl
        have : Fits w (visBase g + v) := fits_top hw (by wram_omega)
        have : Fits w (outBaseAddr g + 2) := fits_top hw (by wram_omega)
        have : Fits w (outBaseAddr g + 2 + v) := fits_top hw (by wram_omega)
        have : Fits w (v + 1) := fits_top hw (by wram_omega)
        cases hgv : (run (List.finRange L) g).get v with
        | none =>
          have hvis0 : z.mem (visBase g + v) = 0 :=
            (hzFr _ (by wram_omega)).trans (hT0.vis_none v hv hgv)
          have h0 : 0 = labVal v := by
            simp only [labVal, labelling, hgv, Option.elim_none, default, Fin.val_zero]
          have hpws := prefix_write_step hzOut hzFr (congrArg _ h0)
          unfold extractBody
          wram_exec [hzC.zero, hzC.one, hzC.two, hzC.visB, hzC.outB, hv_reg, hvis0]
          refine ⟨⟨by wram_simp [hzC], hpws⟩, ?_⟩
          wram_simp
        | some fn =>
          obtain ⟨hvis1, htab_fn⟩ := hT0.vis_some v hv fn hgv
          have hvis1' : z.mem (visBase g + v) = 1 := (hzFr _ (by wram_omega)).trans hvis1
          have hv_cb := tabRow_hi_le_candBase (g := g) hv
          have hf0_mem : z.mem (tabBase g + v * L) = (fn default).val := by
            have hdef : (⟨0, NeZero.pos L⟩ : Fin L) = default := rfl
            rw [hzFr _ (by wram_omega)]
            simpa only [Nat.add_zero, hdef] using htab_fn 0 (NeZero.pos L)
          have : Fits w (v * L) := fits_top hw (by wram_omega)
          have : Fits w (tabBase g + v * L) := fits_top hw (by wram_omega)
          have hfn : (fn default).val = labVal v := by
            simp only [labVal, labelling, hgv, Option.elim_some]
          have hpws := prefix_write_step hzOut hzFr (congrArg _ hfn)
          unfold extractBody
          wram_exec [hzC.one, hzC.two, hzC.regL, hzC.visB, hzC.tabB, hzC.outB, hv_reg, hvis1',
            hf0_mem]
          refine ⟨⟨by wram_simp [hzC], hpws⟩, ?_⟩
          wram_simp)
      (by rw [hidx0]; exact Nat.zero_le _)
      (by rw [hidx0]; exact ⟨hT0.consts, fun _ h => by omega, fun _ _ => rfl⟩)
  rw [hidx0, Nat.sub_zero] at hy
  refine ⟨y, (hx0.seq hy).mono (by omega), hyC,
    hT0.inp.frame (fun a ha => hyFr a (by wram_omega)), fun i => ?_⟩
  simpa only [Block.read, labVal, Fin.getElem_fin, List.getElem_map, List.getElem_range] using
    hyOut i.val (by simpa only [List.length_map, List.length_range] using i.isLt)

/-- Specification for `checkCode`. -/
theorem checkCode_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L)) (x : Data 34)
    (hc : ConstRegs g x) (hinp : InputAt g x.mem)
    (hout : HoldsList (outBaseAddr g + 2)
      ((List.range (slots g)).map fun v => (labelling (List.finRange L) g v).val) x.mem)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w checkCode x y (g.edges.length * 19 + 4) ∧
      ConstRegs g y ∧
      y.regs ok = (check g (labelling (List.finRange L) g)).toNat ∧
      y.mem = x.mem := by
  have hewb := edges_lt_wordBound g
  obtain ⟨x0, hx0, hc0, hok0, hidx0, hm0⟩ : ∃ x0, ExecWithin w checkInit x x0 2 ∧
      ConstRegs g x0 ∧ x0.regs ok = 1 ∧ x0.regs rOuterIdx = 0 ∧ x0.mem = x.mem := by
    unfold checkInit
    wram_exec [hc.zero, hc.one]
    exact ⟨by wram_simp [hc], by wram_simp, by wram_simp, by wram_simp⟩
  set σ := labelling (List.finRange L) g
  let P (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧
    z.regs ok = ((g.edges.take k).all fun e => decide (e.constraint (σ e.src) = σ e.dst)).toNat ∧
    z.mem = x.mem
  obtain ⟨y, hy, ⟨hyC, hyOk, hyMem⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rOuterIdx) (limit := rE) (body := checkBody)
      (N := g.edges.length) (T := 17) P
      (fun z hz => hz.1.regE)
      (fun z hz hj => by
        obtain ⟨hzC, hzOk, hzMem⟩ := hz
        set j := z.regs rOuterIdx
        have hj_reg : z.regs rOuterIdx = j := rfl
        set e := g.edges[j]
        have hs_lt : e.src < slots g := src_lt_slots (List.getElem_mem hj)
        have hd_lt : e.dst < slots g := dst_lt_slots (List.getElem_mem hj)
        have hed := edge_end_le_wordBound hj
        have hsrc_ltL := (σ e.src).isLt
        have hsrc_mem : z.mem (4 + j * (L + 2)) = e.src := hzMem ▸ hinp.edge_src j hj
        have hdst_mem : z.mem (4 + j * (L + 2) + 1) = e.dst := hzMem ▸ hinp.edge_dst j hj
        have hlv (u : ℕ) (hu : u < slots g) : z.mem (outBaseAddr g + 2 + u) = (σ u).val := by
          rw [hzMem, hout.get u (by simpa only [List.length_map, List.length_range] using hu)]
          simp only [List.getElem_map, List.getElem_range]
        have hc_mem : z.mem (4 + j * (L + 2) + ((σ e.src).val + 2)) =
            (e.constraint (σ e.src)).val := by
          rw [hzMem, add_comm (σ e.src).val 2, ← add_assoc]
          simpa only [Fin.eta] using hinp.edge_val j hj (σ e.src).val hsrc_ltL
        have : Fits w (j * (L + 2)) := hw.of_le (by omega)
        have : Fits w (4 + j * (L + 2)) := hw.of_le (by omega)
        have : Fits w (4 + j * (L + 2) + 1) := hw.of_le (by omega)
        have : Fits w (outBaseAddr g + 2) := fits_top hw (by wram_omega)
        have : Fits w (outBaseAddr g + 2 + e.src) := fits_top hw (by wram_omega)
        have : Fits w (outBaseAddr g + 2 + e.dst) := fits_top hw (by wram_omega)
        have : Fits w ((σ e.src).val + 2) := hw.of_le (by omega)
        have : Fits w (4 + j * (L + 2) + ((σ e.src).val + 2)) := hw.of_le (by omega)
        have : Fits w (j + 1) := hw.of_le (by omega)
        have hall_next : ((g.edges.take (j + 1)).all fun d =>
              decide (d.constraint (σ d.src) = σ d.dst)) =
            (((g.edges.take j).all fun d => decide (d.constraint (σ d.src) = σ d.dst)) &&
              decide (e.constraint (σ e.src) = σ e.dst)) := by
          rw [List.take_succ_eq_append_getElem hj, List.all_append, List.all_cons, List.all_nil,
            Bool.and_true]
        by_cases heq_v : (e.constraint (σ e.src)).val = (σ e.dst).val
        · unfold checkBody
          wram_exec [hzC.one, hzC.two, hzC.stride, hzC.edgeB, hzC.outB, hj_reg,
            hsrc_mem, hdst_mem, hlv e.src hs_lt, hlv e.dst hd_lt, hc_mem, heq_v]
          refine ⟨⟨by wram_simp [hzC], ?_, by wram_simp [hzMem]⟩, by wram_simp⟩
          wram_simp [hzOk]
          rw [hall_next, decide_eq_true (Fin.ext heq_v), Bool.and_true]
        · unfold checkBody
          wram_exec [hzC.zero, hzC.one, hzC.two, hzC.stride, hzC.edgeB, hzC.outB, hj_reg,
            hsrc_mem, hdst_mem, hlv e.src hs_lt, hlv e.dst hd_lt, hc_mem, heq_v]
          refine ⟨⟨by wram_simp [hzC], ?_, by wram_simp [hzMem]⟩, by wram_simp⟩
          wram_simp
          rw [hall_next, decide_eq_false (fun h => heq_v (congrArg Fin.val h)),
            Bool.and_false, Bool.toNat_false])
      (by rw [hidx0]; exact Nat.zero_le _)
      (by rw [hidx0]
          exact ⟨hc0, by simp only [hok0, List.take_zero, List.all_nil, Bool.toNat_true], hm0⟩)
  rw [hidx0, Nat.sub_zero] at hy
  exact ⟨y, (hx0.seq hy).mono (by omega), hyC,
    by simpa only [check, List.take_length] using hyOk, hyMem⟩

/-- Specification for `finishCode`. -/
theorem finishCode_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L)) (x : Data 34)
    (hc : ConstRegs g x)
    (hok : x.regs ok = (check g (labelling (List.finRange L) g)).toNat)
    (hout : HoldsList (outBaseAddr g + 2)
      ((List.range (slots g)).map fun v => (labelling (List.finRange L) g v).val) x.mem)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w finishCode x y 6 ∧
      y.regs outBase = outBaseAddr g ∧
      y.regs ok = (solve (List.finRange L) g).isSome.toNat ∧
      outputList y.mem (y.regs outBase) =
        encodeSolution (slots g) (solve (List.finRange L) g) ∧
      Fits w (y.regs outBase + (encodeSolution (slots g) (solve (List.finRange L) g)).length) := by
  have : Fits w (outBaseAddr g + 1) := fits_top hw (by wram_omega)
  have : Fits w (slots g + 1) := fits_top hw (by wram_omega)
  cases hchk : check g (labelling (List.finRange L) g) with
  | true =>
    have hok1 : x.regs ok = 1 := by simp only [hok, hchk, Bool.toNat_true]
    have hsolve : solve (List.finRange L) g = some (labelling (List.finRange L) g) := by
      simp only [solve, hchk, ↓reduceIte]
    unfold finishCode
    wram_exec [hc.one, hc.regN, hc.outB, hok1]
    refine ⟨by wram_simp [hc.outB], ?_, ?_, ?_⟩
    · wram_simp [hok1, hsolve, Option.isSome_some, Bool.toNat_true]
    · wram_simp [hc.outB]
      rw [hsolve, outputList_eq_iff]
      refine ⟨?_, holdsList_cons_iff.mpr ⟨Function.update_self .., hout.frame fun a _ _ => ?_⟩⟩
      · rw [Function.update_of_ne (by omega), Function.update_self]
        simp only [encodeSolution, List.length_cons, List.length_map, List.length_range]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · wram_simp [hc.outB]
      exact hsolve ▸ fits_top hw (by
        simp only [encodeSolution, List.length_cons, List.length_map, List.length_range]
        wram_omega)
  | false =>
    have hok0 : x.regs ok = 0 := by simp only [hok, hchk, Bool.toNat_false]
    have hsolve : solve (List.finRange L) g = none := by
      simp only [solve, hchk, Bool.false_eq_true, ↓reduceIte]
    unfold finishCode
    wram_exec [hc.zero, hc.one, hc.outB, hok0]
    refine ⟨by wram_simp [hc.outB], ?_, ?_, ?_⟩
    · wram_simp [hok0, hsolve, Option.isSome_none, Bool.toNat_false]
    · wram_simp [hc.outB]
      rw [hsolve, outputList_eq_iff]
      refine ⟨?_, holdsList_cons_iff.mpr ⟨Function.update_self .., holdsList_nil _ _⟩⟩
      rw [Function.update_of_ne (by omega), Function.update_self]
      simp only [encodeSolution, List.length_singleton]
    · wram_simp [hc.outB]
      refine hsolve ▸ fits_top hw (by
        simp only [encodeSolution, List.length_singleton]
        wram_omega)

end Cslib.Complexity.UniqueGames.Propagation
