/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime.Layout
import all CslibFrontier.Computability.PCP.Approximation.UniqueGames.Propagation
import CslibFrontier.Computability.WordRAM.CountingLoop

/-!
# Forward/backward constraint composition and preimage inversion (`extendCode`)

This internal module defines and certifies `extendCode`, handling forward composition (`src → dst`),
first-preimage table construction in `[invBase g, invBase g + L)`, backward composition
(`dst → src`), and stack pushing when exactly one endpoint of an incident edge is visited.

## Main definitions

* `Cslib.Complexity.UniqueGames.Propagation.extendCode`: Word-RAM forward/backward edge propagation
  subroutine.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.extendCode_spec`: `ExecWithin` specification matching
  `extend (List.finRange L) S g.edges[j]` in `28 * L + 30` instructions.
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded Cslib.WordRAM Cslib.WordRAM.Block Reg

private def extendFwdBody : Code .standard 34 := ram[
  rTmp4 ← rTmp2 + rLabIdx;
  rTmp4 ← *rTmp4;
  rTmp4 ← rTmp4 + rTwo;
  rTmp4 ← rEdgeIdx + rTmp4;
  rTmp4 ← *rTmp4;
  rTmp5 ← rTmp3 + rLabIdx;
  *rTmp5 ← rTmp4;
  rLabIdx ← rLabIdx + rOne ]

private def invInitBody : Code .standard 34 := ram[
  rTmp4 ← rInvBase + rLabIdx;
  *rTmp4 ← rL;
  rLabIdx ← rLabIdx + rOne ]

private def invFillBody : Code .standard 34 := ram[
  rTmp4 ← rLabIdx + rTwo;
  rTmp4 ← rEdgeIdx + rTmp4;
  rTmp4 ← *rTmp4;
  rTmp5 ← rInvBase + rTmp4;
  rTmp4 ← *rTmp5;
  if rTmp4 = rL then [ *rTmp5 ← rLabIdx ] else [ rLabIdx ← rLabIdx ];
  rLabIdx ← rLabIdx + rOne ]

private def invLoopsCode : Code .standard 34 := ram[
  rLabIdx ← rZero;
  ⟪.loop (.lt rLabIdx rL) invInitBody⟫;
  rLabIdx ← rZero;
  ⟪.loop (.lt rLabIdx rL) invFillBody⟫ ]

private def extendBwdBody : Code .standard 34 := ram[
  rTmp4 ← rTmp2 + rLabIdx;
  rTmp4 ← *rTmp4;
  rTmp5 ← rInvBase + rTmp4;
  rTmp5 ← *rTmp5;
  if rTmp5 = rL then [ rTmp5 ← rTmp4 ] else [ rTmp5 ← rTmp5 ];
  rTmp4 ← rTmp3 + rLabIdx;
  *rTmp4 ← rTmp5;
  rLabIdx ← rLabIdx + rOne ]

private def extendPush (slotReg : Fin 34) : Code .standard 34 := ram[
  rTmp4 ← rVisBase + slotReg;
  *rTmp4 ← rOne;
  rTmp4 ← rStackBase + rStackLen;
  *rTmp4 ← slotReg;
  rStackLen ← rStackLen + rOne ]

/-- Forward or backward propagation along the current edge when exactly one endpoint is visited. -/
def extendCode : Code .standard 34 := ram[
  ⟪edgeVisLoad⟫;
  if rTmp1 = rOne then [
    if rTmp2 = rZero then [
      ⟪extendPrep rSrc rDst⟫;
      ⟪.loop (.lt rLabIdx rL) extendFwdBody⟫;
      ⟪extendPush rDst⟫
    ] else [ rLabIdx ← rLabIdx ]
  ] else [
    if rTmp2 = rOne then [
      ⟪invLoopsCode⟫;
      ⟪extendPrep rDst rSrc⟫;
      ⟪.loop (.lt rLabIdx rL) extendBwdBody⟫;
      ⟪extendPush rSrc⟫
    ] else [ rLabIdx ← rLabIdx ] ] ]

private theorem extendFwdLoop_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (x : Data 34)
    (j : ℕ) (hj : j < g.edges.length) (f : Fin L → Fin L)
    (hc : ConstRegs g x) (hinp : InputAt g x.mem)
    (heptr : x.regs rEdgeIdx = 4 + j * (L + 2))
    (hsrc_lt : g.edges[j].src < slots g) (hdst_lt : g.edges[j].dst < slots g)
    (hsd : g.edges[j].src ≠ g.edges[j].dst)
    (ht2 : x.regs rTmp2 = tabBase g + g.edges[j].src * L)
    (ht3 : x.regs rTmp3 = tabBase g + g.edges[j].dst * L)
    (hlab : x.regs rLabIdx = 0)
    (hf_mem : ∀ a (ha : a < L), x.mem (tabBase g + g.edges[j].src * L + a) = (f ⟨a, ha⟩).val)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w (.loop (.lt rLabIdx rL) extendFwdBody) x y (L * 10 + 2) ∧
      ConstRegs g y ∧ Phase3Regs x y ∧
      (∀ a (ha : a < L), y.mem (tabBase g + g.edges[j].dst * L + a) =
        (g.edges[j].constraint (f ⟨a, ha⟩)).val) ∧
      ∀ addr, ¬ (tabBase g + g.edges[j].dst * L ≤ addr ∧
          addr < tabBase g + g.edges[j].dst * L + L) → y.mem addr = x.mem addr := by
  have hed := edge_end_le_headBase hj
  have hcb_src := tabRow_hi_le_candBase (g := g) hsrc_lt
  have hcb_dst := tabRow_hi_le_candBase (g := g) hdst_lt
  let eVal (a : ℕ) : ℕ :=
    if ha : a < L then (g.edges[j].constraint (f ⟨a, ha⟩)).val else 0
  let P (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ z.regs rTmp2 = tabBase g + g.edges[j].src * L ∧
    z.regs rTmp3 = tabBase g + g.edges[j].dst * L ∧ Phase3Regs x z ∧
    (∀ i < k, z.mem (tabBase g + g.edges[j].dst * L + i) = eVal i) ∧
    ∀ addr, ¬ (tabBase g + g.edges[j].dst * L ≤ addr ∧
        addr < tabBase g + g.edges[j].dst * L + k) → z.mem addr = x.mem addr
  obtain ⟨y, hy, ⟨hyC, _, _, hyR, hyRow, hyFr⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := extendFwdBody)
      (N := L) (T := 8) P
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzT2, hzT3, hzR, hzRow, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have hfk_lt := (f ⟨k, hk⟩).isLt
        have hfa : z.mem (tabBase g + g.edges[j].src * L + k) = (f ⟨k, hk⟩).val := by
          rw [hzFr _ (fun ⟨h1, h2⟩ => not_in_tabRow (g := g) hsd hk ⟨h1, by omega⟩)]
          exact hf_mem k hk
        have hcfa : z.mem (4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2)) =
            (g.edges[j].constraint (f ⟨k, hk⟩)).val := by
          rw [hzFr _ (by wram_omega),
            show 4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2) =
              4 + j * (L + 2) + 2 + (f ⟨k, hk⟩).val by omega]
          exact hinp.edge_val j hj (f ⟨k, hk⟩).val hfk_lt
        have : Fits w (tabBase g + g.edges[j].src * L + k) := fits_top hw (by wram_omega)
        have : Fits w ((f ⟨k, hk⟩).val + 2) := fits_top hw (by wram_omega)
        have : Fits w (4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2)) := fits_top hw (by wram_omega)
        have : Fits w (tabBase g + g.edges[j].dst * L + k) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        have hzE : z.regs rEdgeIdx = 4 + j * (L + 2) := hzR.edgeIdx.trans heptr
        have heVal_k : (g.edges[j].constraint (f ⟨k, hk⟩)).val = eVal k := by
          simp only [eVal, hk, ↓reduceDIte]
        have hpws := prefix_write_step hzRow hzFr
          (rfl : Function.update z.mem (tabBase g + g.edges[j].dst * L + k) (eVal k) = _)
        unfold extendFwdBody
        wram_exec [hzC.one, hzC.two, hzT2, hzT3, hzE, hk_reg, hfa, hcfa]
        exact ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3], by wram_simp [hzR],
          by simpa only [Data.write_mem, Data.set_mem, heVal_k] using hpws.1,
          by simpa only [Data.write_mem, Data.set_mem, heVal_k] using hpws.2⟩, by wram_simp⟩)
      (by rw [hlab]; exact Nat.zero_le _)
      (by rw [hlab]; exact ⟨hc, ht2, ht3, Phase3Regs.refl x, fun _ h => by omega, fun _ _ => rfl⟩)
  rw [hlab, Nat.sub_zero] at hy
  exact ⟨y, hy, hyC, hyR,
    fun a ha => by simpa only [eVal, ha, ↓reduceDIte] using hyRow a ha, hyFr⟩

private theorem invLoops_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (x : Data 34)
    (j : ℕ) (hj : j < g.edges.length)
    (hc : ConstRegs g x) (hinp : InputAt g x.mem)
    (heptr : x.regs rEdgeIdx = 4 + j * (L + 2))
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w invLoopsCode x y (16 * L + 6) ∧
      ConstRegs g y ∧ Phase3Regs x y ∧
      (∀ b (hb : b < L),
        (if y.mem (invBase g + b) = L then b else y.mem (invBase g + b)) =
          (preimage (List.finRange L) g.edges[j].constraint ⟨b, hb⟩).val) ∧
      ∀ addr, ¬ (invBase g ≤ addr ∧ addr < invBase g + L) → y.mem addr = x.mem addr := by
  have hed := edge_end_le_headBase hj
  have resetLab (y0 : Data 34) (hyC : ConstRegs g y0) (hR : Phase3Regs x y0) :
      ∃ y1, ExecWithin w (ram[ rLabIdx ← rZero ] : Code .standard 34) y0 y1 1 ∧
        ConstRegs g y1 ∧ y1.regs rLabIdx = 0 ∧ Phase3Regs x y1 ∧ y1.mem = y0.mem := by
    wram_exec [hyC.zero]
    exact ⟨by wram_simp [hyC], by wram_simp, by wram_simp [hR], by wram_simp⟩
  obtain ⟨x1, hx1, hc1, hlab1, hr1, hm1⟩ := resetLab x hc (Phase3Regs.refl x)
  let Pinit (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ Phase3Regs x z ∧
    (∀ b < k, z.mem (invBase g + b) = L) ∧
    ∀ addr, ¬ (invBase g ≤ addr ∧ addr < invBase g + k) → z.mem addr = x.mem addr
  obtain ⟨x2, hx2, ⟨hc2, hr2, hinit_inv, hfr2⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := invInitBody)
      (N := L) (T := 3) Pinit
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzR, hzInv, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have : Fits w (invBase g + k) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        have hpws := prefix_write_step (e := fun _ => L) hzInv hzFr
          (rfl : Function.update z.mem (invBase g + k) L = _)
        unfold invInitBody
        wram_exec [hzC.one, hzC.regL, hzC.invB, hk_reg]
        exact ⟨⟨by wram_simp [hzC], by wram_simp [hzR],
          by simpa only [Data.write_mem, Data.set_mem] using hpws.1,
          by simpa only [Data.write_mem, Data.set_mem] using hpws.2⟩, by wram_simp⟩)
      (by rw [hlab1]; exact Nat.zero_le _)
      (by rw [hlab1]; exact ⟨hc1, hr1, fun _ h => by omega, fun addr _ => congrFun hm1 addr⟩)
  rw [hlab1, Nat.sub_zero] at hx2
  obtain ⟨x3, hx3, hc3, hlab3, hr3, hm3⟩ := resetLab x2 hc2 hr2
  let invAt (k : ℕ) (b : ℕ) (hb : b < L) : ℕ :=
    (((List.finRange L).take k).find? fun a => decide (g.edges[j].constraint a = ⟨b, hb⟩)).elim
      L Fin.val
  let Pfill (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ Phase3Regs x z ∧
    (∀ b (hb : b < L), z.mem (invBase g + b) = invAt k b hb) ∧
    ∀ addr, ¬ (invBase g ≤ addr ∧ addr < invBase g + L) → z.mem addr = x.mem addr
  obtain ⟨y, hx4, ⟨hyC, hyR, hyInv, hyFr⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := invFillBody)
      (N := L) (T := 9) Pfill
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzR, hzInv, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        set bk := (g.edges[j].constraint ⟨k, hk⟩).val
        have hbk : bk < L := (g.edges[j].constraint ⟨k, hk⟩).isLt
        have hc_mem : z.mem (4 + j * (L + 2) + (k + 2)) = bk := by
          rw [hzFr _ (by wram_omega),
            show 4 + j * (L + 2) + (k + 2) = 4 + j * (L + 2) + 2 + k by omega]
          exact hinp.edge_val j hj k hk
        have hcur_mem : z.mem (invBase g + bk) = invAt k bk hbk := hzInv bk hbk
        have htake_succ : (List.finRange L).take (k + 1) =
            (List.finRange L).take k ++ [⟨k, hk⟩] := by
          rw [List.take_succ_eq_append_getElem (by simp only [List.length_finRange]; exact hk),
            List.getElem_finRange]
          rfl
        have : Fits w (k + 2) := fits_top hw (by wram_omega)
        have : Fits w (4 + j * (L + 2) + (k + 2)) := fits_top hw (by wram_omega)
        have : Fits w (invBase g + bk) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        have hzE : z.regs rEdgeIdx = 4 + j * (L + 2) := hzR.edgeIdx.trans heptr
        have hstep_ne {b : ℕ} (hb : b < L) (hbb : b ≠ bk) : invAt k b hb = invAt (k + 1) b hb := by
          have hne_fin : g.edges[j].constraint ⟨k, hk⟩ ≠ ⟨b, hb⟩ :=
            fun heq => hbb (congrArg Fin.val heq).symm
          simp only [invAt, htake_succ, List.find?_append, List.find?_cons, hne_fin,
            decide_false, List.find?_nil, Option.or_none]
        cases hfind : ((List.finRange L).take k).find?
            (fun a => decide (g.edges[j].constraint a = ⟨bk, hbk⟩)) with
        | none =>
          have hcur_eq : invAt k bk hbk = L := by simp only [invAt, hfind, Option.elim_none]
          unfold invFillBody
          wram_exec [hzC.one, hzC.two, hzC.regL, hzC.invB, hzE, hk_reg, hc_mem, hcur_mem, hcur_eq]
          refine ⟨⟨by wram_simp [hzC], by wram_simp [hzR], fun b hb => ?_, fun addr haddr => ?_⟩,
            by wram_simp⟩
          · simp only [Data.write_mem, Data.set_mem]
            by_cases hbb : b = bk
            · subst hbb
              simp only [Function.update_self, invAt, htake_succ, List.find?_append, hfind,
                Option.none_or, List.find?_cons]
              rw [decide_eq_true (Fin.ext rfl)]; rfl
            · rw [Function.update_of_ne (by omega : invBase g + b ≠ invBase g + bk), hzInv b hb,
                hstep_ne hb hbb]
          · simp only [Data.write_mem, Data.set_mem,
              Function.update_of_ne (by omega : addr ≠ invBase g + bk)]
            exact hzFr addr haddr
        | some a0 =>
          have hcur_ne : invAt k bk hbk ≠ L := by
            simp only [invAt, hfind, Option.elim_some]; exact ne_of_lt a0.isLt
          unfold invFillBody
          wram_exec [hzC.one, hzC.two, hzC.regL, hzC.invB, hzE, hk_reg, hc_mem, hcur_mem, hcur_ne]
          refine ⟨⟨by wram_simp [hzC], by wram_simp [hzR], fun b hb => ?_, ?_⟩, by wram_simp⟩
          · simp only [Data.set_mem]; rw [hzInv b hb]
            by_cases hbb : b = bk
            · subst hbb; simp only [invAt, htake_succ, List.find?_append, hfind, Option.some_or]
            · exact hstep_ne hb hbb
          · simp only [Data.set_mem]; exact hzFr)
      (by rw [hlab3]; exact Nat.zero_le _)
      (by rw [hlab3]; refine ⟨hc3, hr3, fun b hb => ?_, fun addr haddr => ?_⟩
          · rw [hm3, hinit_inv b hb]
            simp only [invAt, List.take_zero, List.find?_nil, Option.elim_none]
          · rw [hm3]; exact hfr2 addr haddr)
  rw [hlab3, Nat.sub_zero] at hx4
  refine ⟨y, (hx1.seq (hx2.seq (hx3.seq hx4))).mono (by omega), hyC, hyR, fun b hb => ?_, hyFr⟩
  rw [hyInv b hb]
  have htakeL : (List.finRange L).take L = List.finRange L :=
    List.take_of_length_le (by simp only [List.length_finRange, le_rfl])
  simp only [invAt, htakeL, preimage]
  cases h : (List.finRange L).find? (fun a => decide (g.edges[j].constraint a = ⟨b, hb⟩)) with
  | none => simp only [↓reduceIte, Option.elim_none, Option.getD_none]
  | some a0 => simp only [Option.elim_some, ne_of_lt a0.isLt, ↓reduceIte, Option.getD_some]

private theorem extendBwdLoop_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (x : Data 34)
    (j : ℕ) (hj : j < g.edges.length) (h : Fin L → Fin L)
    (hc : ConstRegs g x)
    (hsrc_lt : g.edges[j].src < slots g) (hdst_lt : g.edges[j].dst < slots g)
    (hsd : g.edges[j].src ≠ g.edges[j].dst)
    (ht2 : x.regs rTmp2 = tabBase g + g.edges[j].dst * L)
    (ht3 : x.regs rTmp3 = tabBase g + g.edges[j].src * L)
    (hlab : x.regs rLabIdx = 0)
    (hh_mem : ∀ a (ha : a < L), x.mem (tabBase g + g.edges[j].dst * L + a) = (h ⟨a, ha⟩).val)
    (hinv_mem : ∀ b (hb : b < L),
      (if x.mem (invBase g + b) = L then b else x.mem (invBase g + b)) =
        (preimage (List.finRange L) g.edges[j].constraint ⟨b, hb⟩).val)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w (.loop (.lt rLabIdx rL) extendBwdBody) x y (L * 12 + 2) ∧
      ConstRegs g y ∧ Phase3Regs x y ∧
      (∀ a (ha : a < L), y.mem (tabBase g + g.edges[j].src * L + a) =
        (preimage (List.finRange L) g.edges[j].constraint (h ⟨a, ha⟩)).val) ∧
      ∀ addr, ¬ (tabBase g + g.edges[j].src * L ≤ addr ∧
          addr < tabBase g + g.edges[j].src * L + L) → y.mem addr = x.mem addr := by
  have hcb_src := tabRow_hi_le_candBase (g := g) hsrc_lt
  have hcb_dst := tabRow_hi_le_candBase (g := g) hdst_lt
  let eVal (a : ℕ) : ℕ :=
    if ha : a < L then (preimage (List.finRange L) g.edges[j].constraint (h ⟨a, ha⟩)).val else 0
  let P (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ z.regs rTmp2 = tabBase g + g.edges[j].dst * L ∧
    z.regs rTmp3 = tabBase g + g.edges[j].src * L ∧ Phase3Regs x z ∧
    (∀ i < k, z.mem (tabBase g + g.edges[j].src * L + i) = eVal i) ∧
    ∀ addr, ¬ (tabBase g + g.edges[j].src * L ≤ addr ∧
        addr < tabBase g + g.edges[j].src * L + k) → z.mem addr = x.mem addr
  obtain ⟨y, hy, ⟨hyC, _, _, hyR, hyRow, hyFr⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := extendBwdBody)
      (N := L) (T := 10) P
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzT2, hzT3, hzR, hzRow, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have hha : z.mem (tabBase g + g.edges[j].dst * L + k) = (h ⟨k, hk⟩).val := by
          rw [hzFr _ (fun ⟨h1, h2⟩ => not_in_tabRow (g := g) (Ne.symm hsd) hk ⟨h1, by omega⟩)]
          exact hh_mem k hk
        have hiv_fr : z.mem (invBase g + (h ⟨k, hk⟩).val) = x.mem (invBase g + (h ⟨k, hk⟩).val) :=
          hzFr _ (by wram_omega)
        have hiv_val := hinv_mem (h ⟨k, hk⟩).val (h ⟨k, hk⟩).isLt
        simp only [Fin.eta] at hiv_val
        have : Fits w (tabBase g + g.edges[j].dst * L + k) := fits_top hw (by wram_omega)
        have : Fits w (invBase g + (h ⟨k, hk⟩).val) :=
          fits_top hw (by have := (h ⟨k, hk⟩).isLt; wram_omega)
        have : Fits w (tabBase g + g.edges[j].src * L + k) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        have hpws := prefix_write_step hzRow hzFr
          (rfl : Function.update z.mem (tabBase g + g.edges[j].src * L + k) (eVal k) = _)
        have hb : (if x.mem (invBase g + (h ⟨k, hk⟩).val) = L then (h ⟨k, hk⟩).val
            else x.mem (invBase g + (h ⟨k, hk⟩).val)) = eVal k := by
          simp only [eVal, hk, ↓reduceDIte, hiv_val]
        by_cases hivL : x.mem (invBase g + (h ⟨k, hk⟩).val) = L <;>
        · unfold extendBwdBody
          wram_exec [hzC.one, hzC.regL, hzC.invB, hzT2, hzT3, hk_reg, hha, hiv_fr, hivL]
          refine ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3],
            by wram_simp [hzR], ?_, ?_⟩, by wram_simp⟩ <;>
          · simp only [Data.write_mem, Data.set_mem]
            simp only [hivL, ↓reduceIte] at hb
            first | (rw [hb]; exact hpws.1) | (rw [hb]; exact hpws.2))
      (by rw [hlab]; exact Nat.zero_le _)
      (by rw [hlab]; exact ⟨hc, ht2, ht3, Phase3Regs.refl x, fun _ h => by omega, fun _ _ => rfl⟩)
  rw [hlab, Nat.sub_zero] at hy
  exact ⟨y, hy, hyC, hyR,
    fun a ha => by simpa only [eVal, ha, ↓reduceDIte] using hyRow a ha, hyFr⟩

-- Execute `extendPush` and establish `StateAt` on the newly pushed endpoint.
private theorem extendPush_state {L w : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x xb z : Data 34) (j : ℕ) (hj : j < g.edges.length) (slotReg : Fin 34) (u : ℕ)
    (fn : Fin L → Fin L) (hsr : slotReg = rSrc ∨ slotReg = rDst)
    (hu : u < slots g) (hgu : S.get u = none) (hS : StateAt g S x) (hSb : StateAt g S xb)
    (hcz : ConstRegs g z) (hrz : Phase3Regs x z)
    (heptr : x.regs rEdgeIdx = 4 + j * (L + 2))
    (hsrc_reg : x.regs rSrc = g.edges[j].src) (hdst_reg : x.regs rDst = g.edges[j].dst)
    (hslot : z.regs slotReg = u)
    (hrow : ∀ a (ha : a < L), z.mem (tabBase g + u * L + a) = (fn ⟨a, ha⟩).val)
    (hfr : ∀ addr, ¬ (tabBase g + u * L ≤ addr ∧ addr < tabBase g + u * L + L) →
      z.mem addr = xb.mem addr)
    (hlow : ∀ a < visBase g, xb.mem a = x.mem a)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w (extendPush slotReg) z y 5 ∧
      StateAt g (push S u fn) y ∧
      y.regs rEdgeIdx = 4 + j * (L + 2) ∧
      y.regs rSrc = g.edges[j].src ∧ y.regs rDst = g.edges[j].dst ∧
      y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      ∀ a < visBase g, y.mem a = x.mem a := by
  have hstk_lt : S.stack.length < slots g := by
    have hpos : 0 < S.unvisited.card :=
      Finset.card_pos.mpr ⟨u, mem_unvisited (hSb.len_table ▸ hu) hgu⟩
    have hpot : S.potential ≤ slots g := hSb.pot_le
    unfold State.potential at hpot; omega
  have hcb_u := tabRow_hi_le_candBase (g := g) hu
  have hsl : z.regs rStackLen = S.stack.length := hrz.stackLen.trans hS.stack_len
  have : Fits w (visBase g + u) := fits_top hw (by wram_omega)
  have : Fits w (stackBase g + S.stack.length) := fits_top hw (by wram_omega)
  have : Fits w (S.stack.length + 1) := fits_top hw (by wram_omega)
  have hexec : ∃ y, ExecWithin w (extendPush slotReg) z y 5 ∧ ConstRegs g y ∧
      y.regs rEdgeIdx = z.regs rEdgeIdx ∧ y.regs rSrc = z.regs rSrc ∧ y.regs rDst = z.regs rDst ∧
      y.regs rStackLen = S.stack.length + 1 ∧ y.regs rCompLen = z.regs rCompLen ∧
      y.regs rCurNode = z.regs rCurNode ∧ y.regs rRem = z.regs rRem ∧
      y.regs rOuterIdx = z.regs rOuterIdx ∧
      y.mem = Function.update (Function.update z.mem (visBase g + u) 1)
        (stackBase g + S.stack.length) u := by
    rcases hsr with rfl | rfl <;>
    · unfold extendPush
      wram_exec [hcz.one, hcz.visB, hcz.stackB, hslot, hsl]
      exact ⟨by wram_simp [hcz], by wram_simp, by wram_simp, by wram_simp, by wram_simp,
        by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨y, hy, hcy, he', hs', hd', hsl', hcl', hcn', hrem', hidx', hym⟩ := hexec
  have hstk_mem : HoldsList (stackBase g) (S.stack.reverse ++ [u]) y.mem := by
    have hbase : HoldsList (stackBase g) S.stack.reverse
        (Function.update z.mem (visBase g + u) 1) :=
      hSb.stack_mem.frame fun a ha1 ha2 => by
        rw [Function.update_of_ne (by wram_omega), hfr _ (by wram_omega)]
    simpa only [hym, List.length_reverse] using hbase.append_one u
  refine ⟨y, hy, hSb.push_slot hcy hu hgu
      (fun a ha => by
        rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by wram_omega)]
        exact hrow a ha)
      (by rw [hym, Function.update_of_ne (by wram_omega), Function.update_self])
      hstk_mem hsl' (hcl'.trans (hrz.compLen.trans hS.comp_len))
      (fun a hnr hnv hns => by
        rw [hym, Function.update_of_ne hns, Function.update_of_ne hnv, hfr a hnr]),
    he'.trans (hrz.edgeIdx.trans heptr), hs'.trans (hrz.src.trans hsrc_reg),
    hd'.trans (hrz.dst.trans hdst_reg), hcn'.trans hrz.curNode, hrem'.trans hrz.rem,
    hidx'.trans hrz.outerIdx, fun a ha => by
      rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by omega),
        hfr _ (by wram_omega), hlow a ha]⟩

/-- Specification for `extendCode`. -/
theorem extendCode_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) (j : ℕ) (hj : j < g.edges.length)
    (hS : StateAt g S x)
    (heptr : x.regs rEdgeIdx = 4 + j * (L + 2))
    (hsrc_reg : x.regs rSrc = g.edges[j].src)
    (hdst_reg : x.regs rDst = g.edges[j].dst)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w extendCode x y (28 * L + 30) ∧
      StateAt g (extend (List.finRange L) S g.edges[j]) y ∧
      y.regs rEdgeIdx = 4 + j * (L + 2) ∧
      y.regs rSrc = g.edges[j].src ∧ y.regs rDst = g.edges[j].dst ∧
      y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      ∀ a < visBase g, y.mem a = x.mem a := by
  set e := g.edges[j] with he_def
  have hs_lt : e.src < slots g := src_lt_slots (List.getElem_mem hj)
  have hd_lt : e.dst < slots g := dst_lt_slots (List.getElem_mem hj)
  obtain ⟨x1, hx1, hc1, ht1_1, ht2_1, hr1, hm1⟩ :=
    edgeVisLoad_spec (w := w) g S x j hj hS hsrc_reg hdst_reg hw
  have hnop : ExecWithin w (.op (.copy rLabIdx rLabIdx)) x1 x1 1 :=
    ⟨1, le_rfl, exec_nop rLabIdx x1⟩
  have he1 : x1.regs rEdgeIdx = 4 + j * (L + 2) := hr1.edgeIdx.trans heptr
  have hs1 : x1.regs rSrc = e.src := hr1.src.trans hsrc_reg
  have hd1 : x1.regs rDst = e.dst := hr1.dst.trans hdst_reg
  have hS1 : StateAt g S x1 :=
    hS.of_eq hc1 (hr1.stackLen.trans hS.stack_len) (hr1.compLen.trans hS.comp_len) hm1
  have retSame (hext : extend (List.finRange L) S e = S)
      (hex : ExecWithin w extendCode x x1 (28 * L + 30)) :
      ∃ y, ExecWithin w extendCode x y (28 * L + 30) ∧
        StateAt g (extend (List.finRange L) S e) y ∧
        y.regs rEdgeIdx = 4 + j * (L + 2) ∧
        y.regs rSrc = e.src ∧ y.regs rDst = e.dst ∧
        y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
        y.regs rOuterIdx = x.regs rOuterIdx ∧
        ∀ a < visBase g, y.mem a = x.mem a :=
    ⟨x1, hex, hext.symm ▸ hS1, he1, hs1, hd1, hr1.curNode, hr1.rem, hr1.outerIdx,
      fun a _ => by rw [hm1]⟩
  cases hgs : S.get e.src with
  | some f =>
    obtain ⟨hvis_s, htab_s⟩ := hS.vis_some e.src hs_lt f hgs
    have hc_outer : (Cond.eq rTmp1 rOne).Holds x1 := by
      simp only [Cond.holds_eq, ht1_1, ← he_def, hvis_s, hc1.one]
    cases hgd : S.get e.dst with
    | none =>
      have hvis_d : x.mem (visBase g + e.dst) = 0 := hS.vis_none e.dst hd_lt hgd
      have hsd : e.src ≠ e.dst := fun h0 => by rw [← h0, hgs] at hgd; nomatch hgd
      have hc_inner : (Cond.eq rTmp2 rZero).Holds x1 := by
        simp only [Cond.holds_eq, ht2_1, ← he_def, hvis_d, hc1.zero]
      obtain ⟨x2, hx2, hc2, ht2_2, ht3_2, hlab2, hr2', hm2'⟩ :=
        extendPrep_spec (w := w) g rSrc rDst x1 e.src e.dst (Or.inl ⟨rfl, rfl⟩)
          hc1 hs_lt hd_lt hs1 hd1 hw
      have hr2 := hr2'.trans hr1
      have hm2 := hm2'.trans hm1
      obtain ⟨x3, hx3, hc3, hr3', hrow3, hfr3⟩ :=
        extendFwdLoop_spec (w := w) g x2 j hj f hc2 (hm2 ▸ hS.inp) (hr2.edgeIdx.trans heptr)
          hs_lt hd_lt hsd ht2_2 ht3_2 hlab2 (fun a ha => by rw [hm2]; exact htab_s a ha) hw
      have hr3 := hr3'.trans hr2
      simp only [← he_def] at hrow3 hfr3
      obtain ⟨y, hx4, hSy, hrest⟩ :=
        extendPush_state g S x x1 x3 j hj rDst e.dst (e.constraint ∘ f) (Or.inr rfl)
          hd_lt hgd hS hS1 hc3 hr3 heptr hsrc_reg hdst_reg (hr3.dst.trans hdst_reg) hrow3
          (fun a hnr => by rw [hfr3 a hnr, hm2']) (fun a _ => by rw [hm1]) hw
      exact ⟨y, (hx1.seq (ExecWithin.branch_pos hc_outer
        (ExecWithin.branch_pos hc_inner (hx2.seq (hx3.seq hx4))))).mono (by omega),
        by simpa only [extend, hgs, hgd] using hSy, hrest⟩
    | some h =>
      obtain ⟨hvis_d, _⟩ := hS.vis_some e.dst hd_lt h hgd
      have hc_inner : ¬ (Cond.eq rTmp2 rZero).Holds x1 := by
        simp only [Cond.holds_eq, ht2_1, ← he_def, hvis_d, hc1.zero, Nat.one_ne_zero,
          not_false_eq_true]
      exact retSame (by simp only [extend, hgs, hgd])
        ((hx1.seq (ExecWithin.branch_pos hc_outer (ExecWithin.branch_neg hc_inner hnop))).mono
          (by omega))
  | none =>
    have hvis_s : x.mem (visBase g + e.src) = 0 := hS.vis_none e.src hs_lt hgs
    have hc_outer : ¬ (Cond.eq rTmp1 rOne).Holds x1 := by
      simp only [Cond.holds_eq, ht1_1, ← he_def, hvis_s, hc1.one, Nat.zero_ne_one,
        not_false_eq_true]
    cases hgd : S.get e.dst with
    | some h =>
      obtain ⟨hvis_d, htab_d⟩ := hS.vis_some e.dst hd_lt h hgd
      have hsd : e.src ≠ e.dst := fun h0 => by rw [← h0, hgs] at hgd; nomatch hgd
      have hc_inner : (Cond.eq rTmp2 rOne).Holds x1 := by
        simp only [Cond.holds_eq, ht2_1, ← he_def, hvis_d, hc1.one]
      have hcb_d := tabRow_hi_le_candBase (g := g) hd_lt
      obtain ⟨x2, hx2, hc2, hr2', hinv2, hfr2⟩ :=
        invLoops_spec (w := w) g x1 j hj hc1 (hm1 ▸ hS.inp) he1 hw
      have hr2 := hr2'.trans hr1
      simp only [← he_def] at hinv2
      obtain ⟨x3, hx3, hc3, ht2_3, ht3_3, hlab3, hr3', hm3⟩ :=
        extendPrep_spec (w := w) g rDst rSrc x2 e.dst e.src (Or.inr ⟨rfl, rfl⟩)
          hc2 hd_lt hs_lt (hr2.dst.trans hdst_reg) (hr2.src.trans hsrc_reg) hw
      have hr3 := hr3'.trans hr2
      obtain ⟨x4, hx4, hc4, hr4', hrow4, hfr4⟩ :=
        extendBwdLoop_spec (w := w) g x3 j hj h hc3 hs_lt hd_lt hsd ht2_3 ht3_3 hlab3
          (fun a ha => by
            simp only [← he_def]; rw [hm3, hfr2 _ (by wram_omega), hm1]; exact htab_d a ha)
          (fun b hb => by simp only [← he_def]; rw [hm3]; exact hinv2 b hb) hw
      have hr4 := hr4'.trans hr3
      simp only [← he_def] at hrow4 hfr4
      have hS2 : StateAt g S x2 :=
        hS.frame_inv hc2 (hr2.stackLen.trans hS.stack_len) (hr2.compLen.trans hS.comp_len)
          (fun a ha => by rw [hfr2 a ha, hm1])
      obtain ⟨y, hx5, hSy, hrest⟩ :=
        extendPush_state g S x x2 x4 j hj rSrc e.src
          (preimage (List.finRange L) e.constraint ∘ h) (Or.inl rfl)
          hs_lt hgs hS hS2 hc4 hr4 heptr hsrc_reg hdst_reg (hr4.src.trans hsrc_reg) hrow4
          (fun a hnr => by rw [hfr4 a hnr, hm3])
          (fun a ha => by rw [hfr2 _ (by wram_omega), hm1]) hw
      exact ⟨y, (hx1.seq (ExecWithin.branch_neg hc_outer
        (ExecWithin.branch_pos hc_inner (hx2.seq (hx3.seq (hx4.seq hx5)))))).mono (by omega),
        by simpa only [extend, hgs, hgd] using hSy, hrest⟩
    | none =>
      have hvis_d : x.mem (visBase g + e.dst) = 0 := hS.vis_none e.dst hd_lt hgd
      have hc_inner : ¬ (Cond.eq rTmp2 rOne).Holds x1 := by
        simp only [Cond.holds_eq, ht2_1, ← he_def, hvis_d, hc1.one, Nat.zero_ne_one,
          not_false_eq_true]
      exact retSame (by simp only [extend, hgs, hgd])
        ((hx1.seq (ExecWithin.branch_neg hc_outer (ExecWithin.branch_neg hc_inner hnop))).mono
          (by omega))

end Cslib.Complexity.UniqueGames.Propagation
