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
        have hfa : z.mem (tabBase g + g.edges[j].src * L + k) = (f ⟨k, hk⟩).val :=
          (hzFr _ fun ⟨h1, h2⟩ => not_in_tabRow (g := g) hsd hk ⟨h1, by omega⟩).trans (hf_mem k hk)
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
        have hpws := prefix_write_step hzRow hzFr
          (rfl : Function.update z.mem (tabBase g + g.edges[j].dst * L + k) (eVal k) = _)
        wram_exec [extendFwdBody, hzC.one, hzC.two, hzT2, hzT3, hzE, hk_reg, hfa, hcfa]
        refine ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3],
          by wram_simp [hzR], ?_, ?_⟩, by wram_simp⟩
        · simpa only [Data.write_mem, Data.set_mem, eVal, hk, ↓reduceDIte] using hpws.1
        · simpa only [Data.write_mem, Data.set_mem, eVal, hk, ↓reduceDIte] using hpws.2)
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
        wram_exec [invInitBody, hzC.one, hzC.regL, hzC.invB, hk_reg]
        refine ⟨⟨by wram_simp [hzC], by wram_simp [hzR], ?_, ?_⟩, by wram_simp⟩
        · simp only [Data.write_mem, Data.set_mem]; exact hpws.1
        · simp only [Data.write_mem, Data.set_mem]; exact hpws.2)
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
          simp [List.take_succ_eq_append_getElem, hk]
        have : Fits w (k + 2) := fits_top hw (by wram_omega)
        have : Fits w (4 + j * (L + 2) + (k + 2)) := fits_top hw (by wram_omega)
        have : Fits w (invBase g + bk) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        have hzE : z.regs rEdgeIdx = 4 + j * (L + 2) := hzR.edgeIdx.trans heptr
        have hinv_ne (b : ℕ) (hb : b < L) (hbb : b ≠ bk) : invAt (k + 1) b hb = invAt k b hb := by
          have hne : g.edges[j].constraint ⟨k, hk⟩ ≠ ⟨b, hb⟩ := fun h =>
            hbb (congrArg Fin.val h).symm
          simp [invAt, htake_succ, hne]
        cases hfind : ((List.finRange L).take k).find?
            (fun a => decide (g.edges[j].constraint a = ⟨bk, hbk⟩)) with
        | none =>
          have hcur_eq : invAt k bk hbk = L := by simp [invAt, hfind]
          wram_exec [invFillBody,
            hzC.one, hzC.two, hzC.regL, hzC.invB, hzE, hk_reg, hc_mem, hcur_mem, hcur_eq]
          refine ⟨⟨by wram_simp [hzC], by wram_simp [hzR], ?_, ?_⟩, by wram_simp⟩
          · simp only [Data.write_mem, Data.set_mem]
            intro b hb
            by_cases hbb : b = bk
            · subst hbb
              have hfin : g.edges[j].constraint ⟨k, hk⟩ = ⟨bk, hb⟩ := Fin.ext rfl
              simp [Function.update_self, invAt, htake_succ, hfind, hfin]
            · rw [Function.update_of_ne (by omega), hzInv b hb, hinv_ne b hb hbb]
          · simp only [Data.write_mem, Data.set_mem]
            exact fun addr haddr => (Function.update_of_ne (by omega) _ _).trans (hzFr addr haddr)
        | some a0 =>
          have hcur_ne : invAt k bk hbk ≠ L := by simp [invAt, hfind, a0.isLt.ne]
          wram_exec [invFillBody,
            hzC.one, hzC.two, hzC.regL, hzC.invB, hzE, hk_reg, hc_mem, hcur_mem, hcur_ne]
          refine ⟨⟨by wram_simp [hzC], by wram_simp [hzR], ?_, ?_⟩, by wram_simp⟩
          · intro b hb
            simp only [Data.set_mem, hzInv b hb]
            rcases eq_or_ne b bk with rfl | hbb
            · simp only [invAt, htake_succ, List.find?_append, hfind, Option.some_or]
            · exact (hinv_ne b hb hbb).symm
          · simpa only [Data.set_mem] using hzFr)
      (hlab3 ▸ Nat.zero_le _)
      (hlab3 ▸ ⟨hc3, hr3, fun b hb => by simp [hm3, hinit_inv b hb, invAt],
        fun addr haddr => (congrFun hm3 addr).trans (hfr2 addr haddr)⟩)
  rw [hlab3, Nat.sub_zero] at hx4
  refine ⟨y, (hx1.seq (hx2.seq (hx3.seq hx4))).mono (by omega), hyC, hyR, fun b hb => ?_, hyFr⟩
  rw [hyInv b hb]
  simp only [invAt, List.take_of_length_le (List.length_finRange.le), preimage]
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
          rw [hzFr _ (fun ⟨h1, h2⟩ => not_in_tabRow (g := g) (Ne.symm hsd) hk ⟨h1, by omega⟩),
            hh_mem k hk]
        have hiv_fr : z.mem (invBase g + (h ⟨k, hk⟩).val) = x.mem (invBase g + (h ⟨k, hk⟩).val) :=
          hzFr _ (by wram_omega)
        have : Fits w (tabBase g + g.edges[j].dst * L + k) := fits_top hw (by wram_omega)
        have : Fits w (invBase g + (h ⟨k, hk⟩).val) :=
          fits_top hw (by have := (h ⟨k, hk⟩).isLt; wram_omega)
        have : Fits w (tabBase g + g.edges[j].src * L + k) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        have hpws := prefix_write_step hzRow hzFr
          (rfl : Function.update z.mem (tabBase g + g.edges[j].src * L + k) (eVal k) = _)
        have hb : (if x.mem (invBase g + (h ⟨k, hk⟩).val) = L then (h ⟨k, hk⟩).val
            else x.mem (invBase g + (h ⟨k, hk⟩).val)) = eVal k := by
          simpa only [eVal, hk, ↓reduceDIte, Fin.eta] using hinv_mem _ (h ⟨k, hk⟩).isLt
        by_cases hivL : x.mem (invBase g + (h ⟨k, hk⟩).val) = L <;>
        · wram_exec [extendBwdBody,
          hzC.one, hzC.regL, hzC.invB, hzT2, hzT3, hk_reg, hha, hiv_fr, hivL]
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

private theorem extendPush_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (slotReg : Fin 34)
    (x : Data 34) (u stkLen : ℕ)
    (hsr : slotReg = rSrc ∨ slotReg = rDst)
    (hc : ConstRegs g x) (hu : u < slots g) (hstk_lt : stkLen < slots g)
    (hslot : x.regs slotReg = u) (hsl : x.regs rStackLen = stkLen)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w (extendPush slotReg) x y 5 ∧ ConstRegs g y ∧
      y.regs rEdgeIdx = x.regs rEdgeIdx ∧ y.regs rSrc = x.regs rSrc ∧ y.regs rDst = x.regs rDst ∧
      y.regs rStackLen = stkLen + 1 ∧ y.regs rCompLen = x.regs rCompLen ∧
      y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      y.mem = Function.update (Function.update x.mem (visBase g + u) 1)
        (stackBase g + stkLen) u := by
  have : Fits w (visBase g + u) := fits_top hw (by wram_omega)
  have : Fits w (stackBase g + stkLen) := fits_top hw (by wram_omega)
  have : Fits w (stkLen + 1) := fits_top hw (by wram_omega)
  rcases hsr with rfl | rfl <;>
  · wram_exec [extendPush, hc.one, hc.visB, hc.stackB, hslot, hsl]
    exact ⟨by wram_simp [hc], by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩

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
  have hstk_of {v : ℕ} (hv : v < slots g) (hgv : S.get v = none) : S.stack.length < slots g := by
    have hpos := Finset.card_pos.mpr ⟨v, mem_unvisited (hS.len_table ▸ hv) hgv⟩
    have hpot : S.potential ≤ slots g := hS.pot_le
    unfold State.potential at hpot; omega
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
  have mkPush {xb xp y : Data 34} {v : ℕ} {fn : Fin L → Fin L} (hSb : StateAt g S xb)
      (hcy : ConstRegs g y) (hv : v < slots g) (hn : S.get v = none)
      (hrow : ∀ a (ha : a < L), xp.mem (tabBase g + v * L + a) = (fn ⟨a, ha⟩).val)
      (hfr : ∀ a, ¬ (tabBase g + v * L ≤ a ∧ a < tabBase g + v * L + L) → xp.mem a = xb.mem a)
      (hsl : y.regs rStackLen = S.stack.length + 1) (hcl : y.regs rCompLen = S.comp.length)
      (hym : y.mem = Function.update (Function.update xp.mem (visBase g + v) 1)
        (stackBase g + S.stack.length) v) : StateAt g (push S v fn) y := by
    have := tabRow_hi_le_candBase (g := g) hv
    have := hstk_of hv hn
    have hstk : HoldsList (stackBase g) (S.stack.reverse ++ [v]) y.mem := by
      simpa only [hym, List.length_reverse] using
        (hSb.stack_mem.frame fun a ha1 ha2 => by
          rw [Function.update_of_ne (by wram_omega),
            hfr _ (by wram_omega)]).append_one v
    exact hSb.push_slot hcy hv hn
      (fun a ha => by
        rw [hym, Function.update_of_ne (by wram_omega)]
        rw [Function.update_of_ne (by wram_omega)]
        exact hrow a ha)
      (by rw [hym, Function.update_of_ne (by wram_omega), Function.update_self]) hstk hsl hcl
      (fun a hnr hnv hns => by
        rw [hym, Function.update_of_ne hns, Function.update_of_ne hnv, hfr a hnr])
  cases hgs : S.get e.src with
  | some f =>
    obtain ⟨hvis_s, htab_s⟩ := hS.vis_some e.src hs_lt f hgs
    have hc_outer : (Cond.eq rTmp1 rOne).Holds x1 := by
      simp only [Cond.holds_eq, ht1_1, ← he_def, hvis_s, hc1.one]
    cases hgd : S.get e.dst with
    | none =>
      have hsd : e.src ≠ e.dst := by intro h0; rw [← h0, hgs] at hgd; nomatch hgd
      have hc_inner : (Cond.eq rTmp2 rZero).Holds x1 := by
        simp only [Cond.holds_eq, ht2_1, ← he_def, hS.vis_none e.dst hd_lt hgd, hc1.zero]
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
      obtain ⟨y, hx4, hc4, he4', hs4', hd4', hsl4, hcl4', hcn4', hrem4', hidx4', hym⟩ :=
        extendPush_spec (w := w) g rDst x3 e.dst S.stack.length (Or.inr rfl) hc3
          hd_lt (hstk_of hd_lt hgd) (hr3.dst.trans hdst_reg) (hr3.stackLen.trans hS.stack_len) hw
      have hcb_d := tabRow_hi_le_candBase (g := g) hd_lt
      have hSy := mkPush (fn := e.constraint ∘ f) hS hc4 hd_lt hgd hrow3
        (fun a ha => (hfr3 a ha).trans (congrFun hm2 a))
        hsl4 (hcl4'.trans (hr3.compLen.trans hS.comp_len)) hym
      simp only [extend, hgs, hgd]
      refine ⟨y, (hx1.seq (ExecWithin.branch_pos hc_outer
          (ExecWithin.branch_pos hc_inner (hx2.seq (hx3.seq hx4))))).mono (by omega),
        hSy, he4'.trans (hr3.edgeIdx.trans heptr),
        hs4'.trans (hr3.src.trans hsrc_reg), hd4'.trans (hr3.dst.trans hdst_reg),
        hcn4'.trans hr3.curNode, hrem4'.trans hr3.rem, hidx4'.trans hr3.outerIdx, fun a ha => ?_⟩
      · rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by omega),
          hfr3 _ (by wram_omega), hm2]
    | some h =>
      obtain ⟨hvis_d, _⟩ := hS.vis_some e.dst hd_lt h hgd
      have hc_inner : ¬ (Cond.eq rTmp2 rZero).Holds x1 := by
        simp [Cond.holds_eq, ht2_1, ← he_def, hvis_d, hc1.zero]
      exact retSame (by simp only [extend, hgs, hgd])
        ((hx1.seq (ExecWithin.branch_pos hc_outer (ExecWithin.branch_neg hc_inner hnop))).mono
          (by omega))
  | none =>
    have hc_outer : ¬ (Cond.eq rTmp1 rOne).Holds x1 := by
      simp [Cond.holds_eq, ht1_1, ← he_def, hS.vis_none e.src hs_lt hgs, hc1.one]
    cases hgd : S.get e.dst with
    | some h =>
      obtain ⟨hvis_d, htab_d⟩ := hS.vis_some e.dst hd_lt h hgd
      have hsd : e.src ≠ e.dst := by intro h0; rw [← h0, hgs] at hgd; nomatch hgd
      have hc_inner : (Cond.eq rTmp2 rOne).Holds x1 := by
        simp only [Cond.holds_eq, ht2_1, ← he_def, hvis_d, hc1.one]
      have hcb_s := tabRow_hi_le_candBase (g := g) hs_lt
      have hcb_d := tabRow_hi_le_candBase (g := g) hd_lt
      obtain ⟨x2, hx2, hc2, hr2', hinv2, hfr2⟩ :=
        invLoops_spec (w := w) g x1 j hj hc1 (hm1 ▸ hS.inp) he1 hw
      have hr2 := hr2'.trans hr1
      obtain ⟨x3, hx3, hc3, ht2_3, ht3_3, hlab3, hr3', hm3⟩ :=
        extendPrep_spec (w := w) g rDst rSrc x2 e.dst e.src (Or.inr ⟨rfl, rfl⟩)
          hc2 hd_lt hs_lt (hr2.dst.trans hdst_reg) (hr2.src.trans hsrc_reg) hw
      have hr3 := hr3'.trans hr2
      obtain ⟨x4, hx4, hc4, hr4', hrow4, hfr4⟩ :=
        extendBwdLoop_spec (w := w) g x3 j hj h hc3 hs_lt hd_lt hsd ht2_3 ht3_3 hlab3
          (fun a ha => by
            rw [← he_def, hm3, hfr2 _ (by wram_omega), hm1, htab_d a ha])
          (fun b hb => by simpa only [hm3] using hinv2 b hb) hw
      have hr4 := hr4'.trans hr3
      simp only [← he_def] at hrow4 hfr4
      obtain ⟨y, hx5, hc5, he5', hs5', hd5', hsl5, hcl5', hcn5', hrem5', hidx5', hym⟩ :=
        extendPush_spec (w := w) g rSrc x4 e.src S.stack.length (Or.inl rfl) hc4
          hs_lt (hstk_of hs_lt hgs) (hr4.src.trans hsrc_reg) (hr4.stackLen.trans hS.stack_len) hw
      have hS' : StateAt g S x2 :=
        hS.frame_inv hc2 (hr2.stackLen.trans hS.stack_len) (hr2.compLen.trans hS.comp_len)
          (fun a ha => by rw [hfr2 a ha, hm1])
      have hSy := mkPush (fn := preimage (List.finRange L) e.constraint ∘ h) hS' hc5 hs_lt hgs
        hrow4 (fun a ha => (hfr4 a ha).trans (congrFun hm3 a))
        hsl5 (hcl5'.trans (hr4.compLen.trans hS.comp_len)) hym
      simp only [extend, hgs, hgd]
      refine ⟨y, (hx1.seq (ExecWithin.branch_neg hc_outer
          (ExecWithin.branch_pos hc_inner (hx2.seq (hx3.seq (hx4.seq hx5)))))).mono (by omega),
        hSy, he5'.trans (hr4.edgeIdx.trans heptr),
        hs5'.trans (hr4.src.trans hsrc_reg), hd5'.trans (hr4.dst.trans hdst_reg),
        hcn5'.trans hr4.curNode, hrem5'.trans hr4.rem, hidx5'.trans hr4.outerIdx, fun a ha => ?_⟩
      · rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by omega),
          hfr4 _ (by wram_omega), hm3, hfr2 _ (by wram_omega), hm1]
    | none =>
      have hc_inner : ¬ (Cond.eq rTmp2 rOne).Holds x1 := by
        simp [Cond.holds_eq, ht2_1, ← he_def, hS.vis_none e.dst hd_lt hgd, hc1.one]
      exact retSame (by simp only [extend, hgs, hgd])
        ((hx1.seq (ExecWithin.branch_neg hc_outer (ExecWithin.branch_neg hc_inner hnop))).mono
          (by omega))

end Cslib.Complexity.UniqueGames.Propagation
