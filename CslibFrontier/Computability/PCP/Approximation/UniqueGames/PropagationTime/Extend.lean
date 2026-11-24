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
      ConstRegs g y ∧
      y.regs rEdgeIdx = x.regs rEdgeIdx ∧ y.regs rSrc = x.regs rSrc ∧ y.regs rDst = x.regs rDst ∧
      y.regs rStackLen = x.regs rStackLen ∧ y.regs rCompLen = x.regs rCompLen ∧
      y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      (∀ a (ha : a < L), y.mem (tabBase g + g.edges[j].dst * L + a) =
        (g.edges[j].constraint (f ⟨a, ha⟩)).val) ∧
      ∀ addr, ¬ (tabBase g + g.edges[j].dst * L ≤ addr ∧
          addr < tabBase g + g.edges[j].dst * L + L) → y.mem addr = x.mem addr := by
  have hwb := outBaseAddr_lt_wordBound g
  have hed := edge_end_le_headBase hj
  have hcb_src := tabRow_hi_le_candBase (g := g) hsrc_lt
  have hcb_dst := tabRow_hi_le_candBase (g := g) hdst_lt
  have hfit_top : Fits w (outBaseAddr g + slots g) := hw.of_le (by omega)
  let eVal (a : ℕ) : ℕ :=
    if ha : a < L then (g.edges[j].constraint (f ⟨a, ha⟩)).val else 0
  let P (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ z.regs rTmp2 = tabBase g + g.edges[j].src * L ∧
    z.regs rTmp3 = tabBase g + g.edges[j].dst * L ∧
    z.regs rEdgeIdx = 4 + j * (L + 2) ∧
    z.regs rSrc = x.regs rSrc ∧ z.regs rDst = x.regs rDst ∧
    z.regs rStackLen = x.regs rStackLen ∧ z.regs rCompLen = x.regs rCompLen ∧
    z.regs rCurNode = x.regs rCurNode ∧ z.regs rRem = x.regs rRem ∧
    z.regs rOuterIdx = x.regs rOuterIdx ∧
    (∀ i < k, z.mem (tabBase g + g.edges[j].dst * L + i) = eVal i) ∧
    ∀ addr, ¬ (tabBase g + g.edges[j].dst * L ≤ addr ∧
        addr < tabBase g + g.edges[j].dst * L + k) → z.mem addr = x.mem addr
  obtain ⟨y, hy, ⟨hyC, _, _, hyE, hyS, hyD, hySL, hyCL, hyCN, hyRem, hyIdx, hyRow, hyFr⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := extendFwdBody)
      (N := L) (T := 8) P
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzT2, hzT3, hzE, hzS, hzD, hzSL, hzCL, hzCN, hzRem, hzIdx, hzRow, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have hfk_lt := (f ⟨k, hk⟩).isLt
        have hfa : z.mem (tabBase g + g.edges[j].src * L + k) = (f ⟨k, hk⟩).val := by
          rw [hzFr _ (fun ⟨h1, h2⟩ => not_in_tabRow (g := g) hsd hk ⟨h1, by omega⟩)]
          exact hf_mem k hk
        have hcfa : z.mem (4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2)) =
            (g.edges[j].constraint (f ⟨k, hk⟩)).val := by
          rw [hzFr _ (by simp only [tabBase, visBase, nodeBase] at *; omega),
            show 4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2) =
              4 + j * (L + 2) + 2 + (f ⟨k, hk⟩).val by omega]
          exact hinp.edge_val j hj (f ⟨k, hk⟩).val hfk_lt
        have : Fits w (tabBase g + g.edges[j].src * L + k) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
        have : Fits w ((f ⟨k, hk⟩).val + 2) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase, candBase, tabBase, visBase,
            nodeBase] at *; omega)
        have : Fits w (4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2)) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase, candBase, tabBase, visBase,
            nodeBase] at *; omega)
        have : Fits w (tabBase g + g.edges[j].dst * L + k) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
        have : Fits w (k + 1) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
        have heVal_k : (g.edges[j].constraint (f ⟨k, hk⟩)).val = eVal k := by simp [eVal, hk]
        have hpws := prefix_write_step hzRow hzFr
          (rfl : Function.update z.mem (tabBase g + g.edges[j].dst * L + k) (eVal k) = _)
        unfold extendFwdBody
        wram_exec [hzC.one, hzC.two, hzT2, hzT3, hzE, hk_reg, hfa, hcfa]
        refine ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3],
          by wram_simp [hzE], by wram_simp [hzS], by wram_simp [hzD], by wram_simp [hzSL],
          by wram_simp [hzCL], by wram_simp [hzCN], by wram_simp [hzRem], by wram_simp [hzIdx],
          ?_, ?_⟩, by wram_simp⟩
        · simp only [Data.write_mem, Data.set_mem, heVal_k]; exact hpws.1
        · simp only [Data.write_mem, Data.set_mem, heVal_k]; exact hpws.2)
      (by rw [hlab]; exact Nat.zero_le _)
      (by rw [hlab]; exact ⟨hc, ht2, ht3, heptr, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun _ h => by omega, fun _ _ => rfl⟩)
  rw [hlab, Nat.sub_zero] at hy
  exact ⟨y, hy, hyC, hyE.trans heptr.symm, hyS, hyD, hySL, hyCL, hyCN, hyRem, hyIdx,
    fun a ha => by simpa [eVal, ha] using hyRow a ha, hyFr⟩

private theorem invLoops_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (x : Data 34)
    (j : ℕ) (hj : j < g.edges.length)
    (hc : ConstRegs g x) (hinp : InputAt g x.mem)
    (heptr : x.regs rEdgeIdx = 4 + j * (L + 2))
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w invLoopsCode x y (16 * L + 6) ∧
      ConstRegs g y ∧
      y.regs rEdgeIdx = x.regs rEdgeIdx ∧ y.regs rSrc = x.regs rSrc ∧ y.regs rDst = x.regs rDst ∧
      y.regs rStackLen = x.regs rStackLen ∧ y.regs rCompLen = x.regs rCompLen ∧
      y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      (∀ b (hb : b < L),
        (if y.mem (invBase g + b) = L then b else y.mem (invBase g + b)) =
          (preimage (List.finRange L) g.edges[j].constraint ⟨b, hb⟩).val) ∧
      ∀ addr, ¬ (invBase g ≤ addr ∧ addr < invBase g + L) → y.mem addr = x.mem addr := by
  have hwb := outBaseAddr_lt_wordBound g
  have hed := edge_end_le_headBase hj
  have hfit_top : Fits w (outBaseAddr g + slots g) := hw.of_le (by omega)
  have hset0 : ∃ x1, ExecWithin w (ram[ rLabIdx ← rZero ] : Code .standard 34) x x1 1 ∧
      ConstRegs g x1 ∧ x1.regs rLabIdx = 0 ∧ x1.regs rEdgeIdx = 4 + j * (L + 2) ∧
      x1.regs rSrc = x.regs rSrc ∧ x1.regs rDst = x.regs rDst ∧
      x1.regs rStackLen = x.regs rStackLen ∧ x1.regs rCompLen = x.regs rCompLen ∧
      x1.regs rCurNode = x.regs rCurNode ∧ x1.regs rRem = x.regs rRem ∧
      x1.regs rOuterIdx = x.regs rOuterIdx ∧ x1.mem = x.mem := by
    wram_exec [hc.zero]
    exact ⟨by wram_simp [hc], by wram_simp, by wram_simp [heptr], by wram_simp, by wram_simp,
      by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x1, hx1, hc1, hlab1, he1, hs1, hd1, hsl1, hcl1, hcn1, hrem1, hidx1, hm1⟩ := hset0
  let Pinit (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ z.regs rEdgeIdx = 4 + j * (L + 2) ∧
    z.regs rSrc = x.regs rSrc ∧ z.regs rDst = x.regs rDst ∧
    z.regs rStackLen = x.regs rStackLen ∧ z.regs rCompLen = x.regs rCompLen ∧
    z.regs rCurNode = x.regs rCurNode ∧ z.regs rRem = x.regs rRem ∧
    z.regs rOuterIdx = x.regs rOuterIdx ∧
    (∀ b < k, z.mem (invBase g + b) = L) ∧
    ∀ addr, ¬ (invBase g ≤ addr ∧ addr < invBase g + k) → z.mem addr = x.mem addr
  obtain ⟨x2, hx2, ⟨hc2, he2, hs2, hd2, hsl2, hcl2, hcn2, hrem2, hidx2, hinit_inv, hfr2⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := invInitBody)
      (N := L) (T := 3) Pinit
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzE, hzS, hzD, hzSL, hzCL, hzCN, hzRem, hzIdx, hzInv, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have : Fits w (invBase g + k) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase] at *; omega)
        have : Fits w (k + 1) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
        have hpws := prefix_write_step (e := fun _ => L) hzInv hzFr
          (rfl : Function.update z.mem (invBase g + k) L = _)
        unfold invInitBody
        wram_exec [hzC.one, hzC.regL, hzC.invB, hk_reg]
        refine ⟨⟨by wram_simp [hzC], by wram_simp [hzE], by wram_simp [hzS], by wram_simp [hzD],
          by wram_simp [hzSL], by wram_simp [hzCL], by wram_simp [hzCN], by wram_simp [hzRem],
          by wram_simp [hzIdx], ?_, ?_⟩, by wram_simp⟩
        · simp only [Data.write_mem, Data.set_mem]; exact hpws.1
        · simp only [Data.write_mem, Data.set_mem]; exact hpws.2)
      (by rw [hlab1]; exact Nat.zero_le _)
      (by rw [hlab1]; exact ⟨hc1, he1, hs1, hd1, hsl1, hcl1, hcn1, hrem1, hidx1,
        fun _ h => by omega, fun addr _ => congrFun hm1 addr⟩)
  rw [hlab1, Nat.sub_zero] at hx2
  have hset2 : ∃ x3, ExecWithin w (ram[ rLabIdx ← rZero ] : Code .standard 34) x2 x3 1 ∧
      ConstRegs g x3 ∧ x3.regs rLabIdx = 0 ∧ x3.regs rEdgeIdx = 4 + j * (L + 2) ∧
      x3.regs rSrc = x.regs rSrc ∧ x3.regs rDst = x.regs rDst ∧
      x3.regs rStackLen = x.regs rStackLen ∧ x3.regs rCompLen = x.regs rCompLen ∧
      x3.regs rCurNode = x.regs rCurNode ∧ x3.regs rRem = x.regs rRem ∧
      x3.regs rOuterIdx = x.regs rOuterIdx ∧ x3.mem = x2.mem := by
    wram_exec [hc2.zero]
    exact ⟨by wram_simp [hc2], by wram_simp, by wram_simp [he2], by wram_simp [hs2],
      by wram_simp [hd2], by wram_simp [hsl2], by wram_simp [hcl2], by wram_simp [hcn2],
      by wram_simp [hrem2], by wram_simp [hidx2], by wram_simp⟩
  obtain ⟨x3, hx3, hc3, hlab3, he3, hs3, hd3, hsl3, hcl3, hcn3, hrem3, hidx3, hm3⟩ := hset2
  let invAt (k : ℕ) (b : ℕ) (hb : b < L) : ℕ :=
    (((List.finRange L).take k).find? fun a => decide (g.edges[j].constraint a = ⟨b, hb⟩)).elim
      L Fin.val
  let Pfill (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ z.regs rEdgeIdx = 4 + j * (L + 2) ∧
    z.regs rSrc = x.regs rSrc ∧ z.regs rDst = x.regs rDst ∧
    z.regs rStackLen = x.regs rStackLen ∧ z.regs rCompLen = x.regs rCompLen ∧
    z.regs rCurNode = x.regs rCurNode ∧ z.regs rRem = x.regs rRem ∧
    z.regs rOuterIdx = x.regs rOuterIdx ∧
    (∀ b (hb : b < L), z.mem (invBase g + b) = invAt k b hb) ∧
    ∀ addr, ¬ (invBase g ≤ addr ∧ addr < invBase g + L) → z.mem addr = x.mem addr
  obtain ⟨y, hx4, ⟨hyC, hyE, hyS, hyD, hySL, hyCL, hyCN, hyRem, hyIdx, hyInv, hyFr⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := invFillBody)
      (N := L) (T := 9) Pfill
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzE, hzS, hzD, hzSL, hzCL, hzCN, hzRem, hzIdx, hzInv, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        set bk := (g.edges[j].constraint ⟨k, hk⟩).val
        have hbk : bk < L := (g.edges[j].constraint ⟨k, hk⟩).isLt
        have hc_mem : z.mem (4 + j * (L + 2) + (k + 2)) = bk := by
          rw [hzFr _ (by simp only [invBase, candBase, tabBase, visBase, nodeBase] at *; omega),
            show 4 + j * (L + 2) + (k + 2) = 4 + j * (L + 2) + 2 + k by omega]
          exact hinp.edge_val j hj k hk
        have hcur_mem : z.mem (invBase g + bk) = invAt k bk hbk := hzInv bk hbk
        have htake_succ : (List.finRange L).take (k + 1) =
            (List.finRange L).take k ++ [⟨k, hk⟩] := by
          rw [List.take_succ_eq_append_getElem (by simp [hk]), List.getElem_finRange]
          rfl
        have : Fits w (k + 2) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase, candBase, tabBase, visBase,
            nodeBase] at *; omega)
        have : Fits w (4 + j * (L + 2) + (k + 2)) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase, candBase, tabBase, visBase,
            nodeBase] at *; omega)
        have : Fits w (invBase g + bk) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase] at *; omega)
        have : Fits w (k + 1) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
        cases hfind : ((List.finRange L).take k).find?
            (fun a => decide (g.edges[j].constraint a = ⟨bk, hbk⟩)) with
        | none =>
          have hcur_eq : invAt k bk hbk = L := by simp [invAt, hfind]
          unfold invFillBody
          wram_exec [hzC.one, hzC.two, hzC.regL, hzC.invB, hzE, hk_reg, hc_mem, hcur_mem, hcur_eq]
          refine ⟨⟨by wram_simp [hzC], by wram_simp [hzE], by wram_simp [hzS], by wram_simp [hzD],
            by wram_simp [hzSL], by wram_simp [hzCL], by wram_simp [hzCN], by wram_simp [hzRem],
            by wram_simp [hzIdx], ?_, ?_⟩, by wram_simp⟩
          · simp only [Data.write_mem, Data.set_mem]
            intro b hb
            by_cases hbb : b = bk
            · subst hbb
              rw [Function.update_self]
              have hfin_eq : g.edges[j].constraint ⟨k, hk⟩ = ⟨bk, hb⟩ := Fin.ext rfl
              dsimp only [invAt]
              rw [htake_succ, List.find?_append, hfind, Option.none_or]
              simp [hfin_eq]
            · rw [Function.update_of_ne (by omega : invBase g + b ≠ invBase g + bk), hzInv b hb]
              have hne_fin : g.edges[j].constraint ⟨k, hk⟩ ≠ ⟨b, hb⟩ := by
                intro heq; exact hbb ((congrArg Fin.val heq).symm)
              simp [invAt, htake_succ, List.find?_append, hne_fin]
          · simp only [Data.write_mem, Data.set_mem]
            intro addr haddr
            rw [Function.update_of_ne (by omega : addr ≠ invBase g + bk)]
            exact hzFr addr haddr
        | some a0 =>
          have hcur_ne : invAt k bk hbk ≠ L := by
            simp only [invAt, hfind, Option.elim_some]
            exact ne_of_lt a0.isLt
          unfold invFillBody
          wram_exec [hzC.one, hzC.two, hzC.regL, hzC.invB, hzE, hk_reg, hc_mem, hcur_mem, hcur_ne]
          refine ⟨⟨by wram_simp [hzC], by wram_simp [hzE], by wram_simp [hzS], by wram_simp [hzD],
            by wram_simp [hzSL], by wram_simp [hzCL], by wram_simp [hzCN], by wram_simp [hzRem],
            by wram_simp [hzIdx], ?_, ?_⟩, by wram_simp⟩
          · simp only [Data.set_mem]
            intro b hb
            rw [hzInv b hb]
            by_cases hbb : b = bk
            · subst hbb
              simp only [invAt, htake_succ, List.find?_append, hfind, Option.some_or]
            · have hne_fin : g.edges[j].constraint ⟨k, hk⟩ ≠ ⟨b, hb⟩ := by
                intro heq; exact hbb ((congrArg Fin.val heq).symm)
              simp [invAt, htake_succ, List.find?_append, hne_fin]
          · simp only [Data.set_mem]
            exact hzFr)
      (by rw [hlab3]; exact Nat.zero_le _)
      (by rw [hlab3]; refine ⟨hc3, he3, hs3, hd3, hsl3, hcl3, hcn3, hrem3, hidx3,
        fun b hb => ?_, fun addr haddr => ?_⟩
          · rw [hm3, hinit_inv b hb]; simp [invAt]
          · rw [hm3]; exact hfr2 addr haddr)
  rw [hlab3, Nat.sub_zero] at hx4
  refine ⟨y, (hx1.seq (hx2.seq (hx3.seq hx4))).mono (by omega), hyC, hyE.trans heptr.symm,
    hyS, hyD, hySL, hyCL, hyCN, hyRem, hyIdx, fun b hb => ?_, hyFr⟩
  rw [hyInv b hb]
  have htakeL : (List.finRange L).take L = List.finRange L :=
    List.take_of_length_le (by simp)
  simp only [invAt, htakeL, preimage]
  cases h : (List.finRange L).find? (fun a => decide (g.edges[j].constraint a = ⟨b, hb⟩)) with
  | none => simp
  | some a0 => simp [ne_of_lt a0.isLt]

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
      ConstRegs g y ∧
      y.regs rEdgeIdx = x.regs rEdgeIdx ∧ y.regs rSrc = x.regs rSrc ∧ y.regs rDst = x.regs rDst ∧
      y.regs rStackLen = x.regs rStackLen ∧ y.regs rCompLen = x.regs rCompLen ∧
      y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      (∀ a (ha : a < L), y.mem (tabBase g + g.edges[j].src * L + a) =
        (preimage (List.finRange L) g.edges[j].constraint (h ⟨a, ha⟩)).val) ∧
      ∀ addr, ¬ (tabBase g + g.edges[j].src * L ≤ addr ∧
          addr < tabBase g + g.edges[j].src * L + L) → y.mem addr = x.mem addr := by
  have hwb := outBaseAddr_lt_wordBound g
  have hcb_src := tabRow_hi_le_candBase (g := g) hsrc_lt
  have hcb_dst := tabRow_hi_le_candBase (g := g) hdst_lt
  have hfit_top : Fits w (outBaseAddr g + slots g) := hw.of_le (by omega)
  let eVal (a : ℕ) : ℕ :=
    if ha : a < L then (preimage (List.finRange L) g.edges[j].constraint (h ⟨a, ha⟩)).val else 0
  let P (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ z.regs rTmp2 = tabBase g + g.edges[j].dst * L ∧
    z.regs rTmp3 = tabBase g + g.edges[j].src * L ∧
    z.regs rEdgeIdx = x.regs rEdgeIdx ∧ z.regs rSrc = x.regs rSrc ∧ z.regs rDst = x.regs rDst ∧
    z.regs rStackLen = x.regs rStackLen ∧ z.regs rCompLen = x.regs rCompLen ∧
    z.regs rCurNode = x.regs rCurNode ∧ z.regs rRem = x.regs rRem ∧
    z.regs rOuterIdx = x.regs rOuterIdx ∧
    (∀ i < k, z.mem (tabBase g + g.edges[j].src * L + i) = eVal i) ∧
    ∀ addr, ¬ (tabBase g + g.edges[j].src * L ≤ addr ∧
        addr < tabBase g + g.edges[j].src * L + k) → z.mem addr = x.mem addr
  obtain ⟨y, hy, ⟨hyC, _, _, hyE, hyS, hyD, hySL, hyCL, hyCN, hyRem, hyIdx, hyRow, hyFr⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := extendBwdBody)
      (N := L) (T := 10) P
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzT2, hzT3, hzE, hzS, hzD, hzSL, hzCL, hzCN, hzRem, hzIdx, hzRow, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have hha : z.mem (tabBase g + g.edges[j].dst * L + k) = (h ⟨k, hk⟩).val := by
          rw [hzFr _ (fun ⟨h1, h2⟩ => not_in_tabRow (g := g) (Ne.symm hsd) hk ⟨h1, by omega⟩)]
          exact hh_mem k hk
        have hiv_fr : z.mem (invBase g + (h ⟨k, hk⟩).val) = x.mem (invBase g + (h ⟨k, hk⟩).val) :=
          hzFr _ (by simp only [invBase] at *; omega)
        have hiv_val := hinv_mem (h ⟨k, hk⟩).val (h ⟨k, hk⟩).isLt
        simp only [Fin.eta] at hiv_val
        have : Fits w (tabBase g + g.edges[j].dst * L + k) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
        have : Fits w (invBase g + (h ⟨k, hk⟩).val) := hfit_top.of_le (by
          have := (h ⟨k, hk⟩).isLt
          simp only [outBaseAddr, compBase, stackBase] at *; omega)
        have : Fits w (tabBase g + g.edges[j].src * L + k) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
        have : Fits w (k + 1) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
        by_cases hivL : x.mem (invBase g + (h ⟨k, hk⟩).val) = L
        · have heq_b : (h ⟨k, hk⟩).val = eVal k := by
            simp only [hivL, ↓reduceIte] at hiv_val
            simp [eVal, hk, hiv_val]
          have hpws := prefix_write_step hzRow hzFr
            (rfl : Function.update z.mem (tabBase g + g.edges[j].src * L + k) (eVal k) = _)
          unfold extendBwdBody
          wram_exec [hzC.one, hzC.regL, hzC.invB, hzT2, hzT3, hk_reg, hha, hiv_fr, hivL]
          refine ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3],
            by wram_simp [hzE], by wram_simp [hzS], by wram_simp [hzD], by wram_simp [hzSL],
            by wram_simp [hzCL], by wram_simp [hzCN], by wram_simp [hzRem], by wram_simp [hzIdx],
            ?_, ?_⟩, by wram_simp⟩
          · simp only [Data.write_mem, Data.set_mem, heq_b]; exact hpws.1
          · simp only [Data.write_mem, Data.set_mem, heq_b]; exact hpws.2
        · have heq_iv : x.mem (invBase g + (h ⟨k, hk⟩).val) = eVal k := by
            simp only [hivL, ↓reduceIte] at hiv_val
            simp [eVal, hk, hiv_val]
          have hpws := prefix_write_step hzRow hzFr
            (rfl : Function.update z.mem (tabBase g + g.edges[j].src * L + k) (eVal k) = _)
          unfold extendBwdBody
          wram_exec [hzC.one, hzC.regL, hzC.invB, hzT2, hzT3, hk_reg, hha, hiv_fr, hivL]
          refine ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3],
            by wram_simp [hzE], by wram_simp [hzS], by wram_simp [hzD], by wram_simp [hzSL],
            by wram_simp [hzCL], by wram_simp [hzCN], by wram_simp [hzRem], by wram_simp [hzIdx],
            ?_, ?_⟩, by wram_simp⟩
          · simp only [Data.write_mem, Data.set_mem, heq_iv]; exact hpws.1
          · simp only [Data.write_mem, Data.set_mem, heq_iv]; exact hpws.2)
      (by rw [hlab]; exact Nat.zero_le _)
      (by rw [hlab]; exact ⟨hc, ht2, ht3, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun _ h => by omega, fun _ _ => rfl⟩)
  rw [hlab, Nat.sub_zero] at hy
  exact ⟨y, hy, hyC, hyE, hyS, hyD, hySL, hyCL, hyCN, hyRem, hyIdx,
    fun a ha => by simpa [eVal, ha] using hyRow a ha, hyFr⟩

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
  have hwb := outBaseAddr_lt_wordBound g
  have hfit_top : Fits w (outBaseAddr g + slots g) := hw.of_le (by omega)
  have : Fits w (visBase g + u) := hfit_top.of_le (by
    simp only [outBaseAddr, compBase, stackBase, invBase, candBase, tabBase] at *; omega)
  have : Fits w (stackBase g + stkLen) := hfit_top.of_le (by
    simp only [outBaseAddr, compBase] at *; omega)
  have : Fits w (stkLen + 1) := hfit_top.of_le (by
    simp only [outBaseAddr, compBase] at *; omega)
  rcases hsr with rfl | rfl <;>
  · unfold extendPush
    wram_exec [hc.one, hc.visB, hc.stackB, hslot, hsl]
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
  obtain ⟨x1, hx1, hc1, ht1_1, ht2_1, he1, hs1, hd1, hsl1, hcl1, hcn1, hrem1, hidx1, hm1⟩ :=
    edgeVisLoad_spec (w := w) g S x j hj hS heptr hsrc_reg hdst_reg hw
  simp only [← he_def] at ht1_1 ht2_1 hs1 hd1
  have hnop : ExecWithin w (.op (.copy rLabIdx rLabIdx)) x1 x1 1 :=
    ⟨1, le_rfl, exec_nop rLabIdx x1⟩
  have hS1 : StateAt g S x1 := hS.of_eq hc1 hsl1 hcl1 hm1
  cases hgs : S.get e.src with
  | some f =>
    obtain ⟨hvis_s, htab_s⟩ := hS.vis_some e.src hs_lt f hgs
    have hc_outer : (Cond.eq rTmp1 rOne).Holds x1 := by simp [Cond.holds_eq, ht1_1, hvis_s, hc1.one]
    cases hgd : S.get e.dst with
    | none =>
      have hvis_d : x.mem (visBase g + e.dst) = 0 := hS.vis_none e.dst hd_lt hgd
      have hsd : e.src ≠ e.dst := by intro h0; rw [← h0, hgs] at hgd; nomatch hgd
      have hc_inner : (Cond.eq rTmp2 rZero).Holds x1 := by
        simp [Cond.holds_eq, ht2_1, hvis_d, hc1.zero]
      have hstk_lt : S.stack.length < slots g := by
        have hmem := mem_unvisited (hS.len_table ▸ hd_lt) hgd
        have hpos : 0 < S.unvisited.card := Finset.card_pos.mpr ⟨e.dst, hmem⟩
        have hpot : S.potential ≤ slots g := hS.pot_le
        unfold State.potential at hpot; omega
      obtain ⟨x2, hx2, hc2, ht2_2, ht3_2, hlab2, he2', hs2', hd2',
          hsl2', hcl2', hcn2', hrem2', hidx2', hm2'⟩ :=
        extendPrep_spec (w := w) g rSrc rDst x1 e.src e.dst (Or.inl ⟨rfl, rfl⟩)
          hc1 hs_lt hd_lt hs1 hd1 hw
      have he2 := he2'.trans he1
      have hs2 := hs2'.trans hs1
      have hd2 := hd2'.trans hd1
      have hsl2 := hsl2'.trans hsl1
      have hcl2 := hcl2'.trans hcl1
      have hcn2 := hcn2'.trans hcn1
      have hrem2 := hrem2'.trans hrem1
      have hidx2 := hidx2'.trans hidx1
      have hm2 := hm2'.trans hm1
      obtain ⟨x3, hx3, hc3, he3, hs3, hd3, hsl3, hcl3, hcn3, hrem3, hidx3, hrow3, hfr3⟩ :=
        extendFwdLoop_spec (w := w) g x2 j hj f hc2 (hm2 ▸ hS.inp) he2 hs_lt hd_lt hsd
          ht2_2 ht3_2 hlab2 (fun a ha => by rw [hm2]; exact htab_s a ha) hw
      simp only [← he_def] at hrow3 hfr3
      obtain ⟨y, hx4, hc4, he4', hs4', hd4', hsl4, hcl4', hcn4', hrem4', hidx4', hym⟩ :=
        extendPush_spec (w := w) g rDst x3 e.dst S.stack.length (Or.inr rfl)
          hc3 hd_lt hstk_lt (hd3.trans hd2) (hsl3.trans hsl2) hw
      have he4 := he4'.trans (he3.trans he2)
      have hs4 := hs4'.trans (hs3.trans hs2)
      have hd4 := hd4'.trans (hd3.trans hd2)
      have hcl4 := hcl4'.trans (hcl3.trans hcl2)
      have hcn4 := hcn4'.trans (hcn3.trans hcn2)
      have hrem4 := hrem4'.trans (hrem3.trans hrem2)
      have hidx4 := hidx4'.trans (hidx3.trans hidx2)
      have hcb_d := tabRow_hi_le_candBase (g := g) hd_lt
      have hstk_mem : HoldsList (stackBase g) (S.stack.reverse ++ [e.dst]) y.mem := by
        have hbase : HoldsList (stackBase g) S.stack.reverse
            (Function.update x3.mem (visBase g + e.dst) 1) :=
          hS.stack_mem.frame fun a ha1 ha2 => by
            rw [Function.update_of_ne
                (by simp only [stackBase, invBase, candBase, tabBase] at *; omega),
              hfr3 _ (by simp only [stackBase, invBase] at *; omega), hm2]
        simpa only [hym, List.length_reverse] using hbase.append_one e.dst
      have hSy : StateAt g (push S e.dst (e.constraint ∘ f)) y :=
        hS.push_slot hc4 hd_lt hgd
          (fun a ha => by
            rw [hym, Function.update_of_ne (by simp only [stackBase, invBase] at *; omega),
              Function.update_of_ne (by simp only [tabBase]; omega)]
            exact hrow3 a ha)
          (by rw [hym, Function.update_of_ne (by
                simp only [stackBase, invBase, candBase, tabBase] at *; omega),
              Function.update_self])
          hstk_mem hsl4 hcl4
          (fun a hnr hnv hns => by
            rw [hym, Function.update_of_ne hns, Function.update_of_ne hnv, hfr3 a hnr, hm2])
      have hex_tot : ExecWithin w extendCode x y (28 * L + 30) :=
        (hx1.seq (ExecWithin.branch_pos hc_outer
          (ExecWithin.branch_pos hc_inner (hx2.seq (hx3.seq hx4))))).mono (by omega)
      refine ⟨y, hex_tot, ?_, he4, hs4, hd4, hcn4, hrem4, hidx4, fun a ha => ?_⟩
      · simpa only [extend, hgs, hgd] using hSy
      · rw [hym, Function.update_of_ne (by
            simp only [stackBase, invBase, candBase, tabBase] at *; omega),
          Function.update_of_ne (by omega), hfr3 _ (by simp only [tabBase]; omega), hm2]
    | some h =>
      obtain ⟨hvis_d, _⟩ := hS.vis_some e.dst hd_lt h hgd
      have hc_inner : ¬ (Cond.eq rTmp2 rZero).Holds x1 := by
        simp [Cond.holds_eq, ht2_1, hvis_d, hc1.zero]
      have hex_tot : ExecWithin w extendCode x x1 (28 * L + 30) :=
        (hx1.seq (ExecWithin.branch_pos hc_outer (ExecWithin.branch_neg hc_inner hnop))).mono
          (by omega)
      exact ⟨x1, hex_tot, by simpa only [extend, hgs, hgd] using hS1,
        he1, hs1, hd1, hcn1, hrem1, hidx1, fun a _ => by rw [hm1]⟩
  | none =>
    have hvis_s : x.mem (visBase g + e.src) = 0 := hS.vis_none e.src hs_lt hgs
    have hc_outer : ¬ (Cond.eq rTmp1 rOne).Holds x1 := by
      simp [Cond.holds_eq, ht1_1, hvis_s, hc1.one]
    cases hgd : S.get e.dst with
    | some h =>
      obtain ⟨hvis_d, htab_d⟩ := hS.vis_some e.dst hd_lt h hgd
      have hsd : e.src ≠ e.dst := by intro h0; rw [← h0, hgs] at hgd; nomatch hgd
      have hc_inner : (Cond.eq rTmp2 rOne).Holds x1 := by
        simp [Cond.holds_eq, ht2_1, hvis_d, hc1.one]
      have hstk_lt : S.stack.length < slots g := by
        have hmem := mem_unvisited (hS.len_table ▸ hs_lt) hgs
        have hpos : 0 < S.unvisited.card := Finset.card_pos.mpr ⟨e.src, hmem⟩
        have hpot : S.potential ≤ slots g := hS.pot_le
        unfold State.potential at hpot; omega
      have hcb_s := tabRow_hi_le_candBase (g := g) hs_lt
      have hcb_d := tabRow_hi_le_candBase (g := g) hd_lt
      obtain ⟨x2, hx2, hc2, he2', hs2', hd2', hsl2', hcl2', hcn2', hrem2', hidx2', hinv2, hfr2⟩ :=
        invLoops_spec (w := w) g x1 j hj hc1 (hm1 ▸ hS.inp) he1 hw
      simp only [← he_def] at hinv2
      have he2 := he2'.trans he1
      have hs2 := hs2'.trans hs1
      have hd2 := hd2'.trans hd1
      have hsl2 := hsl2'.trans hsl1
      have hcl2 := hcl2'.trans hcl1
      have hcn2 := hcn2'.trans hcn1
      have hrem2 := hrem2'.trans hrem1
      have hidx2 := hidx2'.trans hidx1
      obtain ⟨x3, hx3, hc3, ht2_3, ht3_3, hlab3, he3', hs3', hd3',
          hsl3', hcl3', hcn3', hrem3', hidx3', hm3⟩ :=
        extendPrep_spec (w := w) g rDst rSrc x2 e.dst e.src (Or.inr ⟨rfl, rfl⟩)
          hc2 hd_lt hs_lt hd2 hs2 hw
      have he3 := he3'.trans he2
      have hs3 := hs3'.trans hs2
      have hd3 := hd3'.trans hd2
      have hsl3 := hsl3'.trans hsl2
      have hcl3 := hcl3'.trans hcl2
      have hcn3 := hcn3'.trans hcn2
      have hrem3 := hrem3'.trans hrem2
      have hidx3 := hidx3'.trans hidx2
      obtain ⟨x4, hx4, hc4, he4, hs4, hd4, hsl4, hcl4, hcn4, hrem4, hidx4, hrow4, hfr4⟩ :=
        extendBwdLoop_spec (w := w) g x3 j hj h hc3 hs_lt hd_lt hsd ht2_3 ht3_3 hlab3
          (fun a ha => by
            simp only [← he_def]
            rw [hm3, hfr2 _ (by simp only [invBase] at *; omega), hm1]
            exact htab_d a ha)
          (fun b hb => by simp only [← he_def]; rw [hm3]; exact hinv2 b hb) hw
      simp only [← he_def] at hrow4 hfr4
      obtain ⟨y, hx5, hc5, he5', hs5', hd5', hsl5, hcl5', hcn5', hrem5', hidx5', hym⟩ :=
        extendPush_spec (w := w) g rSrc x4 e.src S.stack.length (Or.inl rfl)
          hc4 hs_lt hstk_lt (hs4.trans hs3) (hsl4.trans hsl3) hw
      have he5 := he5'.trans (he4.trans he3)
      have hs5 := hs5'.trans (hs4.trans hs3)
      have hd5 := hd5'.trans (hd4.trans hd3)
      have hcl5 := hcl5'.trans (hcl4.trans hcl3)
      have hcn5 := hcn5'.trans (hcn4.trans hcn3)
      have hrem5 := hrem5'.trans (hrem4.trans hrem3)
      have hidx5 := hidx5'.trans (hidx4.trans hidx3)
      have hstk_mem : HoldsList (stackBase g) (S.stack.reverse ++ [e.src]) y.mem := by
        have hbase : HoldsList (stackBase g) S.stack.reverse
            (Function.update x4.mem (visBase g + e.src) 1) :=
          hS.stack_mem.frame fun a ha1 ha2 => by
            rw [Function.update_of_ne
                (by simp only [stackBase, invBase, candBase, tabBase] at *; omega),
              hfr4 _ (by simp only [stackBase, invBase] at *; omega), hm3,
              hfr2 _ (by simp only [stackBase] at *; omega), hm1]
        simpa only [hym, List.length_reverse] using hbase.append_one e.src
      have hS' : StateAt g S x2 :=
        hS.frame_inv hc2 hsl2 hcl2 (fun a ha => by rw [hfr2 a ha, hm1])
      have hSy : StateAt g (push S e.src (preimage (List.finRange L) e.constraint ∘ h)) y :=
        hS'.push_slot hc5 hs_lt hgs
          (fun a ha => by
            rw [hym, Function.update_of_ne (by simp only [stackBase, invBase] at *; omega),
              Function.update_of_ne (by simp only [tabBase]; omega)]
            exact hrow4 a ha)
          (by rw [hym, Function.update_of_ne (by
                simp only [stackBase, invBase, candBase, tabBase] at *; omega),
              Function.update_self])
          hstk_mem hsl5 hcl5
          (fun a hnr hnv hns => by
            rw [hym, Function.update_of_ne hns, Function.update_of_ne hnv, hfr4 a hnr, hm3])
      have hex_tot : ExecWithin w extendCode x y (28 * L + 30) :=
        (hx1.seq (ExecWithin.branch_neg hc_outer
          (ExecWithin.branch_pos hc_inner (hx2.seq (hx3.seq (hx4.seq hx5)))))).mono (by omega)
      refine ⟨y, hex_tot, ?_, he5, hs5, hd5, hcn5, hrem5, hidx5, fun a ha => ?_⟩
      · simpa only [extend, hgs, hgd] using hSy
      · rw [hym, Function.update_of_ne (by
            simp only [stackBase, invBase, candBase, tabBase] at *; omega),
          Function.update_of_ne (by omega), hfr4 _ (by simp only [tabBase]; omega), hm3,
          hfr2 _ (by simp only [invBase, candBase, tabBase]; omega), hm1]
    | none =>
      have hvis_d : x.mem (visBase g + e.dst) = 0 := hS.vis_none e.dst hd_lt hgd
      have hc_inner : ¬ (Cond.eq rTmp2 rOne).Holds x1 := by
        simp [Cond.holds_eq, ht2_1, hvis_d, hc1.one]
      have hex_tot : ExecWithin w extendCode x x1 (28 * L + 30) :=
        (hx1.seq (ExecWithin.branch_neg hc_outer (ExecWithin.branch_neg hc_inner hnop))).mono
          (by omega)
      exact ⟨x1, hex_tot, by simpa only [extend, hgs, hgd] using hS1,
        he1, hs1, hd1, hcn1, hrem1, hidx1, fun a _ => by rw [hm1]⟩

end Cslib.Complexity.UniqueGames.Propagation
