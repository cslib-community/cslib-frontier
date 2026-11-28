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
# Component settlement (`settleCode`)

This internal module defines and certifies `settleCode`, which selects the first surviving
candidate guess in `[candBase g, candBase g + L)` (defaulting to `0`) and freezes the table row of
every slot recorded in `[compBase g, compBase g + S.comp.length)` to its constant forced label.

## Main definitions

* `Cslib.Complexity.UniqueGames.Propagation.freezePass`: per-slot instruction budget `5 * L + 22`
  charged during settlement.
* `Cslib.Complexity.UniqueGames.Propagation.settleCode`: Word-RAM component settlement subroutine.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.settleCode_spec`: `ExecWithin` specification matching
  `settle (List.finRange L) S` in `(11 * L + 10) + freezePass L * S.comp.length` instructions.
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded Cslib.WordRAM Cslib.WordRAM.Block Reg

/-- Per-slot instruction budget charged by `freezeCompBody` during `settleCode`. -/
abbrev freezePass (L : ℕ) : ℕ := 5 * L + 22

private def pickChosenBody : Code .standard 34 := ram[
  if rTmp3 = rZero then [
    rTmp1 ← rCandBase + rLabIdx;
    rTmp2 ← *rTmp1;
    if rTmp2 = rOne then [ rChosen ← rLabIdx; rTmp3 ← rOne ] else [ rLabIdx ← rLabIdx ]
  ] else [ rLabIdx ← rLabIdx ];
  rLabIdx ← rLabIdx + rOne ]

private def freezeSlotBody : Code .standard 34 := ram[
  rTmp4 ← rTmp2 + rLabIdx;
  *rTmp4 ← rTmp3;
  rLabIdx ← rLabIdx + rOne ]

private def freezeLoadV : Code .standard 34 := ram[
  rTmp1 ← rCompLen - rOne;
  rTmp1 ← rTmp1 - rRem;
  rTmp1 ← rCompBase + rTmp1;
  rSrc ← *rTmp1;
  rTmp1 ← rVisBase + rSrc;
  rTmp1 ← *rTmp1 ]

private def freezePrep : Code .standard 34 := ram[
  rTmp2 ← rSrc * rL;
  rTmp2 ← rTabBase + rTmp2;
  rTmp3 ← rTmp2 + rChosen;
  rTmp3 ← *rTmp3;
  rLabIdx ← rZero ]

private def freezeCompBody : Code .standard 34 := ram[
  ⟪freezeLoadV⟫;
  if rTmp1 = rOne then [
    ⟪freezePrep⟫;
    ⟪.loop (.lt rLabIdx rL) freezeSlotBody⟫
  ] else [ rRem ← rRem ];
  rRem ← rRem + rOne ]

private def settlePickInit : Code .standard 34 := ram[
  rChosen ← rZero;
  rTmp3 ← rZero;
  rLabIdx ← rZero ]

/-- Pick the first surviving candidate guess and freeze all slots of the current component. -/
def settleCode : Code .standard 34 := ram[
  ⟪settlePickInit⟫;
  ⟪.loop (.lt rLabIdx rL) pickChosenBody⟫;
  rRem ← rZero;
  ⟪.loop (.lt rRem rCompLen) freezeCompBody⟫;
  rCompLen ← rZero ]

private theorem execWithin_inc_rRem {L w : ℕ} {g : Graph (Fin L → Fin L)} {z : Data 34}
    (hw : Fits w (z.regs rRem + 1)) (hC : ConstRegs g z) :
    ∃ z', ExecWithin w (ram[ rRem ← rRem + rOne ] : Code .standard 34) z z' 1 ∧
      ConstRegs g z' ∧ z'.regs rChosen = z.regs rChosen ∧ z'.regs rRem = z.regs rRem + 1 ∧
      z'.regs rCompLen = z.regs rCompLen ∧ z'.regs rOuterIdx = z.regs rOuterIdx ∧
      z'.mem = z.mem := by
  wram_exec [hC.one]
  and_intros <;> wram_simp [hC]

/-- Specification for `settleCode`. -/
theorem settleCode_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L))
    (S : State (Fin L)) (x : Data 34) (hS : StateAt g S x) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w settleCode x y ((11 * L + 10) + freezePass L * S.comp.length) ∧
      TableStateAt g (settle (List.finRange L) S) y ∧
      y.regs rOuterIdx = x.regs rOuterIdx := by
  obtain ⟨x1, hx1, hc1, hch1, ht3_1, hlab1, hcl1, hidx1, hm1⟩ :
      ∃ x1, ExecWithin w settlePickInit x x1 3 ∧
        ConstRegs g x1 ∧ x1.regs rChosen = 0 ∧ x1.regs rTmp3 = 0 ∧ x1.regs rLabIdx = 0 ∧
        x1.regs rCompLen = S.comp.length ∧ x1.regs rOuterIdx = x.regs rOuterIdx ∧
        x1.mem = x.mem := by
    wram_exec [settlePickInit, hS.consts.zero]
    and_intros <;> wram_simp [hS.consts, hS.comp_len]
  let optAt (k : ℕ) : Option (Fin L) := ((List.finRange L).take k).find? S.cand
  let Ppick (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ z.regs rCompLen = S.comp.length ∧ z.regs rOuterIdx = x.regs rOuterIdx ∧
    z.mem = x.mem ∧
    match optAt k with
    | none => z.regs rTmp3 = 0 ∧ z.regs rChosen = 0
    | some c => z.regs rTmp3 = 1 ∧ z.regs rChosen = c.val
  obtain ⟨x2, hx2, ⟨hc2, hcl2, hidx2, hm2, hopt2⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := pickChosenBody)
      (N := L) (T := 9) Ppick
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzCL, hzIdx, hzMem, hzOpt⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have htake_succ : (List.finRange L).take (k + 1) =
            (List.finRange L).take k ++ [⟨k, hk⟩] := by
          simp [List.take_succ_eq_append_getElem, hk]
        have : Fits w (candBase g + k) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        cases hok : optAt k with
        | some c =>
          rw [hok] at hzOpt
          have hnext : optAt (k + 1) = some c := by
            dsimp only [optAt] at hok ⊢
            simp only [htake_succ, List.find?_append, hok, Option.some_or]
          wram_exec [pickChosenBody, hzC.zero, hzC.one, hk_reg, hzOpt.1]
          simp only [Ppick, hnext]
          and_intros <;> wram_simp [hzC, hzCL, hzIdx, hzMem, hzOpt.1, hzOpt.2]
        | none =>
          rw [hok] at hzOpt
          have hck_mem : z.mem (candBase g + k) = (S.cand ⟨k, hk⟩).toNat := by
            rw [hzMem]; exact hS.cand_mem k hk
          have hnext : optAt (k + 1) = if S.cand ⟨k, hk⟩ then some ⟨k, hk⟩ else none := by
            dsimp only [optAt] at hok ⊢
            simp only [htake_succ, List.find?_append, hok, Option.none_or,
              List.find?_cons, List.find?_nil]
            cases S.cand ⟨k, hk⟩ <;> rfl
          cases hck : S.cand ⟨k, hk⟩ <;>
          · simp only [hck, Bool.toNat_true, Bool.toNat_false, ite_true,
              Bool.false_eq_true, ite_false] at hck_mem hnext
            wram_exec [pickChosenBody, hzC.zero, hzC.one, hzC.candB, hk_reg, hzOpt.1, hck_mem]
            simp only [Ppick, hnext]
            and_intros <;> wram_simp [hzC, hzCL, hzIdx, hzMem, hzOpt.1, hzOpt.2])
      (by rw [hlab1]; exact Nat.zero_le _)
      (by rw [hlab1]; refine ⟨hc1, hcl1, hidx1, hm1, ?_⟩
          simp only [optAt, List.take_zero, List.find?_nil, ht3_1, hch1, and_self])
  rw [hlab1, Nat.sub_zero] at hx2
  set chosen : Fin L := ((List.finRange L).find? S.cand).getD default
  have hchosen_reg : x2.regs rChosen = chosen.val := by
    simp only [optAt, List.take_of_length_le List.length_finRange.le] at hopt2
    cases hfind : (List.finRange L).find? S.cand <;>
    · rw [hfind] at hopt2
      simp only [chosen, hfind, Option.getD_none, Option.getD_some]
      exact hopt2.2
  obtain ⟨x3, hx3, hT3, hch3, hrem3, hcl3, hidx3, hcm3⟩ :
      ∃ x3, ExecWithin w (ram[ rRem ← rZero ] : Code .standard 34) x2 x3 1 ∧
        TableStateAt g S x3 ∧ x3.regs rChosen = chosen.val ∧ x3.regs rRem = 0 ∧
        x3.regs rCompLen = S.comp.length ∧ x3.regs rOuterIdx = x.regs rOuterIdx ∧
        HoldsList (compBase g) S.comp.reverse x3.mem := by
    wram_exec [hc2.zero]
    exact ⟨hS.toTableStateAt.of_eq (by wram_simp [hc2]) (by wram_simp [hm2]),
      by wram_simp [hchosen_reg], by wram_simp, by wram_simp [hcl2], by wram_simp [hidx2],
      by simp only [Data.set_mem, hm2]; exact hS.comp_mem⟩
  let tabAt (k : ℕ) := (S.comp.take k).foldl
    (fun t v => t.set v (freeze chosen (t.getD v none))) S.table
  let Pfrz (k : ℕ) (z : Data 34) : Prop :=
    TableStateAt g { S with table := tabAt k } z ∧
    z.regs rChosen = chosen.val ∧ z.regs rCompLen = S.comp.length ∧
    z.regs rOuterIdx = x.regs rOuterIdx ∧
    HoldsList (compBase g) S.comp.reverse z.mem
  obtain ⟨x4, hx4, ⟨hT4, _, _, hidx4, _⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rRem) (limit := rCompLen) (body := freezeCompBody)
      (N := S.comp.length) (T := 5 * L + 20) Pfrz
      (fun z hz => hz.2.2.1)
      (fun z hz hk => by
        obtain ⟨hzT, hzCh, hzCL, hzIdx, hzCM⟩ := hz
        set k := z.regs rRem
        have hk_reg : z.regs rRem = k := rfl
        set v := S.comp[k]
        have hv_lt : v < slots g := hS.comp_lt v (List.getElem_mem hk)
        have hv_cb := tabRow_hi_le_candBase (g := g) hv_lt
        have hcomp_le := hS.comp_le
        have hrev_get : z.mem (compBase g + (S.comp.length - 1 - k)) = v := by
          have hg := hzCM.get (S.comp.length - 1 - k) (by rw [List.length_reverse]; omega)
          have hk_sub : S.comp.length - 1 - (S.comp.length - 1 - k) = k := by omega
          rw [List.getElem_reverse] at hg
          simpa only [hk_sub] using hg
        have htab_next : tabAt (k + 1) =
            (tabAt k).set v (freeze chosen ((tabAt k).getD v none)) := by
          simp only [tabAt]
          rw [List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons,
            List.foldl_nil]
        have : Fits w (compBase g + (S.comp.length - 1 - k)) := fits_top hw (by wram_omega)
        have : Fits w (visBase g + v) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        obtain ⟨z1, hz1_ex, hz1C, hz1S, hz1T1, hz1Ch, hz1Rem, hz1CL, hz1Idx, hz1m⟩ :
            ∃ z1, ExecWithin w freezeLoadV z z1 6 ∧
              ConstRegs g z1 ∧ z1.regs rSrc = v ∧ z1.regs rTmp1 = z.mem (visBase g + v) ∧
              z1.regs rChosen = chosen.val ∧ z1.regs rRem = k ∧
              z1.regs rCompLen = S.comp.length ∧ z1.regs rOuterIdx = x.regs rOuterIdx ∧
              z1.mem = z.mem := by
          wram_exec [freezeLoadV,
            hzT.consts.one, hzT.consts.compB, hzT.consts.visB, hzCL, hk_reg, hrev_get]
          and_intros <;> wram_simp [hzT.consts, hzCh, hk_reg, hzCL, hzIdx]
        cases hgv : ({ S with table := tabAt k } : State (Fin L)).get v with
        | none =>
          have hvis0 : z.mem (visBase g + v) = 0 := hzT.vis_none v hv_lt hgv
          have hc_br : ¬ (Cond.eq rTmp1 rOne).Holds z1 := by
            simp only [Cond.holds_eq, hz1T1, hvis0, hz1C.one, Nat.zero_ne_one, not_false_eq_true]
          obtain ⟨z2, hz2_ex, hz2C, hz2Ch, hz2Rem, hz2CL, hz2Idx, hz2m⟩ :=
            execWithin_inc_rRem (g := g) (z := z1) (by rwa [hz1Rem]) hz1C
          have hz2m' : z2.mem = z.mem := hz2m.trans hz1m
          have hsame_tab : tabAt (k + 1) = tabAt k := by
            have hgv' : (tabAt k).getD v none = none := hgv
            simp only [htab_next, hgv', freeze, Option.map_none]
            refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
            rw [List.getElem_set]
            split_ifs with hiv
            · subst hiv
              simpa [List.getD_eq_getElem?_getD, hi2] using hgv'.symm
            · rfl
          exact ⟨z2, (hz1_ex.seq ((ExecWithin.branch_neg hc_br
              ⟨1, le_rfl, exec_nop rRem z1⟩).seq hz2_ex)).mono (by omega),
            ⟨hsame_tab ▸ hzT.of_eq hz2C hz2m', hz1Ch ▸ hz2Ch, hz1CL ▸ hz2CL, hz1Idx ▸ hz2Idx,
              hz2m' ▸ hzCM⟩, hz1Rem ▸ hz2Rem⟩
        | some fn =>
          obtain ⟨hvis1, htab_fn⟩ := hzT.vis_some v hv_lt fn hgv
          have hc_br : (Cond.eq rTmp1 rOne).Holds z1 := by
            simp only [Cond.holds_eq, hz1T1, hvis1, hz1C.one]
          have : Fits w (v * L) := fits_top hw (by wram_omega)
          have : Fits w (tabBase g + v * L) := fits_top hw (by wram_omega)
          have : Fits w (tabBase g + v * L + chosen.val) :=
            fits_top hw (by have := chosen.isLt; wram_omega)
          obtain ⟨z2, hz2_ex, hz2C, hz2T2, hz2T3, hz2Lab, hz2Ch, hz2Rem, hz2CL, hz2Idx, hz2m⟩ :
              ∃ z2, ExecWithin w freezePrep z1 z2 5 ∧
                ConstRegs g z2 ∧ z2.regs rTmp2 = tabBase g + v * L ∧
                z2.regs rTmp3 = (fn chosen).val ∧ z2.regs rLabIdx = 0 ∧
                z2.regs rChosen = chosen.val ∧ z2.regs rRem = k ∧
                z2.regs rCompLen = S.comp.length ∧ z2.regs rOuterIdx = x.regs rOuterIdx ∧
                z2.mem = z.mem := by
            have hfc_mem : z1.mem (tabBase g + v * L + chosen.val) = (fn chosen).val := by
              rw [hz1m]; simpa only [Fin.eta] using htab_fn chosen.val chosen.isLt
            wram_exec [freezePrep, hz1C.zero, hz1C.regL, hz1C.tabB, hz1S, hz1Ch, hfc_mem]
            and_intros <;> wram_simp [hz1C, hz1Ch, hz1Rem, hz1CL, hz1Idx, hz1m]
          let Pslot (a : ℕ) (w0 : Data 34) : Prop :=
            ConstRegs g w0 ∧ w0.regs rTmp2 = tabBase g + v * L ∧
            w0.regs rTmp3 = (fn chosen).val ∧ w0.regs rChosen = chosen.val ∧
            w0.regs rRem = k ∧ w0.regs rCompLen = S.comp.length ∧
            w0.regs rOuterIdx = x.regs rOuterIdx ∧
            (∀ i < a, w0.mem (tabBase g + v * L + i) = (fn chosen).val) ∧
            ∀ addr, ¬ (tabBase g + v * L ≤ addr ∧ addr < tabBase g + v * L + a) →
              w0.mem addr = z.mem addr
          obtain ⟨z3, hz3_ex, ⟨hz3C, _, _, hz3Ch, hz3Rem, hz3CL, hz3Idx, hz3Row, hz3Fr⟩, _⟩ :=
            ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL)
              (body := freezeSlotBody) (N := L) (T := 3) Pslot
              (fun w0 hw0 => hw0.1.regL)
              (fun w0 hw0 ha => by
                obtain ⟨hwC, hwT2, hwT3, hwCh, hwRem, hwCL, hwIdx, hwRow, hwFr⟩ := hw0
                set a := w0.regs rLabIdx
                have ha_reg : w0.regs rLabIdx = a := rfl
                have : Fits w (tabBase g + v * L + a) := fits_top hw (by wram_omega)
                have : Fits w (a + 1) := fits_top hw (by wram_omega)
                have hpws := prefix_write_step (e := fun _ => (fn chosen).val) hwRow hwFr
                  (rfl : Function.update w0.mem (tabBase g + v * L + a) (fn chosen).val = _)
                wram_exec [freezeSlotBody, hwC.one, hwT2, hwT3, ha_reg]
                simp only [Pslot, Data.write_mem, Data.set_mem]
                and_intros <;> first
                  | wram_simp [hwC, hwT2, hwT3, hwCh, hwRem, hwCL, hwIdx]
                  | exact hpws.1
                  | exact hpws.2)
              (by rw [hz2Lab]; exact Nat.zero_le _)
              (by rw [hz2Lab]; exact ⟨hz2C, hz2T2, hz2T3, hz2Ch, hz2Rem, hz2CL, hz2Idx,
                fun _ h => by omega, fun addr _ => congrFun hz2m addr⟩)
          rw [hz2Lab, Nat.sub_zero] at hz3_ex
          obtain ⟨z4, hz4_ex, hz4C, hz4Ch, hz4Rem, hz4CL, hz4Idx, hz4m⟩ :=
            execWithin_inc_rRem (g := g) (z := z3) (by rwa [hz3Rem]) hz3C
          have hfr_low : ∀ a < tabBase g, z4.mem a = z.mem a := fun a ha => by
            rw [hz4m]; exact hz3Fr a (by omega)
          refine ⟨z4, (hz1_ex.seq ((ExecWithin.branch_pos hc_br (hz2_ex.seq hz3_ex)).seq
              hz4_ex)).mono (by omega),
            ⟨?_, hz3Ch ▸ hz4Ch, hz3CL ▸ hz4CL, hz3Idx ▸ hz4Idx,
              hzCM.frame fun a ha1 _ => (congrFun hz4m a).trans (hz3Fr a (by wram_omega))⟩,
            hz3Rem ▸ hz4Rem⟩
          have hlen_k : (tabAt k).length = slots g := hzT.len_table
          have hgv' : (tabAt k).getD v none = some fn := hgv
          refine ⟨hz4C, hzT.inp.frame (fun a ha => hfr_low a (by wram_omega)),
            hzT.bkt.frame (fun a ha => hfr_low a (by wram_omega)),
            by rw [htab_next, List.length_set, hlen_k],
            fun u hu hun => ?_, fun u hu fn' huf => ?_⟩
          · rw [hfr_low _ (by wram_omega)]
            dsimp only [State.get] at hun
            have huv : u ≠ v := fun h => by
              rw [h, htab_next, List.getD_set_self (hlen_k ▸ hv_lt), hgv'] at hun
              nomatch hun
            rw [htab_next, List.getD_set_ne (Ne.symm huv)] at hun
            exact hzT.vis_none u hu hun
          · dsimp only [State.get] at huf
            by_cases huv : u = v
            · subst huv
              rw [htab_next, List.getD_set_self (hlen_k ▸ hv_lt), hgv'] at huf
              simp only [freeze, Option.map_some, Option.some.injEq] at huf
              subst huf
              exact ⟨by rw [hfr_low _ (by wram_omega)]; exact hvis1,
                fun a ha => by rw [hz4m]; exact hz3Row a ha⟩
            · rw [htab_next, List.getD_set_ne (Ne.symm huv)] at huf
              obtain ⟨hu1, hutab⟩ := hzT.vis_some u hu fn' huf
              exact ⟨by rw [hfr_low _ (by wram_omega)]; exact hu1,
                fun a ha => by rw [hz4m, hz3Fr _ (not_in_tabRow huv ha)]; exact hutab a ha⟩)
      (by rw [hrem3]; exact Nat.zero_le _)
      (by rw [hrem3]; exact ⟨hT3, hch3, hcl3, hidx3, hcm3⟩)
  rw [hrem3, Nat.sub_zero] at hx4
  obtain ⟨y, hx5, hc5, hidx5, hm5⟩ :
      ∃ y, ExecWithin w (ram[ rCompLen ← rZero ] : Code .standard 34) x4 y 1 ∧
        ConstRegs g y ∧ y.regs rOuterIdx = x.regs rOuterIdx ∧ y.mem = x4.mem := by
    wram_exec [hT4.consts.zero]
    exact ⟨by wram_simp [hT4.consts], by wram_simp [hidx4], by wram_simp⟩
  have htab_end : tabAt S.comp.length = (settle (List.finRange L) S).table := by
    simp only [tabAt, settle, chosen, List.take_length]
  have hmul_frz : S.comp.length * (5 * L + 20 + 2) = freezePass L * S.comp.length :=
    Nat.mul_comm S.comp.length (freezePass L)
  refine ⟨y, (hx1.seq (hx2.seq (hx3.seq (hx4.seq hx5)))).mono (by omega),
    ⟨hc5, hm5 ▸ hT4.inp, hm5 ▸ hT4.bkt, htab_end ▸ hT4.len_table,
      fun v hv hvn => ?_, fun v hv fn hvf => ?_⟩, hidx5⟩
  · rw [hm5]; exact hT4.vis_none v hv (by simpa only [State.get, htab_end] using hvn)
  · rw [hm5]; exact hT4.vis_some v hv fn (by simpa only [State.get, htab_end] using hvf)

end Cslib.Complexity.UniqueGames.Propagation
