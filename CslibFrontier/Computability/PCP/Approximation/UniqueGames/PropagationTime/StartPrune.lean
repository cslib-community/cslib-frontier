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
import Mathlib.Data.List.GetD

/-!
# Seed initialization (`startCode`) and candidate pruning (`pruneCode`)

This internal module defines and certifies `startCode` (initializing an unvisited seed's identity
row, candidate array, visited flag, and singleton stack) and `pruneCode` (zeroing candidate bits
that violate an edge whose endpoints are both visited).

## Main definitions

* `Cslib.Complexity.UniqueGames.Propagation.startCode`: Word-RAM component seed initialization.
* `Cslib.Complexity.UniqueGames.Propagation.pruneCode`: Word-RAM candidate-pruning pass on a
  both-visited edge.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.startCode_spec`: `ExecWithin` specification matching
  `start S s` in `7 * L + 12` instructions.
* `Cslib.Complexity.UniqueGames.Propagation.pruneCode_spec`: `ExecWithin` specification matching
  `prune S g.edges[j]` in `16 * L + 16` instructions.
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded Cslib.WordRAM Cslib.WordRAM.Block Reg

private def startBody : Code .standard 34 := ram[
  rTmp1 ← rTmp2 + rLabIdx;
  *rTmp1 ← rLabIdx;
  rTmp1 ← rCandBase + rLabIdx;
  *rTmp1 ← rOne;
  rLabIdx ← rLabIdx + rOne ]

private def startPre : Code .standard 34 := ram[
  rTmp2 ← rSrc * rL;
  rTmp2 ← rTabBase + rTmp2;
  rLabIdx ← rZero ]

private def startPost : Code .standard 34 := ram[
  rTmp1 ← rVisBase + rSrc;
  *rTmp1 ← rOne;
  *rStackBase ← rSrc;
  rStackLen ← rOne;
  rCompLen ← rZero ]

/-- Initialize seed `rSrc`: identity table row, all-1 candidate array, `vis = 1`, singleton
stack. -/
def startCode : Code .standard 34 := ram[
  ⟪startPre⟫;
  ⟪.loop (.lt rLabIdx rL) startBody⟫;
  ⟪startPost⟫ ]

private def pruneBody : Code .standard 34 := ram[
  rTmp1 ← rCandBase + rLabIdx;
  rTmp4 ← *rTmp1;
  if rTmp4 = rOne then [
    rTmp4 ← rTmp2 + rLabIdx;
    rTmp4 ← *rTmp4;
    rTmp4 ← rTmp4 + rTwo;
    rTmp4 ← rEdgeIdx + rTmp4;
    rTmp4 ← *rTmp4;
    rTmp5 ← rTmp3 + rLabIdx;
    rTmp5 ← *rTmp5;
    if rTmp4 = rTmp5 then [ rLabIdx ← rLabIdx ] else [ *rTmp1 ← rZero ]
  ] else [ rLabIdx ← rLabIdx ];
  rLabIdx ← rLabIdx + rOne ]

/-- Prune surviving candidate guesses that violate the current edge when both endpoints are
visited. -/
def pruneCode : Code .standard 34 := ram[
  ⟪edgeVisLoad⟫;
  if rTmp1 = rOne then [
    if rTmp2 = rOne then [
      ⟪extendPrep rSrc rDst⟫;
      ⟪.loop (.lt rLabIdx rL) pruneBody⟫
    ] else [ rLabIdx ← rLabIdx ]
  ] else [ rLabIdx ← rLabIdx ] ]

/-- Specification for `startCode`. -/
theorem startCode_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) (s : ℕ) (hT : TableStateAt g S x) (hs_reg : x.regs rSrc = s)
    (hs : s < slots g) (hnone : S.get s = none) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w startCode x y (7 * L + 12) ∧
      StateAt g (start S s) y ∧ y.regs rOuterIdx = x.regs rOuterIdx := by
  have hcb := tabRow_hi_le_candBase (g := g) hs
  have : Fits w (s * L) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + s * L) := fits_top hw (by wram_omega)
  obtain ⟨x1, hx1, hc1, hs1, htmp1, hlab1, hidx1, hm1⟩ :
      ∃ x1, ExecWithin w startPre x x1 3 ∧
        ConstRegs g x1 ∧ x1.regs rSrc = s ∧ x1.regs rTmp2 = tabBase g + s * L ∧
        x1.regs rLabIdx = 0 ∧ x1.regs rOuterIdx = x.regs rOuterIdx ∧ x1.mem = x.mem := by
    unfold startPre
    wram_exec [hT.consts.zero, hT.consts.regL, hT.consts.tabB, hs_reg]
    exact ⟨by wram_simp [hT.consts], by wram_simp [hs_reg], by wram_simp, by wram_simp,
      by wram_simp, by wram_simp⟩
  let P (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ z.regs rSrc = s ∧ z.regs rTmp2 = tabBase g + s * L ∧
    z.regs rOuterIdx = x.regs rOuterIdx ∧
    (∀ a < k, z.mem (tabBase g + s * L + a) = a) ∧
    (∀ a < k, z.mem (candBase g + a) = 1) ∧
    ∀ addr, ¬ (tabBase g + s * L ≤ addr ∧ addr < tabBase g + s * L + k) →
      ¬ (candBase g ≤ addr ∧ addr < candBase g + k) → z.mem addr = x.mem addr
  obtain ⟨x2, hx2, ⟨hc2, hs2, _, hidx2, htab2, hcand2, hfr2⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := startBody)
      (N := L) (T := 5) P (fun _ hz => hz.1.regL)
      (fun z ⟨hzC, hzS, hzT2, hzIdx, hzTab, hzCand, hzFr⟩ hk => by
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have : Fits w (tabBase g + s * L + k) := fits_top hw (by wram_omega)
        have : Fits w (candBase g + k) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        unfold startBody
        wram_exec [hzC.one, hzC.candB, hzT2, hk_reg]
        refine ⟨⟨by wram_simp [hzC], by wram_simp [hzS], by wram_simp [hzT2],
          by wram_simp [hzIdx], ?_, ?_, ?_⟩, by wram_simp⟩
        · intro a ha
          simp only [Data.write_mem, Data.set_mem,
            Function.update_of_ne (by omega : tabBase g + s * L + a ≠ candBase g + k)]
          by_cases hak : a = k
          · subst hak; exact Function.update_self _ _ _
          · rw [Function.update_of_ne (by omega)]
            exact hzTab a (by omega)
        · intro a ha
          simp only [Data.write_mem, Data.set_mem]
          by_cases hak : a = k
          · subst hak; exact Function.update_self _ _ _
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hzCand a (by omega)
        · intro addr h1 h2
          simp only [Data.write_mem, Data.set_mem,
            Function.update_of_ne (by omega : addr ≠ candBase g + k),
            Function.update_of_ne (by omega : addr ≠ tabBase g + s * L + k)]
          exact hzFr addr (by omega) (by omega))
      (hlab1.symm ▸ Nat.zero_le L)
      (hlab1.symm ▸ ⟨hc1, hs1, htmp1, hidx1, fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ h => absurd h (Nat.not_lt_zero _), fun addr _ _ => congrFun hm1 addr⟩)
  rw [hlab1, Nat.sub_zero] at hx2
  have : Fits w (visBase g + s) := fits_top hw (by wram_omega)
  obtain ⟨y, hx3, hc3, hstk3, hcmp3, hidx3, hym⟩ :
      ∃ y, ExecWithin w startPost x2 y 5 ∧
        ConstRegs g y ∧ y.regs rStackLen = 1 ∧ y.regs rCompLen = 0 ∧
        y.regs rOuterIdx = x.regs rOuterIdx ∧
        y.mem = Function.update (Function.update x2.mem (visBase g + s) 1) (stackBase g) s := by
    unfold startPost
    wram_exec [hc2.zero, hc2.one, hc2.visB, hc2.stackB, hs2]
    exact ⟨by wram_simp [hc2], by wram_simp, by wram_simp, by wram_simp [hidx2], by wram_simp⟩
  have hfr_low : ∀ a < visBase g, y.mem a = x.mem a := fun a ha => by
    rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by omega)]
    exact hfr2 a (by wram_omega) (by wram_omega)
  refine ⟨y, (hx1.seq (hx2.seq hx3)).mono (by omega), ?_, hidx3⟩
  refine ⟨⟨hc3, hT.inp.frame (fun a ha => hfr_low a (by wram_omega)),
      hT.bkt.frame hfr_low, by simp only [start, List.length_set, hT.len_table], fun v hv hvn => ?_,
      fun v hv fn hvf => ?_⟩,
    potential_start hT.len_table (hT.len_table ▸ hs),
    fun a ha => by
      rw [hym, Function.update_of_ne (by wram_omega),
        Function.update_of_ne (by wram_omega)]
      exact hcand2 a ha,
    hstk3, fun u hu => (List.mem_singleton.mp hu) ▸ hs,
    by simp only [start, List.reverse_singleton, holdsList_cons_iff, holdsList_nil, and_true, hym,
      Function.update_self],
    hcmp3, Nat.zero_le _, fun _ h => by simp only [start, List.not_mem_nil] at h, holdsList_nil _ _⟩
  · have hvs : v ≠ s := fun heq =>
      nomatch (heq ▸ hvn).symm.trans (List.getD_set_self (hT.len_table ▸ hs))
    rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by omega),
      hfr2 _ (by wram_omega) (by wram_omega)]
    exact hT.vis_none v hv
      (by rwa [show (start S s).get v = S.get v from List.getD_set_ne hvs.symm] at hvn)
  · by_cases hvs : v = s
    · subst hvs
      rw [show (start S v).get v = some id from List.getD_set_self (hT.len_table ▸ hs)] at hvf
      cases hvf
      exact ⟨by rw [hym, Function.update_of_ne (by wram_omega), Function.update_self],
        fun a ha => by
          rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by wram_omega)]
          exact htab2 a ha⟩
    · obtain ⟨hv1, hvtab⟩ := hT.vis_some v hv fn
        (by rwa [show (start S s).get v = S.get v from List.getD_set_ne (Ne.symm hvs)] at hvf)
      have hv_cb := tabRow_hi_le_candBase (g := g) hv
      exact ⟨by
          rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by omega),
            hfr2 _ (by wram_omega) (by wram_omega)]
          exact hv1,
        fun a ha => by
          rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by wram_omega),
            hfr2 _ (not_in_tabRow hvs ha) (by omega)]
          exact hvtab a ha⟩

/-- Specification for `pruneCode`. -/
theorem pruneCode_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) (j : ℕ) (hj : j < g.edges.length)
    (hS : StateAt g S x)
    (heptr : x.regs rEdgeIdx = 4 + j * (L + 2))
    (hsrc_reg : x.regs rSrc = g.edges[j].src)
    (hdst_reg : x.regs rDst = g.edges[j].dst)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w pruneCode x y (16 * L + 16) ∧
      StateAt g (prune S g.edges[j]) y ∧
      y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      ∀ a < visBase g, y.mem a = x.mem a := by
  set e := g.edges[j] with he_def
  have hs_lt : e.src < slots g := src_lt_slots (List.getElem_mem hj)
  have hd_lt : e.dst < slots g := dst_lt_slots (List.getElem_mem hj)
  have hed := edge_end_le_headBase hj
  obtain ⟨x1, hx1, hc1, ht1_1, ht2_1, hr1, hm1⟩ :=
    edgeVisLoad_spec (w := w) g S x j hj hS hsrc_reg hdst_reg hw
  have hnop : ExecWithin w (.op (.copy rLabIdx rLabIdx)) x1 x1 1 :=
    ⟨1, le_rfl, exec_nop rLabIdx x1⟩
  have hS1 : StateAt g S x1 :=
    hS.of_eq hc1 (hr1.stackLen.trans hS.stack_len) (hr1.compLen.trans hS.comp_len) hm1
  have retSame (hpr : prune S e = S) (hex : ExecWithin w pruneCode x x1 (16 * L + 16)) :
      ∃ y, ExecWithin w pruneCode x y (16 * L + 16) ∧
        StateAt g (prune S e) y ∧
        y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
        y.regs rOuterIdx = x.regs rOuterIdx ∧
        ∀ a < visBase g, y.mem a = x.mem a :=
    ⟨x1, hex, hpr.symm ▸ hS1, hr1.curNode, hr1.rem, hr1.outerIdx, fun a _ => by rw [hm1]⟩
  cases hgs : S.get e.src with
  | none =>
    exact retSame (by simp only [prune, hgs])
      ((hx1.seq (ExecWithin.branch_neg (by
        simp only [Cond.holds_eq, ht1_1, ← he_def, hS.vis_none e.src hs_lt hgs, hc1.one,
          Nat.zero_ne_one, not_false_eq_true]) hnop)).mono (by omega))
  | some f =>
    obtain ⟨hvis_s, htab_s⟩ := hS.vis_some e.src hs_lt f hgs
    have hc_outer : (Cond.eq rTmp1 rOne).Holds x1 := by
      simp only [Cond.holds_eq, ht1_1, ← he_def, hvis_s, hc1.one]
    cases hgd : S.get e.dst with
    | none =>
      exact retSame (by simp only [prune, hgs, hgd])
        ((hx1.seq (ExecWithin.branch_pos hc_outer (ExecWithin.branch_neg (by
          simp only [Cond.holds_eq, ht2_1, ← he_def, hS.vis_none e.dst hd_lt hgd, hc1.one,
            Nat.zero_ne_one, not_false_eq_true]) hnop))).mono (by omega))
    | some h =>
      obtain ⟨hvis_d, htab_d⟩ := hS.vis_some e.dst hd_lt h hgd
      have hc_inner : (Cond.eq rTmp2 rOne).Holds x1 := by
        simp only [Cond.holds_eq, ht2_1, ← he_def, hvis_d, hc1.one]
      have hcb_s := tabRow_hi_le_candBase (g := g) hs_lt
      have hcb_d := tabRow_hi_le_candBase (g := g) hd_lt
      obtain ⟨x2, hx2, hc2, ht2_2, ht3_2, hlab2, hr2', hm2'⟩ :=
        extendPrep_spec (w := w) g rSrc rDst x1 e.src e.dst (Or.inl ⟨rfl, rfl⟩)
          hc1 hs_lt hd_lt (hr1.src.trans hsrc_reg) (hr1.dst.trans hdst_reg) hw
      let cVal (a : ℕ) : ℕ :=
        if ha : a < L then
          (S.cand ⟨a, ha⟩ && decide (e.constraint (f ⟨a, ha⟩) = h ⟨a, ha⟩)).toNat
        else 0
      let P (k : ℕ) (z : Data 34) : Prop :=
        ConstRegs g z ∧ z.regs rTmp2 = tabBase g + e.src * L ∧
        z.regs rTmp3 = tabBase g + e.dst * L ∧ Phase3Regs x z ∧
        (∀ a < k, z.mem (candBase g + a) = cVal a) ∧
        ∀ addr, ¬ (candBase g ≤ addr ∧ addr < candBase g + k) → z.mem addr = x.mem addr
      obtain ⟨y, hx3, ⟨hyC, _, _, hyR, hyCand, hyFr⟩, _⟩ :=
        ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := pruneBody)
          (N := L) (T := 14) P (fun _ hz => hz.1.regL)
          (fun z ⟨hzC, hzT2, hzT3, hzR, hzCand, hzFr⟩ hk => by
            set k := z.regs rLabIdx
            have hk_reg : z.regs rLabIdx = k := rfl
            have hzE : z.regs rEdgeIdx = 4 + j * (L + 2) := hzR.edgeIdx.trans heptr
            have hck_mem : z.mem (candBase g + k) = (S.cand ⟨k, hk⟩).toNat := by
              rw [hzFr _ (by omega)]; exact hS.cand_mem k hk
            have : Fits w (candBase g + k) := fits_top hw (by wram_omega)
            have : Fits w (k + 1) := fits_top hw (by wram_omega)
            have hkeep (heq_c : z.mem (candBase g + k) = cVal k) :
                (∀ a < k + 1, z.mem (candBase g + a) = cVal a) ∧
                (∀ addr, ¬ (candBase g ≤ addr ∧ addr < candBase g + (k + 1)) →
                  z.mem addr = x.mem addr) :=
              ⟨fun a ha => if hak : a = k then hak ▸ heq_c else hzCand a (by omega),
               fun addr haddr => hzFr addr (by omega)⟩
            cases hck : S.cand ⟨k, hk⟩ with
            | false =>
              have hck0 : (S.cand ⟨k, hk⟩).toNat = 0 := by simp only [hck, Bool.toNat_false]
              have hk' := hkeep (by
                rw [hck_mem, hck0]
                simp only [cVal, hk, ↓reduceDIte, hck, Bool.false_and,
                  Bool.toNat_false])
              unfold pruneBody
              wram_exec [hzC.one, hzC.candB, hk_reg, hck_mem, hck0]
              refine ⟨⟨?_, ?_, ?_, ?_,
                  by simpa only [Data.set_mem] using hk'.1,
                  by simpa only [Data.set_mem] using hk'.2⟩, ?_⟩
              all_goals wram_simp [hzC, hzT2, hzT3, hzR]
            | true =>
              have hck1 : (S.cand ⟨k, hk⟩).toNat = 1 := by simp only [hck, Bool.toNat_true]
              have hfk_lt := (f ⟨k, hk⟩).isLt
              have hfa : z.mem (tabBase g + e.src * L + k) = (f ⟨k, hk⟩).val := by
                rw [hzFr _ (by omega)]; exact htab_s k hk
              have hha : z.mem (tabBase g + e.dst * L + k) = (h ⟨k, hk⟩).val := by
                rw [hzFr _ (by omega)]; exact htab_d k hk
              have hcfa : z.mem (4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2)) =
                  (e.constraint (f ⟨k, hk⟩)).val := by
                rw [hzFr _ (by wram_omega),
                  show 4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2) =
                    4 + j * (L + 2) + 2 + (f ⟨k, hk⟩).val by omega]
                exact hS.inp.edge_val j hj (f ⟨k, hk⟩).val hfk_lt
              have : Fits w (tabBase g + e.src * L + k) := fits_top hw (by wram_omega)
              have : Fits w (tabBase g + e.dst * L + k) := fits_top hw (by wram_omega)
              have : Fits w ((f ⟨k, hk⟩).val + 2) := fits_top hw (by wram_omega)
              have : Fits w (4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2)) :=
                fits_top hw (by wram_omega)
              by_cases heq_val : (e.constraint (f ⟨k, hk⟩)).val = (h ⟨k, hk⟩).val
              · have hk' := hkeep (by
                  rw [hck_mem, hck1]
                  simp only [cVal, hk, ↓reduceDIte, hck, Fin.ext heq_val,
                    decide_true, Bool.and_self, Bool.toNat_true])
                unfold pruneBody
                wram_exec [hzC.one, hzC.two, hzC.candB, hzT2, hzT3, hzE, hk_reg, hck_mem, hck1,
                  hfa, hha, hcfa, heq_val]
                refine ⟨⟨?_, ?_, ?_, ?_,
                    by simpa only [Data.set_mem] using hk'.1,
                    by simpa only [Data.set_mem] using hk'.2⟩, ?_⟩
                all_goals wram_simp [hzC, hzT2, hzT3, hzR]
              · have hpws := prefix_write_step hzCand hzFr
                  (show Function.update z.mem (candBase g + k) 0 =
                    Function.update z.mem (candBase g + k) (cVal k) by
                    simp only [cVal, hk, ↓reduceDIte, hck,
                      decide_eq_false (fun heq => heq_val (congrArg Fin.val heq)),
                      Bool.true_and, Bool.toNat_false])
                unfold pruneBody
                wram_exec [hzC.zero, hzC.one, hzC.two, hzC.candB, hzT2, hzT3, hzE, hk_reg,
                  hck_mem, hck1, hfa, hha, hcfa, heq_val]
                refine ⟨⟨?_, ?_, ?_, ?_,
                    by simpa only [Data.write_mem, Data.set_mem] using hpws.1,
                    by simpa only [Data.write_mem, Data.set_mem] using hpws.2⟩, ?_⟩
                all_goals wram_simp [hzC, hzT2, hzT3, hzR])
          (hlab2.symm ▸ Nat.zero_le L)
          (hlab2.symm ▸ ⟨hc2, ht2_2, ht3_2, hr2'.trans hr1,
            fun _ h => absurd h (Nat.not_lt_zero _), fun addr _ => congrFun (hm2'.trans hm1) addr⟩)
      rw [hlab2, Nat.sub_zero] at hx3
      have hpr_eq : prune S e =
          { S with cand := fun a => S.cand a && decide (e.constraint (f a) = h a) } := by
        simp only [prune, hgs, hgd]
      refine ⟨y, (hx1.seq (ExecWithin.branch_pos hc_outer
          (ExecWithin.branch_pos hc_inner (hx2.seq hx3)))).mono (by omega), ?_,
        hyR.curNode, hyR.rem, hyR.outerIdx, fun a ha => hyFr a (by wram_omega)⟩
      rw [hpr_eq]
      exact ⟨hS.toTableStateAt.frame hyC rfl (candBase g) (by wram_omega)
          (fun a ha => hyFr a (by omega)),
        hpr_eq ▸ (step_prune S e).potential_le.trans hS.pot_le,
        fun a ha => by simpa only [cVal, ha, ↓reduceDIte] using hyCand a ha,
        hyR.stackLen.trans hS.stack_len, hS.stack_lt,
        hS.stack_mem.frame (fun a _ _ => hyFr a (by wram_omega)),
        hyR.compLen.trans hS.comp_len, hS.comp_le, hS.comp_lt,
        hS.comp_mem.frame (fun a _ _ => hyFr a (by wram_omega))⟩

end Cslib.Complexity.UniqueGames.Propagation
