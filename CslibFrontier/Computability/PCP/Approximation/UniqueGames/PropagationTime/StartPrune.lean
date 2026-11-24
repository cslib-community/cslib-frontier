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
  have hwb := outBaseAddr_lt_wordBound g
  have hcb := tabRow_hi_le_candBase (g := g) hs
  have hfit_top : Fits w (outBaseAddr g + slots g) := hw.of_le (by omega)
  have : Fits w (s * L) := hfit_top.of_le (by
    simp only [outBaseAddr, compBase, stackBase, invBase, candBase, tabBase] at *; omega)
  have hpre : ∃ x1, ExecWithin w startPre x x1 3 ∧
      ConstRegs g x1 ∧ x1.regs rSrc = s ∧ x1.regs rTmp2 = tabBase g + s * L ∧
      x1.regs rLabIdx = 0 ∧ x1.regs rOuterIdx = x.regs rOuterIdx ∧ x1.mem = x.mem := by
    have : Fits w (tabBase g + s * L) := hfit_top.of_le (by
      simp only [outBaseAddr, compBase, stackBase, invBase, candBase] at *; omega)
    unfold startPre
    wram_exec [hT.consts.zero, hT.consts.regL, hT.consts.tabB, hs_reg]
    exact ⟨by wram_simp [hT.consts], by wram_simp [hs_reg], by wram_simp, by wram_simp,
      by wram_simp, by wram_simp⟩
  obtain ⟨x1, hx1, hc1, hs1, htmp1, hlab1, hidx1, hm1⟩ := hpre
  let P (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ z.regs rSrc = s ∧ z.regs rTmp2 = tabBase g + s * L ∧
    z.regs rOuterIdx = x.regs rOuterIdx ∧
    (∀ a < k, z.mem (tabBase g + s * L + a) = a) ∧
    (∀ a < k, z.mem (candBase g + a) = 1) ∧
    ∀ addr, ¬ (tabBase g + s * L ≤ addr ∧ addr < tabBase g + s * L + k) →
      ¬ (candBase g ≤ addr ∧ addr < candBase g + k) → z.mem addr = x.mem addr
  obtain ⟨x2, hx2, ⟨hc2, hs2, _, hidx2, htab2, hcand2, hfr2⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := startBody)
      (N := L) (T := 5) P
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzS, hzT2, hzIdx, hzTab, hzCand, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have : Fits w (tabBase g + s * L + k) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
        have : Fits w (candBase g + k) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
        have : Fits w (k + 1) := hfit_top.of_le (by
          simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
        unfold startBody
        wram_exec [hzC.one, hzC.candB, hzT2, hk_reg]
        refine ⟨⟨by wram_simp [hzC], by wram_simp [hzS], by wram_simp [hzT2],
          by wram_simp [hzIdx], ?_, ?_, ?_⟩, by wram_simp⟩
        · simp only [Data.write_mem, Data.set_mem]
          intro a ha
          rw [Function.update_of_ne (by omega : tabBase g + s * L + a ≠ candBase g + k)]
          by_cases hak : a = k
          · subst hak; exact Function.update_self _ _ _
          · rw [Function.update_of_ne (by omega : tabBase g + s * L + a ≠ tabBase g + s * L + k)]
            exact hzTab a (by omega)
        · simp only [Data.write_mem, Data.set_mem]
          intro a ha
          by_cases hak : a = k
          · subst hak; exact Function.update_self _ _ _
          · rw [Function.update_of_ne (by omega : candBase g + a ≠ candBase g + k),
              Function.update_of_ne (by omega : candBase g + a ≠ tabBase g + s * L + k)]
            exact hzCand a (by omega)
        · simp only [Data.write_mem, Data.set_mem]
          intro addr h1 h2
          rw [Function.update_of_ne (by omega : addr ≠ candBase g + k),
            Function.update_of_ne (by omega : addr ≠ tabBase g + s * L + k)]
          exact hzFr addr (by omega) (by omega))
      (by rw [hlab1]; exact Nat.zero_le _)
      (by rw [hlab1]; exact ⟨hc1, hs1, htmp1, hidx1, fun _ h => by omega, fun _ h => by omega,
        fun addr _ _ => congrFun hm1 addr⟩)
  rw [hlab1, Nat.sub_zero] at hx2
  have hpost : ∃ y, ExecWithin w startPost x2 y 5 ∧
      ConstRegs g y ∧ y.regs rStackLen = 1 ∧ y.regs rCompLen = 0 ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      y.mem = Function.update (Function.update x2.mem (visBase g + s) 1) (stackBase g) s := by
    have : Fits w (visBase g + s) := hfit_top.of_le (by
      simp only [outBaseAddr, compBase, stackBase, invBase, candBase, tabBase] at *; omega)
    unfold startPost
    wram_exec [hc2.zero, hc2.one, hc2.visB, hc2.stackB, hs2]
    exact ⟨by wram_simp [hc2], by wram_simp, by wram_simp, by wram_simp [hidx2], by wram_simp⟩
  obtain ⟨y, hx3, hc3, hstk3, hcmp3, hidx3, hym⟩ := hpost
  have hfr_low : ∀ a < visBase g, y.mem a = x.mem a := fun a ha => by
    rw [hym,
      Function.update_of_ne (by simp only [stackBase, invBase, candBase, tabBase] at *; omega),
      Function.update_of_ne (by omega)]
    exact hfr2 a (by simp only [tabBase]; omega) (by simp only [candBase, tabBase]; omega)
  have hpot_start : statePotential (start S s) ≤ slots g :=
    potential_start hT.len_table (hT.len_table ▸ hs)
  refine ⟨y, (hx1.seq (hx2.seq hx3)).mono (by omega), ?_, hidx3⟩
  refine ⟨⟨hc3, hT.inp.frame (fun a ha => hfr_low a (by simp only [visBase, nodeBase]; omega)),
      hT.bkt.frame hfr_low, by simp [start, hT.len_table], fun v hv hvn => ?_,
      fun v hv fn hvf => ?_⟩,
    hpot_start,
    fun a ha => ?_, hstk3, fun u hu => ?_, ?_, hcmp3, Nat.zero_le _,
    fun _ h => by simp [start] at h, holdsList_nil _ _⟩
  · have hvs : v ≠ s := by
      rintro rfl
      have hself : (start S v).get v = some id := List.getD_set_self (hT.len_table ▸ hs)
      rw [hself] at hvn
      nomatch hvn
    have hvn' : S.get v = none := by
      change (S.table.set s (some id)).getD v none = none at hvn
      rwa [List.getD_set_ne (Ne.symm hvs)] at hvn
    rw [hym,
      Function.update_of_ne (by simp only [stackBase, invBase, candBase, tabBase] at *; omega),
      Function.update_of_ne (by omega),
      hfr2 _ (by simp only [tabBase]; omega) (by simp only [candBase, tabBase]; omega)]
    exact hT.vis_none v hv hvn'
  · by_cases hvs : v = s
    · subst hvs
      have hself : (start S v).get v = some id := List.getD_set_self (hT.len_table ▸ hs)
      rw [hself] at hvf
      cases hvf
      refine ⟨?_, fun a ha => ?_⟩
      · rw [hym, Function.update_of_ne (by
            simp only [stackBase, invBase, candBase, tabBase] at *; omega),
          Function.update_self]
      · rw [hym, Function.update_of_ne (by simp only [stackBase, invBase] at *; omega),
          Function.update_of_ne (by simp only [tabBase]; omega)]
        exact htab2 a ha
    · have hvf' : S.get v = some fn := by
        change (S.table.set s (some id)).getD v none = some fn at hvf
        rwa [List.getD_set_ne (Ne.symm hvs)] at hvf
      obtain ⟨hv1, hvtab⟩ := hT.vis_some v hv fn hvf'
      refine ⟨?_, fun a ha => ?_⟩
      · rw [hym, Function.update_of_ne (by
            simp only [stackBase, invBase, candBase, tabBase] at *; omega),
          Function.update_of_ne (by omega),
          hfr2 _ (by simp only [tabBase]; omega) (by simp only [candBase, tabBase]; omega)]
        exact hv1
      · have hv_cb := tabRow_hi_le_candBase (g := g) hv
        rw [hym, Function.update_of_ne (by simp only [stackBase, invBase] at *; omega),
          Function.update_of_ne (by simp only [tabBase]; omega),
          hfr2 _ (not_in_tabRow hvs ha) (by omega)]
        exact hvtab a ha
  · rw [hym, Function.update_of_ne (by simp only [stackBase, invBase] at *; omega),
      Function.update_of_ne (by simp only [candBase, tabBase] at *; omega)]
    exact hcand2 a ha
  · simp only [start, List.mem_singleton] at hu
    exact hu ▸ hs
  · simp only [start, List.reverse_singleton]
    refine holdsList_cons_iff.mpr ⟨?_, holdsList_nil _ _⟩
    rw [hym]; exact Function.update_self _ _ _

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
  have hwb := outBaseAddr_lt_wordBound g
  have hfit_top : Fits w (outBaseAddr g + slots g) := hw.of_le (by omega)
  obtain ⟨x1, hx1, hc1, ht1_1, ht2_1, he1, hs1, hd1, hsl1, hcl1, hcn1, hrem1, hidx1, hm1⟩ :=
    edgeVisLoad_spec (w := w) g S x j hj hS heptr hsrc_reg hdst_reg hw
  simp only [← he_def] at ht1_1 ht2_1 hs1 hd1
  have hnop : ExecWithin w (.op (.copy rLabIdx rLabIdx)) x1 x1 1 :=
    ⟨1, le_rfl, exec_nop rLabIdx x1⟩
  have hS1 : StateAt g S x1 := hS.of_eq hc1 hsl1 hcl1 hm1
  cases hgs : S.get e.src with
  | none =>
    have hc_outer : ¬ (Cond.eq rTmp1 rOne).Holds x1 := by
      simp [Cond.holds_eq, ht1_1, hS.vis_none e.src hs_lt hgs, hc1.one]
    exact ⟨x1, (hx1.seq (ExecWithin.branch_neg hc_outer hnop)).mono (by omega),
      by simpa only [prune, hgs] using hS1, hcn1, hrem1, hidx1, fun a _ => by rw [hm1]⟩
  | some f =>
    obtain ⟨hvis_s, htab_s⟩ := hS.vis_some e.src hs_lt f hgs
    have hc_outer : (Cond.eq rTmp1 rOne).Holds x1 := by
      simp [Cond.holds_eq, ht1_1, hvis_s, hc1.one]
    cases hgd : S.get e.dst with
    | none =>
      have hc_inner : ¬ (Cond.eq rTmp2 rOne).Holds x1 := by
        simp [Cond.holds_eq, ht2_1, hS.vis_none e.dst hd_lt hgd, hc1.one]
      exact ⟨x1, (hx1.seq (ExecWithin.branch_pos hc_outer
          (ExecWithin.branch_neg hc_inner hnop))).mono (by omega),
        by simpa only [prune, hgs, hgd] using hS1, hcn1, hrem1, hidx1, fun a _ => by rw [hm1]⟩
    | some h =>
      obtain ⟨hvis_d, htab_d⟩ := hS.vis_some e.dst hd_lt h hgd
      have hc_inner : (Cond.eq rTmp2 rOne).Holds x1 := by
        simp [Cond.holds_eq, ht2_1, hvis_d, hc1.one]
      have hcb_s := tabRow_hi_le_candBase (g := g) hs_lt
      have hcb_d := tabRow_hi_le_candBase (g := g) hd_lt
      obtain ⟨x2, hx2, hc2, ht2_2, ht3_2, hlab2, he2', _, _,
          hsl2', hcl2', hcn2', hrem2', hidx2', hm2'⟩ :=
        extendPrep_spec (w := w) g rSrc rDst x1 e.src e.dst (Or.inl ⟨rfl, rfl⟩)
          hc1 hs_lt hd_lt hs1 hd1 hw
      have he2 := he2'.trans he1
      have hsl2 := hsl2'.trans hsl1
      have hcl2 := hcl2'.trans hcl1
      have hcn2 := hcn2'.trans hcn1
      have hrem2 := hrem2'.trans hrem1
      have hidx2 := hidx2'.trans hidx1
      have hm2 := hm2'.trans hm1
      let cVal (a : ℕ) : ℕ :=
        if ha : a < L then
          (S.cand ⟨a, ha⟩ && decide (e.constraint (f ⟨a, ha⟩) = h ⟨a, ha⟩)).toNat
        else 0
      let P (k : ℕ) (z : Data 34) : Prop :=
        ConstRegs g z ∧ z.regs rTmp2 = tabBase g + e.src * L ∧
        z.regs rTmp3 = tabBase g + e.dst * L ∧ z.regs rEdgeIdx = 4 + j * (L + 2) ∧
        z.regs rStackLen = S.stack.length ∧ z.regs rCompLen = S.comp.length ∧
        z.regs rCurNode = x.regs rCurNode ∧ z.regs rRem = x.regs rRem ∧
        z.regs rOuterIdx = x.regs rOuterIdx ∧
        (∀ a < k, z.mem (candBase g + a) = cVal a) ∧
        ∀ addr, ¬ (candBase g ≤ addr ∧ addr < candBase g + k) → z.mem addr = x.mem addr
      obtain ⟨y, hx3, ⟨hyC, _, _, _, hySL, hyCL, hyCN, hyRem, hyIdx, hyCand, hyFr⟩, _⟩ :=
        ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := pruneBody)
          (N := L) (T := 14) P
          (fun z hz => hz.1.regL)
          (fun z hz hk => by
            obtain ⟨hzC, hzT2, hzT3, hzE, hzSL, hzCL, hzCN, hzRem, hzIdx, hzCand, hzFr⟩ := hz
            set k := z.regs rLabIdx
            have hk_reg : z.regs rLabIdx = k := rfl
            have hck_mem : z.mem (candBase g + k) = (S.cand ⟨k, hk⟩).toNat := by
              rw [hzFr _ (by omega)]; exact hS.cand_mem k hk
            have : Fits w (candBase g + k) := hfit_top.of_le (by
              simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
            have : Fits w (k + 1) := hfit_top.of_le (by
              simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
            cases hck : S.cand ⟨k, hk⟩ with
            | false =>
              have hck0 : (S.cand ⟨k, hk⟩).toNat = 0 := by simp [hck]
              unfold pruneBody
              wram_exec [hzC.one, hzC.candB, hk_reg, hck_mem, hck0]
              refine ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3],
                by wram_simp [hzE], by wram_simp [hzSL], by wram_simp [hzCL],
                by wram_simp [hzCN], by wram_simp [hzRem], by wram_simp [hzIdx],
                ?_, ?_⟩, by wram_simp⟩
              · simp only [Data.set_mem]
                intro a ha
                by_cases hak : a = k
                · subst hak; rw [hck_mem, hck0]; simp [cVal, hk, hck]
                · exact hzCand a (by omega)
              · simp only [Data.set_mem]
                intro addr haddr; exact hzFr addr (by omega)
            | true =>
              have hck1 : (S.cand ⟨k, hk⟩).toNat = 1 := by simp [hck]
              have hfk_lt := (f ⟨k, hk⟩).isLt
              have hfa : z.mem (tabBase g + e.src * L + k) = (f ⟨k, hk⟩).val := by
                rw [hzFr _ (by omega)]; exact htab_s k hk
              have hha : z.mem (tabBase g + e.dst * L + k) = (h ⟨k, hk⟩).val := by
                rw [hzFr _ (by omega)]; exact htab_d k hk
              have hcfa : z.mem (4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2)) =
                  (e.constraint (f ⟨k, hk⟩)).val := by
                rw [hzFr _ (by simp only [candBase, tabBase, visBase, nodeBase] at *; omega),
                  show 4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2) =
                    4 + j * (L + 2) + 2 + (f ⟨k, hk⟩).val by omega]
                exact hS.inp.edge_val j hj (f ⟨k, hk⟩).val hfk_lt
              have : Fits w (tabBase g + e.src * L + k) := hfit_top.of_le (by
                simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
              have : Fits w (tabBase g + e.dst * L + k) := hfit_top.of_le (by
                simp only [outBaseAddr, compBase, stackBase, invBase] at *; omega)
              have : Fits w ((f ⟨k, hk⟩).val + 2) := hfit_top.of_le (by
                simp only [outBaseAddr, compBase, stackBase, invBase, candBase, tabBase,
                  visBase, nodeBase] at *; omega)
              have : Fits w (4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2)) := hfit_top.of_le (by
                simp only [outBaseAddr, compBase, stackBase, invBase, candBase, tabBase,
                  visBase, nodeBase] at *; omega)
              by_cases heq_val : (e.constraint (f ⟨k, hk⟩)).val = (h ⟨k, hk⟩).val
              · have heq_fin : e.constraint (f ⟨k, hk⟩) = h ⟨k, hk⟩ := Fin.ext heq_val
                unfold pruneBody
                wram_exec [hzC.one, hzC.two, hzC.candB, hzT2, hzT3, hzE, hk_reg, hck_mem, hck1,
                  hfa, hha, hcfa, heq_val]
                refine ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3],
                  by wram_simp [hzE], by wram_simp [hzSL], by wram_simp [hzCL],
                  by wram_simp [hzCN], by wram_simp [hzRem], by wram_simp [hzIdx],
                  ?_, ?_⟩, by wram_simp⟩
                · simp only [Data.set_mem]
                  intro a ha
                  by_cases hak : a = k
                  · subst hak; rw [hck_mem, hck1]; simp [cVal, hk, hck, heq_fin]
                  · exact hzCand a (by omega)
                · simp only [Data.set_mem]
                  intro addr haddr; exact hzFr addr (by omega)
              · have hne_fin : e.constraint (f ⟨k, hk⟩) ≠ h ⟨k, hk⟩ :=
                  fun heq => heq_val (congrArg Fin.val heq)
                have hpws := prefix_write_step hzCand hzFr
                  (show Function.update z.mem (candBase g + k) 0 =
                    Function.update z.mem (candBase g + k) (cVal k) by
                    simp [cVal, hk, hck, hne_fin])
                unfold pruneBody
                wram_exec [hzC.zero, hzC.one, hzC.two, hzC.candB, hzT2, hzT3, hzE, hk_reg,
                  hck_mem, hck1, hfa, hha, hcfa, heq_val]
                refine ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3],
                  by wram_simp [hzE], by wram_simp [hzSL], by wram_simp [hzCL],
                  by wram_simp [hzCN], by wram_simp [hzRem], by wram_simp [hzIdx],
                  ?_, ?_⟩, by wram_simp⟩
                · simp only [Data.write_mem, Data.set_mem]; exact hpws.1
                · simp only [Data.write_mem, Data.set_mem]; exact hpws.2)
          (by rw [hlab2]; exact Nat.zero_le _)
          (by rw [hlab2]; exact ⟨hc2, ht2_2, ht3_2, he2, hsl2, hcl2, hcn2, hrem2, hidx2,
            fun _ h => by omega, fun addr _ => congrFun hm2 addr⟩)
      rw [hlab2, Nat.sub_zero] at hx3
      have hfr_below : ∀ a < candBase g, y.mem a = x.mem a := fun a ha =>
        hyFr a (by omega)
      have hfr_low : ∀ a < visBase g, y.mem a = x.mem a := fun a ha =>
        hfr_below a (by simp only [candBase, tabBase]; omega)
      have hpot_prune : statePotential (prune S e) ≤ slots g :=
        (step_prune S e).potential_le.trans hS.pot_le
      refine ⟨y, (hx1.seq (ExecWithin.branch_pos hc_outer
          (ExecWithin.branch_pos hc_inner (hx2.seq hx3)))).mono (by omega),
        ?_, hyCN, hyRem, hyIdx, hfr_low⟩
      have hpr_eq : prune S e =
          { S with cand := fun a => S.cand a && decide (e.constraint (f a) = h a) } := by
        simp [prune, hgs, hgd]
      rw [hpr_eq]
      refine ⟨⟨hyC, hS.inp.frame (fun a ha => hfr_low a (by simp only [visBase, nodeBase]; omega)),
          hS.bkt.frame hfr_low, hS.len_table,
          fun v hv hvn => by
            rw [hfr_below _ (by simp only [candBase, tabBase]; omega)]
            exact hS.vis_none v hv hvn,
          fun v hv fn hvf => by
            obtain ⟨hv1, hvtab⟩ := hS.vis_some v hv fn hvf
            have hv_cb := tabRow_hi_le_candBase (g := g) hv
            exact ⟨by rw [hfr_below _ (by simp only [candBase, tabBase]; omega)]; exact hv1,
              fun a ha => by rw [hfr_below _ (by omega)]; exact hvtab a ha⟩⟩,
        by rw [← hpr_eq]; exact hpot_prune,
        fun a ha => by simpa [cVal, ha] using hyCand a ha,
        hySL, hS.stack_lt,
        hS.stack_mem.frame (fun a ha1 _ => hyFr a (by simp only [stackBase, invBase] at *; omega)),
        hyCL, hS.comp_le, hS.comp_lt,
        hS.comp_mem.frame (fun a ha1 _ => hyFr a
          (by simp only [compBase, stackBase, invBase] at *; omega))⟩

end Cslib.Complexity.UniqueGames.Propagation
