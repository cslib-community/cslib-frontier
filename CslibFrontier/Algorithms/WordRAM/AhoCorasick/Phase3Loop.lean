/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Phase3Mem
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Phase 3b: BFS Inner/Outer Loops (`bfsBuildCode`)

Verifies `bfsBuildCode` (`Algorithm 3` and Section 6 of `[AhoCorasick1975]`): inner failure /
next-move / output-link expansion loops and the outer FIFO queue sweep from `PBFS.init` to
`inp.bfs`, running in at most `52 * inp.maxS * inp.alphabetSize + 10 * inp.maxS + 7` instructions.

## Main results

* `Cslib.Algorithms.WordRAM.AhoCorasick.exec_bfsBuild`: end-to-end execution proof for Phase 3.
-/

public section

namespace Cslib.Algorithms.WordRAM.AhoCorasick

open Cslib.WordRAM
open Cslib.Algorithms.Lean.AhoCorasick
open Reg

/-- Add `LayoutInv` to the postcondition of a block that writes no layout register. -/
private theorem exists_layoutInv {inp : Input} {w t : ℕ} {c : Code .standard 26} {x : Data 26}
    {P : Data 26 → Prop} (hL : LayoutInv inp x) (h : ∃ y, ExecWithin w c x y t ∧ P y)
    (hk : 18 ≤ c.writeStart := by decide) : ∃ y, ExecWithin w c x y t ∧ LayoutInv inp y ∧ P y :=
  let ⟨y, he, hP⟩ := h
  ⟨y, he, hL.of_preserves he hk, hP⟩

private theorem exec_bfsInnerStore (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound)
    {r a s df qt : ℕ} {x₀ : Data 26} {mem₀ : ℕ → ℕ}
    (ha : a < inp.alphabetSize) (hr_maxS : r < inp.maxS)
    (hs_maxS : s < inp.maxS) (hqt_maxS : qt < inp.maxS)
    (hL₀ : LayoutInv inp x₀)
    (hx₀_r2 : x₀.regs r2 = qt) (hx₀_r3 : x₀.regs r3 = r)
    (hx₀_r5 : x₀.regs r5 = a) (hx₀_r6 : x₀.regs r6 = s) (hx₀_r7 : x₀.regs r7 = df)
    (hx₀_mem : x₀.mem = mem₀) :
    ∃ x_s, ExecWithin w bfsInnerStoreCode x₀ x_s 9 ∧
      LayoutInv inp x_s ∧
      x_s.regs r6 = s ∧ x_s.regs r7 = df ∧
      x_s.regs r1 = x₀.regs r1 ∧ x_s.regs r2 = qt + 1 ∧
      x_s.regs r3 = r ∧ x_s.regs r4 = x₀.regs r4 ∧ x_s.regs r5 = a ∧
      x_s.mem = Function.update
        (Function.update
          (Function.update mem₀ (inp.deltaBase + (r * inp.alphabetSize + a)) s)
          (inp.failBase + s) df)
        (inp.queueBase + qt) s := by
  have hlo := layout_order inp
  have hrm_r := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hr_maxS ha
  have hf_mr : Fits w (r * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
  have hf_ra : Fits w (r * inp.alphabetSize + a) := fits_of_le_outBase hw (by omega)
  have hf_dra : Fits w (inp.deltaBase + (r * inp.alphabetSize + a)) :=
    fits_of_le_outBase hw (by omega)
  have hf_fs : Fits w (inp.failBase + s) := fits_of_le_outBase hw (by omega)
  have hf_qt : Fits w (inp.queueBase + qt) := fits_of_le_outBase hw (by omega)
  have hf_qt1 : Fits w (qt + 1) := fits_of_le_outBase hw (by omega)
  refine exists_layoutInv hL₀ (WP.exists_execWithin ?_)
  unfold bfsInnerStoreCode
  wram_exec [hL₀.h_sigma, hL₀.h_deltaBase, hL₀.h_failBase, hL₀.h_queueBase, hL₀.h_one,
    hx₀_r3, hx₀_r5, hx₀_r6, hx₀_r7, hx₀_r2, hf_mr, hf_ra, hf_dra, hf_fs, hf_qt, hf_qt1]
  exact ⟨by wram_simp [hx₀_r6], by wram_simp [hx₀_r7], by wram_simp,
    by wram_simp, by wram_simp [hx₀_r3], by wram_simp, by wram_simp [hx₀_r5],
    by wram_simp [hx₀_mem]⟩

private theorem exec_bfsInnerLink (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound)
    {r a s df qt ohdf tms : ℕ} {x_s : Data 26} {mem₀ : ℕ → ℕ}
    (ha : a < inp.alphabetSize) (hr_maxS : r < inp.maxS)
    (hdf_maxS : df < inp.maxS) (hs_maxS : s < inp.maxS)
    (hL_s : LayoutInv inp x_s)
    (hxs_r6 : x_s.regs r6 = s) (hxs_r7 : x_s.regs r7 = df)
    (hxs_mem : x_s.mem = Function.update
      (Function.update
        (Function.update mem₀ (inp.deltaBase + (r * inp.alphabetSize + a)) s)
        (inp.failBase + s) df)
      (inp.queueBase + qt) s)
    (hoh_read : mem₀ (inp.outHeadBase + df) = ohdf)
    (htm_read : mem₀ (inp.termBase + s) = tms) :
    ∃ x_m, ExecWithin w bfsInnerLinkCode x_s x_m 6 ∧
      LayoutInv inp x_m ∧
      x_m.regs rState = tms ∧ x_m.regs r6 = s ∧ x_m.regs r7 = ohdf ∧
      x_m.regs r1 = x_s.regs r1 ∧ x_m.regs r2 = x_s.regs r2 ∧
      x_m.regs r3 = x_s.regs r3 ∧ x_m.regs r4 = x_s.regs r4 ∧ x_m.regs r5 = x_s.regs r5 ∧
      x_m.mem = Function.update x_s.mem (inp.outNextBase + s) ohdf := by
  have hlo := layout_order inp
  have hrm_r := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hr_maxS ha
  have hf_ohdf : Fits w (inp.outHeadBase + df) := fits_of_le_outBase hw (by omega)
  have hf_ons : Fits w (inp.outNextBase + s) := fits_of_le_outBase hw (by omega)
  have hf_tms : Fits w (inp.termBase + s) := fits_of_le_outBase hw (by omega)
  have hoh_xs : x_s.mem (inp.outHeadBase + df) = ohdf := by
    rw [hxs_mem]
    simpa (disch := omega) only [Function.update_of_ne] using hoh_read
  have htm_xs : x_s.mem (inp.termBase + s) = tms := by
    rw [hxs_mem]
    simpa (disch := omega) only [Function.update_of_ne] using htm_read
  have hne_tm_on : inp.termBase + s ≠ inp.outNextBase + s := by omega
  refine exists_layoutInv hL_s (WP.exists_execWithin ?_)
  unfold bfsInnerLinkCode
  wram_exec [hL_s.h_outHeadBase, hL_s.h_outNextBase, hL_s.h_termBase,
    hxs_r6, hxs_r7, hf_ohdf, hf_ons, hf_tms, hoh_xs, htm_xs, hne_tm_on]
  exact ⟨by wram_simp, by wram_simp [hxs_r6], by wram_simp, by wram_simp,
    by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩

private theorem exec_bfsInnerBranch (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound)
    {a s ohdf tms : ℕ} {x_m : Data 26}
    (ha : a < inp.alphabetSize) (hs_maxS : s < inp.maxS)
    (hL_m : LayoutInv inp x_m)
    (hxm_rS : x_m.regs rState = tms) (hxm_r6 : x_m.regs r6 = s)
    (hxm_r7 : x_m.regs r7 = ohdf) (hxm_r5 : x_m.regs r5 = a) :
    ∃ x₁, ExecWithin w
        (.branch (.lt zero rState)
          (ram[ rState ← outHeadBase + r6; *rState ← r6; r5 ← r5 + one ])
          (ram[ rState ← outHeadBase + r6; *rState ← r7; r5 ← r5 + one ])) x_m x₁ 5 ∧
      x₁.regs r1 = x_m.regs r1 ∧ x₁.regs r2 = x_m.regs r2 ∧
      x₁.regs r3 = x_m.regs r3 ∧ x₁.regs r4 = x_m.regs r4 ∧ x₁.regs r5 = a + 1 ∧
      x₁.mem = Function.update x_m.mem (inp.outHeadBase + s)
        (if 0 < tms then s else ohdf) := by
  have hlo := layout_order inp
  have h0_maxS : 0 < inp.maxS := by omega
  have ha_rm := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt h0_maxS ha
  have hf_ohs : Fits w (inp.outHeadBase + s) := fits_of_le_outBase hw (by omega)
  have hf_a1 : Fits w (a + 1) := fits_of_le_outBase hw (by omega)
  refine WP.exists_execWithin ?_
  wram_exec [hL_m.h_zero, hL_m.h_outHeadBase, hL_m.h_one, hxm_rS, hxm_r6, hxm_r7, hxm_r5, hf_ohs,
    hf_a1]
  all_goals
    simp only [hc, ↓reduceIte]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩

private theorem exec_bfsInnerStep_pos (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) {qh r fr a s df : ℕ} {B : PBFS} {x x₀ : Data 26}
    (ha : a < inp.alphabetSize) (hr_maxS : r < inp.maxS) (hdf_maxS : df < inp.maxS)
    (hs_pos : 0 < s) (hs_lt : s < inp.trie.numStates)
    (hL : LayoutInv inp x) (hM : BFSMem inp inp.trie B x.mem)
    (hinv : InnerLoopInv inp.patterns inp.alphabetSize inp.trie qh r fr a B)
    (he₀ : ExecWithin w (ram[r6 ← r3 * sigma; r6 ← r6 + r5; r6 ← trieBase + r6; r6 ← *r6;
      r7 ← r4 * sigma; r7 ← r7 + r5; r7 ← deltaBase + r7; r7 ← *r7]) x x₀ 8)
    (hx₀_r6 : x₀.regs r6 = s) (hx₀_r7 : x₀.regs r7 = df)
    (hx₀_r1 : x₀.regs r1 = B.qHead) (hx₀_r2 : x₀.regs r2 = B.qTail)
    (hx₀_r3 : x₀.regs r3 = r) (hx₀_r4 : x₀.regs r4 = fr) (hx₀_r5 : x₀.regs r5 = a)
    (hx₀_mem : x₀.mem = x.mem)
    (hs_eq : inp.trie.trie r a = s) (hdf_eq : B.delta fr a = df) :
    ∃ x₁, ExecWithin w bfsInnerStepCode x x₁ 29 ∧
      LayoutInv inp x₁ ∧ BFSMem inp inp.trie (PBFS.innerStep inp.trie r fr B a) x₁.mem ∧
      x₁.regs r1 = (PBFS.innerStep inp.trie r fr B a).qHead ∧
      x₁.regs r2 = (PBFS.innerStep inp.trie r fr B a).qTail ∧
      x₁.regs r3 = r ∧ x₁.regs r4 = fr ∧ x₁.regs r5 = a + 1 := by
  obtain ⟨hT, hT_maxS, _, _, _⟩ := inp.trie_spec hvalid
  have hL₀ : LayoutInv inp x₀ := hL.of_preserves he₀
  have hs_maxS : s < inp.maxS := lt_of_lt_of_le hs_lt hT_maxS
  have hqt_maxS : B.qTail < inp.maxS :=
    lt_of_lt_of_le (qTail_lt_numStates hT.one_le hinv.q_bounds hinv.q_inj) hT_maxS
  have hcond_s : (Cond.lt zero r6).Holds x₀ := by
    simp only [Cond.holds_lt, hL₀.h_zero, hx₀_r6]; exact hs_pos
  obtain ⟨x_s, he_s, hL_s, hxs_r6, hxs_r7, hxs_r1, hxs_r2, hxs_r3, hxs_r4, hxs_r5, hxs_mem⟩ :=
    exec_bfsInnerStore inp w hw ha hr_maxS hs_maxS hqt_maxS hL₀ hx₀_r2 hx₀_r3 hx₀_r5 hx₀_r6
      hx₀_r7 hx₀_mem
  obtain ⟨x_m, he_l, hL_m, hxm_rS, hxm_r6, hxm_r7, hxm_r1, hxm_r2, hxm_r3, hxm_r4, hxm_r5,
      hxm_mem⟩ :=
    exec_bfsInnerLink inp w hw ha hr_maxS hdf_maxS hs_maxS hL_s hxs_r6 hxs_r7 hxs_mem
      (hM.outHead_cell df hdf_maxS) (hM.term_cell s hs_maxS)
  obtain ⟨x₁, he_oh, hx₁_r1, hx₁_r2, hx₁_r3, hx₁_r4, hx₁_r5, hx₁_mem⟩ :=
    exec_bfsInnerBranch inp w hw ha hs_maxS hL_m hxm_rS hxm_r6 hxm_r7 (hxm_r5.trans hxs_r5)
  have he_tot : ExecWithin w bfsInnerStepCode x x₁ 29 :=
    (he₀.seq (ExecWithin.branch_pos hcond_s ((he_s.seq he_l).seq he_oh))).mono (by omega)
  have hB'_eq : PBFS.innerStep inp.trie r fr B a =
      { B with
        delta := fun u c => if u = r ∧ c = a then s else B.delta u c
        fail := Function.update B.fail s df
        outHead := Function.update B.outHead s
          (if 0 < inp.trie.isTerm s then s else B.outHead df)
        outNext := Function.update B.outNext s (B.outHead df)
        queue := Function.update B.queue B.qTail s
        qTail := B.qTail + 1 } := by
    dsimp only [PBFS.innerStep]
    simp only [hs_eq, hdf_eq, hs_pos, ↓reduceIte]
  rw [hB'_eq]
  refine ⟨x₁, he_tot, hL.of_preserves he_tot, ?_,
    hx₁_r1.trans (hxm_r1.trans (hxs_r1.trans hx₀_r1)),
    hx₁_r2.trans (hxm_r2.trans hxs_r2),
    hx₁_r3.trans (hxm_r3.trans hxs_r3),
    hx₁_r4.trans (hxm_r4.trans (hxs_r4.trans hx₀_r4)),
    hx₁_r5⟩
  rw [hx₁_mem, hxm_mem, hxs_mem]
  exact bfsMem_of_enqueue hr_maxS ha hs_maxS hM

private theorem exec_bfsInnerStep (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) {qh r fr a : ℕ} {B : PBFS} {x : Data 26}
    (ha : a < inp.alphabetSize) (hL : LayoutInv inp x) (hM : BFSMem inp inp.trie B x.mem)
    (hinv : InnerLoopInv inp.patterns inp.alphabetSize inp.trie qh r fr a B)
    (hr1 : x.regs r1 = B.qHead) (hr2 : x.regs r2 = B.qTail)
    (hr3 : x.regs r3 = r) (hr4 : x.regs r4 = fr) (hr5 : x.regs r5 = a) :
    ∃ x₁, ExecWithin w bfsInnerStepCode x x₁ 29 ∧
      LayoutInv inp x₁ ∧ BFSMem inp inp.trie (PBFS.innerStep inp.trie r fr B a) x₁.mem ∧
      x₁.regs r1 = (PBFS.innerStep inp.trie r fr B a).qHead ∧
      x₁.regs r2 = (PBFS.innerStep inp.trie r fr B a).qTail ∧
      x₁.regs r3 = r ∧ x₁.regs r4 = fr ∧ x₁.regs r5 = a + 1 := by
  obtain ⟨hT, hT_maxS, _, _, _⟩ := inp.trie_spec hvalid
  have hlo := layout_order inp
  have hqh_lt : qh < B.qTail := by
    have := hinv.qHead_eq
    have := hinv.qHead_le
    omega
  have hr_lt : r < inp.trie.numStates := hinv.r_eq ▸ (hinv.q_bounds qh hqh_lt).2
  have hr_maxS : r < inp.maxS := lt_of_lt_of_le hr_lt hT_maxS
  have hfr_lt : fr < inp.trie.numStates := by
    have hfexp := hinv.fr_mem
    simp only [PBFS.expAt, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hfexp
    rcases hfexp with rfl | ⟨i, hi, rfl⟩
    · exact hT.one_le
    · exact (hinv.q_bounds i (lt_trans hi hqh_lt)).2
  have hfr_maxS : fr < inp.maxS := lt_of_lt_of_le hfr_lt hT_maxS
  have hrm_r : r * inp.alphabetSize + a < inp.maxS * inp.alphabetSize :=
    Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hr_maxS ha
  have hrm_fr : fr * inp.alphabetSize + a < inp.maxS * inp.alphabetSize :=
    Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hfr_maxS ha
  have ht_read : x.mem (inp.trieBase + (r * inp.alphabetSize + a)) = inp.trie.trie r a := by
    rw [← Nat.add_assoc]; exact hM.trie_cell r hr_maxS a ha
  have hd_read : x.mem (inp.deltaBase + (fr * inp.alphabetSize + a)) = B.delta fr a := by
    rw [← Nat.add_assoc]; exact hM.delta_cell fr hfr_maxS a ha
  have hdf_lt : B.delta fr a < inp.trie.numStates :=
    mem_disc_lt hT.one_le hinv.q_bounds (hinv.delta_exp fr hinv.fr_mem a ha).1
  have hdf_maxS : B.delta fr a < inp.maxS := lt_of_lt_of_le hdf_lt hT_maxS
  have hf_mr : Fits w (r * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
  have hf_ra : Fits w (r * inp.alphabetSize + a) := fits_of_le_outBase hw (by omega)
  have hf_tra : Fits w (inp.trieBase + (r * inp.alphabetSize + a)) :=
    fits_of_le_outBase hw (by omega)
  have hf_dra : Fits w (inp.deltaBase + (r * inp.alphabetSize + a)) :=
    fits_of_le_outBase hw (by omega)
  have hf_mfr : Fits w (fr * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
  have hf_fra : Fits w (fr * inp.alphabetSize + a) := fits_of_le_outBase hw (by omega)
  have hf_dfra : Fits w (inp.deltaBase + (fr * inp.alphabetSize + a)) :=
    fits_of_le_outBase hw (by omega)
  have hf_a1 : Fits w (a + 1) := fits_of_le_outBase hw (by omega)
  have hld : ∃ x₀, ExecWithin w (ram[
      r6 ← r3 * sigma; r6 ← r6 + r5; r6 ← trieBase + r6; r6 ← *r6;
      r7 ← r4 * sigma; r7 ← r7 + r5; r7 ← deltaBase + r7; r7 ← *r7 ]) x x₀ 8 ∧
      x₀.regs r6 = inp.trie.trie r a ∧ x₀.regs r7 = B.delta fr a ∧
      x₀.regs r1 = B.qHead ∧ x₀.regs r2 = B.qTail ∧
      x₀.regs r3 = r ∧ x₀.regs r4 = fr ∧ x₀.regs r5 = a ∧ x₀.mem = x.mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hL.h_sigma, hL.h_trieBase, hL.h_deltaBase, hr3, hr4, hr5, ht_read, hd_read,
      hf_mr, hf_ra, hf_tra, hf_mfr, hf_fra, hf_dfra]
    exact ⟨by wram_simp, by wram_simp, by wram_simp [hr1], by wram_simp [hr2],
      by wram_simp [hr3], by wram_simp [hr4], by wram_simp [hr5], by wram_simp⟩
  obtain ⟨x₀, he₀, hx₀_r6, hx₀_r7, hx₀_r1, hx₀_r2, hx₀_r3, hx₀_r4, hx₀_r5, hx₀_mem⟩ := hld
  by_cases hs_pos : 0 < inp.trie.trie r a
  · exact exec_bfsInnerStep_pos inp w hvalid hw ha hr_maxS hdf_maxS hs_pos
      (hT.trie_lt r hr_lt a ha) hL hM hinv he₀ hx₀_r6 hx₀_r7 hx₀_r1 hx₀_r2 hx₀_r3 hx₀_r4
      hx₀_r5 hx₀_mem rfl rfl
  · have hL₀ : LayoutInv inp x₀ := hL.of_preserves he₀
    have hcond_s : ¬(Cond.lt zero r6).Holds x₀ := by
      simp only [Cond.holds_lt, hL₀.h_zero, hx₀_r6]; exact hs_pos
    generalize hdf_eq : B.delta fr a = df at hx₀_r7
    have hneg : ∃ x₁, ExecWithin w (ram[
        rState ← r3 * sigma; rState ← rState + r5; rState ← deltaBase + rState; *rState ← r7;
        r5 ← r5 + one ]) x₀ x₁ 5 ∧
        x₁.regs r1 = B.qHead ∧ x₁.regs r2 = B.qTail ∧
        x₁.regs r3 = r ∧ x₁.regs r4 = fr ∧ x₁.regs r5 = a + 1 ∧
        x₁.mem = Function.update x.mem (inp.deltaBase + (r * inp.alphabetSize + a)) df := by
      refine WP.exists_execWithin ?_
      wram_exec [hL₀.h_sigma, hL₀.h_deltaBase, hL₀.h_one, hx₀_r3, hx₀_r5, hx₀_r7,
        hf_mr, hf_ra, hf_dra, hf_a1]
      exact ⟨by wram_simp [hx₀_r1], by wram_simp [hx₀_r2], by wram_simp [hx₀_r3],
        by wram_simp [hx₀_r4], by wram_simp, by wram_simp [hx₀_mem]⟩
    obtain ⟨x₁, he_n, hx₁_r1, hx₁_r2, hx₁_r3, hx₁_r4, hx₁_r5, hx₁_mem⟩ := hneg
    have he_tot : ExecWithin w bfsInnerStepCode x x₁ 29 :=
      (he₀.seq (ExecWithin.branch_neg hcond_s he_n)).mono (by omega)
    have hB'_eq : PBFS.innerStep inp.trie r fr B a =
        { B with delta := fun u c => if u = r ∧ c = a then df else B.delta u c } := by
      simp only [PBFS.innerStep, hs_pos, hdf_eq, ↓reduceIte]
    rw [hB'_eq]
    refine ⟨x₁, he_tot, hL.of_preserves he_tot, ?_, hx₁_r1, hx₁_r2, hx₁_r3, hx₁_r4, hx₁_r5⟩
    rw [hx₁_mem]
    exact bfsMem_of_set_delta hr_maxS ha hM

private theorem exec_bfsInnerLoop (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) :
    ∀ (qh r fr k a : ℕ) (B : PBFS) (x : Data 26),
      a + k = inp.alphabetSize →
      LayoutInv inp x →
      BFSMem inp inp.trie B x.mem →
      InnerLoopInv inp.patterns inp.alphabetSize inp.trie qh r fr a B →
      x.regs r1 = B.qHead →
      x.regs r2 = B.qTail →
      x.regs r3 = r →
      x.regs r4 = fr →
      x.regs r5 = a →
      ∃ y, ExecWithin w (.loop (.lt r5 sigma) bfsInnerStepCode) x y (31 * k + 2) ∧
        LayoutInv inp y ∧
        BFSMem inp inp.trie (PBFS.innerLoop inp.trie r fr k a B) y.mem ∧
        y.regs r1 = (PBFS.innerLoop inp.trie r fr k a B).qHead ∧
        y.regs r2 = (PBFS.innerLoop inp.trie r fr k a B).qTail := by
  intro qh r fr k
  obtain ⟨hT, _, _, _, hterm⟩ := inp.trie_spec hvalid
  have hchar := inp.char_iff hvalid
  induction k with
  | zero =>
    intro a B x hak hL hM _ hr1 hr2 _ _ hr5
    have hstop : ¬(Cond.lt r5 sigma).Holds x := by
      simp only [Cond.holds_lt, hr5, hL.h_sigma]; omega
    exact ⟨x, ExecWithin.loop_exit hstop, hL, hM, hr1, hr2⟩
  | succ k ih =>
    intro a B x hak hL hM hinv hr1 hr2 hr3 hr4 hr5
    have ha : a < inp.alphabetSize := by omega
    have hc : (Cond.lt r5 sigma).Holds x := by
      simp only [Cond.holds_lt, hr5, hL.h_sigma]; exact ha
    have hinv_next := innerStep_spec hT hchar hterm ha hinv
    obtain ⟨x₁, he_st, hL₁, hM₁, hx₁_r1, hx₁_r2, hx₁_r3, hx₁_r4, hx₁_r5⟩ :=
      exec_bfsInnerStep inp w hvalid hw ha hL hM hinv hr1 hr2 hr3 hr4 hr5
    obtain ⟨y, he_tl, hLy, hMy, hy_r1, hy_r2⟩ :=
      ih (a + 1) (PBFS.innerStep inp.trie r fr B a) x₁ (by omega) hL₁ hM₁ hinv_next
        hx₁_r1 hx₁_r2 hx₁_r3 hx₁_r4 hx₁_r5
    exact ⟨y, (ExecWithin.loop_iter hc he_st he_tl).mono (by omega), hLy, hMy, hy_r1, hy_r2⟩

private theorem exec_bfsOuterLoop (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) :
    ∀ (fuel : ℕ) (B : PBFS) (x : Data 26),
      LayoutInv inp x →
      BFSMem inp inp.trie B x.mem →
      BFSInv inp.patterns inp.alphabetSize inp.trie B →
      inp.trie.numStates ≤ B.qHead + fuel →
      x.regs r1 = B.qHead →
      x.regs r2 = B.qTail →
      ∃ y, ExecWithin w (.loop (.lt r1 r2) bfsOuterStepCode) x y
          ((31 * inp.alphabetSize + 10) * fuel + 2) ∧
        LayoutInv inp y ∧
        BFSMem inp inp.trie (PBFS.outerLoop inp.trie inp.alphabetSize fuel B) y.mem := by
  intro fuel
  obtain ⟨hT, hT_maxS, _, _, hterm⟩ := inp.trie_spec hvalid
  have hchar := inp.char_iff hvalid
  have hlo := layout_order inp
  induction fuel with
  | zero =>
    intro B x hL hM hinv hfuel hr1 hr2
    have hqt : B.qTail < inp.trie.numStates := qTail_lt_numStates hT.one_le hinv.q_bounds hinv.q_inj
    have hstop : ¬(Cond.lt r1 r2).Holds x := by
      simp only [Cond.holds_lt, hr1, hr2]; omega
    exact ⟨x, ExecWithin.loop_exit hstop, hL, hM⟩
  | succ fuel ih =>
    intro B x hL hM hinv hfuel hr1 hr2
    dsimp only [PBFS.outerLoop]
    by_cases hlt : B.qHead < B.qTail
    · simp only [hlt, ↓reduceIte]
      have hc : (Cond.lt r1 r2).Holds x := by
        simp only [Cond.holds_lt, hr1, hr2]; exact hlt
      set qh := B.qHead
      set r := B.queue qh
      set fr := B.fail r
      obtain ⟨_, hr_lt⟩ := hinv.q_bounds qh hlt
      have hr_maxS : r < inp.maxS := lt_of_lt_of_le hr_lt hT_maxS
      have hqt_lt : B.qTail < inp.trie.numStates :=
        qTail_lt_numStates hT.one_le hinv.q_bounds hinv.q_inj
      have hqh_maxS : qh < inp.maxS := lt_of_lt_of_le (lt_trans hlt hqt_lt) hT_maxS
      have hInner₀ := innerLoopInv_of_bfsInv hT hinv hlt
      have hq_read : x.mem (inp.queueBase + qh) = r := hM.queue_cell qh hqh_maxS
      have hf_read : x.mem (inp.failBase + r) = fr := hM.fail_cell r hr_maxS
      have hf_qaddr : Fits w (inp.queueBase + qh) := fits_of_le_outBase hw (by omega)
      have hf_qh1 : Fits w (qh + 1) := fits_of_le_outBase hw (by omega)
      have hf_faddr : Fits w (inp.failBase + r) := fits_of_le_outBase hw (by omega)
      have hhd : ∃ x₁, ExecWithin w (ram[
          r3 ← queueBase + r1; r3 ← *r3;
          r1 ← r1 + one;
          r4 ← failBase + r3; r4 ← *r4;
          r5 ← #0 ]) x x₁ 6 ∧
          x₁.regs r1 = qh + 1 ∧ x₁.regs r2 = B.qTail ∧
          x₁.regs r3 = r ∧ x₁.regs r4 = fr ∧ x₁.regs r5 = 0 ∧ x₁.mem = x.mem := by
        refine WP.exists_execWithin ?_
        wram_exec [hL.h_queueBase, hL.h_failBase, hL.h_one, hr1, hq_read, hf_read,
          hf_qaddr, hf_qh1, hf_faddr]
        exact ⟨by wram_simp, by wram_simp [hr2], by wram_simp, by wram_simp, by wram_simp,
          by wram_simp⟩
      obtain ⟨x₁, he_hd, hx₁_r1, hx₁_r2, hx₁_r3, hx₁_r4, hx₁_r5, hx₁_mem⟩ := hhd
      set B₁ : PBFS := { B with qHead := qh + 1 }
      obtain ⟨x₂, he_in, hL₂, hM₂, hx₂_r1, hx₂_r2⟩ :=
        exec_bfsInnerLoop inp w hvalid hw qh r fr inp.alphabetSize 0 B₁ x₁ (Nat.zero_add _)
          (hL.of_preserves he_hd) (hx₁_mem ▸ { hM with }) hInner₀ hx₁_r1 hx₁_r2 hx₁_r3 hx₁_r4
          hx₁_r5
      obtain ⟨hinv₂, hqh₂⟩ := outerStep_spec hT hchar hterm hinv hlt
      have hqh₂' : (PBFS.innerLoop inp.trie r fr inp.alphabetSize 0 B₁).qHead = B.qHead + 1 :=
        hqh₂
      obtain ⟨y, he_tl, hLy, hMy⟩ := ih _ x₂ hL₂ hM₂ hinv₂ (by omega) hx₂_r1 hx₂_r2
      exact ⟨y, (ExecWithin.loop_iter hc (he_hd.seq he_in) he_tl).mono
        (by rw [Nat.mul_succ]; omega), hLy, hMy⟩
    · simp only [hlt, ↓reduceIte]
      have hstop : ¬(Cond.lt r1 r2).Holds x := by
        simpa only [Cond.holds_lt, hr1, hr2] using hlt
      exact ⟨x, (ExecWithin.loop_exit hstop).mono (by omega), hL, hM⟩

theorem exec_bfsBuild (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) (x : Data 26)
    (hL : LayoutInv inp x) (hM : TrieMem inp inp.trie x.mem) :
    ∃ y, ExecWithin w bfsBuildCode x y
        (52 * inp.maxS * inp.alphabetSize + 10 * inp.maxS + 7) ∧
      LayoutInv inp y ∧
      BFSMem inp inp.trie inp.bfs y.mem := by
  obtain ⟨hT, hT_maxS, _, _, hterm⟩ := inp.trie_spec hvalid
  have hchar := inp.char_iff hvalid
  have hlo := layout_order inp
  have h1_maxS : 1 ≤ inp.maxS := by omega
  have h0_code : ∃ x₀, ExecWithin (B := .standard) w
      (ram[ r1 ← #0; r2 ← #0; r5 ← #0 ]) x x₀ 3 ∧
      x₀.regs r1 = 0 ∧ x₀.regs r2 = 0 ∧ x₀.regs r5 = 0 ∧ x₀.mem = x.mem := by
    refine WP.exists_execWithin ?_
    wram_exec
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x₀, he₀, hx₀_r1, hx₀_r2, hx₀_r5, hx₀_mem⟩ := h0_code
  have hL₀ : LayoutInv inp x₀ := hL.of_preserves he₀
  obtain ⟨x₁, he_rt, hL₁, hM₁, hx₁_r1, hx₁_r2⟩ :=
    exec_bfsRootLoop inp w hvalid hw inp.alphabetSize 0 PBFS.init x₀ (Nat.zero_add _)
      hL₀ (bfsMem_init (by rwa [hx₀_mem])) (rootLoopInv_init hT) hx₀_r1 hx₀_r2 hx₀_r5
  set B₀ := PBFS.rootLoop inp.trie inp.alphabetSize 0 PBFS.init
  obtain ⟨hBFS₀, hqh₀⟩ := bfsInv_rootLoop hT hchar hterm
  obtain ⟨y, he_out, hLy, hMy⟩ :=
    exec_bfsOuterLoop inp w hvalid hw inp.trie.numStates B₀ x₁ hL₁ hM₁ hBFS₀
      (by rw [hqh₀]; omega) (hx₁_r1.trans hqh₀.symm) hx₁_r2
  have hcost_le :
      3 + (21 * inp.alphabetSize + 2) + ((31 * inp.alphabetSize + 10) * inp.trie.numStates + 2) ≤
        52 * inp.maxS * inp.alphabetSize + 10 * inp.maxS + 7 := by
    linarith [Nat.mul_le_mul_left inp.alphabetSize hT_maxS,
      Nat.mul_le_mul_right inp.alphabetSize h1_maxS]
  rw [Input.bfs_eq]
  exact ⟨y, ((he₀.seq he_rt).seq he_out).mono hcost_le, hLy, hMy⟩

end Cslib.Algorithms.WordRAM.AhoCorasick
