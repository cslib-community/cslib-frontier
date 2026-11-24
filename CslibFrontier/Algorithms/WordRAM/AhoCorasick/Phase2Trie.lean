/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Phase1Setup
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.Nat.Div

/-!
# Phase 2: Flat Array-Trie Construction (`buildTrieCode`)

Verifies `buildTrieCode`: iterates over the serialized pattern words `encodePatterns inp.patterns`
and builds the flat `maxS × σ` array trie representing `inp.trie = PTrie.build inp.patterns` in
`19 * inp.maxS + 11 * inp.patterns.length + 5` instructions (`Algorithm 2` of `[AhoCorasick1975]`).

## Main results

* `Cslib.Algorithms.WordRAM.AhoCorasick.exec_buildTrie`: execution proof for Phase 2 (`TrieMem`
  from `PTrie.init` to `inp.trie`).
-/

public section

namespace Cslib.Algorithms.WordRAM.AhoCorasick

open Cslib.WordRAM
open Cslib.Algorithms.Lean.AhoCorasick
open Reg

/-! ## Phase 2: Array-trie construction (`buildTrieCode`) -/

private theorem trieMem_stepChar_new {inp : Input} {T : PTrie} {mem : ℕ → ℕ}
    {u₀ a : ℕ} (hu₀ : u₀ < inp.maxS) (ha : a < inp.alphabetSize)
    (hs : T.numStates < inp.maxS) (h0 : T.trie u₀ a = 0)
    (hM : TrieMem inp T mem) :
    TrieMem inp (T.stepChar u₀ a).1
      (Function.update
        (Function.update mem (inp.trieBase + u₀ * inp.alphabetSize + a) T.numStates)
        (inp.depthBase + T.numStates) (T.depth u₀ + 1)) := by
  have hlo := layout_order inp
  have hrm₀ := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu₀ ha
  have hlen := length_encodePatterns inp.patterns
  dsimp only [PTrie.stepChar]
  simp only [h0, ↓reduceIte]
  refine
    { pats := hM.pats.frame fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
      txt := hM.txt.frame fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
      trie_cell := fun u hu c hc => by
        have huc_lt := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
        dsimp only
        rw [Function.update_of_ne (by omega)]
        by_cases huc : u = u₀ ∧ c = a
        · obtain ⟨rfl, rfl⟩ := huc
          simp only [and_self, ↓reduceIte, Function.update_self]
        · simp only [huc, ↓reduceIte]
          have hne_addr : inp.trieBase + u * inp.alphabetSize + c ≠
              inp.trieBase + u₀ * inp.alphabetSize + a := fun heq => by
            obtain ⟨hc_eq, hu_eq⟩ := Nat.eq_of_add_mul_eq (b := u) (b' := u₀) hc ha (by omega)
            exact huc ⟨hu_eq, hc_eq⟩
          rw [Function.update_of_ne hne_addr]
          exact hM.trie_cell u hu c hc
      depth_cell := fun u hu => by
        dsimp only
        by_cases hus : u = T.numStates
        · subst hus
          rw [Function.update_self, Function.update_self]
        · simp (disch := omega) only [Function.update_of_ne]
          exact hM.depth_cell u hu
      term_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.term_cell u hu
      zero_df := fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.zero_df addr ha1 ha2
      zero_rest := fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.zero_rest addr ha1 ha2 }

private theorem trieMem_insertPat_pos {inp : Input} {T : PTrie} {mem : ℕ → ℕ}
    {u₁ : ℕ} (hu₁ : u₁ < inp.maxS) (hM : TrieMem inp T mem) :
    TrieMem inp { T with isTerm := Function.update T.isTerm u₁ 1 }
      (Function.update mem (inp.termBase + u₁) 1) := by
  have hlo := layout_order inp
  have hlen := length_encodePatterns inp.patterns
  refine
    { pats := hM.pats.frame fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
      txt := hM.txt.frame fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
      trie_cell := fun u hu c hc => by
        have huc_lt := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.trie_cell u hu c hc
      depth_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.depth_cell u hu
      term_cell := fun u hu => by
        dsimp only
        by_cases huu : u = u₁
        · subst huu; rw [Function.update_self, Function.update_self]
        · simp (disch := omega) only [Function.update_of_ne]
          exact hM.term_cell u hu
      zero_df := fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.zero_df addr ha1 ha2
      zero_rest := fun addr ha1 ha2 => by
        simp (disch := omega) only [Function.update_of_ne]
        exact hM.zero_rest addr ha1 ha2 }

private theorem exec_trieCharLoop (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound) :
    ∀ (chars rest : List ℕ) (T : PTrie) (x : Data 26),
      LayoutInv inp x →
      TrieMem inp T x.mem →
      TreeInv inp.alphabetSize T →
      T.numStates + chars.length ≤ inp.maxS →
      x.regs rState = T.numStates →
      x.regs r4 < T.numStates →
      x.regs r3 = chars.length →
      x.regs r2 + (chars ++ rest).length ≤ inp.textBase →
      Block.HoldsList (x.regs r2) (chars ++ rest) x.mem →
      (∀ a ∈ chars, a < inp.alphabetSize) →
      ∃ y, ExecWithin w (.loop (.lt zero r3) trieCharStepCode) x y (19 * chars.length + 2) ∧
        LayoutInv inp y ∧
        TrieMem inp (T.insertChars (x.regs r4) chars).1 y.mem ∧
        y.regs rState = (T.insertChars (x.regs r4) chars).1.numStates ∧
        y.regs r4 = (T.insertChars (x.regs r4) chars).2 ∧
        y.regs r2 = x.regs r2 + chars.length ∧
        y.regs r1 = x.regs r1 ∧
        Block.HoldsList (y.regs r2) rest y.mem := by
  intro chars
  have hlo := layout_order inp
  induction chars with
  | nil =>
    intro rest T x hL hM _ _ hrS _ hr3 _ hhold _
    have hstop : ¬(Cond.lt zero r3).Holds x := by
      simp only [Cond.holds_lt, hL.h_zero, hr3, List.length_nil]; omega
    refine ⟨x, ExecWithin.loop_exit hstop, hL, hM, hrS, rfl, by simp, rfl, ?_⟩
    simpa only [List.nil_append, Nat.add_zero] using hhold
  | cons a as ih =>
    intro rest T x hL hM hT hbud hrS hu_lt hr3 hptr_ub hhold hchars
    have hc : (Cond.lt zero r3).Holds x := by
      simp only [Cond.holds_lt, hL.h_zero, hr3, List.length_cons]; omega
    have ha_lt : a < inp.alphabetSize := hchars a List.mem_cons_self
    have has_lt : ∀ b ∈ as, b < inp.alphabetSize := fun b hb =>
      hchars b (List.mem_cons_of_mem a hb)
    obtain ⟨hm_a, hhold_tail⟩ := Block.holdsList_cons_iff.mp hhold
    have hu_maxS : x.regs r4 < inp.maxS := by simp only [List.length_cons] at hbud; omega
    have hrm_lt : x.regs r4 * inp.alphabetSize + a < inp.maxS * inp.alphabetSize :=
      Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu_maxS ha_lt
    have htrie_read :
        x.mem (inp.trieBase + (x.regs r4 * inp.alphabetSize + a)) = T.trie (x.regs r4) a := by
      rw [← Nat.add_assoc]; exact hM.trie_cell (x.regs r4) hu_maxS a ha_lt
    have hf_ptr1 : Fits w (x.regs r2 + 1) := fits_of_le_outBase hw (by
      simp only [List.cons_append, List.length_cons, List.length_append] at hptr_ub; omega)
    have hf_rem1 : Fits w (x.regs r3 - 1) := fits_of_le_outBase hw (by
      rw [hr3]; simp only [List.cons_append, List.length_cons, List.length_append] at hptr_ub ⊢
      omega)
    have hf_mul : Fits w (x.regs r4 * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
    have hf_rm : Fits w (x.regs r4 * inp.alphabetSize + a) := fits_of_le_outBase hw (by omega)
    have hf_taddr : Fits w (inp.trieBase + (x.regs r4 * inp.alphabetSize + a)) :=
      fits_of_le_outBase hw (by omega)
    have hhead : ∃ x₁, ExecWithin w (ram[
        r5 ← *r2;
        r2 ← r2 + one;
        r3 ← r3 - one;
        r6 ← r4 * sigma;
        r6 ← r6 + r5;
        r6 ← trieBase + r6;
        r7 ← *r6 ]) x x₁ 7 ∧
      x₁.regs r2 = x.regs r2 + 1 ∧
      x₁.regs r3 = as.length ∧
      x₁.regs r4 = x.regs r4 ∧
      x₁.regs r5 = a ∧
      x₁.regs r6 = inp.trieBase + x.regs r4 * inp.alphabetSize + a ∧
      x₁.regs r7 = T.trie (x.regs r4) a ∧
      x₁.regs rState = T.numStates ∧
      x₁.regs r1 = x.regs r1 ∧
      x₁.mem = x.mem := by
      refine WP.exists_execWithin ?_
      wram_exec [hm_a, hL.h_one, hL.h_sigma, hL.h_trieBase, htrie_read, hf_ptr1, hf_rem1,
        hf_mul, hf_rm, hf_taddr]
      refine ⟨by wram_simp, ?_, by wram_simp, by wram_simp,
        by wram_simp; omega, by wram_simp, by wram_simp [hrS], by wram_simp, by wram_simp⟩
      wram_simp [hr3]
      simp only [List.length_cons, Nat.add_sub_cancel]
    obtain ⟨x₁, he_hd, hx₁_r2, hx₁_r3, hx₁_r4, hx₁_r5, hx₁_r6, hx₁_r7, hx₁_rS, hx₁_r1,
      hx₁_mem⟩ := hhead
    have hL₁ : LayoutInv inp x₁ := hL.of_preserves he_hd
    obtain ⟨hT_step, _, hub_step, _, hs_lt_step, _, _⟩ := stepChar_spec hT hu_lt ha_lt
    dsimp only [PTrie.insertChars]
    generalize hT₁_def : (T.stepChar (x.regs r4) a).1 = T₁ at hT_step hub_step hs_lt_step ⊢
    generalize hu₁_def : (T.stepChar (x.regs r4) a).2 = u₁ at hs_lt_step ⊢
    have hbranch : ∃ x₂, ExecWithin w trieCharBranchCode x₁ x₂ 10 ∧
      LayoutInv inp x₂ ∧
      TrieMem inp T₁ x₂.mem ∧
      x₂.regs rState = T₁.numStates ∧
      x₂.regs r4 = u₁ ∧
      x₂.regs r2 = x.regs r2 + 1 ∧
      x₂.regs r3 = as.length ∧
      x₂.regs r1 = x.regs r1 ∧
      Block.HoldsList (x.regs r2 + 1) (as ++ rest) x₂.mem := by
      by_cases hpos : 0 < T.trie (x.regs r4) a
      · have hcond : (Cond.lt zero r7).Holds x₁ := by
          simp only [Cond.holds_lt, hL₁.h_zero, hx₁_r7]; exact hpos
        have hnot0 : T.trie (x.regs r4) a ≠ 0 := by omega
        have hT₁_eq : T₁ = T := by
          rw [← hT₁_def]; dsimp only [PTrie.stepChar]; simp only [hnot0, ↓reduceIte]
        have hu₁_eq : u₁ = T.trie (x.regs r4) a := by
          rw [← hu₁_def]; dsimp only [PTrie.stepChar]; simp only [hnot0, ↓reduceIte]
        have hpos_step : ∃ x₂, ExecWithin (B := .standard) w (ram[ r4 ← r7 ]) x₁ x₂ 1 ∧
            x₂.regs r4 = u₁ ∧ x₂.regs rState = T.numStates ∧
            x₂.regs r2 = x₁.regs r2 ∧ x₂.regs r3 = x₁.regs r3 ∧
            x₂.regs r1 = x₁.regs r1 ∧ x₂.mem = x₁.mem := by
          refine WP.exists_execWithin ?_
          wram_exec
          exact ⟨by wram_simp [hx₁_r7, hu₁_eq], by wram_simp [hx₁_rS], by wram_simp,
            by wram_simp, by wram_simp, by wram_simp⟩
        obtain ⟨x₂, he_p, hx₂_r4, hx₂_rS, hx₂_r2, hx₂_r3, hx₂_r1, hx₂_mem⟩ := hpos_step
        have he_br : ExecWithin w trieCharBranchCode x₁ x₂ 10 :=
          (ExecWithin.branch_pos hcond he_p).mono (by omega)
        have hL₂ : LayoutInv inp x₂ := hL₁.of_preserves he_br
        refine ⟨x₂, he_br, hL₂, ?_, hx₂_rS.trans (congrArg PTrie.numStates hT₁_eq.symm), hx₂_r4,
          hx₂_r2.trans hx₁_r2, hx₂_r3.trans hx₁_r3, hx₂_r1.trans hx₁_r1, ?_⟩
        · rwa [hx₂_mem, hx₁_mem, hT₁_eq]
        · rwa [hx₂_mem, hx₁_mem]
      · have h0 : T.trie (x.regs r4) a = 0 := by omega
        have hcond : ¬(Cond.lt zero r7).Holds x₁ := by
          simp only [Cond.holds_lt, hL₁.h_zero, hx₁_r7, h0]; omega
        have hs_maxS : T.numStates < inp.maxS := by simp only [List.length_cons] at hbud; omega
        have hdu_le : T.depth (x.regs r4) < T.numStates :=
          lt_of_le_of_lt (depth_le_self hT _ hu_lt) hu_lt
        have hd_read : x₁.mem (inp.depthBase + x.regs r4) = T.depth (x.regs r4) := by
          rw [hx₁_mem]; exact hM.depth_cell (x.regs r4) hu_maxS
        have hf_dpu : Fits w (inp.depthBase + x.regs r4) := fits_of_le_outBase hw (by omega)
        have hf_du1 : Fits w (T.depth (x.regs r4) + 1) := fits_of_le_outBase hw (by omega)
        have hf_dps : Fits w (inp.depthBase + T.numStates) := fits_of_le_outBase hw (by omega)
        have hf_s1 : Fits w (T.numStates + 1) := fits_of_le_outBase hw (by omega)
        have hne_dp_tr :
            inp.depthBase + x.regs r4 ≠ inp.trieBase + x.regs r4 * inp.alphabetSize + a := by
          omega
        have hneg_step : ∃ x₂, ExecWithin w (ram[
            *r6 ← rState;
            r7 ← depthBase + r4;
            r7 ← *r7;
            r7 ← r7 + one;
            r6 ← depthBase + rState;
            *r6 ← r7;
            r4 ← rState;
            rState ← rState + one ]) x₁ x₂ 8 ∧
          x₂.regs rState = T.numStates + 1 ∧
          x₂.regs r4 = T.numStates ∧
          x₂.regs r2 = x₁.regs r2 ∧
          x₂.regs r3 = x₁.regs r3 ∧
          x₂.regs r1 = x₁.regs r1 ∧
          x₂.mem = Function.update
            (Function.update x.mem (inp.trieBase + x.regs r4 * inp.alphabetSize + a) T.numStates)
            (inp.depthBase + T.numStates) (T.depth (x.regs r4) + 1) := by
          refine WP.exists_execWithin ?_
          wram_exec [hL₁.h_depthBase, hL₁.h_one, hx₁_r4, hx₁_r6, hx₁_rS, hd_read,
            hf_dpu, hf_du1, hf_dps, hf_s1, hne_dp_tr]
          exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
            by wram_simp [hx₁_mem]⟩
        obtain ⟨x₂, he_n, hx₂_rS, hx₂_r4, hx₂_r2, hx₂_r3, hx₂_r1, hx₂_mem⟩ := hneg_step
        have he_br : ExecWithin w trieCharBranchCode x₁ x₂ 10 := ExecWithin.branch_neg hcond he_n
        have hL₂ : LayoutInv inp x₂ := hL₁.of_preserves he_br
        have hT₁_num : T₁.numStates = T.numStates + 1 := by
          rw [← hT₁_def]; dsimp only [PTrie.stepChar]; simp only [h0, ↓reduceIte]
        have hu₁_eq : u₁ = T.numStates := by
          rw [← hu₁_def]; dsimp only [PTrie.stepChar]; simp only [h0, ↓reduceIte]
        have hM₂ : TrieMem inp T₁ x₂.mem := by
          rw [hx₂_mem, ← hT₁_def]
          exact trieMem_stepChar_new hu_maxS ha_lt hs_maxS h0 hM
        have hhold₂ : Block.HoldsList (x.regs r2 + 1) (as ++ rest) x₂.mem := by
          rw [hx₂_mem]
          refine hhold_tail.frame fun addr ha1 ha2 => ?_
          simp only [List.append_eq, List.cons_append, List.length_cons, List.length_append]
            at hptr_ub ha2
          simp (disch := omega) only [Function.update_of_ne]
        exact ⟨x₂, he_br, hL₂, hM₂, hx₂_rS.trans hT₁_num.symm, hx₂_r4.trans hu₁_eq.symm,
          hx₂_r2.trans hx₁_r2, hx₂_r3.trans hx₁_r3, hx₂_r1.trans hx₁_r1, hhold₂⟩
    obtain ⟨x₂, he_br, hL₂, hM₂, hx₂_rS, hx₂_r4, hx₂_r2, hx₂_r3, hx₂_r1, hhold₂⟩ := hbranch
    have hT₁_bud : T₁.numStates + as.length ≤ inp.maxS := by
      simp only [List.length_cons] at hbud
      omega
    obtain ⟨y, he_tl, hLy, hMy, hy_rS, hy_r4, hy_r2, hy_r1, hholdy⟩ :=
      ih rest T₁ x₂ hL₂ hM₂ hT_step hT₁_bud hx₂_rS
        (by rw [hx₂_r4]; exact hs_lt_step) hx₂_r3
        (by
          rw [hx₂_r2]
          simp only [List.cons_append, List.length_cons, List.length_append] at hptr_ub ⊢
          omega)
        (by rwa [hx₂_r2]) has_lt
    rw [hx₂_r4] at hMy hy_rS hy_r4
    refine ⟨y, (ExecWithin.loop_iter hc (he_hd.seq he_br) he_tl).mono
      (by simp only [List.length_cons]; omega),
      hLy, hMy, hy_rS, hy_r4, ?_, hy_r1.trans hx₂_r1, hholdy⟩
    rw [hy_r2, hx₂_r2, List.length_cons]
    omega

private theorem exec_triePatLoop (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound) :
    ∀ (ps : List (List ℕ)) (T : PTrie) (x : Data 26),
      LayoutInv inp x →
      TrieMem inp T x.mem →
      TreeInv inp.alphabetSize T →
      T.numStates + totalPatternLen ps ≤ inp.maxS →
      x.regs rState = T.numStates →
      x.regs r1 = ps.length →
      x.regs r2 + (encodePatterns ps).length ≤ inp.textBase →
      Block.HoldsList (x.regs r2) (encodePatterns ps) x.mem →
      (∀ p ∈ ps, ∀ a ∈ p, a < inp.alphabetSize) →
      ∃ y, ExecWithin w (.loop (.lt zero r1) triePatStepCode) x y
          (19 * totalPatternLen ps + 11 * ps.length + 2) ∧
        LayoutInv inp y ∧
        TrieMem inp (ps.foldl PTrie.insertPat T) y.mem ∧
        y.regs rState = (ps.foldl PTrie.insertPat T).numStates
  | [], T, x, hL, hM, _, _, hrS, hr1, _, _, _ => by
    have hstop : ¬(Cond.lt zero r1).Holds x := by
      simp only [Cond.holds_lt, hL.h_zero, hr1, List.length_nil]; omega
    exact ⟨x, ExecWithin.loop_exit hstop, hL, hM, hrS⟩
  | p :: ps, T, x, hL, hM, hT, hbud, hrS, hr1, hptr_ub, hhold, hps => by
    have hlo := layout_order inp
    have hc : (Cond.lt zero r1).Holds x := by
      simp only [Cond.holds_lt, hL.h_zero, hr1, List.length_cons]; omega
    have hp_val : ∀ a ∈ p, a < inp.alphabetSize := hps p List.mem_cons_self
    have hps_val : ∀ q ∈ ps, ∀ a ∈ q, a < inp.alphabetSize := fun q hq =>
      hps q (List.mem_cons_of_mem p hq)
    dsimp only [encodePatterns] at hhold hptr_ub
    obtain ⟨hm_plen, hhold_body⟩ := Block.holdsList_cons_iff.mp hhold
    have hf_ptr1 : Fits w (x.regs r2 + 1) := fits_of_le_outBase hw (by
      simp only [List.length_cons, List.length_append] at hptr_ub; omega)
    have hpat_hd : ∃ x₁, ExecWithin w (ram[ r3 ← *r2; r2 ← r2 + one; r4 ← #0 ]) x x₁ 3 ∧
        x₁.regs r3 = p.length ∧ x₁.regs r2 = x.regs r2 + 1 ∧ x₁.regs r4 = 0 ∧
        x₁.regs rState = T.numStates ∧ x₁.regs r1 = x.regs r1 ∧ x₁.mem = x.mem := by
      refine WP.exists_execWithin ?_
      wram_exec [hm_plen, hL.h_one, hf_ptr1]
      exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp [hrS], by wram_simp,
        by wram_simp⟩
    obtain ⟨x₁, he_hd, hx₁_r3, hx₁_r2, hx₁_r4, hx₁_rS, hx₁_r1, hx₁_mem⟩ := hpat_hd
    have hL₁ : LayoutInv inp x₁ :=
      hL.of_preserves he_hd
    obtain ⟨hT₁_inv, _, hub₁, hu₁_lt, _, _, _, _, _⟩ :=
      insertChars_spec p T 0 hT hT.one_le hp_val
    obtain ⟨x₂, he_chars, hL₂, hM₂, hx₂_rS, hx₂_r4, hx₂_r2, hx₂_r1, hhold₂⟩ :=
      exec_trieCharLoop inp w hw p (encodePatterns ps) T x₁ hL₁ (by rwa [hx₁_mem]) hT
        (by simp only [totalPatternLen_cons] at hbud; omega) hx₁_rS
        (by rw [hx₁_r4]; exact hT.one_le) hx₁_r3
        (by rw [hx₁_r2]; simp only [List.length_cons, List.length_append] at hptr_ub ⊢; omega)
        (by rwa [hx₁_r2, hx₁_mem]) hp_val
    rw [hx₁_r4] at hM₂ hx₂_rS hx₂_r4
    set T₁ := (T.insertChars 0 p).1
    set u₁ := (T.insertChars 0 p).2
    set T₂ := PTrie.insertPat T p
    have hT₁_maxS : T₁.numStates ≤ inp.maxS := by
      simp only [totalPatternLen_cons] at hbud; omega
    have hu₁_maxS : u₁ < inp.maxS := lt_of_lt_of_le hu₁_lt hT₁_maxS
    have hf_p1 : Fits w (x₂.regs r1 - 1) := fits_of_le_outBase hw (by
      rw [hx₂_r1, hx₁_r1, hr1]
      simp only [List.length_cons, List.length_append, length_encodePatterns] at hptr_ub ⊢
      omega)
    have hpat_tl : ∃ x₃, ExecWithin w triePatBranchCode x₂ x₃ 4 ∧
      LayoutInv inp x₃ ∧
      TrieMem inp T₂ x₃.mem ∧
      x₃.regs rState = T₂.numStates ∧
      x₃.regs r1 = ps.length ∧
      x₃.regs r2 = x₂.regs r2 ∧
      Block.HoldsList (x₂.regs r2) (encodePatterns ps) x₃.mem := by
      by_cases hpos : 0 < u₁
      · have hcond : (Cond.lt zero r4).Holds x₂ := by
          simp only [Cond.holds_lt, hL₂.h_zero, hx₂_r4]; exact hpos
        have hf_taddr : Fits w (inp.termBase + u₁) := fits_of_le_outBase hw (by omega)
        have hpos_tl : ∃ x₃, ExecWithin w
            (ram[ r6 ← termBase + r4; *r6 ← one; r1 ← r1 - one ]) x₂ x₃ 3 ∧
            x₃.regs rState = x₂.regs rState ∧ x₃.regs r1 = ps.length ∧
            x₃.regs r2 = x₂.regs r2 ∧
            x₃.mem = Function.update x₂.mem (inp.termBase + u₁) 1 := by
          refine WP.exists_execWithin ?_
          wram_exec [hL₂.h_termBase, hL₂.h_one, hx₂_r4, hf_taddr, hf_p1]
          exact ⟨by wram_simp, by wram_simp [hx₂_r1, hx₁_r1, hr1]; simp, by wram_simp,
            by wram_simp⟩
        obtain ⟨x₃, he_p, hx₃_rS, hx₃_r1, hx₃_r2, hx₃_mem⟩ := hpos_tl
        have he_br : ExecWithin w triePatBranchCode x₂ x₃ 4 := ExecWithin.branch_pos hcond he_p
        have hL₃ : LayoutInv inp x₃ :=
          hL₂.of_preserves he_br
        have hpos' : 0 < (T.insertChars 0 p).2 := hpos
        have hT₂_eq : T₂ = { T₁ with isTerm := Function.update T₁.isTerm u₁ 1 } := by
          dsimp only [T₂, PTrie.insertPat]; simp only [hpos', ↓reduceIte]; rfl
        have hM₃ : TrieMem inp T₂ x₃.mem := by
          rw [hx₃_mem, hT₂_eq]
          exact trieMem_insertPat_pos hu₁_maxS hM₂
        have hhold₃ : Block.HoldsList (x₂.regs r2) (encodePatterns ps) x₃.mem := by
          rw [hx₃_mem]
          refine hhold₂.frame fun addr ha1 ha2 => ?_
          have : x₂.regs r2 + (encodePatterns ps).length ≤ inp.textBase := by
            rw [hx₂_r2, hx₁_r2]
            simp only [List.length_cons, List.length_append] at hptr_ub
            omega
          simp (disch := omega) only [Function.update_of_ne]
        exact ⟨x₃, he_br, hL₃, hM₃, by rw [hx₃_rS, hx₂_rS, hT₂_eq], hx₃_r1, hx₃_r2, hhold₃⟩
      · have hpos' : ¬0 < (T.insertChars 0 p).2 := hpos
        have hcond : ¬(Cond.lt zero r4).Holds x₂ := by
          simp only [Cond.holds_lt, hL₂.h_zero, hx₂_r4]; exact hpos
        have hneg_tl : ∃ x₃, ExecWithin w (ram[ r1 ← r1 - one ]) x₂ x₃ 1 ∧
            x₃.regs rState = x₂.regs rState ∧ x₃.regs r1 = ps.length ∧
            x₃.regs r2 = x₂.regs r2 ∧ x₃.mem = x₂.mem := by
          refine WP.exists_execWithin ?_
          wram_exec [hL₂.h_one, hf_p1]
          exact ⟨by wram_simp, by wram_simp [hx₂_r1, hx₁_r1, hr1]; simp, by wram_simp,
            by wram_simp⟩
        obtain ⟨x₃, he_n, hx₃_rS, hx₃_r1, hx₃_r2, hx₃_mem⟩ := hneg_tl
        have he_br : ExecWithin w triePatBranchCode x₂ x₃ 4 :=
          (ExecWithin.branch_neg hcond he_n).mono (by omega)
        have hL₃ : LayoutInv inp x₃ := hL₂.of_preserves he_br
        have hT₂_eq : T₂ = T₁ := by
          dsimp only [T₂, PTrie.insertPat]; simp only [hpos', ↓reduceIte]; rfl
        refine ⟨x₃, he_br, hL₃, ?_,
          (hx₃_rS.trans hx₂_rS).trans (congrArg PTrie.numStates hT₂_eq.symm),
          hx₃_r1, hx₃_r2, ?_⟩
        · rwa [hx₃_mem, hT₂_eq]
        · rwa [hx₃_mem]
    obtain ⟨x₃, he_tl_br, hL₃, hM₃, hx₃_rS, hx₃_r1, hx₃_r2, hhold₃⟩ := hpat_tl
    have hT₂_inv : TreeInv inp.alphabetSize T₂ := by
      dsimp only [T₂, PTrie.insertPat]
      split_ifs with hp0
      · refine { hT₁_inv with
          term_zero := by dsimp only; rw [Function.update_of_ne (by omega)]; exact hT₁_inv.term_zero
          term_oob := fun z hz => by
            dsimp only [T₁, u₁] at hu₁_lt hz ⊢
            rw [Function.update_of_ne (by omega)]; exact hT₁_inv.term_oob z hz }
      · exact hT₁_inv
    have hT₂_num_eq : T₂.numStates = T₁.numStates := by
      dsimp only [T₂, PTrie.insertPat]; split_ifs <;> rfl
    obtain ⟨y, he_rest, hLy, hMy, hy_rS⟩ :=
      exec_triePatLoop inp w hw ps T₂ x₃ hL₃ hM₃ hT₂_inv
        (by rw [hT₂_num_eq]; simp only [totalPatternLen_cons] at hbud; omega)
        hx₃_rS hx₃_r1
        (by
          rw [hx₃_r2, hx₂_r2, hx₁_r2]
          simp only [List.length_cons, List.length_append] at hptr_ub
          omega)
        (by rwa [hx₃_r2]) hps_val
    refine ⟨y, (ExecWithin.loop_iter hc (he_hd.seq (he_chars.seq he_tl_br)) he_rest).mono
      (by simp only [totalPatternLen_cons, List.length_cons]; omega), hLy, hMy, hy_rS⟩

theorem exec_buildTrie (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) (x : Data 26)
    (hL : LayoutInv inp x) (hM : TrieMem inp PTrie.init x.mem) :
    ∃ y, ExecWithin w buildTrieCode x y
        (19 * inp.maxS + 11 * inp.patterns.length + 5) ∧
      LayoutInv inp y ∧
      TrieMem inp inp.trie y.mem := by
  have hlo := layout_order inp
  have hf1 : Fits w 1 := fits_of_le_outBase hw (by omega)
  have hinit : ∃ x₀, ExecWithin (B := .standard) w
      (ram[ rState ← #1; r1 ← numPat; r2 ← patBase ]) x x₀ 3 ∧
      x₀.regs rState = 1 ∧ x₀.regs r1 = inp.patterns.length ∧ x₀.regs r2 = 5 ∧
      x₀.mem = x.mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hf1, hL.h_numPat, hL.h_patBase]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x₀, he₀, hrS₀, hr1₀, hr2₀, hm₀⟩ := hinit
  have hL₀ : LayoutInv inp x₀ :=
    hL.of_preserves he₀
  obtain ⟨y, he_loop, hLy, hMy, _⟩ :=
    exec_triePatLoop inp w hw inp.patterns PTrie.init x₀ hL₀ (by rwa [hm₀])
      (treeInv_init _) (by dsimp only [PTrie.init]; omega)
      hrS₀ hr1₀
      (by rw [hr2₀, length_encodePatterns]; omega)
      (by rw [hr2₀, hm₀]; exact hM.pats) hvalid.1
  rw [Input.trie_eq]
  exact ⟨y, (he₀.seq he_loop).mono (by omega), hLy, hMy⟩

end Cslib.Algorithms.WordRAM.AhoCorasick
