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
        · rcases huc with ⟨rfl, rfl⟩
          simp
        · have hne_addr : inp.trieBase + u * inp.alphabetSize + c ≠
              inp.trieBase + u₀ * inp.alphabetSize + a := fun heq =>
            huc (Nat.eq_of_add_mul_eq (b := u) (b' := u₀) hc ha (by omega)).symm
          simp [huc, Function.update_of_ne hne_addr, hM.trie_cell u hu c hc]
      depth_cell := fun u hu => by
        rcases eq_or_ne u T.numStates with rfl | hus
        · simp
        · simp (disch := omega) [Function.update_of_ne, hM.depth_cell u hu]
      term_cell := fun u hu => by simp (disch := omega) [Function.update_of_ne, hM.term_cell u hu]
      zero_df := fun addr ha1 ha2 => by
        simp (disch := omega) [Function.update_of_ne, hM.zero_df addr ha1 ha2]
      zero_rest := fun addr ha1 ha2 => by
        simp (disch := omega) [Function.update_of_ne, hM.zero_rest addr ha1 ha2] }

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
        simp (disch := omega) [Function.update_of_ne, hM.trie_cell u hu c hc]
      depth_cell := fun u hu => by
        simp (disch := omega) [Function.update_of_ne, hM.depth_cell u hu]
      term_cell := fun u hu => by
        rcases eq_or_ne u u₁ with rfl | huu
        · simp
        · simp (disch := omega) [Function.update_of_ne, hM.term_cell u hu]
      zero_df := fun addr ha1 ha2 => by
        simp (disch := omega) [Function.update_of_ne, hM.zero_df addr ha1 ha2]
      zero_rest := fun addr ha1 ha2 => by
        simp (disch := omega) [Function.update_of_ne, hM.zero_rest addr ha1 ha2] }

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
    simp only [List.cons_append, List.length_cons, List.length_append] at hbud hr3 hptr_ub ⊢
    have hc : (Cond.lt zero r3).Holds x := by simp only [Cond.holds_lt, hL.h_zero, hr3]; omega
    have ha_lt : a < inp.alphabetSize := hchars a List.mem_cons_self
    obtain ⟨hm_a, hhold_tail⟩ := Block.holdsList_cons_iff.mp hhold
    simp only [List.append_eq] at hhold_tail
    have hu_maxS : x.regs r4 < inp.maxS := by omega
    have hrm_lt : x.regs r4 * inp.alphabetSize + a < inp.maxS * inp.alphabetSize :=
      Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu_maxS ha_lt
    have htrie_read :
        x.mem (inp.trieBase + (x.regs r4 * inp.alphabetSize + a)) = T.trie (x.regs r4) a := by
      rw [← Nat.add_assoc]; exact hM.trie_cell (x.regs r4) hu_maxS a ha_lt
    have hf_ptr1 : Fits w (x.regs r2 + 1) := fits_of_le_outBase hw (by omega)
    have hf_rem1 : Fits w (x.regs r3 - 1) := fits_of_le_outBase hw (by omega)
    have hf_mul : Fits w (x.regs r4 * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
    have hf_rm : Fits w (x.regs r4 * inp.alphabetSize + a) := fits_of_le_outBase hw (by omega)
    have hf_taddr : Fits w (inp.trieBase + (x.regs r4 * inp.alphabetSize + a)) :=
      fits_of_le_outBase hw (by omega)
    have hstep : ∃ x₂, ExecWithin w trieCharStepCode x x₂ 17 ∧
        TrieMem inp (T.stepChar (x.regs r4) a).1 x₂.mem ∧
        x₂.regs rState = (T.stepChar (x.regs r4) a).1.numStates ∧
        x₂.regs r4 = (T.stepChar (x.regs r4) a).2 ∧
        x₂.regs r2 = x.regs r2 + 1 ∧ x₂.regs r3 = as.length ∧ x₂.regs r1 = x.regs r1 ∧
        Block.HoldsList (x.regs r2 + 1) (as ++ rest) x₂.mem := by
      refine WP.exists_execWithin ?_
      unfold trieCharStepCode trieCharBranchCode
      by_cases h0 : T.trie (x.regs r4) a = 0
      · have hdu_le : T.depth (x.regs r4) < T.numStates :=
          lt_of_le_of_lt (depth_le_self hT _ hu_lt) hu_lt
        have hd_read : x.mem (inp.depthBase + x.regs r4) = T.depth (x.regs r4) :=
          hM.depth_cell (x.regs r4) hu_maxS
        have hf_dpu : Fits w (inp.depthBase + x.regs r4) := fits_of_le_outBase hw (by omega)
        have hf_du1 : Fits w (T.depth (x.regs r4) + 1) := fits_of_le_outBase hw (by omega)
        have hf_dps : Fits w (inp.depthBase + T.numStates) := fits_of_le_outBase hw (by omega)
        have hf_s1 : Fits w (T.numStates + 1) := fits_of_le_outBase hw (by omega)
        wram_exec [hm_a, hL.h_one, hL.h_sigma, hL.h_trieBase, hL.h_depthBase, htrie_read, h0, hrS,
          hd_read, hf_ptr1, hf_rem1, hf_mul, hf_rm, hf_taddr, hf_dpu, hf_du1, hf_dps, hf_s1]
        have hM' := trieMem_stepChar_new hu_maxS ha_lt (by omega) h0 hM
        simp only [PTrie.stepChar, h0, ↓reduceIte] at hM' ⊢
        refine ⟨by wram_simp; rw [← Nat.add_assoc]; exact hM', by wram_simp, by wram_simp,
          by wram_simp, by wram_simp [hr3], by wram_simp, hhold_tail.frame fun addr ha1 ha2 => ?_⟩
        rw [List.length_append] at ha2
        wram_simp
      · wram_exec [hm_a, hL.h_zero, hL.h_one, hL.h_sigma, hL.h_trieBase, htrie_read, h0, hf_ptr1,
          hf_rem1, hf_mul, hf_rm, hf_taddr]
        simp only [PTrie.stepChar, h0, ↓reduceIte]
        exact ⟨by wram_simp [hM], by wram_simp [hrS], by wram_simp, by wram_simp,
          by wram_simp [hr3], by wram_simp, by wram_simp [hhold_tail]⟩
    obtain ⟨hT_step, _, hub_step, _, hs_lt_step, _, _⟩ := stepChar_spec hT hu_lt ha_lt
    obtain ⟨x₂, he_st, hM₂, hx₂_rS, hx₂_r4, hx₂_r2, hx₂_r3, hx₂_r1, hhold₂⟩ := hstep
    obtain ⟨y, he_tl, hLy, hMy, hy_rS, hy_r4, hy_r2, hy_r1, hholdy⟩ :=
      ih rest _ x₂ (hL.of_preserves he_st) hM₂ hT_step (by omega) hx₂_rS (hx₂_r4 ▸ hs_lt_step)
        hx₂_r3 (by rw [hx₂_r2, List.length_append]; omega) (hx₂_r2 ▸ hhold₂)
        fun b hb => hchars b (List.mem_cons_of_mem a hb)
    rw [hx₂_r4] at hMy hy_rS hy_r4
    exact ⟨y, (ExecWithin.loop_iter hc he_st he_tl).mono (by omega), hLy, hMy, hy_rS, hy_r4,
      by omega, hy_r1.trans hx₂_r1, hholdy⟩

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
    dsimp only [encodePatterns] at hhold hptr_ub
    simp only [totalPatternLen_cons, List.length_cons, List.length_append, length_encodePatterns]
      at hbud hr1 hptr_ub ⊢
    have hc : (Cond.lt zero r1).Holds x := by simp only [Cond.holds_lt, hL.h_zero, hr1]; omega
    have hp_val : ∀ a ∈ p, a < inp.alphabetSize := hps p List.mem_cons_self
    obtain ⟨hm_plen, hhold_body⟩ := Block.holdsList_cons_iff.mp hhold
    have hf_ptr1 : Fits w (x.regs r2 + 1) := fits_of_le_outBase hw (by omega)
    have hpat_hd : ∃ x₁, ExecWithin w (ram[ r3 ← *r2; r2 ← r2 + one; r4 ← #0 ]) x x₁ 3 ∧
        x₁.regs r3 = p.length ∧ x₁.regs r2 = x.regs r2 + 1 ∧ x₁.regs r4 = 0 ∧
        x₁.regs rState = T.numStates ∧ x₁.regs r1 = x.regs r1 ∧ x₁.mem = x.mem := by
      refine WP.exists_execWithin ?_
      wram_exec [hm_plen, hL.h_one, hf_ptr1]
      wram_simp [hrS]
    obtain ⟨x₁, he_hd, hx₁_r3, hx₁_r2, hx₁_r4, hx₁_rS, hx₁_r1, hx₁_mem⟩ := hpat_hd
    obtain ⟨hT₁_inv, _, hub₁, hu₁_lt, _, _, _, _, _⟩ := insertChars_spec p T 0 hT hT.one_le hp_val
    obtain ⟨x₂, he_chars, hL₂, hM₂, hx₂_rS, hx₂_r4, hx₂_r2, hx₂_r1, hhold₂⟩ :=
      exec_trieCharLoop inp w hw p (encodePatterns ps) T x₁ (hL.of_preserves he_hd)
        (hx₁_mem ▸ hM) hT (by omega) hx₁_rS (hx₁_r4 ▸ hT.one_le) hx₁_r3
        (by rw [hx₁_r2, List.length_append, length_encodePatterns]; omega)
        (by rwa [hx₁_r2, hx₁_mem]) hp_val
    rw [hx₁_r4] at hM₂ hx₂_rS hx₂_r4
    have hu₁_maxS : (T.insertChars 0 p).2 < inp.maxS := by omega
    have hf_p1 : Fits w (x₂.regs r1 - 1) := fits_of_le_outBase hw (by omega)
    have hpat_tl : ∃ x₃, ExecWithin w triePatBranchCode x₂ x₃ 4 ∧
        TrieMem inp (T.insertPat p) x₃.mem ∧ x₃.regs rState = (T.insertPat p).numStates ∧
        x₃.regs r1 = ps.length ∧ x₃.regs r2 = x₂.regs r2 ∧
        Block.HoldsList (x₂.regs r2) (encodePatterns ps) x₃.mem := by
      refine WP.exists_execWithin ?_
      unfold triePatBranchCode
      by_cases hpos : 0 < (T.insertChars 0 p).2
      · have hf_taddr : Fits w (inp.termBase + (T.insertChars 0 p).2) :=
          fits_of_le_outBase hw (by omega)
        wram_exec [hL₂.h_zero, hL₂.h_termBase, hL₂.h_one, hx₂_r4, hpos, hf_taddr, hf_p1]
        simp only [PTrie.insertPat, hpos, ↓reduceIte]
        refine ⟨by wram_simp; exact trieMem_insertPat_pos hu₁_maxS hM₂, by wram_simp [hx₂_rS],
          by wram_simp [hx₂_r1, hx₁_r1, hr1], by wram_simp, hhold₂.frame fun addr ha1 ha2 => ?_⟩
        rw [length_encodePatterns] at ha2
        wram_simp
      · wram_exec [hL₂.h_zero, hL₂.h_one, hx₂_r4, hpos, hf_p1]
        simp only [PTrie.insertPat, hpos, ↓reduceIte]
        exact ⟨by wram_simp [hM₂], by wram_simp [hx₂_rS], by wram_simp [hx₂_r1, hx₁_r1, hr1],
          by wram_simp, by wram_simp [hhold₂]⟩
    obtain ⟨x₃, he_tl_br, hM₃, hx₃_rS, hx₃_r1, hx₃_r2, hhold₃⟩ := hpat_tl
    have hT₂_inv : TreeInv inp.alphabetSize (T.insertPat p) := by
      dsimp only [PTrie.insertPat]
      split_ifs with hp0
      · refine { hT₁_inv with
          term_zero := by dsimp only; rw [Function.update_of_ne (by omega)]; exact hT₁_inv.term_zero
          term_oob := fun z hz => by
            dsimp only at hz ⊢
            rw [Function.update_of_ne (by omega)]; exact hT₁_inv.term_oob z hz }
      · exact hT₁_inv
    have hT₂_num_eq : (T.insertPat p).numStates = (T.insertChars 0 p).1.numStates := by
      dsimp only [PTrie.insertPat]; split_ifs <;> rfl
    obtain ⟨y, he_rest, hLy, hMy, hy_rS⟩ :=
      exec_triePatLoop inp w hw ps _ x₃ (hL₂.of_preserves he_tl_br) hM₃
        hT₂_inv (by omega) hx₃_rS hx₃_r1
        (by rw [hx₃_r2, hx₂_r2, hx₁_r2, length_encodePatterns]; omega)
        (by rwa [hx₃_r2]) fun q hq => hps q (List.mem_cons_of_mem p hq)
    exact ⟨y, (ExecWithin.loop_iter hc (he_hd.seq (he_chars.seq he_tl_br)) he_rest).mono
      (by omega), hLy, hMy, hy_rS⟩

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
