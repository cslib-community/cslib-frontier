/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Phase3Mem
import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Phase4Step
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Phase 4b: Output Emission and Full Text Scan (`scanCode`)

Verifies `emitCode`, the full text-scanning loop `scanStepCode`, and `scanCode`, establishing that
the length-prefixed word list written at `Reg.out` equals
`encodeOccurrences (occurrences inp.patterns inp.text)` in at most
`38 * inp.text.length + 10 * (occurrences inp.patterns inp.text).length + 8` instructions.

## Main results

* `Cslib.Algorithms.WordRAM.AhoCorasick.exec_scanCode`: end-to-end execution proof for Phase 4.
-/

public section

namespace Cslib.Algorithms.WordRAM.AhoCorasick

open Cslib.WordRAM
open Cslib.Algorithms.Lean.AhoCorasick
open Reg

private theorem length_flatMap_pair (pos : ℕ) : ∀ ls : List ℕ,
    (ls.flatMap fun len => [pos, len]).length = 2 * ls.length
  | [] => rfl
  | l :: ls => by
    change ([pos, l] ++ ls.flatMap fun len => [pos, len]).length = 2 * (ls.length + 1)
    simp only [List.cons_append, List.nil_append, List.length_cons, length_flatMap_pair pos ls]
    omega

private theorem flatMap_length_eq_encodeOccurrences (pos : ℕ) : ∀ ys : List (List ℕ),
    (ys.map List.length).flatMap (fun len => [pos, len]) =
      encodeOccurrences (ys.map fun y => (pos, y))
  | [] => rfl
  | y :: ys => by
    change [pos, y.length] ++ (ys.map List.length).flatMap (fun len => [pos, len]) =
      [pos, y.length] ++ encodeOccurrences (ys.map fun y => (pos, y))
    rw [flatMap_length_eq_encodeOccurrences pos ys]

private theorem exec_emitLoop (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) :
    ∀ (fuel : ℕ) (acc : List ℕ) (x : Data 26),
      LayoutInv inp x →
      BFSMem inp inp.trie inp.bfs x.mem →
      x.regs r4 < inp.trie.numStates →
      (x.regs r4 = 0 ∨ inp.trie.depth (x.regs r4) < fuel) →
      x.regs r2 = inp.outBase + 1 + acc.length →
      Block.HoldsList (inp.outBase + 1) acc x.mem →
      acc.length + 2 * (followOut inp.trie.depth inp.bfs.outNext fuel (x.regs r4)).length ≤
        2 * (occurrences inp.patterns inp.text).length →
      ∃ y, ExecWithin w (.loop (.lt zero r4) emitStepCode) x y
          (10 * (followOut inp.trie.depth inp.bfs.outNext fuel (x.regs r4)).length + 2) ∧
        LayoutInv inp y ∧
        BFSMem inp inp.trie inp.bfs y.mem ∧
        Block.HoldsList (inp.outBase + 1)
          (acc ++ (followOut inp.trie.depth inp.bfs.outNext fuel (x.regs r4)).flatMap
            fun len => [x.regs r3, len])
          y.mem ∧
        y.regs r2 = inp.outBase + 1 + acc.length +
          2 * (followOut inp.trie.depth inp.bfs.outNext fuel (x.regs r4)).length ∧
        y.regs rState = x.regs rState ∧
        y.regs r1 = x.regs r1 ∧
        y.regs r3 = x.regs r3 := by
  intro fuel
  obtain ⟨_, hT_maxS, _, _, _⟩ := inp.trie_spec hvalid
  have hB := inp.bfs_spec hvalid
  have hlo := layout_order inp
  have hwb := wordBound_eq_outBase inp
  induction fuel <;> intro acc x hL hM hq_lt hfuel hr2 hhold hbud <;>
    rcases Nat.eq_zero_or_pos (x.regs r4) with hq0 | hqpos
  case zero.inr => omega
  case zero.inl | succ.inl =>
    have hstop : ¬(Cond.lt zero r4).Holds x := by simp [Cond.holds_lt, hL.h_zero, hq0]
    rw [hq0, followOut_zero_right]
    simp only [List.flatMap_nil, List.append_nil, List.length_nil, Nat.mul_zero, Nat.add_zero]
    exact ⟨x, ExecWithin.loop_exit hstop, hL, hM, hhold, hr2, rfl, rfl, rfl⟩
  case succ.inr fuel ih =>
    have hc : (Cond.lt zero r4).Holds x := by simpa [Cond.holds_lt, hL.h_zero] using hqpos
    rw [followOut_pos _ _ hqpos] at hbud ⊢
    simp only [List.length_cons] at hbud ⊢
    have hq_maxS : x.regs r4 < inp.maxS := lt_of_lt_of_le hq_lt hT_maxS
    obtain ⟨hqn_lt, hqn_dec⟩ := hB.outNext_spec (x.regs r4) hq_lt hqpos
    have hf_dp : Fits w (inp.depthBase + x.regs r4) := hw.of_le (by omega)
    have hf_p1 : Fits w (inp.outBase + 1 + acc.length + 1) := hw.of_le (by omega)
    have hf_p2 : Fits w (inp.outBase + 1 + acc.length + 1 + 1) := hw.of_le (by omega)
    have hf_on : Fits w (inp.outNextBase + x.regs r4) := hw.of_le (by omega)
    obtain ⟨x₁, he_st, hx₁_r4, hx₁_r2, hx₁_rS, hx₁_r1, hx₁_r3, hx₁_mem⟩ :
        ∃ x₁, ExecWithin w emitStepCode x x₁ 8 ∧
          x₁.regs r4 = inp.bfs.outNext (x.regs r4) ∧
          x₁.regs r2 = inp.outBase + 1 + acc.length + 2 ∧
          x₁.regs rState = x.regs rState ∧ x₁.regs r1 = x.regs r1 ∧ x₁.regs r3 = x.regs r3 ∧
          x₁.mem = Function.update
            (Function.update x.mem (inp.outBase + 1 + acc.length) (x.regs r3))
            (inp.outBase + 1 + acc.length + 1) (inp.trie.depth (x.regs r4)) :=
      WP.exists_execWithin <| by
        unfold emitStepCode
        wram_exec [hL.h_depthBase, hL.h_outNextBase, hL.h_one, hr2,
          hM.depth_cell _ hq_maxS, hM.outNext_cell _ hq_maxS, hf_dp, hf_p1, hf_p2, hf_on]
        exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
          by wram_simp⟩
    have hL₁ := hL.of_preserves he_st
    have hM₁ : BFSMem inp inp.trie inp.bfs x₁.mem :=
      bfsMem_of_eq_below_outBase hM fun addr hlt_ob => by
        rw [hx₁_mem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hhold₁ : Block.HoldsList (inp.outBase + 1)
        (acc ++ [x.regs r3, inp.trie.depth (x.regs r4)]) x₁.mem := by
      simpa only [hx₁_mem, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, Nat.add_assoc] using
        (hhold.append_one (x.regs r3)).append_one (inp.trie.depth (x.regs r4))
    have hdq : inp.trie.depth (x.regs r4) < fuel + 1 := hfuel.resolve_left (by omega)
    obtain ⟨y, he_tl, hLy, hMy, hholdy, hy_r2, hy_rS, hy_r1, hy_r3⟩ :=
      ih (acc ++ [x.regs r3, inp.trie.depth (x.regs r4)]) x₁ hL₁ hM₁
        (hx₁_r4 ▸ hqn_lt) (hx₁_r4 ▸ hqn_dec.imp_right fun _ => by omega)
        (by simp [hx₁_r2]; omega) hhold₁
        (by simp [hx₁_r4]; omega)
    rw [hx₁_r4] at he_tl hy_r2
    simp only [hx₁_r4, hx₁_r3, List.flatMap_cons, List.cons_append, List.nil_append,
      List.append_assoc] at hholdy ⊢
    exact ⟨y, (ExecWithin.loop_iter hc he_st he_tl).mono (by omega), hLy, hMy, hholdy,
      by simp [hy_r2]; omega, hy_rS.trans hx₁_rS, hy_r1.trans hx₁_r1, hy_r3.trans hx₁_r3⟩

private theorem exec_emitCode (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) (acc : List ℕ) (x : Data 26)
    (hL : LayoutInv inp x)
    (hM : BFSMem inp inp.trie inp.bfs x.mem)
    (hu_lt : x.regs rState < inp.trie.numStates)
    (hr2 : x.regs r2 = inp.outBase + 1 + acc.length)
    (hhold : Block.HoldsList (inp.outBase + 1) acc x.mem)
    (hbud : acc.length + 2 * (output inp.patterns (inp.trie.strOf (x.regs rState))).length ≤
      2 * (occurrences inp.patterns inp.text).length) :
    ∃ y, ExecWithin w emitCode x y
        (10 * (output inp.patterns (inp.trie.strOf (x.regs rState))).length + 4) ∧
      LayoutInv inp y ∧
      BFSMem inp inp.trie inp.bfs y.mem ∧
      Block.HoldsList (inp.outBase + 1)
        (acc ++ encodeOccurrences
          ((output inp.patterns (inp.trie.strOf (x.regs rState))).map fun p => (x.regs r3, p)))
        y.mem ∧
      y.regs r2 = inp.outBase + 1 + acc.length +
        2 * (output inp.patterns (inp.trie.strOf (x.regs rState))).length ∧
      y.regs rState = x.regs rState ∧
      y.regs r1 = x.regs r1 ∧
      y.regs r3 = x.regs r3 := by
  obtain ⟨hT, hT_maxS, _, _, _⟩ := inp.trie_spec hvalid
  have hB := inp.bfs_spec hvalid
  have hlo := layout_order inp
  have hu_maxS : x.regs rState < inp.maxS := lt_of_lt_of_le hu_lt hT_maxS
  obtain ⟨hoh_lt, _⟩ := hB.outHead_spec (x.regs rState) hu_lt
  have hoh_depth_lt : inp.trie.depth (inp.bfs.outHead (x.regs rState)) < inp.trie.numStates :=
    lt_of_le_of_lt (depth_le_self hT _ hoh_lt) hoh_lt
  have hfol_eq := hB.follow_spec (x.regs rState) hu_lt
  have hfol_len := (congrArg List.length hfol_eq).trans (List.length_map _)
  have hf_oh : Fits w (inp.outHeadBase + x.regs rState) := fits_of_le_outBase hw (by omega)
  have hld : ∃ x₀, ExecWithin w (ram[ r6 ← outHeadBase + rState; r4 ← *r6 ]) x x₀ 2 ∧
      x₀.regs r4 = inp.bfs.outHead (x.regs rState) ∧
      x₀.regs r2 = x.regs r2 ∧ x₀.regs rState = x.regs rState ∧
      x₀.regs r1 = x.regs r1 ∧ x₀.regs r3 = x.regs r3 ∧ x₀.mem = x.mem := WP.exists_execWithin <| by
    wram_exec [hL.h_outHeadBase, hM.outHead_cell _ hu_maxS, hf_oh]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x₀, he₀, hx₀_r4, hx₀_r2, hx₀_rS, hx₀_r1, hx₀_r3, hx₀_mem⟩ := hld
  have hL₀ := hL.of_preserves he₀
  obtain ⟨y, he_lp, hLy, hMy, hholdy, hy_r2, hy_rS, hy_r1, hy_r3⟩ :=
    exec_emitLoop inp w hvalid hw inp.trie.numStates acc x₀ hL₀ (by rwa [hx₀_mem])
      (by rw [hx₀_r4]; exact hoh_lt) (Or.inr (by rw [hx₀_r4]; exact hoh_depth_lt))
      (hx₀_r2.trans hr2) (by rwa [hx₀_mem])
      (by rw [hx₀_r4, hfol_len]; exact hbud)
  rw [hx₀_r4, hx₀_r3, hfol_eq, flatMap_length_eq_encodeOccurrences] at hholdy
  rw [hx₀_r4, hfol_len] at he_lp hy_r2
  exact ⟨y, (he₀.seq he_lp).mono (by omega), hLy, hMy, hholdy, hy_r2,
    hy_rS.trans hx₀_rS, hy_r1.trans hx₀_r1, hy_r3.trans hx₀_r3⟩

private theorem exec_scanLoop (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) :
    ∀ (ts pref : List ℕ) (x : Data 26),
      pref ++ ts = inp.text →
      LayoutInv inp x →
      BFSMem inp inp.trie inp.bfs x.mem →
      x.regs rState < inp.trie.numStates →
      inp.trie.strOf (x.regs rState) = longestNodeSuffix inp.patterns pref →
      x.regs r1 = pref.length →
      x.regs r2 = inp.outBase + 1 + 2 * (occurrences inp.patterns pref).length →
      Block.HoldsList (inp.outBase + 1) (encodeOccurrences (occurrences inp.patterns pref)) x.mem →
      ∃ y, ExecWithin w (.loop (.lt r1 textLen) scanStepCode) x y
          (13 * inp.trie.depth (x.regs rState) + 38 * ts.length +
            10 * ((occurrences inp.patterns inp.text).length -
              (occurrences inp.patterns pref).length) + 2) ∧
        LayoutInv inp y ∧
        BFSMem inp inp.trie inp.bfs y.mem ∧
        Block.HoldsList (inp.outBase + 1)
          (encodeOccurrences (occurrences inp.patterns inp.text)) y.mem ∧
        y.regs r2 = inp.outBase + 1 + 2 * (occurrences inp.patterns inp.text).length := by
  intro ts
  have hlo := layout_order inp
  induction ts with
  | nil =>
    intro pref x hpt hL hM _ _ hr1 hr2 hhold
    obtain rfl : pref = inp.text := by simpa using hpt
    have hstop : ¬(Cond.lt r1 textLen).Holds x := by simp [Cond.holds_lt, hr1, hL.h_textLen]
    exact ⟨x, (ExecWithin.loop_exit hstop).mono (by omega), hL, hM, hhold, hr2⟩
  | cons a ts ih =>
    intro pref x hpt hL hM hu_lt hu_str hr1 hr2 hhold
    have ht_len : pref.length + (ts.length + 1) = inp.text.length := by
      simpa using congrArg List.length hpt
    have hc : (Cond.lt r1 textLen).Holds x := by simp [Cond.holds_lt, hr1, hL.h_textLen]; omega
    have ha_lt : a < inp.alphabetSize :=
      hvalid.2 a (hpt ▸ List.mem_append_right _ List.mem_cons_self)
    have ht_hold : Block.HoldsList inp.textBase (pref ++ a :: ts) x.mem := hpt ▸ hM.txt
    have ht_read : x.mem (inp.textBase + pref.length) = a :=
      (Block.holdsList_cons_iff.mp (Block.holdsList_append_iff.mp ht_hold).2).1
    have hf_taddr : Fits w (inp.textBase + pref.length) := fits_of_le_outBase hw (by omega)
    have hf_pos : Fits w (pref.length + 1) := fits_of_le_outBase hw (by omega)
    have hhd : ∃ x₁, ExecWithin w
        (ram[ r6 ← textBase + r1; r5 ← *r6; r3 ← r1 + one ]) x x₁ 3 ∧
        x₁.regs rState = x.regs rState ∧ x₁.regs r1 = pref.length ∧
        x₁.regs r2 = x.regs r2 ∧ x₁.regs r3 = pref.length + 1 ∧
        x₁.regs r5 = a ∧ x₁.mem = x.mem := WP.exists_execWithin <| by
      wram_exec [hL.h_textBase, hL.h_one, hr1, ht_read, hf_taddr, hf_pos]
      exact ⟨by wram_simp, by wram_simp [hr1], by wram_simp, by wram_simp, by wram_simp,
        by wram_simp⟩
    obtain ⟨x₁, he_hd, hs1, h11, h21, h31, h51, hm1⟩ := hhd
    have hL₁ := hL.of_preserves he_hd
    obtain ⟨x₂, u', hu'_lt, he_st, hL₂, hm2, hs2, hu'_str, hu'_depth, h12, h22, h32, _⟩ :=
      exec_stepCode inp w hvalid hw x₁ hL₁ (by rwa [hm1]) (by rw [hs1]; exact hu_lt)
        (by rw [h51]; exact ha_lt)
    rw [hs1] at he_st hu'_depth
    have hu'_lns : inp.trie.strOf u' = longestNodeSuffix inp.patterns (pref ++ [a]) := by
      rw [hu'_str, hs1, h51, hu_str, ← longestNodeSuffix_append_singleton_eq_nextMove]
    have hout_eq : output inp.patterns (inp.trie.strOf u') = output inp.patterns (pref ++ [a]) := by
      rw [hu'_lns, output_longestNodeSuffix]
    have hocc_pref_le : (occurrences inp.patterns (pref ++ [a])).length ≤
        (occurrences inp.patterns inp.text).length := by
      simpa [List.append_assoc, hpt] using
        (occurrences_prefix_append inp.patterns (pref ++ [a]) ts).length_le
    have hocc_next_len : (occurrences inp.patterns (pref ++ [a])).length =
        (occurrences inp.patterns pref).length + (output inp.patterns (pref ++ [a])).length := by
      simp [occurrences_append_singleton]
    obtain ⟨x₃, he_em, hL₃, hM₃, hhold₃, hr2₃, hs3, _, hr3₃⟩ :=
      exec_emitCode inp w hvalid hw (encodeOccurrences (occurrences inp.patterns pref)) x₂
        hL₂ (by rwa [hm2, hm1]) (by rw [hs2]; exact hu'_lt)
        (by rw [h22, h21, hr2, length_encodeOccurrences])
        (by rwa [hm2, hm1])
        (by rw [hs2, hout_eq, length_encodeOccurrences]; omega)
    rw [hs2, hout_eq] at he_em hhold₃ hr2₃
    rw [h32, h31, ← encodeOccurrences_append, ← occurrences_append_singleton] at hhold₃
    rw [length_encodeOccurrences] at hr2₃
    set x₄ := x₃.set r1 (pref.length + 1)
    have he_adv : ExecWithin (B := .standard) w (ram[ r1 ← r3 ]) x₃ x₄ 1 := WP.execWithin <| by
      wram_exec
      wram_simp [x₄, hr3₃, h32, h31]
    have hs4 : x₄.regs rState = u' := by wram_simp [x₄, hs3, hs2]
    have h14 : x₄.regs r1 = (pref ++ [a]).length := by simp [x₄]
    have h24 : x₄.regs r2 =
        inp.outBase + 1 + 2 * (occurrences inp.patterns (pref ++ [a])).length := by
      have hr2_eq : x₄.regs r2 = x₃.regs r2 := by wram_simp [x₄]
      rw [hr2_eq, hr2₃, hocc_next_len]; omega
    obtain ⟨y, he_tl, hLy, hMy, hholdy, hy_r2⟩ :=
      ih (pref ++ [a]) x₄ (by rw [List.append_assoc, List.singleton_append, hpt])
        (hL₃.of_preserves he_adv) hM₃ (hs4 ▸ hu'_lt) (hs4 ▸ hu'_lns)
        h14 h24 hhold₃
    rw [hs4] at he_tl
    exact ⟨y, (ExecWithin.loop_iter hc (he_hd.seq (he_st.seq (he_em.seq he_adv))) he_tl).mono
      (by simp only [List.length_cons]; omega), hLy, hMy, hholdy, hy_r2⟩

theorem exec_scanCode (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) (x : Data 26)
    (hL : LayoutInv inp x)
    (hM : BFSMem inp inp.trie inp.bfs x.mem) :
    ∃ y, ExecWithin w scanCode x y
        (38 * inp.text.length + 10 * (occurrences inp.patterns inp.text).length + 8) ∧
      LayoutInv inp y ∧
      outputList y.mem (y.regs out) =
        encodeOccurrences (occurrences inp.patterns inp.text) := by
  obtain ⟨hT, _, _, _, _⟩ := inp.trie_spec hvalid
  have hlo := layout_order inp
  have hwb := wordBound_eq_outBase inp
  have hf_ob1 : Fits w (inp.outBase + 1) := hw.of_le (by omega)
  have hinit : ∃ x₀, ExecWithin w (ram[ rState ← #0; r1 ← #0; r2 ← out + one ]) x x₀ 3 ∧
      x₀.regs rState = 0 ∧ x₀.regs r1 = 0 ∧ x₀.regs r2 = inp.outBase + 1 ∧ x₀.mem = x.mem :=
    WP.exists_execWithin <| by
      wram_exec [hL.h_out, hL.h_one, hf_ob1]
      exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x₀, he₀, hs0, h10, h20, hm0⟩ := hinit
  have hL₀ := hL.of_preserves he₀
  obtain ⟨x₁, he_lp, hL₁, _, hhold₁, hr2₁⟩ :=
    exec_scanLoop inp w hvalid hw inp.text [] x₀ (List.nil_append _) hL₀ (by rwa [hm0])
      (by rw [hs0]; exact hT.one_le)
      (by rw [hs0, hT.str_zero, longestNodeSuffix_nil])
      h10
      (by rw [h20, occurrences_nil, List.length_nil, Nat.mul_zero, Nat.add_zero])
      (by rw [occurrences_nil, encodeOccurrences_nil]; exact Block.holdsList_nil _ _)
  rw [hs0, hT.depth_zero, occurrences_nil, List.length_nil, Nat.sub_zero, Nat.mul_zero,
    Nat.zero_add] at he_lp
  have hf_sub : Fits w (x₁.regs r2 - (inp.outBase + 1)) := hw.of_le (by rw [hr2₁]; omega)
  have hfin : ∃ y, ExecWithin w (ram[ r6 ← out + one; r6 ← r2 - r6; *out ← r6 ]) x₁ y 3 ∧
      y.mem = Function.update x₁.mem inp.outBase
        (2 * (occurrences inp.patterns inp.text).length) := WP.exists_execWithin <| by
    wram_exec [hL₁.h_out, hL₁.h_one, hf_ob1, hf_sub]
    wram_simp [hr2₁]
  obtain ⟨y, he_fin, hy_mem⟩ := hfin
  have hLy := hL₁.of_preserves he_fin
  refine ⟨y, (he₀.seq (he_lp.seq he_fin)).mono (by omega), hLy, ?_⟩
  rw [hLy.h_out, hy_mem, outputList_eq_iff]
  exact ⟨by rw [Function.update_self, length_encodeOccurrences],
    hhold₁.frame fun a ha _ => Function.update_of_ne (by omega) _ _⟩

end Cslib.Algorithms.WordRAM.AhoCorasick
