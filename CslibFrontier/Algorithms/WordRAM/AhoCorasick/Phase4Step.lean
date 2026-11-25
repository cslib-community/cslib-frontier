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
# Phase 4a: Amortized Failure-Link Transition Step (`stepCode`)

Verifies `stepCode` (`Algorithm 1` of `[AhoCorasick1975]`): follows failure links using the
failure-depth potential `depth[u]` (`Theorem 2`) to compute the next automaton state in amortized
constant time (`17 * (depth[u] - depth[u']) + 20` instructions, independent of `σ`).

## Main results

* `Cslib.Algorithms.WordRAM.AhoCorasick.exec_stepCode`: execution and amortized potential proof
  for one character transition of `scanCode`.
-/

public section

namespace Cslib.Algorithms.WordRAM.AhoCorasick

open Cslib.WordRAM
open Cslib.Algorithms.Lean.AhoCorasick
open Reg

/-! ## Phase 4: Amortized text scanning (`scanCode`) -/

private theorem exec_computeFailCond (inp : Input) (w : ℕ) (hw : Fits w inp.wordBound)
    {T : PTrie} {B : PBFS} {x : Data 26}
    (hL : LayoutInv inp x) (hM : BFSMem inp T B x.mem)
    (hu : x.regs rState < inp.maxS) (ha : x.regs r5 < inp.alphabetSize) :
    ∃ y, ExecWithin w computeFailCond x y 9 ∧
      LayoutInv inp y ∧
      y.mem = x.mem ∧
      y.regs rState = x.regs rState ∧
      y.regs r1 = x.regs r1 ∧
      y.regs r2 = x.regs r2 ∧
      y.regs r3 = x.regs r3 ∧
      y.regs r5 = x.regs r5 ∧
      y.regs r7 =
        (if 0 < x.regs rState ∧ T.trie (x.regs rState) (x.regs r5) = 0 then 1 else 0) := by
  have hlo := layout_order inp
  have hrm := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu ha
  have hf1 : Fits w 1 := fits_of_le_outBase hw (by omega)
  have hf_m : Fits w (x.regs rState * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
  have hf_a : Fits w (x.regs rState * inp.alphabetSize + x.regs r5) :=
    fits_of_le_outBase hw (by omega)
  have hf_t : Fits w (inp.trieBase + (x.regs rState * inp.alphabetSize + x.regs r5)) :=
    fits_of_le_outBase hw (by omega)
  have ht_read : x.mem (inp.trieBase + (x.regs rState * inp.alphabetSize + x.regs r5)) =
      T.trie (x.regs rState) (x.regs r5) := by
    rw [← Nat.add_assoc]; exact hM.trie_cell _ hu _ ha
  obtain ⟨y, he, hy⟩ : ∃ y, ExecWithin w computeFailCond x y 9 ∧ y.mem = x.mem ∧
      y.regs rState = x.regs rState ∧ y.regs r1 = x.regs r1 ∧ y.regs r2 = x.regs r2 ∧
      y.regs r3 = x.regs r3 ∧ y.regs r5 = x.regs r5 ∧
      y.regs r7 =
        (if 0 < x.regs rState ∧ T.trie (x.regs rState) (x.regs r5) = 0 then 1 else 0) := by
    refine WP.exists_execWithin ?_
    unfold computeFailCond
    by_cases hupos : 0 < x.regs rState
    · wram_exec [hL.h_sigma, hL.h_trieBase, hL.h_zero, hupos, ht_read, hf1, hf_m, hf_a, hf_t]
      all_goals exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
        by wram_simp, by wram_simp; split_ifs <;> omega⟩
    · wram_exec [hL.h_zero, hupos]
      exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
        by wram_simp [hupos, false_and]⟩
  exact ⟨y, he, hL.of_preserves he, hy⟩

private theorem exec_failLoop (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) :
    ∀ (d : ℕ) (x : Data 26),
      LayoutInv inp x →
      BFSMem inp inp.trie inp.bfs x.mem →
      x.regs rState < inp.trie.numStates →
      inp.trie.depth (x.regs rState) = d →
      x.regs r5 < inp.alphabetSize →
      x.regs r7 =
        (if 0 < x.regs rState ∧ inp.trie.trie (x.regs rState) (x.regs r5) = 0 then 1 else 0) →
      ∃ y, ∃ u_exit < inp.trie.numStates,
        ExecWithin w
          (.loop (.lt zero r7)
            (.seq (ram[ r6 ← failBase + rState; rState ← *r6 ]) computeFailCond))
          x y (13 * (d - inp.trie.depth u_exit) + 2) ∧
        LayoutInv inp y ∧
        y.mem = x.mem ∧
        y.regs rState = u_exit ∧
        inp.trie.depth u_exit ≤ d ∧
        ¬(0 < u_exit ∧ inp.trie.trie u_exit (x.regs r5) = 0) ∧
        nextMove inp.patterns (inp.trie.strOf u_exit) (x.regs r5) =
          nextMove inp.patterns (inp.trie.strOf (x.regs rState)) (x.regs r5) ∧
        y.regs r1 = x.regs r1 ∧
        y.regs r2 = x.regs r2 ∧
        y.regs r3 = x.regs r3 ∧
        y.regs r5 = x.regs r5 := by
  intro d
  obtain ⟨hT, hT_maxS, _, _, _⟩ := inp.trie_spec hvalid
  have hchar := inp.char_iff hvalid
  have hB := inp.bfs_spec hvalid
  have hlo := layout_order inp
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro x hL hM hu_lt hd_eq ha_lt hr7
    by_cases hgo : 0 < x.regs rState ∧ inp.trie.trie (x.regs rState) (x.regs r5) = 0
    · obtain ⟨hupos, ht0⟩ := hgo
      have hc : (Cond.lt zero r7).Holds x := by
        simp only [Cond.holds_lt, hL.h_zero, hr7, hupos, ht0, and_self, ↓reduceIte]
        exact Nat.zero_lt_one
      obtain ⟨hfu_lt, hfu_str, hfu_depth⟩ := hB.fail_spec (x.regs rState) hu_lt hupos
      have hu_maxS : x.regs rState < inp.maxS := lt_of_lt_of_le hu_lt hT_maxS
      have hfu_maxS : inp.bfs.fail (x.regs rState) < inp.maxS := lt_of_lt_of_le hfu_lt hT_maxS
      have hf_read : x.mem (inp.failBase + x.regs rState) = inp.bfs.fail (x.regs rState) :=
        hM.fail_cell _ hu_maxS
      have hf_addr : Fits w (inp.failBase + x.regs rState) := fits_of_le_outBase hw (by omega)
      have hhop : ∃ x₁, ExecWithin w (ram[ r6 ← failBase + rState; rState ← *r6 ]) x x₁ 2 ∧
          x₁.regs rState = inp.bfs.fail (x.regs rState) ∧
          x₁.regs r1 = x.regs r1 ∧ x₁.regs r2 = x.regs r2 ∧ x₁.regs r3 = x.regs r3 ∧
          x₁.regs r5 = x.regs r5 ∧ x₁.mem = x.mem := by
        refine WP.exists_execWithin ?_
        wram_exec [hL.h_failBase, hf_read, hf_addr]
        exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
      obtain ⟨x₁, he_hop, hs1, h11, h21, h31, h51, hm1⟩ := hhop
      have hL₁ := hL.of_preserves he_hop
      obtain ⟨x₂, he_cond, hL₂, hm2, hs2, h12, h22, h32, h52, hr7_2⟩ :=
        exec_computeFailCond inp w hw hL₁ (by rwa [hm1]) (by rw [hs1]; exact hfu_maxS)
          (by rw [h51]; exact ha_lt)
      rw [hs1, h51] at hr7_2
      have hfu_d_lt : inp.trie.depth (inp.bfs.fail (x.regs rState)) < d := by rwa [← hd_eq]
      obtain ⟨y, u_exit, hu_ex_lt, he_tl, hLy, hmy, hsy, hd_ex, hstop_ex, hnm_ex,
        h1y, h2y, h3y, h5y⟩ :=
        ih (inp.trie.depth (inp.bfs.fail (x.regs rState))) hfu_d_lt x₂ hL₂ (by rwa [hm2, hm1])
          (by rw [hs2, hs1]; exact hfu_lt) (by rw [hs2, hs1])
          (by rw [h52, h51]; exact ha_lt) (by rw [hs2, hs1, h52, h51]; exact hr7_2)
      rw [h52, h51] at hstop_ex hnm_ex
      rw [hs2, hs1] at hnm_ex
      have hnot_node : ¬IsNode inp.patterns (inp.trie.strOf (x.regs rState) ++ [x.regs r5]) := by
        intro his
        have hpos_t := (hchar _ hu_lt _ ha_lt).1 his
        omega
      have hnm_step :
          nextMove inp.patterns (inp.trie.strOf (x.regs rState)) (x.regs r5) =
            nextMove inp.patterns (inp.trie.strOf (inp.bfs.fail (x.regs rState))) (x.regs r5) := by
        rw [hfu_str]
        exact nextMove_of_not_isNode hnot_node (hT.str_ne_nil _ hupos hu_lt)
      refine ⟨y, u_exit, hu_ex_lt,
        (ExecWithin.loop_iter hc (he_hop.seq he_cond) he_tl).mono (by omega),
        hLy, hmy.trans (hm2.trans hm1), hsy, by omega, hstop_ex, hnm_ex.trans hnm_step.symm,
        h1y.trans (h12.trans h11), h2y.trans (h22.trans h21),
        h3y.trans (h32.trans h31), h5y.trans (h52.trans h51)⟩
    · have hstop : ¬(Cond.lt zero r7).Holds x := by
        simp only [Cond.holds_lt, hL.h_zero, hr7, hgo, ↓reduceIte]; omega
      exact ⟨x, x.regs rState, hu_lt,
        (ExecWithin.loop_exit hstop).mono (by rw [hd_eq, Nat.sub_self]),
        hL, rfl, rfl, le_of_eq hd_eq, hgo, rfl, rfl, rfl, rfl, rfl⟩

theorem exec_stepCode (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) (x : Data 26)
    (hL : LayoutInv inp x)
    (hM : BFSMem inp inp.trie inp.bfs x.mem)
    (hu_lt : x.regs rState < inp.trie.numStates)
    (ha_lt : x.regs r5 < inp.alphabetSize) :
    ∃ y, ∃ u' < inp.trie.numStates,
      ExecWithin w stepCode x y
        (13 * (inp.trie.depth (x.regs rState) + 1 - inp.trie.depth u') + 15) ∧
      LayoutInv inp y ∧
      y.mem = x.mem ∧
      y.regs rState = u' ∧
      inp.trie.strOf u' = nextMove inp.patterns (inp.trie.strOf (x.regs rState)) (x.regs r5) ∧
      inp.trie.depth u' ≤ inp.trie.depth (x.regs rState) + 1 ∧
      y.regs r1 = x.regs r1 ∧
      y.regs r2 = x.regs r2 ∧
      y.regs r3 = x.regs r3 ∧
      y.regs r5 = x.regs r5 := by
  obtain ⟨hT, hT_maxS, hnode, _, _⟩ := inp.trie_spec hvalid
  have hchar := inp.char_iff hvalid
  have hlo := layout_order inp
  obtain ⟨x₁, he_c0, hL₁, hm1, hs1, h11, h21, h31, h51, hr7_1⟩ :=
    exec_computeFailCond inp w hw hL hM (lt_of_lt_of_le hu_lt hT_maxS) ha_lt
  obtain ⟨x₂, u_ex, hu_ex_lt, he_fl, hL₂, hm2, hs2, hd_ex, hstop_ex, hnm_ex,
    h12, h22, h32, h52⟩ :=
    exec_failLoop inp w hvalid hw (inp.trie.depth (x.regs rState)) x₁ hL₁ (by rwa [hm1])
      (by rw [hs1]; exact hu_lt) (by rw [hs1]) (by rw [h51]; exact ha_lt)
      (by rw [hs1, h51]; exact hr7_1)
  rw [h51] at hstop_ex hnm_ex
  rw [hs1] at hnm_ex
  set a := x.regs r5
  set u' := inp.trie.trie u_ex a
  have hu'_lt : u' < inp.trie.numStates := hT.trie_lt u_ex hu_ex_lt a ha_lt
  have hu_ex_maxS : u_ex < inp.maxS := lt_of_lt_of_le hu_ex_lt hT_maxS
  have hrm := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu_ex_maxS ha_lt
  have ht_read : x₂.mem (inp.trieBase + (u_ex * inp.alphabetSize + a)) = u' := by
    rw [hm2, hm1, ← Nat.add_assoc]; exact hM.trie_cell u_ex hu_ex_maxS a ha_lt
  have hf_m : Fits w (u_ex * inp.alphabetSize) := fits_of_le_outBase hw (by omega)
  have hf_a : Fits w (u_ex * inp.alphabetSize + a) := fits_of_le_outBase hw (by omega)
  have hf_t : Fits w (inp.trieBase + (u_ex * inp.alphabetSize + a)) :=
    fits_of_le_outBase hw (by omega)
  have hfin : ∃ y, ExecWithin w (ram[
      r6 ← rState * sigma; r6 ← r6 + r5; r6 ← trieBase + r6; rState ← *r6 ]) x₂ y 4 ∧
      y.regs rState = u' ∧ y.regs r1 = x₂.regs r1 ∧ y.regs r2 = x₂.regs r2 ∧
      y.regs r3 = x₂.regs r3 ∧ y.regs r5 = x₂.regs r5 ∧ y.mem = x₂.mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hL₂.h_sigma, hL₂.h_trieBase, hs2, h52, h51, ht_read, hf_m, hf_a, hf_t]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨y, he_fin, hsy, h1y, h2y, h3y, h5y, hmy⟩ := hfin
  have hLy := hL₂.of_preserves he_fin
  have hu'_props :
      inp.trie.strOf u' = nextMove inp.patterns (inp.trie.strOf u_ex) a ∧
        inp.trie.depth u' ≤ inp.trie.depth u_ex + 1 := by
    rcases hT.trie_spec u_ex hu_ex_lt a ha_lt with h0 | ⟨_, hstr⟩
    · have hu_ex0 : u_ex = 0 := by omega
      subst hu_ex0
      have hnot_node : ¬IsNode inp.patterns ([] ++ [a]) := by
        intro his
        have hp := (hchar 0 hT.one_le a ha_lt).1 (by rwa [hT.str_zero])
        omega
      have hu'0 : u' = 0 := h0
      rw [hu'0, hT.str_zero, hT.depth_zero, nextMove_of_not_isNode_of_eq_nil hnot_node rfl]
      exact ⟨rfl, Nat.zero_le _⟩
    · have hnode_u' : IsNode inp.patterns (inp.trie.strOf u_ex ++ [a]) := by
        rw [← hstr]; exact hnode u' hu'_lt
      refine ⟨hstr.trans (nextMove_of_isNode hnode_u').symm, ?_⟩
      rw [hT.depth_eq u' hu'_lt, hstr, List.length_append, List.length_singleton,
        ← hT.depth_eq u_ex hu_ex_lt]
  refine ⟨y, u', hu'_lt,
    (he_c0.seq (he_fl.seq he_fin)).mono (by have := hu'_props.2; omega),
    hLy, hmy.trans (hm2.trans hm1), hsy, hu'_props.1.trans hnm_ex, by have := hu'_props.2; omega,
    h1y.trans (h12.trans h11), h2y.trans (h22.trans h21),
    h3y.trans (h32.trans h31), h5y.trans (h52.trans h51)⟩

end Cslib.Algorithms.WordRAM.AhoCorasick
