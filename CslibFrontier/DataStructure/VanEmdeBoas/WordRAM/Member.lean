/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Model
public import CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Native van Emde Boas membership descent

The proof state records only the registers required by membership; all other registers and
all memory outside the represented tree may be arbitrary. Queries need not belong to the
tree universe. The maximum guard is checked before any cluster address is calculated.

## Main definitions

* `MemberEntry`: the membership-loop register invariant.

## Main results

* `memberLoop_spec`: membership takes at most `28 * (d + 1) + 2` loop instructions,
  gives the functional answer and preserves all memory.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.DataStructure.VanEmdeBoas.WordRAM

open Cslib.WordRAM
open Cslib.DataStructure.VanEmdeBoas

/-- The constant, traversal and result registers at entry to an unfinished lookup. -/
structure MemberEntry (base query : ℕ) (s : Data 32) : Prop where
  zero_eq : s.regs zero = 0
  one_eq : s.regs one = 1
  two_eq : s.regs two = 2
  three_eq : s.regs three = 3
  four_eq : s.regs four = 4
  five_eq : s.regs five = 5
  p_eq : s.regs p = base
  x_eq : s.regs x = query
  out_eq : s.regs out = 0
  runFlag_eq : s.regs runFlag = 1

/-- A query above the cached maximum is absent; this fact uses validity, not outside memory. -/
theorem member_eq_false_of_max_lt {d m M query : ℕ} {tree : Tree d}
    (ht : tree.Valid) (hb : tree.bounds = some (m, M)) (hx : M < query) :
    tree.member query = false := by
  have hnot : ¬tree.Contains query := by
    intro hc
    have := ((ht.extrema_of_bounds hb).2.2.2.2 query hc).2
    omega
  cases he : tree.member query
  · rfl
  · exact False.elim (hnot ((Tree.member_iff_contains ht query).mp he))

/-- The cached maximum is a valid early successful membership result. -/
theorem member_maximum {d m M : ℕ} {tree : Tree d}
    (ht : tree.Valid) (hb : tree.bounds = some (m, M)) : tree.member M = true :=
  (Tree.member_iff_contains ht M).mpr (ht.contains_maximum hb)

/-- Terminate `memberLoop` in one `memberBody` pass when the body clears `runFlag` while
preserving `zero = 0` and memory. -/
private theorem memberLoop_finish {d w base query answer : ℕ} {s : Data 32}
    (hs : MemberEntry base query s)
    (hstep : ∃ s₁, ExecWithin w memberBody s s₁ 26 ∧
      s₁.regs zero = 0 ∧ s₁.regs runFlag = 0 ∧ s₁.regs out = answer ∧ s₁.mem = s.mem) :
    ∃ z, ExecWithin w memberLoop s z (28 * (d + 1) + 2) ∧
      z.regs out = answer ∧ z.mem = s.mem := by
  obtain ⟨s₁, he, hz0, hk, hout, hmem⟩ := hstep
  refine ⟨s₁, (he.loop_once (cond := .lt zero runFlag) ?_ ?_).mono (by omega), hout, hmem⟩
  · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
    decide
  · simp only [Cond.holds_lt, hz0, hk, lt_self_iff_false, not_false_eq_true]

/-- The membership loop is correct for every depth and arbitrary surrounding memory.
Its bound charges each body, loop test and jump; setup, dispatch and halt are separate. -/
theorem memberLoop_spec {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : MemberEntry base query s) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) :
    ∃ z, ExecWithin w memberLoop s z (28 * (d + 1) + 2) ∧
      z.regs out = (if tree.member query then 1 else 0) ∧ z.mem = s.mem := by
  obtain ⟨hz, ho, htwo, hthree, hfour, hfive, hp, hx, hout0, hrun⟩ := hs
  have hbase4 : Fits w (base + 4) := ha.of_le (by have := five_le_span d; omega)
  have hheader := hr.header
  rcases hb : tree.bounds with _ | ⟨m, M⟩ <;> rw [hb] at hheader
  · have he : s.mem base = 0 := hheader.1
    have hmem_f : tree.member query = false := by
      cases tree <;> simp_all [Tree.bounds, Tree.member]
    apply memberLoop_finish ⟨hz, ho, htwo, hthree, hfour, hfive, hp, hx, hout0, hrun⟩
    apply WP.exists_execWithin
    unfold memberBody
    wram_exec [hp, hz, he]
    exact ⟨by wram_simp [hz], by wram_simp,
      by wram_simp [hout0, hmem_f, Bool.false_eq_true, ↓reduceIte], by wram_simp⟩
  obtain ⟨he_raw, ⟨hm, hM⟩, hq, hspan⟩ := hheader
  have he : s.mem base = 1 := he_raw
  by_cases heq : query = m
  · have hmem_t : tree.member query = true := by
      cases tree <;> simp_all [Tree.bounds, Tree.member]
    apply memberLoop_finish ⟨hz, ho, htwo, hthree, hfour, hfive, hp, hx, hout0, hrun⟩
    apply WP.exists_execWithin
    unfold memberBody readAt
    wram_exec [hp, hx, hz, ho, he, hm, heq]
    exact ⟨by wram_simp [hz], by wram_simp, by wram_simp [hmem_t, ↓reduceIte], by wram_simp⟩
  by_cases heq' : query = M
  · have hneM : M ≠ m := by simpa only [heq'] using heq
    have hmem_t : tree.member query = true := heq' ▸ member_maximum ht hb
    apply memberLoop_finish ⟨hz, ho, htwo, hthree, hfour, hfive, hp, hx, hout0, hrun⟩
    apply WP.exists_execWithin
    unfold memberBody readAt
    wram_exec [hp, hx, hz, ho, htwo, he, hm, hM, heq, heq', hneM]
    exact ⟨by wram_simp [hz], by wram_simp, by wram_simp [hmem_t, ↓reduceIte], by wram_simp⟩
  by_cases hlt : query < M
  · cases tree with
    | leaf b =>
      obtain rfl : b = some (m, M) := hb
      have hmem_f : (Tree.leaf (some (m, M))).member query = false := by
        simp [Tree.member, heq, heq']
      apply memberLoop_finish ⟨hz, ho, htwo, hthree, hfour, hfive, hp, hx, hout0, hrun⟩
      apply WP.exists_execWithin
      unfold memberBody readAt
      wram_exec [hp, hx, hz, ho, htwo, hthree, he, hm, hM, hq, splitSize, heq, heq', hlt]
      exact ⟨by wram_simp [hz], by wram_simp,
        by wram_simp [hout0, hmem_f, Bool.false_eq_true, ↓reduceIte], by wram_simp⟩
    | @node d b summary cluster =>
      obtain rfl : b = some (m, M) := hb
      have hsafe := member_descent_safe ht hr (by simpa only [hM] using hlt)
      have hi := hsafe.1
      have hu := universeSize_le_span d
      have hu' := span_le_succ d
      have hlo : Fits w (query % universeSize d) := ha.of_le (by omega)
      have hnext : Fits w (query / universeSize d + 1) := ha.of_le (by omega)
      have hchild : Fits w (base + 5 + (query / universeSize d + 1) * span d) := by
        apply ha.of_le
        dsimp only [clusterOffset] at hsafe
        omega
      have hqne : universeSize d ≠ 0 := Nat.ne_of_gt (universeSize_pos d)
      let i : Fin (universeSize d) := ⟨query / universeSize d, hi⟩
      have hstep : ∃ s₁, ExecWithin w memberBody s s₁ 26 ∧
          MemberEntry (base + clusterOffset d i.val) (query % universeSize d) s₁ ∧
          s₁.mem = s.mem := by
        apply WP.exists_execWithin
        unfold memberBody readAt coordinates
        wram_exec [hp, hx, hz, ho, htwo, hthree, hfour, hfive, he, hm, hM, hq, hspan,
          splitSize, childSpan, heq, heq', hlt, hqne]
        exact ⟨⟨by wram_simp [hz], by wram_simp [ho], by wram_simp [htwo],
          by wram_simp [hthree], by wram_simp [hfour], by wram_simp [hfive],
          by wram_simp [clusterOffset, i, Nat.add_assoc], by wram_simp,
          by wram_simp [hout0], by wram_simp [hrun]⟩, by wram_simp⟩
      obtain ⟨s₁, he_step, hentry, hs₁_mem⟩ := hstep
      have hrep : Rep (cluster i) (base + clusterOffset d i.val) s₁.mem :=
        hs₁_mem ▸ hr.2.2 i
      have hfit : Fits w (base + clusterOffset d i.val + span d) :=
        ha.of_le (by have := cluster_end_le_span d hi; dsimp only [i]; omega)
      obtain ⟨z, hz_loop, ho_z, hmem_z⟩ := memberLoop_spec hentry (ht.2.2.1 i) hrep hfit
      refine ⟨z, (he_step.loop_iter (cond := .lt zero runFlag) ?_ hz_loop).mono (by omega),
        ?_, hmem_z.trans hs₁_mem⟩
      · simp only [Cond.holds_lt, hz, hrun]
        decide
      · simpa only [Tree.member, heq, hi, ↓reduceDIte, ↓reduceIte] using ho_z
  · have hmem_f := member_eq_false_of_max_lt (query := query) ht hb (by omega)
    apply memberLoop_finish ⟨hz, ho, htwo, hthree, hfour, hfive, hp, hx, hout0, hrun⟩
    apply WP.exists_execWithin
    unfold memberBody readAt
    wram_exec [hp, hx, hz, ho, htwo, he, hm, hM, heq, heq', hlt]
    exact ⟨by wram_simp [hz], by wram_simp,
      by wram_simp [hout0, hmem_f, Bool.false_eq_true, ↓reduceIte], by wram_simp⟩

end Cslib.DataStructure.VanEmdeBoas.WordRAM
