/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Model
public import CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Program
public import CslibFrontier.Computability.WordRAM.Compile
import CslibFrontier.Computability.WordRAM.SymbolicExec
import Mathlib.Tactic.Linarith

/-!
# Van Emde Boas initializer program and Phase 1–2 lookup-table construction

This module defines the fixed 32-register structured initializer program `initProgram` for
recursive van Emde Boas trees and certifies its first two phases:
1. Computing `(universeSize d, span d)` by `d` iterations of the layout recurrences (`sizeLoop`).
2. Populating the `(splitSize k, childSpan k)` lookup table of `2 * (d + 1)` words at
   `[base + span d, base + span d + 2 * (d + 1))` (`tableLoop`).

## Main definitions

* `initSetup`, `sizeBody`, `sizeLoop`: Phase 1 constant setup and `(universeSize, span)` recurrence
  loop.
* `tableSetup`, `tableBody`, `tableLoop`: Phase 2 setup and `(splitSize, childSpan)` lookup-table
  loop.
* `dfsSetup`, `dfsEnterBody`, `dfsExitBody`, `dfsBody`, `dfsLoop`: Phase 3 setup and iterative
  depth-first header initialization loop.
* `initProgram`: the fixed 32-register structured initializer program.
* `TableInv`: the lookup-table invariant for `(splitSize j, childSpan j)`.

## Main results

* `sizeLoop_spec`: Phase 1 recurrence loop specification.
* `tableLoop_spec`: Phase 2 lookup-table loop specification.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.DataStructure.VanEmdeBoas.WordRAM

open Cslib.WordRAM
open Cslib.DataStructure.VanEmdeBoas

/-! ## Structured initializer program -/

/-- Constant and recurrence-seed setup for Phase 1. -/
def initSetup : Code .standard 32 := ram[
  zero ← #0; one ← #1; two ← #2; three ← #3; four ← #4; five ← #5;
  q ← two; t ← five; high ← zero ]

/-- One step of the `(universeSize, span)` recurrence loop. -/
def sizeBody : Code .standard 32 := ram[
  tmp ← q + one; tmp ← tmp * t; tmp ← tmp + five;
  q ← q * q; t ← tmp; high ← high + one ]

/-- Phase 1 loop computing `(universeSize d, span d)`. -/
def sizeLoop : Code .standard 32 := ram[
  while high < depth do [ ⟪sizeBody⟫ ] ]

/-- Setup for the Phase 2 `(splitSize, childSpan)` table construction. -/
def tableSetup : Code .standard 32 := ram[
  payload ← root + t; tableBase ← payload; stackBase ← payload; sp ← tableBase;
  *sp ← zero; sp ← sp + one; *sp ← zero; sp ← sp + one;
  q ← two; t ← five; high ← zero ]

/-- One step of the Phase 2 table-population loop. -/
def tableBody : Code .standard 32 := ram[
  *sp ← q; sp ← sp + one; *sp ← t; sp ← sp + one;
  tmp ← q + one; tmp ← tmp * t; tmp ← tmp + five;
  q ← q * q; t ← tmp; high ← high + one ]

/-- Phase 2 loop writing `(splitSize (k + 1), childSpan (k + 1))` for `k < d`. -/
def tableLoop : Code .standard 32 := ram[
  while high < depth do [ ⟪tableBody⟫ ] ]

/-- Setup for the Phase 3 depth-first header initialization. -/
def dfsSetup : Code .standard 32 := ram[
  low ← sp; p ← root; x ← depth; kind ← zero; runFlag ← one ]

/-- Downward step of the DFS initializer: write the current node's empty header and either
turn around at a leaf or initialize the cluster counter and descend into the summary. -/
def dfsEnterBody : Code .standard 32 := ram[
  *p ← zero;
  tmp ← x * two; addr ← tableBase + tmp; q ← *addr;
  addr ← addr + one; t ← *addr;
  child ← p + three; *child ← q; child ← child + one; *child ← t;
  p ← p + five;
  if x = zero then [ kind ← one ] else [
    addr ← low + x; *addr ← q; x ← x - one
  ] ]

/-- Upward/sibling step of the DFS initializer: ascend to the parent level and either finish
when above `depth`, continue ascending when all clusters are done, or decrement the remaining
cluster counter and descend into the next cluster. -/
def dfsExitBody : Code .standard 32 := ram[
  x ← x + one;
  if depth < x then [ runFlag ← zero ] else [
    addr ← low + x; present ← *addr;
    if present = zero then [ kind ← kind ] else [
      present ← present - one; *addr ← present; x ← x - one; kind ← zero
    ]
  ] ]

/-- Full body of the Phase 3 DFS loop. -/
def dfsBody : Code .standard 32 := ram[
  if kind = zero then [ ⟪dfsEnterBody⟫ ] else [ ⟪dfsExitBody⟫ ] ]

/-- Phase 3 DFS traversal loop. -/
def dfsLoop : Code .standard 32 := ram[
  while zero < runFlag do [ ⟪dfsBody⟫ ] ]

/-- Fixed 32-register structured program initializing an empty van Emde Boas tree of depth
`depth` at `root` and placing `stackBase` at `root + span depth`. -/
def initProgram : Code .standard 32 := ram[
  ⟪initSetup⟫;
  ⟪sizeLoop⟫;
  ⟪tableSetup⟫;
  ⟪tableLoop⟫;
  ⟪dfsSetup⟫;
  ⟪dfsLoop⟫;
  out ← payload ]

/-- The structured initializer program `initProgram` does not read the word width. -/
theorem initProgram_not_readsWidth : ¬initProgram.ReadsWidth := by decide

/-- The compiled flat initializer program does not read the word width. -/
theorem compiled_initProgram_not_readsWidth : ¬(initProgram.program out).ReadsWidth :=
  Code.not_readsWidth_program initProgram_not_readsWidth out

/-! ## Phase 1: computing `(universeSize d, span d)` -/

/-- One size step at depth `k < d`, as in `sizeBody` and `tableBody`, computes
`(universeSize k + 1) * span k + 5 = span (k + 1)` with word-fit bounds for `universeSize k + 1`,
`(universeSize k + 1) * span k + 5`, and `universeSize k * universeSize k` from `Fits w (span d)`.
-/
private theorem sizeStep_fits {w d k : ℕ} (hk : k < d) (hspan : Fits w (span d)) :
    (universeSize k + 1) * span k + 5 = span (k + 1) ∧
      Fits w (universeSize k + 1) ∧
      Fits w ((universeSize k + 1) * span k + 5) ∧
      Fits w (universeSize k * universeSize k) := by
  have hle : span (k + 1) ≤ span d := span_mono (by omega)
  have hspan_eq : (universeSize k + 1) * span k + 5 = span (k + 1) := Nat.add_comm _ _
  have hu_le : universeSize k * universeSize k ≤ span (k + 1) := universeSize_le_span (k + 1)
  have huk_le : universeSize k + 1 ≤ universeSize k * universeSize k := by
    have := two_le_universeSize k; nlinarith
  exact ⟨hspan_eq, hspan.of_le (by omega), hspan.of_le (by omega), hspan.of_le (by omega)⟩

/-- `sizeLoop` advances `(q, t, high)` from `(universeSize k, span k, k)` to
`(universeSize d, span d, d)` in `8 * (d - k) + 2` instructions without modifying memory. -/
theorem sizeLoop_spec {w d : ℕ} (rem : ℕ) {k : ℕ} {s : Data 32} (hk : k + rem = d)
    (hspan : Fits w (span d)) (hd : Fits w d)
    (h0 : s.regs zero = 0) (h1 : s.regs one = 1) (h2 : s.regs two = 2)
    (h3 : s.regs three = 3) (h4 : s.regs four = 4) (h5 : s.regs five = 5)
    (hdepth : s.regs depth = d) (hq : s.regs q = universeSize k) (ht : s.regs t = span k)
    (hhigh : s.regs high = k) :
    ∃ z, ExecWithin w sizeLoop s z (8 * rem + 2) ∧
      z.regs zero = 0 ∧ z.regs one = 1 ∧ z.regs two = 2 ∧
      z.regs three = 3 ∧ z.regs four = 4 ∧ z.regs five = 5 ∧
      z.regs root = s.regs root ∧ z.regs depth = d ∧
      z.regs q = universeSize d ∧ z.regs t = span d ∧ z.mem = s.mem := by
  induction rem generalizing k s with
  | zero =>
    obtain rfl : k = d := by omega
    have hc : ¬(Cond.lt high depth).Holds s := by simp [Cond.holds_lt, hhigh, hdepth]
    exact ⟨s, ExecWithin.loop_exit hc, h0, h1, h2, h3, h4, h5, rfl, hdepth, hq, ht, rfl⟩
  | succ rem ih =>
    have hk_lt : k < d := by omega
    obtain ⟨hspan_eq, hf1, hf3, hf4⟩ := sizeStep_fits hk_lt hspan
    have hf5 : Fits w (k + 1) := hd.of_le (by omega)
    have hstep : ∃ s₁, ExecWithin w sizeBody s s₁ 6 ∧
        s₁.regs zero = 0 ∧ s₁.regs one = 1 ∧ s₁.regs two = 2 ∧
        s₁.regs three = 3 ∧ s₁.regs four = 4 ∧ s₁.regs five = 5 ∧
        s₁.regs root = s.regs root ∧ s₁.regs depth = d ∧
        s₁.regs q = universeSize (k + 1) ∧ s₁.regs t = span (k + 1) ∧
        s₁.regs high = k + 1 ∧ s₁.mem = s.mem := by
      apply WP.exists_execWithin
      unfold sizeBody
      wram_exec [h1, h5, hq, ht, hhigh]
      exact ⟨by wram_simp [h0], by wram_simp [h1], by wram_simp [h2],
        by wram_simp [h3], by wram_simp [h4], by wram_simp [h5],
        by wram_simp, by wram_simp [hdepth], by wram_simp [universeSize_succ],
        by wram_simp [hspan_eq], by wram_simp, by wram_simp⟩
    obtain ⟨s₁, hbody, h0₁, h1₁, h2₁, h3₁, h4₁, h5₁, hr₁, hd₁, hq₁, ht₁, hh₁, hm₁⟩ := hstep
    have hc : (Cond.lt high depth).Holds s := by simp [Cond.holds_lt, hhigh, hdepth, hk_lt]
    obtain ⟨z, hz, hz0, hz1, hz2, hz3, hz4, hz5, hzr, hzd, hzq, hzt, hzm⟩ :=
      ih (by omega) h0₁ h1₁ h2₁ h3₁ h4₁ h5₁ hd₁ hq₁ ht₁ hh₁
    exact ⟨z, (ExecWithin.loop_iter hc hbody hz).mono (by omega),
      hz0, hz1, hz2, hz3, hz4, hz5, hzr.trans hr₁, hzd, hzq, hzt, hzm.trans hm₁⟩

/-! ## Phase 2: populating the `(splitSize, childSpan)` table -/

/-- Lookup-table invariant up to depth `m`: for all `j ≤ m`, `mem (tbl + 2 * j) = splitSize j`
and `mem (tbl + 2 * j + 1) = childSpan j`. -/
def TableInv (tbl m : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ j ≤ m, mem (tbl + 2 * j) = splitSize j ∧ mem (tbl + 2 * j + 1) = childSpan j

/-- `tableLoop` populates the lookup table from depth `k` up to `d` in `12 * (d - k) + 2`
instructions, advancing `sp` to `base + span d + 2 * (d + 1)` and preserving all memory outside
`[base + span d + 2 * (k + 1), base + span d + 2 * (d + 1))`. -/
theorem tableLoop_spec {w base d : ℕ} (rem : ℕ) {k : ℕ} {s : Data 32} (hk : k + rem = d)
    (ha : Fits w (base + span d + 4 * (d + 1)))
    (h0 : s.regs zero = 0) (h1 : s.regs one = 1) (h2 : s.regs two = 2)
    (h3 : s.regs three = 3) (h4 : s.regs four = 4) (h5 : s.regs five = 5)
    (hroot : s.regs root = base) (hdepth : s.regs depth = d)
    (hpay : s.regs payload = base + span d)
    (htbl : s.regs tableBase = base + span d)
    (hstk : s.regs stackBase = base + span d)
    (hsp : s.regs sp = base + span d + 2 * (k + 1))
    (hq : s.regs q = universeSize k) (ht : s.regs t = span k) (hhigh : s.regs high = k)
    (hinv : TableInv (base + span d) k s.mem) :
    ∃ z, ExecWithin w tableLoop s z (12 * rem + 2) ∧
      z.regs zero = 0 ∧ z.regs one = 1 ∧ z.regs two = 2 ∧
      z.regs three = 3 ∧ z.regs four = 4 ∧ z.regs five = 5 ∧
      z.regs root = base ∧ z.regs depth = d ∧
      z.regs payload = base + span d ∧
      z.regs tableBase = base + span d ∧
      z.regs stackBase = base + span d ∧
      z.regs sp = base + span d + 2 * (d + 1) ∧
      TableInv (base + span d) d z.mem ∧
      (∀ a, a < base + span d + 2 * (k + 1) ∨ base + span d + 2 * (d + 1) ≤ a →
        z.mem a = s.mem a) := by
  induction rem generalizing k s with
  | zero =>
    obtain rfl : k = d := by omega
    have hc : ¬(Cond.lt high depth).Holds s := by simp [Cond.holds_lt, hhigh, hdepth]
    refine ⟨s, ExecWithin.loop_exit hc, h0, h1, h2, h3, h4, h5, hroot, hdepth,
      hpay, htbl, hstk, hsp, hinv, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < d := by omega
    obtain ⟨hspan_eq, hf1, hf3, hf4⟩ := sizeStep_fits hk_lt (ha.of_le (by omega))
    let sp₀ := base + span d + 2 * (k + 1)
    have hf_sp2 : Fits w (sp₀ + 1 + 1) := ha.of_le (by dsimp only [sp₀]; omega)
    rcases (show ∃ s₁, ExecWithin w tableBody s s₁ 10 ∧
        s₁.regs zero = 0 ∧ s₁.regs one = 1 ∧ s₁.regs two = 2 ∧
        s₁.regs three = 3 ∧ s₁.regs four = 4 ∧ s₁.regs five = 5 ∧
        s₁.regs root = base ∧ s₁.regs depth = d ∧
        s₁.regs payload = base + span d ∧ s₁.regs tableBase = base + span d ∧
        s₁.regs stackBase = base + span d ∧
        s₁.regs sp = base + span d + 2 * (k + 1 + 1) ∧
        s₁.regs q = universeSize (k + 1) ∧ s₁.regs t = span (k + 1) ∧
        s₁.regs high = k + 1 ∧
        TableInv (base + span d) (k + 1) s₁.mem ∧
        (∀ a, a ≠ sp₀ → a ≠ sp₀ + 1 → s₁.mem a = s.mem a) by
      apply WP.exists_execWithin
      unfold tableBody
      wram_exec [h1, h5, hsp, hq, ht, hhigh]
      refine ⟨by wram_simp [h0], by wram_simp [h1], by wram_simp [h2],
        by wram_simp [h3], by wram_simp [h4], by wram_simp [h5],
        by wram_simp [hroot], by wram_simp [hdepth], by wram_simp [hpay],
        by wram_simp [htbl], by wram_simp [hstk], ?_,
        by wram_simp [universeSize_succ], by wram_simp [hspan_eq], by wram_simp, ?_, ?_⟩
      · wram_simp; omega
      · intro j hj
        by_cases hjk : j ≤ k
        · have ha0 : base + span d + 2 * j ≠ sp₀ := by dsimp only [sp₀]; omega
          have ha1 : base + span d + 2 * j ≠ sp₀ + 1 := by dsimp only [sp₀]; omega
          have hb0 : base + span d + 2 * j + 1 ≠ sp₀ := by dsimp only [sp₀]; omega
          have hb1 : base + span d + 2 * j + 1 ≠ sp₀ + 1 := by dsimp only [sp₀]; omega
          exact ⟨by wram_simp [sp₀, (hinv j hjk).1], by wram_simp [sp₀, (hinv j hjk).2]⟩
        · obtain rfl : j = k + 1 := by omega
          exact ⟨by wram_simp [splitSize], by wram_simp [childSpan, Nat.add_assoc]⟩
      · intro a ha0 ha1
        wram_simp [sp₀]) with
      ⟨s₁, hbody, h0₁, h1₁, h2₁, h3₁, h4₁, h5₁, hr₁, hd₁, hp₁, htbl₁, hstk₁,
        hsp₁, hq₁, ht₁, hh₁, hinv₁, haway₁⟩
    have hc : (Cond.lt high depth).Holds s := by simp [Cond.holds_lt, hhigh, hdepth, hk_lt]
    obtain ⟨z, hz, hz0, hz1, hz2, hz3, hz4, hz5, hzr, hzd, hzp, hztbl, hzstk, hzsp, hzinv,
      hzframe⟩ :=
      ih (by omega) h0₁ h1₁ h2₁ h3₁ h4₁ h5₁ hr₁ hd₁ hp₁ htbl₁ hstk₁ hsp₁ hq₁ ht₁ hh₁ hinv₁
    clear h0 h1 h2 h3 h4 h5 hroot hdepth hpay htbl hstk hsp hq ht hhigh
      h0₁ h1₁ h2₁ h3₁ h4₁ h5₁ hr₁ hd₁ hp₁ htbl₁ hstk₁ hsp₁ hq₁ ht₁ hh₁
    refine ⟨z, (ExecWithin.loop_iter hc hbody hz).mono (by omega),
      hz0, hz1, hz2, hz3, hz4, hz5, hzr, hzd, hzp, hztbl, hzstk, hzsp, hzinv, ?_⟩
    intro a ha_out
    have ha_out₁ : a < base + span d + 2 * (k + 1 + 1) ∨ base + span d + 2 * (d + 1) ≤ a := by
      omega
    rw [hzframe a ha_out₁, haway₁ a (by dsimp only [sp₀]; omega) (by dsimp only [sp₀]; omega)]

end Cslib.DataStructure.VanEmdeBoas.WordRAM
