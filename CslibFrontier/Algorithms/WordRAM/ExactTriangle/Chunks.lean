/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Foundations.Data.Nat.CeilDiv
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Tactic.UpdateSimp

/-!
# Native query-chunk descriptors

For one computed query class, the program writes consecutive triples `(residue, pair pointer,
pair count)`. It computes the last chunk's shorter length and advances over the actual two-word
coordinate representation. The input query list is preserved.

This adapts the chunk loop in the pinned
[Theorem 17 chunk builder](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Instances/Chunks.lean).

## Main definitions

* `Chunks.program`: fixed fourteen-register descriptor writer.

## Main results

* `Chunks.exec`: exact chunk count, descriptor readback and a memory frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.Chunks

open Cslib.WordRAM

/-- Query pair array base. -/
abbrev queries : Fin 14 := 0
/-- Descriptor output base. -/
abbrev dst : Fin 14 := 1
/-- Actual number of query pairs. -/
abbrev total : Fin 14 := 2
/-- Positive maximum pairs per chunk. -/
abbrev capacity : Fin 14 := 3
/-- Class residue. -/
abbrev residue : Fin 14 := 4
/-- Consumed pair count. -/
abbrev pos : Fin 14 := 5
/-- Number of written chunks. -/
abbrev count : Fin 14 := 6
/-- Constant one. -/
abbrev one : Fin 14 := 7
/-- Number of words per descriptor. -/
abbrev three : Fin 14 := 8
/-- Current chunk length. -/
abbrev length : Fin 14 := 9
/-- Output address. -/
abbrev addr : Fin 14 := 10
/-- Current pair pointer. -/
abbrev ptr : Fin 14 := 11

/-- Compute a nonempty chunk, write its descriptor and advance both counters. -/
def body : Code .standard 14 := ram[
  length ← total - pos;
  if capacity < length then [ length ← capacity ] else [ length ← length ];
  addr ← count * three; addr ← addr + dst; *addr ← residue; addr ← addr + one;
  *addr ← ptr; addr ← addr + one; *addr ← length;
  ptr ← ptr + length; ptr ← ptr + length; pos ← pos + length; count ← count + one ]

/-- Initialize all loop state with charged instructions. -/
def program : Code .standard 14 :=
  .seq (ram[ one ← #1; three ← #3; pos ← #0; count ← #0; ptr ← queries ])
    (.loop (.lt pos total) body)

/-- Fixed code and no physical-width reads. -/
theorem program_fixed : program.size ≤ 48 ∧ ¬program.ReadsWidth := by decide

private theorem body_preserves : ∀ i : Fin 14,
    (i.val < 5 ∨ i = one ∨ i = three) → body.Preserves i := by decide +kernel

private theorem exec_body {w : ℕ} (x : Data 14) (ho : x.regs one = 1)
    (hthree : x.regs three = 3) (hp : x.regs pos < x.regs total)
    (hcle : x.regs count ≤ x.regs pos)
    (hptr : x.regs ptr = x.regs queries + 2 * x.regs pos)
    (hfit : Fits w (x.regs dst + 3 * x.regs total + 3))
    (hquery : Fits w (x.regs queries + 2 * x.regs total)) :
    ∃ y, ExecWithin w body x y 15 ∧
      y.regs pos = x.regs pos + min (x.regs capacity) (x.regs total - x.regs pos) ∧
      y.regs count = x.regs count + 1 ∧
      y.regs ptr = x.regs queries +
        2 * (x.regs pos + min (x.regs capacity) (x.regs total - x.regs pos)) ∧
      y.mem = Function.update (Function.update (Function.update x.mem
        (x.regs dst + 3 * x.regs count) (x.regs residue))
          (x.regs dst + 3 * x.regs count + 1) (x.regs queries + 2 * x.regs pos))
            (x.regs dst + 3 * x.regs count + 2)
              (min (x.regs capacity) (x.regs total - x.regs pos)) := by
  have haddr' : x.regs count * 3 + x.regs dst = x.regs dst + 3 * x.regs count := by omega
  wram_exec [body, ho, hthree, hptr]
  · have hmin : min (x.regs capacity) (x.regs total - x.regs pos) = x.regs capacity :=
      min_eq_left hc.le
    refine ⟨by wram_simp [hmin], by wram_simp, by wram_simp [hmin]; omega, ?_⟩
    simp only [hmin, Data.set_mem, Data.write_mem, haddr']
  · have hmin : min (x.regs capacity) (x.regs total - x.regs pos) = x.regs total - x.regs pos :=
      min_eq_right (by omega)
    refine ⟨by wram_simp [hmin], by wram_simp, by wram_simp [hmin]; omega, ?_⟩
    simp only [hmin, Data.set_mem, Data.write_mem, haddr']

/-- Write the exact nonempty chunks of one class. Descriptor `k` names the query slice beginning
at pair `k * capacity`, with its final length truncated to the class size. All other memory is
preserved, so placing the query array outside the descriptor block preserves its coordinates.
The final halt is excluded from the `17 total + 7` bound. -/
theorem exec {w : ℕ} (x : Data 14) (hcap : 0 < x.regs capacity)
    (hfit : Fits w (x.regs dst + 3 * x.regs total + 3))
    (hquery : Fits w (x.regs queries + 2 * x.regs total)) :
    ∃ y, ExecWithin w program x y (17 * x.regs total + 7) ∧
      y.regs count = x.regs total ⌈/⌉ x.regs capacity ∧
      (∀ i : Fin 14, i.val < 5 → y.regs i = x.regs i) ∧
      (∀ k < y.regs count,
        y.mem (x.regs dst + 3 * k) = x.regs residue ∧
        y.mem (x.regs dst + 3 * k + 1) = x.regs queries + 2 * (k * x.regs capacity) ∧
        y.mem (x.regs dst + 3 * k + 2) =
          min (x.regs capacity) (x.regs total - k * x.regs capacity)) ∧
      (∀ a, ¬(x.regs dst ≤ a ∧ a < x.regs dst + 3 * y.regs count) → y.mem a = x.mem a) := by
  let N := x.regs total
  let Q := x.regs capacity
  let d := x.regs dst
  let b := x.regs queries
  change 0 < Q at hcap
  let I (y : Data 14) : Prop :=
    (∀ i : Fin 14, i.val < 5 → y.regs i = x.regs i) ∧
      y.regs one = 1 ∧ y.regs three = 3 ∧ y.regs pos ≤ N ∧
      y.regs pos = min N (y.regs count * Q) ∧ y.regs count ≤ y.regs pos ∧
      (y.regs count = 0 ∨ (y.regs count - 1) * Q < N) ∧
      y.regs ptr = b + 2 * y.regs pos ∧
      (∀ k < y.regs count,
        y.mem (d + 3 * k) = x.regs residue ∧
        y.mem (d + 3 * k + 1) = b + 2 * (k * Q) ∧
        y.mem (d + 3 * k + 2) = min Q (N - k * Q)) ∧
      (∀ a, ¬(d ≤ a ∧ a < d + 3 * y.regs count) → y.mem a = x.mem a)
  have hbody (y : Data 14) (hy : I y) (hc : (Cond.lt pos total).Holds y) :
      ∃ z, ExecWithin w body y z 15 ∧ I z ∧ N - z.regs pos < N - y.regs pos := by
    obtain ⟨hyr, hyo, hyt, hyp, hymin, hyc, hylast, hyptr, hycells, hyframe⟩ := hy
    have hyN : y.regs total = N := hyr total (by decide)
    have hyQ : y.regs capacity = Q := hyr capacity (by decide)
    have hyd : y.regs dst = d := hyr dst (by decide)
    have hyb : y.regs queries = b := hyr queries (by decide)
    have hyrho : y.regs residue = x.regs residue := hyr residue (by decide)
    have hlt : y.regs pos < N := by simpa only [Cond.holds_lt, hyN] using hc
    have hprod : y.regs pos = y.regs count * Q := by
      by_cases h : y.regs count * Q ≤ N
      · simpa only [min_eq_right h] using hymin
      · rw [min_eq_left (by omega)] at hymin; omega
    let L := min Q (N - y.regs pos)
    have hL : 0 < L := lt_min hcap (by omega)
    have hLle : L ≤ N - y.regs pos := min_le_right ..
    obtain ⟨z, he, hzp, hzc, hzptr, hzmem⟩ := exec_body y hyo hyt
      (by simpa only [hyN] using hlt) hyc (by simpa only [hyb] using hyptr)
      (by simpa only [hyd, hyN] using hfit) (by simpa only [hyb, hyN] using hquery)
    simp only [hyN, hyQ, hyb, hyd, hyrho] at hzp hzptr hzmem
    have hzmin : z.regs pos = min N (z.regs count * Q) := by
      rw [hzp, hzc, Nat.add_mul, Nat.one_mul, ← hprod]; omega
    have hpres (i : Fin 14) (hi : i.val < 5 ∨ i = one ∨ i = three) :
        z.regs i = y.regs i := he.regs_eq (body_preserves i hi)
    refine ⟨z, he, ⟨fun i hi => (hpres i (Or.inl hi)).trans (hyr i hi),
      (hpres one (by simp)).trans hyo, (hpres three (by simp)).trans hyt,
      by omega, hzmin, by omega, Or.inr (by rw [hzc, Nat.add_sub_cancel, ← hprod]; exact hlt),
      by simpa only [hzp] using hzptr, ?_, ?_⟩, by omega⟩
    · intro k hk; rw [hzc] at hk; rw [hzmem]
      by_cases h : k = y.regs count
      · subst k; exact ⟨by update_simp, by update_simp; rw [hprod], by update_simp; rw [hprod]⟩
      · obtain ⟨h0, h1, h2⟩ := hycells k (by omega)
        exact ⟨by update_simp; exact h0, by update_simp; exact h1, by update_simp; exact h2⟩
    · intro a ha; rw [hzmem]; update_simp; exact hyframe a (by omega)
  refine WP.exists_execWithin ?_
  wram_exec [program]
  have hx₀ : I (((((x.set one 1).set three 3).set pos 0).set count 0).set ptr b) :=
    ⟨fun i hi => by
      have hne : i ≠ one ∧ i ≠ three ∧ i ≠ pos ∧ i ≠ count ∧ i ≠ ptr := by revert i hi; decide
      wram_simp [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2],
     by wram_simp, by wram_simp, by wram_simp; exact Nat.zero_le _,
     by wram_simp [Nat.zero_mul, Nat.min_zero], by wram_simp, Or.inl (by wram_simp),
     by wram_simp, fun _ hk => by wram_simp at hk, fun _ _ => rfl⟩
  wram_call (ExecWithin.loop_invariant I (fun y => N - y.regs pos) hbody hx₀)
    with y ⟨⟨hyr, -, -, hyp, hymin, hyc, hylast, -, hycells, hyframe⟩, hc⟩
  have hyN : y.regs total = N := hyr total (by decide)
  have hend : y.regs pos = N := by simp only [Cond.holds_lt, hyN] at hc; omega
  have hcover : N ≤ y.regs count * Q := by omega
  have hcount : y.regs count = N ⌈/⌉ Q := by
    apply Nat.le_antisymm
    · rcases hylast with h | h
      · omega
      · have hcov := Nat.le_ceilDiv_mul hcap (a := N)
        by_contra hgt
        have hm : (N ⌈/⌉ Q) * Q ≤ (y.regs count - 1) * Q := Nat.mul_le_mul_right Q (by omega)
        omega
    · exact (Nat.ceilDiv_le_iff hcap).mpr hcover
  refine ⟨by wram_simp; dsimp [N]; omega, hcount, hyr, hycells, hyframe⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.Chunks
