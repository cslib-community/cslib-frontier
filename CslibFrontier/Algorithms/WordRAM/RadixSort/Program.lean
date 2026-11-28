/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.RadixSort.Scan
public import CslibFrontier.Computability.WordRAM.Compile

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Fixed-code native unsigned radix sorter

Two stable scans per bit partition the source into zeros followed by ones in scratch. Swapping
the pointers avoids a copy-back scan. Code and registers are independent of length and key width.
The source pointer on exit identifies the sorted array; the other block is scratch.

## Main definitions

* `pass`: two digit scans and pointer swap.
* `code`: the complete radix sorter with a register-supplied bit bound.
* `timeBound`: explicit instruction bound, excluding halt.

## Main results

* `exec`: complete charged sorting, with permutation, sortedness and a two-array frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.RadixSort

open Cslib.WordRAM

/-- Exchange source and scratch, then advance to the next bit. -/
def advance : Code .standard 16 := ram[
  swap ← src; src ← dst; dst ← swap; bit ← bit + one ]

/-- Exactly two stable scans per bit. -/
def pass : Code .standard 16 :=
  .seq (ram[ out ← #0; tag ← #0 ])
    (ram[ ⟪Scan.code⟫; tag ← #1; ⟪Scan.code⟫; ⟪advance⟫ ])

/-- Complete unsigned radix sorter. Parameters are length, two disjoint array bases, and bits.
The returned source register identifies the sorted block. -/
def code : Code .standard 16 :=
  .seq (ram[ one ← #1; two ← #2; bit ← #0 ]) (.loop (.lt bit bits) pass)

/-- All instructions of radix sorting, excluding a final halt. -/
def timeBound (n keyBits : ℕ) : ℕ := keyBits * (22 * n + 15) + 5

private theorem pass_exec {w b s d : ℕ} (xs : List ℕ) (x : Data 16)
    (hn : x.regs len = xs.length) (hs : x.regs src = s) (hd : x.regs dst = d)
    (hb : x.regs bit = b) (ho : x.regs one = 1) (h2 : x.regs two = 2)
    (hmem : Block.HoldsList s xs x.mem) (hwords : ∀ v ∈ xs, Fits w v)
    (hdisj : s + xs.length ≤ d ∨ d + xs.length ≤ s)
    (hsfit : Fits w (s + xs.length)) (hdfit : Fits w (d + xs.length))
    (hbit : Fits w (b + 1)) (h1 : Fits w 1) :
    ∃ y, ExecWithin w pass x y (22 * xs.length + 13) ∧
      Block.HoldsList d (partition b xs) y.mem ∧
      y.regs src = d ∧ y.regs dst = s ∧ y.regs bit = b + 1 ∧
      Modifies (Block.mk d xs.length).footprint x.mem y.mem := by
  apply WP.exists_execWithin
  unfold pass advance
  wram_exec
  wram_call (Scan.exec (s := s) (d := d) (b := b) (t := 0) xs [] _
    (by wram_simp; exact hn) (by wram_simp; exact hs) (by wram_simp; exact hd)
    (by wram_simp; exact hb) (by wram_simp) (by wram_simp; exact ho) (by wram_simp; exact h2)
    (by wram_simp; rfl) hmem (Block.holdsList_nil _ _) hwords
    (by simpa using length_select_le b 0 xs) hdisj hsfit hdfit) with y ⟨hym, hysrc, hyout, hyf⟩
  wram_exec
  wram_call (Scan.exec (s := s) (d := d) (b := b) (t := 1) xs (select b 0 xs) _
    (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by wram_simp)
    (by regs_frame) (by regs_frame) (by wram_simp; exact hyout) hysrc
    (by simpa only [Data.set_mem, List.nil_append] using hym) hwords
    (by rw [← partition, length_partition]) hdisj hsfit hdfit) with z ⟨hzm, _, _, hzf⟩
  wram_exec *
  wram_simp *
  exact ⟨hzm, fun a hnot => (hzf a hnot).trans (hyf a hnot)⟩

/-- Sort all keys below `2^keyBits` in `keyBits * (22n+15)+5` instructions. The two arrays
have length `n`, are adjacent, and start at caller-supplied `base`. Only these `2n` cells may
change. The sorted block is returned in `src`; it is one of the two original blocks. This
includes empty lists and zero bit bounds. The key-bit bound and both one-past-end addresses
must fit; constant two must fit. No ordering contract is assumed. -/
theorem exec {w base keyBits : ℕ} (xs : List ℕ) (x : Data 16)
    (hn : x.regs len = xs.length) (hs : x.regs src = base)
    (hd : x.regs dst = base + xs.length) (hb : x.regs bits = keyBits)
    (hmem : Block.HoldsList base xs x.mem)
    (hkeys : ∀ v ∈ xs, v < 2 ^ keyBits)
    (hwords : ∀ v ∈ xs, Fits w v)
    (hfit : Fits w (base + 2 * xs.length)) (hbits : Fits w keyBits) (h2 : Fits w 2) :
    ∃ y, ExecWithin w code x y (timeBound xs.length keyBits) ∧
      Block.HoldsList (y.regs src) (passes keyBits xs) y.mem ∧
      (passes keyBits xs).Perm xs ∧ (passes keyBits xs).Pairwise (· ≤ ·) ∧
      (y.regs src = base ∨ y.regs src = base + xs.length) ∧
      Modifies (Block.mk base (2 * xs.length)).footprint x.mem y.mem := by
  let n := xs.length
  let P (j : ℕ) (y : Data 16) : Prop :=
    y.regs len = n ∧ y.regs bits = keyBits ∧ y.regs one = 1 ∧ y.regs two = 2 ∧
    ((y.regs src = base ∧ y.regs dst = base + n) ∨
      (y.regs src = base + n ∧ y.regs dst = base)) ∧
    Block.HoldsList (y.regs src) (passes j xs) y.mem ∧
    Modifies (Block.mk base (2 * n)).footprint x.mem y.mem
  have hbody (y : Data 16) (hy : P (y.regs bit) y) (hlt : y.regs bit < keyBits) :
      ∃ z, ExecWithin w pass y z (22 * n + 13) ∧ P (y.regs bit + 1) z ∧
        z.regs bit = y.regs bit + 1 := by
    obtain ⟨hyn, hyB, hyo, hy2, hyp, hym, hyf⟩ := hy
    have hl : (passes (y.regs bit) xs).length = n := (passes_perm _ _).length_eq
    obtain ⟨z, he, hzm, hzs, hzd, hzb, hzf⟩ := pass_exec (passes (y.regs bit) xs) y
      (hyn.trans hl.symm) rfl rfl rfl hyo hy2 hym
      (fun v hv => hwords v ((passes_perm _ _).mem_iff.mp hv)) (by rw [hl]; omega)
      (hfit.of_le (by rw [hl]; omega)) (hfit.of_le (by rw [hl]; omega))
      (hbits.of_le (by omega)) (h2.of_le (by omega))
    refine ⟨z, by simpa only [hl] using he, ⟨by regs_frame, by regs_frame, by regs_frame,
      by regs_frame, ?_, by rw [hzs, passes]; exact hzm, fun a hnot => ?_⟩, hzb⟩
    · rw [hzs, hzd]; exact hyp.symm.imp And.symm And.symm
    · refine (hzf a fun ha => hnot ?_).trans (hyf a hnot)
      simp only [Block.mem_footprint, Block.Owns, hl] at ha ⊢
      omega
  let x₀ := ((x.set one 1).set two 2).set bit 0
  have hx₀ : P (x₀.regs bit) x₀ := by
    refine ⟨by regs_frame, by regs_frame, by simp +decide [x₀], by simp +decide [x₀],
      Or.inl ⟨by regs_frame, by regs_frame⟩, ?_, Modifies.refl _ _⟩
    simpa +decide [x₀, passes, hs] using hmem
  obtain ⟨y, he, ⟨_, _, _, _, hyp, hym, hyf⟩, _⟩ := ExecWithin.loop_count P
    (fun _ ⟨_, hbits, _⟩ => hbits) hbody (by simp [x₀]) hx₀
  have hinit : ExecWithin (B := .standard) w (ram[ one ← #1; two ← #2; bit ← #0 ]) x x₀ 3 := by
    wram_exec
  refine ⟨y, (hinit.seq he).mono (by simp +decide [timeBound, n, x₀, Nat.add_assoc]; omega), hym,
    (passes_correct keyBits xs hkeys).1, (passes_correct keyBits xs hkeys).2,
    hyp.imp And.left And.left, hyf⟩

end Cslib.Algorithms.WordRAM.RadixSort
