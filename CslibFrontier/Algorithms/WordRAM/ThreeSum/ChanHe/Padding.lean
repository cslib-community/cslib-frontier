/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Initializing the four columns of a Chan–He node

## Main definitions

* `Padding.program`: a fixed loop writing a four-word pattern to every group.

## Main results

* `Padding.exec`: exact memory and a charged `12N+5` instruction bound.

## References

This native program and its execution proof are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Padding

open Cslib.WordRAM

/-- Packed output base. -/
abbrev dst : Fin 10 := 0
/-- Number of four-cell groups. -/
abbrev len : Fin 10 := 1
/-- Padding word for column zero. -/
abbrev pad0 : Fin 10 := 2
/-- Padding word for column one. -/
abbrev pad1 : Fin 10 := 3
/-- Padding word for column two. -/
abbrev pad2 : Fin 10 := 4
/-- Padding word for column three. -/
abbrev pad3 : Fin 10 := 5
/-- Group cursor. -/
abbrev idx : Fin 10 := 6
/-- Temporary address. -/
abbrev addr : Fin 10 := 7
/-- Constant one. -/
abbrev one : Fin 10 := 8
/-- Constant four. -/
abbrev four : Fin 10 := 9

/-- A concrete four-word pattern, addressed by its residue modulo four. -/
def pattern (p₀ p₁ p₂ p₃ u : ℕ) : ℕ :=
  if u % 4 = 0 then p₀ else if u % 4 = 1 then p₁ else if u % 4 = 2 then p₂ else p₃

/-- Initial memory with the first `k` groups overwritten, including all padding. -/
def memory (mem : ℕ → ℕ) (dst p₀ p₁ p₂ p₃ k : ℕ) : ℕ → ℕ := fun a =>
  if dst ≤ a ∧ a < dst + 4 * k then pattern p₀ p₁ p₂ p₃ (a - dst) else mem a

@[simp] theorem memory_zero (mem : ℕ → ℕ) (dst p₀ p₁ p₂ p₃ : ℕ) :
    memory mem dst p₀ p₁ p₂ p₃ 0 = mem := by
  funext a
  simp [memory]

/-- Four distinct stores make one complete group. -/
theorem memory_succ (mem : ℕ → ℕ) (dst p₀ p₁ p₂ p₃ k : ℕ) :
    memory mem dst p₀ p₁ p₂ p₃ (k + 1) =
      Function.update (Function.update (Function.update (Function.update
        (memory mem dst p₀ p₁ p₂ p₃ k) (dst + 4 * k) p₀)
          (dst + 4 * k + 1) p₁) (dst + 4 * k + 2) p₂) (dst + 4 * k + 3) p₃ := by
  funext a
  by_cases h₀ : a = dst + 4 * k
  · subst a; simp [memory, pattern]
  by_cases h₁ : a = dst + 4 * k + 1
  · subst a
    simp [memory, pattern, show dst + 4 * k + 1 - dst = 4 * k + 1 by omega,
      show dst ≤ dst + 4 * k + 1 ∧ dst + 4 * k + 1 < dst + 4 * (k + 1) by omega]
  by_cases h₂ : a = dst + 4 * k + 2
  · subst a
    simp [memory, pattern, show dst + 4 * k + 2 - dst = 4 * k + 2 by omega,
      show dst ≤ dst + 4 * k + 2 ∧ dst + 4 * k + 2 < dst + 4 * (k + 1) by omega]
  by_cases h₃ : a = dst + 4 * k + 3
  · subst a
    simp [memory, pattern, show dst + 4 * k + 3 - dst = 4 * k + 3 by omega,
      show dst ≤ dst + 4 * k + 3 ∧ dst + 4 * k + 3 < dst + 4 * (k + 1) by omega]
  simp only [Function.update_of_ne h₃, Function.update_of_ne h₂, Function.update_of_ne h₁,
    Function.update_of_ne h₀, memory,
    show (dst ≤ a ∧ a < dst + 4 * (k + 1)) ↔ (dst ≤ a ∧ a < dst + 4 * k) by omega]

/-- Every address, store and increment of a four-word group is charged. -/
def body : Code .standard 10 := ram[
  addr ← four * idx; addr ← dst + addr; *addr ← pad0;
  addr ← addr + one; *addr ← pad1; addr ← addr + one; *addr ← pad2;
  addr ← addr + one; *addr ← pad3; idx ← idx + one ]

/-- Runtime pattern values and length, with fixed code and registers. -/
def program : Code .standard 10 :=
  .seq (ram[ idx ← #0; one ← #1; four ← #4 ]) (.loop (.lt idx len) body)

/-- Initialize exactly `4N` cells from arbitrary old memory. -/
theorem exec {w : ℕ} (x : Data 10) (h4 : Fits w 4)
    (hfit : Fits w (x.regs dst + 4 * x.regs len)) :
    ∃ y, ExecWithin w program x y (12 * x.regs len + 5) ∧
      y.mem = memory x.mem (x.regs dst) (x.regs pad0) (x.regs pad1)
        (x.regs pad2) (x.regs pad3) (x.regs len) ∧
      ∀ i, i.val < 6 → y.regs i = x.regs i := by
  let P (j : ℕ) (y : Data 10) : Prop :=
    (∀ i, i.val < 6 → y.regs i = x.regs i) ∧ y.regs one = 1 ∧ y.regs four = 4 ∧
      y.mem = memory x.mem (x.regs dst)
        (x.regs pad0) (x.regs pad1) (x.regs pad2) (x.regs pad3) j
  have hbody (y : Data 10) (hy : P (y.regs idx) y) (hlt : y.regs idx < x.regs len) :
      ∃ z, ExecWithin w body y z 10 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, h1, hfour, hm⟩ := hy
    refine WP.exists_execWithin ?_
    unfold body
    wram_exec [h1, hfour, hr dst (by decide), hr pad0 (by decide), hr pad1 (by decide),
      hr pad2 (by decide), hr pad3 (by decide)]
    refine ⟨⟨fun i hi => by
      simp only [Data.set_regs, Data.write_regs, Function.update_apply, Fin.ext_iff,
        idx, addr, hr i hi]
      split_ifs <;> omega,
      by wram_simp [h1], by wram_simp [hfour], ?_⟩, by wram_simp⟩
    wram_simp
    rw [hm, memory_succ]
  refine WP.exists_execWithin ?_
  unfold program
  wram_exec
  wram_call (ExecWithin.loop_count P (fun y hy => hy.1 len (by decide)) hbody
    (by wram_simp; omega) ⟨fun i hi => by
      simp only [Data.set_regs, Function.update_apply, Fin.ext_iff, idx, one, four]
      split_ifs <;> omega,
      by wram_simp, by wram_simp, by wram_simp [memory_zero]⟩)
    with y ⟨⟨hr, _, _, hm⟩, _⟩
  exact ⟨by wram_simp; omega, hm, hr⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Padding
