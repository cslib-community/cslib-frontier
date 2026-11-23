/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Call
public import CslibFrontier.Algorithms.WordRAM.PrimeTrial
public import Mathlib.NumberTheory.PrimeCounting

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Native prime tables

This fixed program tests every candidate through the supplied bound, writes its primality
bit, and counts the primes. Trial division, table addresses, writes and loops are charged.
There is no primality oracle or assumed sieve.

## Main definitions

* `PrimeTable.program`: the complete native table builder.
* `PrimeTable.memory`: its output bitmap and memory frame.

## Main results

* `PrimeTable.exec`: exact bitmap and prime count in an explicit quadratic instruction bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PrimeTable

open Cslib.WordRAM
open Finset

/-- Registers of the trial-division subroutine. -/
def trialRegisters (i : Fin 6) : Fin 15 := ⟨i.val, by omega⟩

private theorem trial_injective : Function.Injective trialRegisters := by
  intro i j h
  exact Fin.ext (by simpa only [trialRegisters] using congrArg Fin.val h)

/-- Current trial-division candidate. -/
abbrev arg : Fin 15 := 0
/-- Current candidate's primality bit. -/
abbrev flag : Fin 15 := 2
/-- Largest candidate. -/
abbrev limit : Fin 15 := 6
/-- Output bitmap base. -/
abbrev base : Fin 15 := 7
/-- First candidate not yet written. -/
abbrev cursor : Fin 15 := 8
/-- Address scratch. -/
abbrev addr : Fin 15 := 9
/-- Number of primes written. -/
abbrev count : Fin 15 := 10
/-- One past the largest candidate. -/
abbrev stop : Fin 15 := 11
/-- Constant one. -/
abbrev one : Fin 15 := 12
/-- Constant zero. -/
abbrev zero : Fin 15 := 13
/-- Constant two. -/
abbrev two : Fin 15 := 14

/-- Handle zero and one directly; test all larger candidates by charged native trial division. -/
def test : Code .standard 15 :=
  .branch (.lt cursor two) (ram[ flag ← #0 ])
    (.seq (ram[ arg ← cursor ]) (PrimeTrial.program.rename trialRegisters))

/-- Test, write the bit, update the count, and advance the candidate. -/
def body : Code .standard 15 :=
  .seq test (ram[ addr ← base + cursor; *addr ← flag;
    count ← count + flag; cursor ← cursor + one ])

/-- A finite native prime-table program with its bound and base supplied in registers. -/
def program : Code .standard 15 :=
  .seq (ram[ one ← #1; zero ← #0; two ← #2; cursor ← #0; count ← #0;
    stop ← limit + one ]) (.loop (.lt cursor stop) body)

/-- The first `k` primality bits, preserving all other memory cells. -/
def memory (mem : ℕ → ℕ) (base k : ℕ) : ℕ → ℕ :=
  fun a => if base ≤ a ∧ a < base + k then if (a - base).Prime then 1 else 0 else mem a

private theorem memory_zero (mem : ℕ → ℕ) (base : ℕ) : memory mem base 0 = mem := by
  funext a; simp [memory]

private theorem memory_succ (mem : ℕ → ℕ) (base k : ℕ) :
    memory mem base (k + 1) = Function.update (memory mem base k)
      (base + k) (if k.Prime then 1 else 0) := by
  funext a
  by_cases ha : a = base + k
  · subst a; simp [memory]
  · rw [Function.update_of_ne ha]
    simp only [memory, show (base ≤ a ∧ a < base + (k + 1)) ↔ (base ≤ a ∧ a < base + k) by omega]

private theorem exec_test {w m : ℕ} (x : Data 15) (htwo : x.regs two = 2)
    (hbound : x.regs cursor ≤ m) (hfit : Fits w (m + 3)) :
    ∃ y, ExecWithin w test x y (7 * m + 9) ∧
      y.regs flag = (if (x.regs cursor).Prime then 1 else 0) ∧ y.mem = x.mem ∧
      ∀ i, 6 ≤ i.val → y.regs i = x.regs i := by
  unfold test
  wram_exec [htwo]
  · have hnp : ¬(x.regs cursor).Prime := fun h => by have := h.two_le; omega
    wram_simp [hnp]
    intro i hi
    exact Data.set_regs_of_ne (fun h => absurd (h ▸ hi) (by decide)) _
  · refine WP.of_spec (ExecWithin.rename_post trial_injective (PrimeTrial.exec _ ?_ ?_)) ?_
    · dsimp only [Data.comap_regs, trialRegisters, PrimeTrial.arg]; wram_simp; omega
    · dsimp only [Data.comap_regs, trialRegisters, PrimeTrial.arg]; wram_simp; fits
    rintro y ⟨⟨hyf, _, hym⟩, hframe⟩
    dsimp only [Data.comap_regs, Data.comap_mem, trialRegisters, PrimeTrial.arg,
      PrimeTrial.flag] at hyf hym ⊢
    wram_simp at hyf ⊢
    refine ⟨by omega, hyf, hym, fun i hi => ?_⟩
    refine (hframe i fun j hj => ?_).trans
      (Data.set_regs_of_ne (fun h => absurd (h ▸ hi) (by decide)) _)
    have hv := congrArg Fin.val hj
    dsimp only [trialRegisters] at hv
    omega

/-- Write every primality bit through `m`, count exactly `Nat.primesLE m`, and preserve
all cells outside the bitmap. Trial division gives the explicit quadratic bound
`(m+1)(7m+15)+8`; the final halt is excluded. -/
theorem exec {w : ℕ} (x : Data 15)
    (hfit : Fits w (x.regs limit + 3))
    (haddr : Fits w (x.regs base + (x.regs limit + 1))) :
    ∃ y, ExecWithin w program x y ((x.regs limit + 1) * (7 * x.regs limit + 15) + 8) ∧
      y.mem = memory x.mem (x.regs base) (x.regs limit + 1) ∧
      y.regs count = #(Nat.primesLE (x.regs limit)) ∧
      y.regs limit = x.regs limit ∧ y.regs base = x.regs base := by
  let m := x.regs limit
  unfold program
  wram_exec
  let P (j : ℕ) (y : Data 15) : Prop := y.regs limit = m ∧ y.regs base = x.regs base ∧
    y.regs stop = m + 1 ∧ y.regs one = 1 ∧ y.regs zero = 0 ∧ y.regs two = 2 ∧
    y.regs count = Nat.primeCounting' j ∧ y.mem = memory x.mem (x.regs base) j
  refine WP.of_spec
    (ExecWithin.loop_count (N := m + 1) (T := 7 * m + 13) P (fun _ hy => hy.2.2.1) ?_ ?_ ?_) ?_
  · rintro y ⟨hl, hb, hs, ho, hz, ht, hcount, hm⟩ hlt
    unfold body
    refine (WP.seq ?_).exists_execWithin
    wram_call (exec_test y ht (by omega) hfit) with z ⟨hzf, hzm, hzr⟩
    have hzb : z.regs base = x.regs base := (hzr base (by decide)).trans hb
    have hzi : z.regs cursor = y.regs cursor := hzr cursor (by decide)
    have hzc : z.regs count = Nat.primeCounting' (y.regs cursor) :=
      (hzr count (by decide)).trans hcount
    have hzo : z.regs one = 1 := (hzr one (by decide)).trans ho
    have hzf_le : z.regs flag ≤ 1 := by rw [hzf]; split_ifs <;> omega
    have hcnt_le : Nat.primeCounting' (y.regs cursor) ≤ y.regs cursor := Nat.count_le _
    wram_exec [hzb, hzi, hzc, hzo]
    dsimp only [P]
    wram_simp [hzb, hzi, hzm, hm, hzf]
    exact ⟨(hzr limit (by decide)).trans hl, (hzr stop (by decide)).trans hs, hzo,
      (hzr zero (by decide)).trans hz, (hzr two (by decide)).trans ht,
      by simp only [Nat.primeCounting', Nat.count_succ],
      (memory_succ x.mem (x.regs base) (y.regs cursor)).symm⟩
  · wram_simp
  · dsimp only [P, m]; wram_simp [Nat.primeCounting', Nat.count_zero, memory_zero]
  · rintro y ⟨⟨hl, hb, _, _, _, _, hcount, hm⟩, _⟩
    refine ⟨?_, hm, ?_, hl, hb⟩
    · wram_simp; dsimp only [m]; exact le_rfl
    · rw [hcount, Nat.primesLE_card_eq_primeCounting, Nat.primeCounting]

end Cslib.Algorithms.WordRAM.PrimeTable
