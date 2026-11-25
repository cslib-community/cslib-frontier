/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged initialization from the actual depth header

## Main results

* `Encoding.exec_setup`: load the header and compute both powers, buffer addresses and
  loop parameters within `5L+18` native instructions, preserving every memory cell.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

open Cslib.WordRAM

/-- An explicit bound for the encoder's unsigned addresses, index products and counters. -/
def addressBound (L : ℕ) : ℕ := L + 64 + 64 * 10 ^ L

/-- Registers and memory after header initialization. This is only a postcondition; it
contains no execution, resource or intermediate-fit assumption. -/
structure SetupPost (L : ℕ) (x y : Data 32) : Prop where
  /-- Memory is unchanged. -/
  mem : y.mem = x.mem
  /-- Depth loaded from memory address one. -/
  depth : y.regs Encoding.depth = L
  /-- Computed input size. -/
  inputSize : y.regs Encoding.inputSize = 7 ^ L
  /-- Computed buffer capacity. -/
  capacity : y.regs Encoding.capacity = 10 ^ L
  /-- First output address. -/
  output : y.regs Encoding.output = outputBase L
  /-- First scratch address. -/
  scratch : y.regs Encoding.scratch = scratchBase L
  /-- Original input base. -/
  src : y.regs Encoding.src = 2
  /-- First destination buffer. -/
  dst : y.regs Encoding.dst = outputBase L
  /-- First source suffix length. -/
  stride : y.regs Encoding.stride = 7 ^ L
  /-- The empty transformed prefix. -/
  prefixes : y.regs Encoding.prefixes = 1
  /-- No coordinates transformed yet. -/
  stage : y.regs Encoding.stage = 0
  /-- Counter increment. -/
  one : y.regs Encoding.one = 1
  /-- Input radix. -/
  seven : y.regs Encoding.seven = 7
  /-- Output radix. -/
  ten : y.regs Encoding.ten = 10

/-- Header loads, both power computations, address arithmetic and counter initialization
are included. The only fit premise is the explicit bound on ordinary natural numbers. -/
theorem exec_setup {w : ℕ} (L : ℕ) (x : Data 32) (hheader : x.mem 1 = L)
    (haddr : Fits w (addressBound L)) :
    ∃ y, ExecWithin w setup x y (5 * L + 18) ∧ SetupPost L x y := by
  have h1 : Fits w 1 := haddr.of_le (by unfold addressBound; omega)
  have h2 : Fits w 2 := haddr.of_le (by unfold addressBound; omega)
  have h7 : Fits w 7 := haddr.of_le (by unfold addressBound; omega)
  have h10 : Fits w 10 := haddr.of_le (by unfold addressBound; omega)
  have hpow (b j : ℕ) (hb : b ≤ 10) (hj : j ≤ L) : Fits w (b ^ j) := by
    apply haddr.of_le
    have hbj := Nat.pow_le_pow_left hb j
    have hjL := Nat.pow_le_pow_right (by decide : 1 ≤ (10 : ℕ)) hj
    unfold addressBound
    omega
  let P (j : ℕ) (y : Data 32) : Prop :=
    y.mem = x.mem ∧ y.regs depth = L ∧ y.regs inputSize = 7 ^ j ∧
      y.regs capacity = 10 ^ j ∧
      y.regs one = 1 ∧ y.regs seven = 7 ∧ y.regs ten = 10
  have hbody (y : Data 32) (hy : P (y.regs stage) y) (hjL : y.regs stage < L) :
      ∃ z, ExecWithin w powerBody y z 3 ∧ P (y.regs stage + 1) z ∧
        z.regs stage = y.regs stage + 1 := by
    obtain ⟨hm, hd, hi, hcap, ho, hs, ht⟩ := hy
    have hpi : Fits w (y.regs inputSize * 7) := by
      rw [hi, ← pow_succ]
      exact hpow 7 _ (by decide) (by omega)
    have hpc : Fits w (y.regs capacity * 10) := by
      rw [hcap, ← pow_succ]
      exact hpow 10 _ (by decide) (by omega)
    have hjfit : Fits w (y.regs stage + 1) :=
      haddr.of_le (by unfold addressBound; omega)
    refine WP.exists_execWithin ?_
    unfold powerBody
    wram_exec [hi, hcap, ho, hs, ht, hpi, hpc, hjfit]
    dsimp only [P]
    wram_simp [hd, ho, hs, ht, pow_succ]
    exact hm
  have hout : Fits w (2 + 7 ^ L) := haddr.of_le (by
    have := Nat.pow_le_pow_left (by decide : 7 ≤ 10) L
    unfold addressBound
    omega)
  have hscratch : Fits w (2 + 7 ^ L + 10 ^ L) := haddr.of_le (by
    have := Nat.pow_le_pow_left (by decide : 7 ≤ 10) L
    unfold addressBound
    omega)
  refine WP.exists_execWithin ?_
  unfold setup setupHead setupTail
  wram_exec [hheader, h1, h7, h10]
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.2.1) hbody (by wram_simp; omega)
    (by dsimp only [P]; wram_simp [pow_zero]))
    with u ⟨⟨hm, hd, hin, hcap, ho, hs, ht⟩, _⟩
  wram_exec [hin, hcap, h2, h1, hout, hscratch]
  constructor <;> wram_simp [outputBase, scratchBase, hm, hd, hin, hcap, ho, hs, ht]

/-- The actual flat input fits the target machine. Each signed input value uses the existing
canonical encoding; the depth and the ordinary unsigned length header are bounded separately. -/
theorem input_fits {w L : ℕ} (hw : 0 < w) (a : Fin (7 ^ L) → ℤ) (A : ℤ)
    (hA : 0 ≤ A) (ha : ∀ i, |a i| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L)) : InputFits (w + 2) (input L a) := by
  have hpow : (1 : ℤ) ≤ (7 ^ L : ℕ) := by
    exact_mod_cast Nat.one_le_pow L 7 (by decide)
  have hAfit : A < (2 : ℤ) ^ (w - 1) := by nlinarith
  refine ⟨?_, ?_⟩
  · simp only [input, List.length_cons, List.length_ofFn]
    apply haddr.of_le
    have := Nat.pow_le_pow_left (by decide : 7 ≤ 10) L
    unfold addressBound
    omega
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact haddr.of_le (by unfold addressBound; omega)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      have hi : GenericRAM.Signed.Fits w (a i) := by
        have h := abs_lt.mp ((ha i).trans_lt hAfit)
        exact ⟨hw, h.1.le, h.2⟩
      exact (Cslib.WordRAM.Signed.encode_fits hi).mono (by omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
