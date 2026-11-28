/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.PackProgram
import Mathlib.Tactic.Linarith
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Execution of the native wanted-output digit loop

## Main results

* `Wanted.exec_pack`: actual unsigned packing with an explicit linear instruction bound
  and unchanged memory, for arbitrary initial scratch-register contents.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage.QueryDigits

/-- Scalar contents retained throughout packing. These are only register equalities. -/
structure PackParameters (L : ℕ) (x : Data 16) : Prop where
  /-- Original depth. -/
  depth : x.regs depth = L
  /-- Initialized unit. -/
  one : x.regs one = 1
  /-- Binary radix. -/
  two : x.regs two = 2
  /-- Compressed offset radix. -/
  three : x.regs three = 3
  /-- Output radix. -/
  ten : x.regs ten = 10
  /-- Inner output digit. -/
  nine : x.regs nine = 9

/-- A consumed prefix and the remaining arithmetic recurrence give the original output. -/
structure PackProgress (L M R C : ℕ) (x : Data 16) : Prop where
  /-- Persistent constants and depth. -/
  fixed : PackParameters L x
  /-- A coordinate is visited at most once. -/
  level_le : x.regs level ≤ L
  /-- Binary division decreases the mask. -/
  mask_le : x.regs mask ≤ M
  /-- Ternary division decreases the row offset. -/
  row_le : x.regs row ≤ R
  /-- Ternary division decreases the column offset. -/
  col_le : x.regs col ≤ C
  /-- Actual next output place. -/
  power_eq : x.regs power = 10 ^ x.regs level
  /-- Already emitted digits fit below the next place. -/
  code_lt : x.regs code < x.regs power
  /-- Prefix and residual recurrence have the desired complete value. -/
  value : x.regs code + x.regs power *
    pack (L - x.regs level) (x.regs mask) (x.regs row) (x.regs col) = pack L M R C

/-- One coordinate's actual test, arithmetic and register updates. The numeric budget is
derived from original inputs, rather than an assumed bound on intermediate states. -/
theorem exec_packBody {w L M R C : ℕ} (x : Data 16) (hx : PackProgress L M R C x)
    (hc : (Cond.lt level depth).Holds x)
    (hfit : Fits w (M + R + C + L + 32 * 10 ^ L + 32)) :
    ∃ y, ExecWithin w packBody x y 13 ∧ PackProgress L M R C y ∧ y.mem = x.mem ∧
      L - y.regs level < L - x.regs level := by
  have hj : x.regs level < L := by simpa only [Cond.holds_lt, hx.fixed.depth] using hc
  clear hc
  have hr := Nat.mod_lt (x.regs row) (by decide : 0 < 3)
  have hcol := Nat.mod_lt (x.regs col) (by decide : 0 < 3)
  have hp : x.regs power ≤ 10 ^ L := by
    rw [hx.power_eq]
    exact Nat.pow_le_pow_right (by decide) hx.level_le
  have hmfit : Fits w (x.regs mask / 2) := hfit.of_le
    ((Nat.div_le_self _ _).trans (by have := hx.mask_le; omega))
  have hbit : Fits w (x.regs mask % 2) := hfit.of_le (by
    have := Nat.mod_lt (x.regs mask) (by decide : 0 < 2)
    omega)
  have hpfit : Fits w (x.regs power * 10) := hfit.of_le (by omega)
  have hjfit : Fits w (x.regs level + 1) := hfit.of_le (by omega)
  have hrest : L - x.regs level = L - (x.regs level + 1) + 1 := by omega
  let d := (x.regs row % 3) * 3 + x.regs col % 3
  have hd : d < 9 := by dsimp [d]; omega
  have hrd : Fits w (x.regs row % 3) := hfit.of_le (by omega)
  have hr3 : Fits w (x.regs row % 3 * 3) := hfit.of_le (by omega)
  have hcd : Fits w (x.regs col % 3) := hfit.of_le (by omega)
  have hdf : Fits w d := hfit.of_le (by omega)
  have hrq : Fits w (x.regs row / 3) := hfit.of_le
    ((Nat.div_le_self _ _).trans (by have := hx.row_le; omega))
  have hcq : Fits w (x.regs col / 3) := hfit.of_le
    ((Nat.div_le_self _ _).trans (by have := hx.col_le; omega))
  have hmul0 : Fits w (d * x.regs power) := hfit.of_le (by nlinarith)
  have hadd0 : Fits w (x.regs code + d * x.regs power) := hfit.of_le (by
    have := hx.code_lt; nlinarith)
  have h9 : Fits w 9 := hfit.of_le (by omega)
  have hmul9 : Fits w (9 * x.regs power) := hfit.of_le (by omega)
  have hadd9 : Fits w (x.regs code + 9 * x.regs power) := hfit.of_le (by
    have := hx.code_lt; omega)
  dsimp only [d] at hdf hmul0 hadd0
  refine WP.exists_execWithin ?_
  wram_exec [packBody, hx.fixed.one, hx.fixed.two, hx.fixed.three, hx.fixed.nine, hx.fixed.ten,
    hmfit, hbit, hpfit, hjfit, hrd, hr3, hcd, hdf, hrq, hcq, hmul0, hadd0,
    h9, hmul9, hadd9]
  · have hb : x.regs mask % 2 = 0 := Nat.lt_one_iff.mp hc
    refine ⟨⟨by regs_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
    · wram_simp; omega
    · wram_simp; exact (Nat.div_le_self _ _).trans hx.mask_le
    · wram_simp; exact (Nat.div_le_self _ _).trans hx.row_le
    · wram_simp; exact (Nat.div_le_self _ _).trans hx.col_le
    · wram_simp [hx.power_eq, pow_succ]
    · have := hx.code_lt
      wram_simp
      dsimp [d] at hd
      nlinarith
    · have hv := hx.value
      rw [hrest, pack, ite_eq_left hb] at hv
      wram_simp
      nlinarith only [hv]
    · wram_simp; omega
  · have hb : x.regs mask % 2 ≠ 0 := fun h => hc (by omega)
    refine ⟨⟨by regs_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
    · wram_simp; omega
    · wram_simp; exact (Nat.div_le_self _ _).trans hx.mask_le
    · wram_simp; exact hx.row_le
    · wram_simp; exact hx.col_le
    · wram_simp [hx.power_eq, pow_succ]
    · have := hx.code_lt
      wram_simp
      omega
    · have hv := hx.value
      rw [hrest, pack, ite_eq_right hb] at hv
      wram_simp
      nlinarith only [hv]
    · wram_simp; omega

/-- Execute the entire fixed packer from ordinary register inputs. Every branch, division,
remainder, index update and loop control is charged; memory and the depth are preserved. -/
theorem exec_pack {w : ℕ} (L M R C : ℕ) (x : Data 16)
    (hL : x.regs depth = L) (hM : x.regs mask = M) (hR : x.regs row = R)
    (hC : x.regs col = C) (hfit : Fits w (M + R + C + L + 32 * 10 ^ L + 32)) :
    ∃ y, ExecWithin w packCode x y (15 * L + 10) ∧
      y.regs code = pack L M R C ∧ y.regs depth = L ∧ y.mem = x.mem := by
  have hf (v : ℕ) (hv : v ≤ 10) : Fits w v := hfit.of_le (by omega)
  let I (z : Data 16) : Prop := PackProgress L M R C z ∧ z.mem = x.mem
  have hb (z : Data 16) (hz : I z) (hc : (Cond.lt level depth).Holds z) :
      ∃ u, ExecWithin w packBody z u 13 ∧ I u ∧
        L - u.regs level < L - z.regs level := by
    obtain ⟨u, he, hu, hm, ht⟩ := exec_packBody z hz.1 hc hfit
    exact ⟨u, he, ⟨hu, hm.trans hz.2⟩, ht⟩
  refine WP.exists_execWithin ?_
  wram_exec [packCode, packHead,
    hf 1 (by decide), hf 2 (by decide), hf 3 (by decide), hf 9 (by decide),
    hf 10 (by decide)]
  wram_call (ExecWithin.loop_invariant I (fun z => L - z.regs level) hb
    ⟨⟨by constructor <;> wram_simp [hL], by wram_simp; omega, by wram_simp [hM]; exact le_rfl,
      by wram_simp [hR]; exact le_rfl, by wram_simp [hC]; exact le_rfl, by wram_simp [pow_zero],
      by wram_simp, by wram_simp [hM, hR, hC]; simp⟩, rfl⟩) with y ⟨hy, hc⟩
  have hend : y.regs level = L := by
    simp only [Cond.holds_lt, hy.1.fixed.depth] at hc
    have := hy.1.level_le
    omega
  refine ⟨by wram_simp; omega, ?_, hy.1.fixed.depth, hy.2⟩
  simpa only [hend, Nat.sub_self, pack, Nat.mul_zero, Nat.add_zero] using hy.1.value

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
