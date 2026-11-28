/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandMeaning
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged native splitting of tensor-string digits

## Main results

* `BandPreparation.exec_split`: the actual base-seven digit loop computes the binary mask
  and both compressed offsets with every native arithmetic operation charged.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open BandDigits

/-- Fixed scalar inputs to a digit loop, without execution or fit assumptions. -/
structure SplitParameters (L : ℕ) (x : Data 96) : Prop where
  /-- Original depth. -/
  levels : x.regs levels = L
  /-- Constant one. -/
  one : x.regs one = 1
  /-- Constant two. -/
  two : x.regs two = 2
  /-- Constant three. -/
  three : x.regs three = 3
  /-- Constant four. -/
  four : x.regs four = 4
  /-- Constant seven. -/
  seven : x.regs seven = 7

/-- Remaining-digit equations and elementary counter bounds during the native scan. -/
structure SplitProgress (L a : ℕ) (x : Data 96) : Prop where
  /-- Parameters are retained. -/
  fixed : SplitParameters L x
  /-- Number of consumed levels. -/
  level_le : x.regs level ≤ L
  /-- Division only decreases the residual index. -/
  residue_le : x.regs residue ≤ a
  /-- Binary place weight. -/
  mask_power : x.regs maskPower = 2 ^ x.regs level
  /-- At most one outer place is consumed per level. -/
  outer_power : x.regs outerPower ≤ 3 ^ x.regs level
  /-- At most one inner place is consumed per level. -/
  inner_power : x.regs innerPower ≤ 4 ^ x.regs level
  /-- Partial binary value is below its next place. -/
  mask_acc : x.regs maskAcc < x.regs maskPower
  /-- Partial base-three value is below its next place. -/
  outer_acc : x.regs outerAcc < x.regs outerPower
  /-- Partial base-four value is below its next place. -/
  inner_acc : x.regs innerAcc < x.regs innerPower
  /-- The binary accumulator and remaining digits give the complete mask. -/
  mask_value : x.regs maskAcc + x.regs maskPower *
    (parts (L - x.regs level) (x.regs residue)).mask = (parts L a).mask
  /-- The outer accumulator and remaining digits give the complete outer offset. -/
  outer_value : x.regs outerAcc + x.regs outerPower *
    (parts (L - x.regs level) (x.regs residue)).outer = (parts L a).outer
  /-- The inner accumulator and remaining digits give the complete inner offset. -/
  inner_value : x.regs innerAcc + x.regs innerPower *
    (parts (L - x.regs level) (x.regs residue)).inner = (parts L a).inner

/-- One native digit iteration, using only bounds derived from the original index/depth. -/
theorem exec_splitBody {w : ℕ} (L a : ℕ) (x : Data 96) (hx : SplitProgress L a x)
    (hc : (Cond.lt level levels).Holds x) (hfit : Fits w (a + L + 16 * 10 ^ L + 16)) :
    ∃ y, ExecWithin w splitBody x y 11 ∧ SplitProgress L a y ∧ y.mem = x.mem ∧
      L - y.regs level < L - x.regs level := by
  have hj : x.regs level < L := by simpa only [Cond.holds_lt, hx.fixed.levels] using hc
  have hd : x.regs residue % 7 < 7 := Nat.mod_lt _ (by decide)
  have hpow (b : ℕ) (hb : b ≤ 10) : b ^ x.regs level ≤ 10 ^ L :=
    (Nat.pow_le_pow_left hb _).trans (Nat.pow_le_pow_right (by decide) hx.level_le)
  have h2pow : 2 ^ x.regs level ≤ 10 ^ L := hpow 2 (by decide)
  have hop : x.regs outerPower ≤ 10 ^ L := hx.outer_power.trans (hpow 3 (by decide))
  have hip : x.regs innerPower ≤ 10 ^ L := hx.inner_power.trans (hpow 4 (by decide))
  have hdiv : x.regs residue / 7 ≤ a := (Nat.div_le_self _ _).trans hx.residue_le
  have hsuble : x.regs residue % 7 - 3 < 4 := by omega
  have hmulO : x.regs residue % 7 * x.regs outerPower ≤ 6 * 10 ^ L := by nlinarith
  have hmulI : (x.regs residue % 7 - 3) * x.regs innerPower ≤ 4 * 10 ^ L := by
    nlinarith only [hip, hsuble]
  have haccO := hx.outer_acc
  have haccI := hx.inner_acc
  have haccM : x.regs maskAcc < 2 ^ x.regs level := hx.mask_power ▸ hx.mask_acc
  have hrest : L - x.regs level = L - (x.regs level + 1) + 1 := by omega
  wram_exec * [splitBody]
  · have hmval := hx.mask_value
    have hoval := hx.outer_value
    have hival := hx.inner_value
    rw [hrest, parts, ite_eq_left hc] at hmval hoval hival
    dsimp only at hmval hoval hival
    rw [hx.mask_power] at hmval
    refine ⟨?_, rfl, by wram_simp; omega⟩
    refine ⟨by regs_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals wram_simp
    · omega
    · exact hdiv
    · rw [pow_succ]
    · rw [pow_succ]; exact Nat.mul_le_mul_right 3 hx.outer_power
    · exact hx.inner_power.trans (Nat.pow_le_pow_right (by decide) (by omega))
    · omega
    · nlinarith only [haccO, hc]
    · exact haccI
    · nlinarith only [hmval]
    · nlinarith only [hoval]
    · exact hival
  · have hmval := hx.mask_value
    have hoval := hx.outer_value
    have hival := hx.inner_value
    rw [hrest, parts, ite_eq_right hc] at hmval hoval hival
    dsimp only at hmval hoval hival
    rw [hx.mask_power] at hmval
    refine ⟨?_, rfl, by wram_simp; omega⟩
    refine ⟨by regs_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals wram_simp
    · omega
    · exact hdiv
    · rw [pow_succ]
    · exact hx.outer_power.trans (Nat.pow_le_pow_right (by decide) (by omega))
    · rw [pow_succ]; exact Nat.mul_le_mul_right 4 hx.inner_power
    · omega
    · exact haccO
    · nlinarith only [haccI, hsuble]
    · nlinarith only [hmval]
    · exact hoval
    · nlinarith only [hival]

/-- All digits are split by the fixed native loop. Scratch need not start at zero: every
accumulator and place weight is explicitly initialized and its initialization is charged. -/
theorem exec_split {w : ℕ} (L a : ℕ) (x : Data 96) (hx : SplitParameters L x)
    (ha : x.regs index = a) (hfit : Fits w (a + L + 16 * 10 ^ L + 16)) :
    ∃ y, ExecWithin w splitCode x y (13 * L + 10) ∧ SplitParameters L y ∧
      y.regs maskAcc = (parts L a).mask ∧ y.regs outerAcc = (parts L a).outer ∧
      y.regs innerAcc = (parts L a).inner ∧ y.mem = x.mem := by
  let I (y : Data 96) : Prop := SplitProgress L a y ∧ y.mem = x.mem
  have hb (y : Data 96) (hy : I y) (hc : (Cond.lt level levels).Holds y) :
      ∃ z, ExecWithin w splitBody y z 11 ∧ I z ∧ L - z.regs level < L - y.regs level := by
    obtain ⟨z, he, hz, hm, ht⟩ := exec_splitBody L a y hy.1 hc hfit
    exact ⟨z, he, ⟨hz, hm.trans hy.2⟩, ht⟩
  wram_exec * [splitCode, splitHead]
  wram_call (ExecWithin.loop_invariant I (fun y => L - y.regs level) hb ?_)
    with y ⟨⟨hy, hym⟩, hc⟩
  · have hlevel : y.regs level = L := by
      simp only [Cond.holds_lt, hy.fixed.levels] at hc
      have := hy.level_le
      omega
    refine ⟨by wram_simp; omega, hy.fixed, ?_, ?_, ?_, hym⟩
    · simpa only [hlevel, Nat.sub_self, parts, Nat.mul_zero, Nat.add_zero] using hy.mask_value
    · simpa only [hlevel, Nat.sub_self, parts, Nat.mul_zero, Nat.add_zero] using hy.outer_value
    · simpa only [hlevel, Nat.sub_self, parts, Nat.mul_zero, Nat.add_zero] using hy.inner_value
  · refine ⟨⟨by regs_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · wram_simp; exact Nat.zero_le L
    · wram_simp; exact le_rfl
    · wram_simp; rfl
    · wram_simp; exact le_rfl
    · wram_simp; exact le_rfl
    · wram_simp
    · wram_simp
    · wram_simp
    · wram_simp; simp only [Nat.one_mul]
    · wram_simp; simp only [Nat.one_mul]
    · wram_simp; simp only [Nat.one_mul]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
