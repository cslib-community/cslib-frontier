/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Program
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Digits

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Execution of the box-geometry digit scan

The native remainder/division loop counts P0 digits and records the place value of
the requested P0 occurrence. Every scalar fit follows from the original code, depth
and final power. The memory is preserved, including dirty caller scratch.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

/-- Registers changed by a native digit step. -/
@[expose] def DigitLocal (i : Fin registers) : Prop :=
  i = Reg.digit ∨ i = Reg.suffix ∨ i = Reg.population ∨ i = Reg.starPower ∨
    i = Reg.power ∨ i = Reg.level ∨ i = Reg.temporary

instance (i : Fin registers) : Decidable (DigitLocal i) :=
  inferInstanceAs (Decidable (i = Reg.digit ∨ i = Reg.suffix ∨ i = Reg.population ∨
    i = Reg.starPower ∨ i = Reg.power ∨ i = Reg.level ∨ i = Reg.temporary))

/-- One charged step of the real native scan, with its original-input-derived fits. -/
theorem exec_countDigit {w L c e k : ℕ} (x : Data registers) (hk : k < L)
    (h10 : x.regs Reg.ten = 10) (h9 : x.regs Reg.nine = 9)
    (h1 : x.regs Reg.one = 1) (he : x.regs Reg.stars = e)
    (hl : x.regs Reg.level = k) (hq : x.regs Reg.suffix = c / 10 ^ k)
    (hp : x.regs Reg.population = population c k)
    (hpow : x.regs Reg.power = 10 ^ k)
    (hs : x.regs Reg.starPower = starStride c e k)
    (hfit : Fits w (c + 10 ^ L + L + 12)) :
    ∃ y, ExecWithin w countDigit x y 9 ∧ y.regs Reg.level = k + 1 ∧
      y.regs Reg.suffix = c / 10 ^ (k + 1) ∧
      y.regs Reg.population = population c (k + 1) ∧
      y.regs Reg.power = 10 ^ (k + 1) ∧
      y.regs Reg.starPower = starStride c e (k + 1) ∧ y.mem = x.mem ∧
      (∀ i, ¬DigitLocal i → y.regs i = x.regs i) := by
  have hp0 := population_le c k
  have hdm : c / 10 ^ k % 10 < 10 := Nat.mod_lt _ (by decide)
  have hdiv : c / 10 ^ k / 10 ≤ c := (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
  have hpowle : 10 ^ (k + 1) ≤ 10 ^ L :=
    Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hk)
  have hpow10 : 10 ^ k * 10 = 10 ^ (k + 1) := (pow_succ 10 k).symm
  have hpowq : c / 10 ^ k / 10 = c / 10 ^ (k + 1) := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  suffices ∃ y, ExecWithin w countDigit x y 9 ∧ y.regs Reg.level = k + 1 ∧
      y.regs Reg.suffix = c / 10 ^ (k + 1) ∧
      y.regs Reg.population = population c (k + 1) ∧
      y.regs Reg.power = 10 ^ (k + 1) ∧
      y.regs Reg.starPower = starStride c e (k + 1) ∧ y.mem = x.mem by
    obtain ⟨y, hy, hl', hq', hp', hpow', hs', hm'⟩ := this
    exact ⟨y, hy, hl', hq', hp', hpow', hs', hm',
      fun i hi => hy.regs_eq (by unfold DigitLocal at hi; decide +revert)⟩
  unfold countDigit
  wram_exec [*]
  · rename_i hd
    wram_simp [population_succ, starStride, digitAt, hd, hc, hpowq, hpow10]
  · rename_i hd
    wram_simp [population_succ, starStride, digitAt, hd, hc, hs, hpowq, hpow10]
  · wram_simp [population_succ, starStride, digitAt, hc, hs, hp, hpowq, hpow10, false_and]

/-- Registers changed by the scan, including its descriptor initialization. -/
@[expose] def InspectLocal (i : Fin registers) : Prop :=
  DigitLocal i ∨ i = Reg.stars ∨ i = Reg.completion

instance (i : Fin registers) : Decidable (InspectLocal i) :=
  inferInstanceAs (Decidable (DigitLocal i ∨ i = Reg.stars ∨ i = Reg.completion))

/-- The complete digit loop computes the population and highest-star stride from a raw slot. -/
theorem exec_inspect {w L s : ℕ} (x : Data registers)
    (hL : x.regs Reg.levels = L) (hT : x.regs Reg.span = 10 ^ L)
    (hslot : x.regs Reg.slot = s) (h1 : x.regs Reg.one = 1)
    (h10 : x.regs Reg.ten = 10) (h9 : x.regs Reg.nine = 9)
    (hfit : Fits w (s + 10 ^ L + L + 12)) :
    ∃ y, ExecWithin w inspect x y (11 * L + 9) ∧
      y.regs Reg.stars = s / 10 ^ L ∧ y.regs Reg.completion = s % 10 ^ L ∧
      y.regs Reg.population = population (s % 10 ^ L) L ∧
      y.regs Reg.starPower = starStride (s % 10 ^ L) (s / 10 ^ L) L ∧
      y.mem = x.mem ∧ (∀ i, ¬InspectLocal i → y.regs i = x.regs i) := by
  let e := s / 10 ^ L
  let c := s % 10 ^ L
  have hc : c ≤ s := Nat.mod_le _ _
  have he : e ≤ s := Nat.div_le_self _ _
  suffices ∃ y, ExecWithin w inspect x y (11 * L + 9) ∧
      y.regs Reg.stars = e ∧ y.regs Reg.completion = c ∧
      y.regs Reg.population = population c L ∧
      y.regs Reg.starPower = starStride c e L ∧ y.mem = x.mem by
    obtain ⟨y, hy, hs', hc', hp', hsp', hm'⟩ := this
    exact ⟨y, hy, hs', hc', hp', hsp', hm',
      fun i hi => hy.regs_eq (by unfold InspectLocal DigitLocal at hi; decide +revert)⟩
  let P (j : ℕ) (y : Data registers) : Prop :=
    y.regs Reg.levels = L ∧ y.regs Reg.one = 1 ∧ y.regs Reg.ten = 10 ∧ y.regs Reg.nine = 9 ∧
      y.regs Reg.stars = e ∧ y.regs Reg.completion = c ∧
      y.regs Reg.suffix = c / 10 ^ j ∧ y.regs Reg.population = population c j ∧
      y.regs Reg.power = 10 ^ j ∧ y.regs Reg.starPower = starStride c e j ∧ y.mem = x.mem
  have hb (y : Data registers) (hy : P (y.regs Reg.level) y) (hk : y.regs Reg.level < L) :
      ∃ z, ExecWithin w countDigit y z 9 ∧ P (y.regs Reg.level + 1) z ∧
        z.regs Reg.level = y.regs Reg.level + 1 := by
    obtain ⟨yL, y1, y10, y9, ystars, ycomp, hq, hp, hpow, hstar, hm⟩ := hy
    obtain ⟨z, hz, hzl, hzq, hzp, hzpow, hzs, hzm, hzf⟩ :=
      exec_countDigit y hk y10 y9 y1 ystars rfl hq hp hpow hstar (hfit.of_le (by omega))
    refine ⟨z, hz, ⟨(hzf _ (by decide)).trans yL, (hzf _ (by decide)).trans y1,
      (hzf _ (by decide)).trans y10, (hzf _ (by decide)).trans y9,
      (hzf _ (by decide)).trans ystars, (hzf _ (by decide)).trans ycomp,
      hzq, hzp, hzpow, hzs, hzm.trans hm⟩, hzl⟩
  refine WP.exists_execWithin ?_
  unfold inspect inspectSetup
  wram_exec [*]
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.1) hb (by wram_simp; exact Nat.zero_le _)
    (by wram_simp [P, population_zero, starStride, pow_zero, Nat.div_one, e, c, *]))
    with y ⟨⟨_, _, _, _, ystars, ycomp, _, hpop, _, hstar, hm⟩, _⟩
  exact ⟨by wram_simp; omega, ystars, ycomp, hpop, hstar, by simpa only [Data.set_mem] using hm⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
