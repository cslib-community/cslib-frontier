/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Actual cube-digit lookup step

The native scan reads a real cube digit, checks its alphabet and order, and updates
the completed-leaf code and star/P0 counts. The step theorem consumes ordinary scalar
and memory readback, with all intermediate fits derived from one address/depth envelope.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

/-- Registers modified by the actual lookup digit scan. -/
@[expose] def LookupLocal (i : Fin registers) : Prop :=
  i = Reg.address ∨ i = Reg.digit ∨ i = Reg.invalid ∨ i = Reg.fixedSeen ∨
    i = Reg.stars ∨ i = Reg.population ∨ i = Reg.temporary ∨ i = Reg.completion ∨
    i = Reg.power ∨ i = Reg.level

instance (i : Fin registers) : Decidable (LookupLocal i) :=
  inferInstanceAs (Decidable (i = Reg.address ∨ i = Reg.digit ∨ i = Reg.invalid ∨
    i = Reg.fixedSeen ∨ i = Reg.stars ∨ i = Reg.population ∨ i = Reg.temporary ∨
    i = Reg.completion ∨ i = Reg.power ∨ i = Reg.level))

/-- The real scan preserves a valid prefix and charges both failed branch instructions. -/
theorem exec_lookupDigit {w L k C d s f c v : ℕ} (x : Data registers)
    (hk : k < L) (hd : d ≤ 10) (hs : s ≤ k) (hf : f ≤ k)
    (hc : c < 10 ^ k) (_hv : v ≤ 1) (horder : d = 10 → v = 0)
    (hC : x.regs Reg.cube = C) (hread : x.mem (C + k) = d)
    (hlevel : x.regs Reg.level = k) (hstars : x.regs Reg.stars = s)
    (hpop : x.regs Reg.population = f) (hcode : x.regs Reg.completion = c)
    (hseen : x.regs Reg.fixedSeen = v) (hinvalid : x.regs Reg.invalid = 0)
    (hpow : x.regs Reg.power = 10 ^ k) (h0 : x.regs Reg.nil = 0)
    (h1 : x.regs Reg.one = 1) (h9 : x.regs Reg.nine = 9)
    (h10 : x.regs Reg.ten = 10)
    (hfit : Fits w (C + 10 ^ L + L + 20)) :
    ∃ y, ExecWithin w lookupDigit x y 16 ∧ y.mem = x.mem ∧
      y.regs Reg.level = k + 1 ∧ y.regs Reg.power = 10 ^ (k + 1) ∧
      y.regs Reg.completion = c + (if d = 10 then 9 else d) * 10 ^ k ∧
      y.regs Reg.stars = s + (if d = 10 then 1 else 0) ∧
      y.regs Reg.population = f + (if d = 9 ∨ d = 10 then 1 else 0) ∧
      y.regs Reg.fixedSeen = (if d = 9 then 1 else v) ∧ y.regs Reg.invalid = 0 ∧
      (∀ i, ¬LookupLocal i → y.regs i = x.regs i) := by
  have hpowle : 10 ^ (k + 1) ≤ 10 ^ L :=
    Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hk)
  have hpow10 : 10 ^ k * 10 = 10 ^ (k + 1) := (pow_succ 10 k).symm
  suffices ∃ y, ExecWithin w lookupDigit x y 16 ∧ y.mem = x.mem ∧
      y.regs Reg.level = k + 1 ∧ y.regs Reg.power = 10 ^ (k + 1) ∧
      y.regs Reg.completion = c + (if d = 10 then 9 else d) * 10 ^ k ∧
      y.regs Reg.stars = s + (if d = 10 then 1 else 0) ∧
      y.regs Reg.population = f + (if d = 9 ∨ d = 10 then 1 else 0) ∧
      y.regs Reg.fixedSeen = (if d = 9 then 1 else v) ∧ y.regs Reg.invalid = 0 by
    obtain ⟨y, he, hm, hl, hp, hcomp, hst, hpop', hfx, hinv⟩ := this
    exact ⟨y, he, hm, hl, hp, hcomp, hst, hpop', hfx, hinv,
      fun i hi => he.regs_eq (by unfold LookupLocal at hi; decide +revert)⟩
  unfold lookupDigit
  rcases Nat.eq_or_lt_of_le hd with rfl | hdlt
  · have hv0 : v = 0 := horder rfl
    wram_exec [*]
    wram_simp [hpow10, hv0, or_true, *]
  · have hdm : d * 10 ^ k ≤ 9 * 10 ^ k := Nat.mul_le_mul_right _ (by omega)
    have hd10 : d ≠ 10 := by omega
    wram_exec [*]
    · wram_simp [hpow10, hc, true_or, *]
    · wram_simp [hpow10, hd10, hc, or_self, *]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
