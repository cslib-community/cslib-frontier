/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Algorithms.WordRAM.LRAT.Program

/-!
# An LRAT checker on the word RAM: scanning a hinted clause

The literal loop of the word-RAM LRAT checker (`Cslib.Algorithms.WordRAM.LRAT.litLoop`) scans a
hinted clause for the literals that are not false. This file states what it computes as a fold
over the clause (`Cslib.Algorithms.WordRAM.LRAT.scanLits`), relates the fold to the filter that
`Cslib.Logic.PL.CNF.propagateHints` takes, and proves that the loop computes the fold.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.LRAT

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL

/-! ### Literal codes -/

theorem litCode_injective : Function.Injective litCode := by
  rintro ⟨v, b⟩ ⟨v', b'⟩ h
  simp only [litCode] at h
  cases b <;> cases b' <;> simp_all <;> omega

theorem litCode_inj {l l' : Literal ℕ} : litCode l = litCode l' ↔ l = l' :=
  litCode_injective.eq_iff

theorem two_mul_xor_one (v : ℕ) : (2 * v) ^^^ 1 = 2 * v + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · simp [Nat.testBit_zero]
  · have : (2 * v + 1) / 2 = v := by omega
    simp [Nat.testBit_succ, this]

theorem two_mul_add_one_xor_one (v : ℕ) : (2 * v + 1) ^^^ 1 = 2 * v := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · simp [Nat.testBit_zero]
  · have : (2 * v + 1) / 2 = v := by omega
    simp [Nat.testBit_succ, this]

/-- The code of the negation of a literal flips the low bit. -/
theorem litCode_xor_one (l : Literal ℕ) : litCode l ^^^ 1 = litCode (Std.Sat.Literal.negate l) := by
  obtain ⟨v, b⟩ := l
  cases b
  · simpa [litCode, Std.Sat.Literal.negate] using two_mul_xor_one v
  · simpa [litCode, Std.Sat.Literal.negate] using two_mul_add_one_xor_one v

theorem litCode_le (l : Literal ℕ) : litCode l ≤ 2 * l.1 + 1 := by
  have := Bool.toNat_le l.2
  simp only [litCode]; omega

/-! ### The fold of the literal loop -/

/-- The state of the literal loop after a literal: a false literal is skipped; the first non-false
literal becomes the unit; a later one different from the unit sets the flag `bad`. -/
def scanStep (F : Literal ℕ → Bool) (st : Bool × ℕ × Bool) (l : Literal ℕ) : Bool × ℕ × Bool :=
  if F l then st else if !st.1 then (true, litCode l, st.2.2)
  else if st.2.1 = litCode l then st else (st.1, st.2.1, true)

/-- The state of the literal loop after a clause. -/
def scanLits (F : Literal ℕ → Bool) (st : Bool × ℕ × Bool) (ls : List (Literal ℕ)) :
    Bool × ℕ × Bool :=
  ls.foldl (scanStep F) st

/-- The abstract state of the scan after the non-false literals `f`. -/
def scanOf (f : List (Literal ℕ)) : Bool × ℕ × Bool :=
  match f with
  | [] => (false, 0, false)
  | l :: ls => (true, litCode l, !ls.all (· == l))

theorem scanStep_scanOf (F : Literal ℕ → Bool) (f : List (Literal ℕ)) (l : Literal ℕ) :
    scanStep F (scanOf f) l = scanOf (f ++ (if F l then [] else [l])) := by
  unfold scanStep
  cases hF : F l
  · rcases f with _ | ⟨a, f⟩
    · simp [scanOf]
    · simp only [scanOf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.cons_append,
        List.all_append, List.all_cons, List.all_nil, Bool.and_true]
      by_cases h : litCode a = litCode l
      · rw [litCode_inj] at h; subst h; simp
      · simp only [h, ↓reduceIte]
        have : (l == a) = false := by
          rw [beq_eq_false_iff_ne]; rintro rfl; exact h rfl
        simp [this]
  · simp

/-- **The fold computes the filter.** Scanning a clause from the initial state gives the abstract
state of its non-false literals. -/
theorem scanLits_eq (F : Literal ℕ → Bool) (ls : List (Literal ℕ)) :
    scanLits F (false, 0, false) ls = scanOf (ls.filter fun l => !F l) := by
  suffices ∀ f, scanLits F (scanOf f) ls = scanOf (f ++ ls.filter fun l => !F l) by
    simpa [scanOf] using this []
  induction ls with
  | nil => simp [scanLits]
  | cons l ls ih =>
    intro f
    simp only [scanLits, List.foldl_cons] at ih ⊢
    rw [scanStep_scanOf, ih]
    cases h : F l <;> simp [h]

/-! ### The literal loop -/

open Reg

section Specs

variable {w : ℕ}

/-- One literal of the literal loop performs `scanStep F`. -/
theorem litBody_spec (F : Literal ℕ → Bool) (l : Literal ℕ) (st : Bool × ℕ × Bool) (x : Data 28)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hlit : x.mem (x.regs lptr) = litCode l)
    (hFl : x.mem (x.regs tbase + (litCode (Std.Sat.Literal.negate l) +
      litCode (Std.Sat.Literal.negate l) + 1)) = x.regs stamp ↔ F l = true)
    (hhas : x.regs has = st.1.toNat) (hunit : x.regs unit = st.2.1)
    (hbad : x.regs bad = st.2.2.toNat)
    (hfit : Fits w (x.regs tbase + (litCode (Std.Sat.Literal.negate l) +
      litCode (Std.Sat.Literal.negate l) + 1)))
    (hfit' : Fits w (x.regs lptr + 1)) :
    ∃ y, ExecWithin w litBody x y 18 ∧ y.mem = x.mem ∧
      y.regs has = (scanStep F st l).1.toNat ∧ y.regs unit = (scanStep F st l).2.1 ∧
      y.regs bad = (scanStep F st l).2.2.toNat ∧ y.regs lptr = x.regs lptr + 1 ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧ y.regs tbase = x.regs tbase ∧
      y.regs stamp = x.regs stamp ∧ y.regs lend = x.regs lend := by
  have : Fits w (litCode l) := hfit.of_le (by
    have : litCode l ≤ litCode (Std.Sat.Literal.negate l) + 1 := by
      obtain ⟨v, b⟩ := l; cases b <;> simp [litCode, Std.Sat.Literal.negate]; omega
    omega)
  have : Fits w (litCode (Std.Sat.Literal.negate l)) := hfit.of_le (by omega)
  have : Fits w (litCode (Std.Sat.Literal.negate l) + litCode (Std.Sat.Literal.negate l)) :=
    hfit.of_le (by omega)
  have : Fits w (litCode (Std.Sat.Literal.negate l) + litCode (Std.Sat.Literal.negate l) + 1) :=
    hfit.of_le (by omega)
  have : Fits w 1 := hfit'.of_le (by omega)
  obtain ⟨h0, u0, b0⟩ := st
  simp only at hhas hunit hbad
  refine WP.exists_execWithin ?_
  unfold litBody
  by_cases hF : F l = true
  · have hv := hFl.mpr hF
    wram_exec [hlit, hone, litCode_xor_one, hv]
    wram_simp
    simp [scanStep, hF, hhas, hunit, hbad, hzero, hone]
  · have hv : ¬ _ := mt hFl.mp hF
    cases h0
    · wram_exec [hlit, hone, litCode_xor_one, hhas, hzero]
      wram_simp
      simp [scanStep, hF, hbad, hzero, hone]
    · by_cases hu : u0 = litCode l
      · wram_exec [hlit, hone, litCode_xor_one, hhas, hzero, hunit, hu]
        wram_simp
        simp [scanStep, hF, hbad, hzero, hhas, hu, hunit, hone]
      · wram_exec [hlit, hone, litCode_xor_one, hhas, hzero, hunit]
        wram_simp
        simp [scanStep, hF, hzero, hhas, hu, hunit, hone]

/-- **The literal loop** computes the fold `scanLits F` of the clause at `lptr`, where `F l` says
that the cell of the complement of `l` holds the stamp, and leaves memory unchanged. -/
theorem litLoop_spec (F : Literal ℕ → Bool) (ls : List (Literal ℕ)) (st : Bool × ℕ × Bool)
    (x : Data 28) (M : ℕ)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hl : HoldsList (x.regs lptr) (ls.map litCode) x.mem)
    (hend : x.regs lend = x.regs lptr + ls.length)
    (hF : ∀ l ∈ ls, (x.mem (x.regs tbase + (litCode (Std.Sat.Literal.negate l) +
      litCode (Std.Sat.Literal.negate l) + 1)) = x.regs stamp ↔ F l = true))
    (hhas : x.regs has = st.1.toNat) (hunit : x.regs unit = st.2.1)
    (hbad : x.regs bad = st.2.2.toNat)
    (hM : ∀ l ∈ ls, litCode l + 1 ≤ M)
    (hw : Fits w (x.regs tbase + 2 * M + 2)) (hlw : Fits w (x.regs lend)) :
    ∃ y, ExecWithin w litLoop x y (20 * ls.length + 2) ∧ y.mem = x.mem ∧
      y.regs has = (scanLits F st ls).1.toNat ∧ y.regs unit = (scanLits F st ls).2.1 ∧
      y.regs bad = (scanLits F st ls).2.2.toNat ∧ y.regs lptr = x.regs lend ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧ y.regs tbase = x.regs tbase ∧
      y.regs stamp = x.regs stamp ∧ y.regs lend = x.regs lend := by
  induction ls generalizing x st with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), rfl, hhas, hunit, hbad, by simp [hend],
      hzero, hone, rfl, rfl, rfl⟩
    simp [Cond.holds_lt, hend]
  | cons l ls ih =>
    simp only [List.length_cons] at hend
    have hc : (Cond.lt lptr lend).Holds x := by simp only [Cond.holds_lt, hend]; omega
    obtain ⟨hlit, hrest⟩ := holdsList_cons_iff.mp (by simpa using hl)
    have hMl := hM l (by simp)
    have hx1 : litCode (Std.Sat.Literal.negate l) ≤ litCode l + 1 := by
      obtain ⟨v, b⟩ := l
      cases b <;> simp [litCode, Std.Sat.Literal.negate]; omega
    obtain ⟨y, hy, hym, hyh, hyu, hyb, hyp, hy0, hy1, hyt, hys, hye⟩ :=
      litBody_spec (w := w) F l st x hzero hone hlit (hF l (by simp)) hhas hunit hbad
        (hw.of_le (by omega)) (hlw.of_le (by omega))
    obtain ⟨z, hz, hzm, hzh, hzu, hzb, hzp, hz0, hz1, hzt, hzs, hze⟩ :=
      ih (scanStep F st l) y hy0 hy1 (by rw [hym, hyp]; exact hrest) (by rw [hye, hyp, hend]; omega)
        (fun l' hl' => by rw [hym, hyt, hys]; exact hF l' (by simp [hl']))
        hyh hyu hyb (fun l' hl' => hM l' (by simp [hl'])) (by rw [hyt]; exact hw)
        (by rw [hye]; exact hlw)
    refine ⟨z, (ExecWithin.loop_iter hc hy hz).mono (by simp only [List.length_cons]; omega),
      by rw [hzm, hym], hzh, hzu, hzb, by rw [hzp, hye], hz0, hz1, by rw [hzt, hyt],
      by rw [hzs, hys], by rw [hze, hye]⟩
end Specs

end Cslib.Algorithms.WordRAM.LRAT

end
