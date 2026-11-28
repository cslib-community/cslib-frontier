/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontierTests.SpaceStoredLoop

/-!
# Substituting the context of a loop body

The body of `CslibFrontierTests.SpaceStoredLoop` compares a stored power of two with the number of
ones of the word it reads. Composing it after the logspace map that complements the word
(`Turing.MultiTapeTM.ComputableInSpace.comp_logSpace_context`) gives, without touching its
certificate, the body of the loop that computes the binary length of the number of zeros. The
complemented word is never stored.
-/

open Turing Turing.MultiTapeTM

namespace SpaceContextSubstitutionTest

open SpaceStoredLoopTest

/-- Complement the word and keep the registers. -/
def flip (p : Pow × List Bool) : Pow × List Bool := (p.1, p.2.map not)

example : step (flip (⟨1, 2⟩, [false, true, false])) = some ⟨2, 4⟩ := rfl
example : step (flip (⟨2, 4⟩, [false, true, false])) = none := rfl

theorem flip_logSpace :
    ComputableInLogSpace flip (encPair encPow encBits) (encPair encPow encBits) :=
  ComputableInLogSpace.pair (ComputableInLogSpace.fst encPow encBits)
    ((ComputableInLogSpace.bitsMap not).comp' (ComputableInLogSpace.snd encPow encBits))

/-- The body on the complemented word, within the same budget. -/
theorem step_flip_inSpace : ComputableInSpace (fun p => step (flip p))
    (encPair encPow encBits) (encOption encPow) budget :=
  step_inSpace.comp_logSpace_context flip_logSpace
    (.of_le fun p => by simp [budget, flip]) fun _ => le_rfl

/-- **The binary length of the number of zeros of a word** is computable within logarithmic
space. -/
theorem size_count_false_inSpace :
    ComputableInSpace (fun w : List Bool => Nat.size (w.count false)) encBits encNat
      fun w => Nat.log2 w.length := by
  have hcount (w : List Bool) : (w.map not).count true = w.count false := by
    induction w with
    | nil => rfl
    | cons b w ih => cases b <;> simp [ih]
  have hloop := ComputableInSpace.loopWith (encA := encBits) (encR := encPow)
    (step := fun p => step (flip p)) (init := fun _ => ⟨0, 1⟩)
    (S := fun w => Nat.log2 (encBits w).length) (B := fun w => 4 * Nat.log2 w.length + 7)
    (fun _ j => ⟨j, 2 ^ j⟩) (fun w => Nat.size (w.count false))
    (ComputableInSpace.budget_const _) step_flip_inSpace
    (fun _ => rfl)
    (fun w j hj => by
      have h : ¬w.count false < 2 ^ j := Nat.not_lt.mpr (Nat.lt_size.mp hj)
      simp only [SpaceStoredLoopTest.step, flip, hcount, h, ↓reduceIte, pow_succ, Nat.mul_comm])
    (fun w => by
      simp only [SpaceStoredLoopTest.step, flip, hcount, Nat.lt_size_self, ↓reduceIte])
    (fun w j hj => by
      have := length_encPow_le (hj.trans (by
        have := length_encNat_le_log2 (List.count_le_length (a := false) (l := w))
        rwa [encNat_apply, Nat.size_eq_bits_len] at this))
      simp only [budget, encBits_apply]
      omega)
  exact (encPow_exp_budget hloop).weaken ⟨7, fun w => by simp only [encBits_apply]; omega⟩

end SpaceContextSubstitutionTest
