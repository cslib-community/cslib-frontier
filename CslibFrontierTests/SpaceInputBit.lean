/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.InputBit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Tactic.Space

/-!
# A loop body that reads the input where its registers point

Counting the ones of a word again, as in `CslibFrontierTests.SpaceQueryLoop`, but with the body
written as a function of the registers and the word: it looks up `w[pos]?` with the library
accessor `Turing.MultiTapeTM.ComputableInSpace.inputBit` and returns the next registers. There is
no reading protocol, no phase and no finished flag in the registers.
-/

-- This module contains only checked clients.
set_option linter.privateModule false

open Turing Turing.MultiTapeTM

namespace SpaceInputBitTest

/-- The registers: the position and the number of ones before it, both in binary; the position is
framed. -/
abbrev encReg : ℕ × ℕ ↪ List Bool := encPair encNat encNat

/-- The body: count the bit at the position, or stop past the end of the word. -/
def step (p : (ℕ × ℕ) × List Bool) : Option (ℕ × ℕ) :=
  if p.2[p.1.1]?.isSome then some (p.1.1 + 1, p.1.2 + if p.2[p.1.1]?.getD false then 1 else 0)
  else none

example : step ((1, 1), [true, false, true]) = some (2, 1) := rfl
example : step ((2, 1), [true, false, true]) = some (3, 2) := rfl
example : step ((3, 2), [true, false, true]) = none := rfl

/-- The budget of the body: the registers and the logarithm of the length of the word. -/
abbrev budget (p : (ℕ × ℕ) × List Bool) : ℕ := (encReg p.1).length + Nat.log2 (encBits p.2).length

theorem reg_inSpace : ComputableInSpace (fun p : (ℕ × ℕ) × List Bool => p.1)
    (encPair encReg encBits) encReg budget :=
  (ComputableInLogSpace.fst encReg encBits).inSpace_context (.of_le fun _ => Nat.le_add_right _ _)

/-- The bit of the word at the stored position: the accessor after the logspace map that keeps the
position of the registers. -/
theorem bit_inSpace : ComputableInSpace (fun p : (ℕ × ℕ) × List Bool => p.2[p.1.1]?)
    (encPair encReg encBits) (encOption encBool) budget :=
  (ComputableInSpace.inputBit encBits).comp_logSpace_context
    (f := fun p : (ℕ × ℕ) × List Bool => (p.1.1, p.2))
    (ComputableInLogSpace.pair
      ((ComputableInLogSpace.fst encNat encNat).comp' (ComputableInLogSpace.fst encReg encBits))
      (ComputableInLogSpace.snd encReg encBits))
    (.of_le fun p => by simp only [length_encPair]; omega) fun _ => le_rfl

theorem step_inSpace :
    ComputableInSpace step (encPair encReg encBits) (encOption encReg) budget := by
  have hreg := reg_inSpace
  have hbit := bit_inSpace
  space [step]

/-- **The number of ones of a word**, by a loop whose body reads the word at its stored
position. -/
theorem count_inSpace : ComputableInSpace (fun w : List Bool => w.count true) encBits encNat
    fun w => Nat.log2 w.length := by
  have hloop := ComputableInSpace.loopWith (encA := encBits) (encR := encReg) (step := step)
    (init := fun _ => (0, 0)) (S := fun w => Nat.log2 (encBits w).length)
    (B := fun w => 4 * Nat.log2 w.length + 4)
    (fun w j => (j, (w.take j).count true)) (fun w => w.length)
    (ComputableInSpace.budget_const _) step_inSpace
    (fun _ => rfl)
    (fun w j hj => by
      have htake := List.take_succ_eq_append_getElem hj
      cases hb : w[j] <;> simp [step, List.getElem?_eq_getElem hj, hb, htake])
    (fun w => by simp [step])
    (fun w j hj => by
      have h₁ := length_encNat_le_log2 hj
      have h₂ := length_encNat_le_log2 (((List.take_sublist j w).count_le true).trans
        List.count_le_length)
      simp only [budget, length_encPair, encBits_apply]
      omega)
  exact (hloop.snd'.of_enc_eq fun w => by simp).weaken
    ⟨6, fun w => by simp only [encBits_apply]; omega⟩

end SpaceInputBitTest
