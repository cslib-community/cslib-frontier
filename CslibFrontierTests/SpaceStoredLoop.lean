/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredLoop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontierTests.SpaceQueryLoop

/-!
# A loop whose body calls a logspace routine on the input

The binary length of the number of ones of a word, by doubling a power of two until it exceeds that
number. Every round calls the whole counting routine of `CslibFrontierTests.SpaceQueryLoop` on the
input and compares its value with the stored registers: the body is an ordinary function of the
registers and the input, assembled from the budget rules, and
`Turing.MultiTapeTM.ComputableInSpace.loopWith` runs it. No query machine is declared.
-/

open Turing Turing.MultiTapeTM

namespace SpaceStoredLoopTest

/-- The registers: an exponent and the power of two with that exponent. -/
structure Pow where
  /-- The exponent. -/
  exp : ℕ
  /-- The power of two. -/
  pow : ℕ

enc_structure encPow : Pow where exp : encNat, pow : encNat

/-- The body: double the power while it is at most the number of ones of the word. -/
def step (p : Pow × List Bool) : Option Pow :=
  if p.2.count true < p.1.pow then none else some ⟨p.1.exp + 1, 2 * p.1.pow⟩

/-- The budget of the body: the registers and the logarithm of the length of the word. -/
abbrev budget (p : Pow × List Bool) : ℕ := (encPow p.1).length + Nat.log2 (encBits p.2).length

/-- The registers, in context form. -/
theorem reg_inSpace :
    ComputableInSpace (fun p : Pow × List Bool => p.1) (encPair encPow encBits) encPow budget :=
  (ComputableInLogSpace.fst encPow encBits).inSpace_context ⟨1, fun p => by dsimp only; omega⟩

/-- The counting routine on the input, in context form. -/
theorem count_inSpace : ComputableInSpace (fun p : Pow × List Bool => p.2.count true)
    (encPair encPow encBits) encNat budget :=
  (SpaceQueryLoopTest.count_inSpace.computableInLogSpace.comp'
    (ComputableInLogSpace.snd encPow encBits)).inSpace_context ⟨1, fun p => by
      have := length_encNat_le_log2 (List.count_le_length (a := true) (l := p.2))
      dsimp only
      rw [encBits_apply]
      omega⟩

-- On a word with two ones the body doubles `1` and `2` and stops at `4`.
example : step (⟨0, 1⟩, [true, false, true]) = some ⟨1, 2⟩ := rfl
example : step (⟨1, 2⟩, [true, false, true]) = some ⟨2, 4⟩ := rfl
example : step (⟨2, 4⟩, [true, false, true]) = none := rfl

theorem step_inSpace :
    ComputableInSpace step (encPair encPow encBits) (encOption encPow) budget := by
  have hreg := reg_inSpace
  have hcount := count_inSpace
  have htwo : ComputableInSpace (fun _ : Pow × List Bool => 2) (encPair encPow encBits) encNat
      budget := ComputableInSpace.budget_const 2
  have hnone : ComputableInSpace (fun _ : Pow × List Bool => (none : Option Pow))
      (encPair encPow encBits) (encOption encPow) budget :=
    ComputableInSpace.budget_const none
  have hpow := encPow_pow_budget hreg
  have hsome := ComputableInSpace.budget_optionSome (encPow_mk_budget
    (ComputableInSpace.budget_natSucc (encPow_exp_budget hreg))
    (ComputableInSpace.budget_natMul htwo hpow))
  exact (ComputableInSpace.budget_ite (ComputableInSpace.budget_natLt hcount hpow) hnone
    hsome).of_enc_eq fun p => by
      unfold step
      by_cases h : p.2.count true < p.1.pow <;> simp [h]

theorem length_encPow_le {j ℓ : ℕ} (hj : j ≤ ℓ + 1) :
    (encPow ⟨j, 2 ^ j⟩).length ≤ 3 * ℓ + 7 := by
  have h₁ : (encNat j).length ≤ j + 1 :=
    (length_encNat_le_log2 le_rfl).trans (Nat.add_le_add_right (Nat.log2_le_self j) 1)
  have h₂ : (encNat (2 ^ j)).length = j + 1 := by
    rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_pow]
  simp only [encPow_apply, encPowFields, length_encPair, h₂]
  omega

/-- **The binary length of the number of ones of a word** is computable within logarithmic
space. -/
theorem size_count_inSpace :
    ComputableInSpace (fun w : List Bool => Nat.size (w.count true)) encBits encNat
      fun w => Nat.log2 w.length := by
  have hloop := ComputableInSpace.loopWith (encA := encBits) (encR := encPow) (step := step)
    (init := fun _ => ⟨0, 1⟩) (S := fun w => Nat.log2 (encBits w).length)
    (B := fun w => 4 * Nat.log2 w.length + 7)
    (fun _ j => ⟨j, 2 ^ j⟩) (fun w => Nat.size (w.count true))
    (ComputableInSpace.budget_const _) step_inSpace
    (fun _ => rfl)
    (fun w j hj => by
      have h : ¬w.count true < 2 ^ j := Nat.not_lt.mpr (Nat.lt_size.mp hj)
      simp only [step, h, ↓reduceIte, pow_succ, Nat.mul_comm])
    (fun w => by simp only [step, Nat.lt_size_self, ↓reduceIte])
    (fun w j hj => by
      have := length_encPow_le (hj.trans (by
        have := length_encNat_le_log2 (List.count_le_length (a := true) (l := w))
        rwa [encNat_apply, Nat.size_eq_bits_len] at this))
      simp only [budget, encBits_apply]
      omega)
  exact (encPow_exp_budget hloop).weaken ⟨7, fun w => by simp only [encBits_apply]; omega⟩

example : ComputableInLogSpace (fun w : List Bool => Nat.size (w.count true)) encBits encNat :=
  size_count_inSpace.computableInLogSpace

end SpaceStoredLoopTest
