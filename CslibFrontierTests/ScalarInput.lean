/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ScalarInput

public section

namespace CslibFrontierTests.ScalarInput

open Cslib.Circuits.Frontier.FastContraction (representative modulus)
open Cslib.Circuits.Frontier.FastContraction.ScalarInput
open Cslib.GaloisRingArith

-- Negative constants use their two's-complement residue, and both claim polarities are checked.
example : run ⟨-3, 0, 5, 0, 0, true⟩ = true := by decide
example : run ⟨-3, 0, 5, 0, 1, false⟩ = false := by decide
example : accept ⟨-3, 0, 5, 0, 1, false⟩ = true := by decide
example : accept ⟨-3, 0, 5, 0, 1, true⟩ = false := by decide

-- Precision zero, a nonconstant coefficient and the first excluded precision bit all read zero.
example : run ⟨-1, 0, 0, 0, 0, false⟩ = false := by decide
example : run ⟨-1, 0, 7, 1, 0, false⟩ = false := by decide
example : run ⟨-1, 0, 7, 0, 7, false⟩ = false := by decide

-- A binary shift never creates lower bits, and preserves the sign extension above the shift.
example : run ⟨-1, 3, 7, 0, 2, false⟩ = false := by decide
example : run ⟨-1, 3, 7, 0, 3, true⟩ = true := by decide
example : run ⟨1, 3, 7, 0, 4, false⟩ = false := by decide

/-- The selected bit of a shifted unit is one at every binary shift. -/
theorem run_one_at_shift (shift : ℕ) :
    run ⟨1, shift, shift + 2, 0, shift, true⟩ = true := by
  change (decide (0 = 0 ∧ shift < shift + 2 ∧ shift ≤ shift) &&
    (1 : ℕ).testBit (shift - shift)) = true
  simp

/-- The bit after a shifted unit is zero at every binary shift. -/
theorem run_one_above_shift (shift : ℕ) :
    run ⟨1, shift, shift + 2, 0, shift + 1, false⟩ = false := by
  change (decide (0 = 0 ∧ shift + 1 < shift + 2 ∧ shift ≤ shift + 1) &&
    (1 : ℕ).testBit (shift + 1 - shift)) = false
  simp only [add_lt_add_iff_left, Order.lt_two_iff, Std.le_refl, le_add_iff_nonneg_right,
    zero_le, and_self, decide_true, add_tsub_cancel_left, Bool.true_and]
  decide

/-- Negative sign extension holds at arbitrary precision and binary bit index. -/
theorem run_negOne (p bit : ℕ) (hbit : bit < p) :
    run ⟨-1, 0, p, 0, bit, true⟩ = true := by
  change (decide (0 = 0 ∧ bit < p ∧ 0 ≤ bit) && !Nat.testBit 0 (bit - 0)) = true
  simp [hbit]

-- The semantic theorem transports negative sign extension at every precision and modulus.
example (m p bit : ℕ) (hbit : bit < p) :
    ((representative m p (-1 : Ring p (modulus m))).coeff 0).val.testBit bit = true := by
  have hneg : (-1 : ℤ).testBit bit = true := by
    change (!Nat.testBit 0 bit) = true
    simp
  simpa [hneg, hbit] using representative_shiftedInt_bit m p 0 0 bit (-1)

-- One actual native leaf accepts both matching claims and rejects both mismatches, with the
-- host input and the protected raw assignment arbitrary and before any query is chosen.
example :
    ∃ (K : ℕ) (assignment query : Fin K) (S : Type) (_ : Finite S)
      (runner : Turing.MultiTapeATM K Bool S) (C D : ℕ), assignment ≠ query ∧
      ∀ (outer raw : List Bool) (value claim : Bool),
        let q : Input := ⟨(value.toNat : ℤ), 0, 1, 0, 0, claim⟩
        let cfg := (Turing.MultiTapeATM.TwoWordInput.ready assignment query outer raw
          (encInput q)).withState (some runner.toPTM.initial)
        let time := C * (raw.length + (encInput q).length ^ D + 1)
        runner.HaltsWithin time cfg ∧ (runner.AcceptsWithin time cfg ↔ value = claim) := by
  obtain ⟨K, assignment, query, S, hS, runner, C, D, hne, hrunner⟩ :=
    Turing.MultiTapeATM.ScalarInput.exists_evaluator_on_words
  refine ⟨K, assignment, query, S, hS, runner, C, D, hne, ?_⟩
  intro outer raw value claim q cfg time
  have h := hrunner outer raw q 0
  have hbit : (value.toNat : ℤ).testBit 0 = value := by cases value <;> decide
  have hv : run q = value := by
    simpa [q, run] using hbit
  refine ⟨h.1, h.2.trans ?_⟩
  rw [← run_eq_representative_bit 0 q, hv]

end CslibFrontierTests.ScalarInput
