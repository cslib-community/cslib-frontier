/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test suite)

import CslibFrontier.Crypto.Computational.OneTimeSignature.DominationFree
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.Nat.Log

/-! Checked positive clients, parameter-table checks, and counterexamples for
`Cslib.Crypto.OneTimeSignature.DominationFree`,
`Cslib.Crypto.OneTimeSignature.winternitzDigits`, and
`Cslib.Crypto.OneTimeSignature.winternitzDigitList_polyTime`. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.DominationFree

open Cslib.Crypto.OneTimeSignature Turing.MultiTapeTM

-- Lemma 14.5 as printed (p. 593): messages below `2 ^ v`, `2 ^ v ≤ (d + 1) ^ n0`, printed `n1`.
example {v d n0 : ℕ} (hn0 : 2 ^ v ≤ (d + 1) ^ n0) :
    DominationFree (fun m : Fin (2 ^ v) =>
      winternitzDigits d n0 (Nat.clog (d + 1) (d * n0) + 1) m.val) :=
  winternitzDigits_dominationFree Fin.val_injective (fun m => m.isLt.trans_le hn0) (by
    rcases d with _ | d
    · simp
    · exact (Nat.le_pow_clog (by lia) _).trans_lt
        (Nat.pow_lt_pow_right (by lia) (Nat.lt_succ_self _)))

-- The table of p. 592 (`v = 256`; `d = 1, 3, 15, 1023`): least `n0`, least `n1`, and `n = n0 + n1`.
example : (2 ^ 256 ≤ 2 ^ 256 ∧ ¬ 2 ^ 256 ≤ 2 ^ 255) ∧ (1 * 256 < 2 ^ 9 ∧ ¬ 1 * 256 < 2 ^ 8) ∧
    256 + 9 = 265 := by decide
example : (2 ^ 256 ≤ 4 ^ 128 ∧ ¬ 2 ^ 256 ≤ 4 ^ 127) ∧ (3 * 128 < 4 ^ 5 ∧ ¬ 3 * 128 < 4 ^ 4) ∧
    128 + 5 = 133 := by decide
example : (2 ^ 256 ≤ 16 ^ 64 ∧ ¬ 2 ^ 256 ≤ 16 ^ 63) ∧ (15 * 64 < 16 ^ 3 ∧ ¬ 15 * 64 < 16 ^ 2) ∧
    64 + 3 = 67 := by decide
example : (2 ^ 256 ≤ 1024 ^ 26 ∧ ¬ 2 ^ 256 ≤ 1024 ^ 25) ∧
    (1023 * 26 < 1024 ^ 2 ∧ ¬ 1023 * 26 < 1024 ^ 1) ∧ 26 + 2 = 28 := by decide

-- The printed `n1 = ⌈log_{d+1}(d * n0)⌉ + 1` is 9, 6, 4, 3: one more than the table for
-- `d = 3, 15, 1023`.
example : Nat.clog 2 (1 * 256) + 1 = 9 ∧ Nat.clog 4 (3 * 128) + 1 = 6 ∧
    Nat.clog 16 (15 * 64) + 1 = 4 ∧ Nat.clog 1024 (1023 * 26) + 1 = 3 := by decide

-- Positive `DominationFree` applications (`d = 3`, and `d = 0` on a subsingleton message type).
example : DominationFree (fun m : Fin 16 => winternitzDigits 3 2 2 m.val) :=
  winternitzDigits_dominationFree Fin.val_injective (fun m => m.isLt) (by decide)

example : DominationFree (fun m : Fin 1 => winternitzDigits 0 5 0 m.val) :=
  winternitzDigits_dominationFree Fin.val_injective (fun m => by simp) (by simp)

-- Direct checks of `dominationFree_of_append_checksum` and the `radixDigits` lemmas.
example :
    DominationFree (fun m : Fin 3 =>
      Fin.append (fun _ : Fin 1 => m) (fun _ : Fin 1 => (⟨2 - m.val, by omega⟩ : Fin 3))) :=
  dominationFree_of_append_checksum (checksum := fun m : Fin 3 => 2 - m.val) (C := 2)
    (fun _ _ h => congrFun h 0)
    (fun m => by simp; omega)
    (fun _ _ h => by simpa using h 0)

example : ∑ i : Fin 2, (radixDigits 3 2 6 i).val * 4 ^ i.val = 6 :=
  sum_radixDigits_mul_pow (by decide)

example {x y : ℕ} (hx : x < 16) (hy : y < 16)
    (h : radixDigits 3 2 x = radixDigits 3 2 y) : x = y :=
  radixDigits_injOn 3 2 hx hy h

example : 5 ≤ 6 :=
  le_of_radixDigits_le (by decide) (by decide) (by decide : radixDigits 3 2 5 ≤ radixDigits 3 2 6)

-- List form checks (`winternitzDigitList_eq_ofFn`, length, and `getElem`).
example : winternitzDigitList 3 2 2 6 = [2, 1, 3, 0] := by
  rw [winternitzDigitList_eq_ofFn]
  decide

example : (winternitzDigitList 3 2 2 6).length = 4 :=
  winternitzDigitList_length 3 2 2 6

example : (winternitzDigitList 3 2 2 6)[0]'(by simp [winternitzDigitList_length]) = 2 := by
  rw [getElem_winternitzDigitList]
  decide

example : (winternitzDigitList 3 2 2 6)[2]'(by simp [winternitzDigitList_length]) = 3 := by
  rw [getElem_winternitzDigitList]
  decide

-- Caller of `winternitzDigitList_polyTime` at fixed `d = 15`, `n0 = 64`, `n1 = 3`.
example : ComputableInPolyTime (fun m : ℕ => winternitzDigitList 15 64 3 m) encNat
    (encList encNat) :=
  ComputableInPolyTime.of_tidy <| winternitzDigitList_polyTime.tidy.comp
    ((ComputableTidilyInPolyTime.const 15).prod ((ComputableTidilyInPolyTime.const 64).prod
      ((ComputableTidilyInPolyTime.const 3).prod ComputableTidilyInPolyTime.id')))

-- Dropping `hf_inj` breaks `winternitzDigits_dominationFree`.
example : ¬ DominationFree (fun _ : Fin 2 => winternitzDigits 1 1 1 0) :=
  fun h => h (by decide : (0 : Fin 2) ≠ 1) le_rfl

-- Dropping `hf_bound` (`∀ m, f m < (d + 1) ^ n0`) breaks `winternitzDigits_dominationFree`.
example : ¬ DominationFree (fun m : Fin 5 => winternitzDigits 1 2 2 m.val) := by
  intro h
  have hne : (0 : Fin 5) ≠ 4 := by decide
  exact h hne (by decide)

-- Dropping `hn1` (`d * n0 < (d + 1) ^ n1`) breaks `winternitzDigits_dominationFree`.
example : ¬ DominationFree (fun m : Fin 4 => winternitzDigits 1 2 1 m.val) := by
  intro h
  have hne : (0 : Fin 4) ≠ 3 := by decide
  exact h hne (by decide)

end CslibFrontierTests.Crypto.DominationFree
