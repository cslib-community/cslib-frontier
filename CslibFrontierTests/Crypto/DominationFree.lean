/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test suite)

public import CslibFrontier.Crypto.Computational.OneTimeSignature.DominationFree
import Mathlib.Data.Nat.Log

/-! Checked positive clients, parameter-table checks, and counterexample probes for
`Cslib.Crypto.DominationFree` and `Cslib.Crypto.winternitzDigits`. -/

public section

namespace DominationFreeTests

open Cslib.Crypto

/-- Tight `n1` sufficiency via `Nat.clog` when `0 < d`: `(d + 1) ^ (Nat.clog (d + 1) (d * n0) + 1)`
always exceeds `d * n0`, as does `(d + 1) ^ Nat.clog (d + 1) (d * n0 + 1)`. -/
example {d n0 : ℕ} (hd : 0 < d) :
    d * n0 < (d + 1) ^ (Nat.clog (d + 1) (d * n0) + 1) := by
  have h1 : 1 < d + 1 := Nat.succ_lt_succ hd
  calc
    d * n0 ≤ (d + 1) ^ Nat.clog (d + 1) (d * n0) := Nat.le_pow_clog h1 _
    _ < (d + 1) ^ (Nat.clog (d + 1) (d * n0) + 1) :=
      Nat.pow_lt_pow_right h1 (Nat.lt_succ_self _)

example {d n0 : ℕ} (hd : 0 < d) :
    d * n0 < (d + 1) ^ Nat.clog (d + 1) (d * n0 + 1) :=
  Nat.lt_of_succ_le (Nat.le_pow_clog (Nat.succ_lt_succ hd) (d * n0 + 1))

-- Boneh–Shoup §14.3.1, p. 592 table for 256-bit messages (`w = 2, 4, 10`, i.e., `d = 3, 15, 1023`).
example : 3 * 128 < 4 ^ 5 ∧ Nat.clog 4 (3 * 128 + 1) = 5 := by decide
example : 15 * 64 < 16 ^ 3 ∧ Nat.clog 16 (15 * 64 + 1) = 3 := by decide
example : 1023 * 26 < 1024 ^ 2 ∧ Nat.clog 1024 (1023 * 26 + 1) = 2 := by decide

-- When `d * n0` is an exact power of `d + 1`, `Nat.clog (d + 1) (d * n0)` is one short of strict
-- inequality, whereas `Nat.clog (d + 1) (d * n0 + 1)` matches `⌊log_{d+1}(d * n0)⌋ + 1`.
example : ¬ (1 * 4 < 2 ^ Nat.clog 2 (1 * 4)) ∧ 1 * 4 < 2 ^ Nat.clog 2 (1 * 4 + 1) := by decide

-- Positive `DominationFree` application on `Fin 16` with `d = 3, n0 = 2, n1 = 2`.
example : DominationFree (fun m : Fin 16 => winternitzDigits 3 2 2 m.val) :=
  winternitzDigits_dominationFree Fin.val_injective (fun m => m.isLt) (by decide)

-- Concrete digit values and agreement between `winternitzDigits` and `winternitzDigitList`.
example : (winternitzDigits 3 2 2 6 0).val = 2 := by decide
example : (winternitzDigits 3 2 2 6 1).val = 1 := by decide
example : (winternitzDigits 3 2 2 6 2).val = 3 := by decide
example : (winternitzDigits 3 2 2 6 3).val = 0 := by decide

example : (winternitzDigitList 3 2 2 6).length = 4 :=
  winternitzDigitList_length 3 2 2 6

example : (winternitzDigitList 3 2 2 6)[0]'(by simp [winternitzDigitList_length]) = 2 := by
  rw [getElem_winternitzDigitList]
  decide

example : (winternitzDigitList 3 2 2 6)[2]'(by simp [winternitzDigitList_length]) = 3 := by
  rw [getElem_winternitzDigitList]
  decide

-- Counterexample probe 5: dropping `∀ m, f m < (d + 1) ^ n0` breaks
-- `winternitzDigits_dominationFree`.
example : ¬ DominationFree (fun m : Fin 5 => winternitzDigits 1 2 2 m.val) := by
  intro h
  have hne : (0 : Fin 5) ≠ 4 := by decide
  exact h hne (by decide)

-- Counterexample probe 6: dropping `d * n0 < (d + 1) ^ n1` breaks
-- `winternitzDigits_dominationFree`.
example : ¬ DominationFree (fun m : Fin 4 => winternitzDigits 1 2 1 m.val) := by
  intro h
  have hne : (0 : Fin 4) ≠ 3 := by decide
  exact h hne (by decide)

end DominationFreeTests
