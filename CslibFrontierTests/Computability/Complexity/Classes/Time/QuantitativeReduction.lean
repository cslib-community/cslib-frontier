/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.Time.QuantitativeReduction

set_option linter.privateModule false

open Cslib.Complexity

example {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℕ, ∀ n : ℕ, (n + 1) + (n + 1) ^ d ≤ C * (n + 1) ^ d + C :=
  (clockBudget_iff id id (fun n => n + 1) hd).mpr ⟨1, 1, fun n => by
    simp only [id_eq, one_mul, le_refl, and_true]
    have h := Nat.pow_le_pow_right (Nat.succ_pos n) hd
    simp only [pow_one, Nat.succ_eq_add_one] at h
    omega⟩

example {d : ℕ} (hd : 1 ≤ d) :
    ¬ ∃ C : ℕ, ∀ n : ℕ, ((n + 1) ^ 2 + 1) ^ d ≤ C * (n + 1) ^ d + C := by
  intro h
  have budget : ∃ C : ℕ, ∀ n : ℕ, 0 + ((n + 1) ^ 2 + 1) ^ d ≤ C * (n + 1) ^ d + C := by
    simpa only [Nat.zero_add] using h
  obtain ⟨_, B, bound⟩ :=
    (clockBudget_iff id (fun n => (n + 1) ^ 2) (fun _ => 0) hd).mp budget
  have hB : (B + 1) ^ 2 + 1 ≤ B * (B + 1) := (bound B).2
  nlinarith

example : 3 + (2 * (4 + 1) ^ 2 + 7) + 4 * 4 + 9 ≤
    (1 + 2 * 2 ^ 2 + 4 * 2) * (3 + 1) ^ 2 + (1 + 7 + 9) :=
  materializedClock (d := 2) (by decide) (by decide) (by decide)
