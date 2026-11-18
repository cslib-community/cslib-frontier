/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.AgreementLimit

/-! Checked instances of Goldreich's Exercise 7.10
(`Cslib.Circuits.Boolean.exists_complexity_le_and_add_le_card_agree`): both claims, for an
arbitrary function, in the exercise's form. -/

set_option linter.privateModule false

open Finset Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-- First claim: for `n ≥ 1`, a circuit of size `2 n + 4` agrees with `f` on a
`1 / 2 + 2 ^ (-n)` fraction of the inputs. -/
example {n : ℕ} (hn : 1 ≤ n) (f : BooleanFunction n) :
    ∃ g : BooleanFunction n, complexity interpretation
        (single g) ≤ 2 * n + 4 ∧
      1 / 2 + (2 : ℝ)⁻¹ ^ n ≤ (#{x | g x = f x} : ℝ) / 2 ^ n := by
  have h2 : 2 * 1 ≤ 2 ^ n := by
    calc 2 * 1 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨g, hg, hagree⟩ := exists_complexity_le_and_add_le_card_agree f h2
  refine ⟨g, by simpa [two_mul, add_assoc] using hg, ?_⟩
  simpa [inv_pow, div_eq_mul_inv] using hagree

/-- Second claim: for `t ≤ 2 ^ (n - 1)` with `n ≥ 1`, a circuit of size `t (2 n + 3) + 1` agrees
with `f` on a `1 / 2 + t 2 ^ (-n)` fraction of the inputs. -/
example {n t : ℕ} (hn : 1 ≤ n) (ht : t ≤ 2 ^ (n - 1)) (f : BooleanFunction n) :
    ∃ g : BooleanFunction n, complexity interpretation
        (single g) ≤ t * (2 * n + 3) + 1 ∧
      1 / 2 + (t : ℝ) / 2 ^ n ≤ (#{x | g x = f x} : ℝ) / 2 ^ n := by
  refine exists_complexity_le_and_add_le_card_agree f ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [Nat.add_sub_cancel] at ht
  rw [pow_succ]
  omega
