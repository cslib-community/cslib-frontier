/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification
import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.RandomFunction

/-! Checked clients of Arora and Barak's Exercise 16.3
(`Cslib.Circuits.Boolean.exists_forall_complexity_le_card_agree_lt`). -/

set_option linter.privateModule false

open Finset Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-- The exercise at `n = 400`: some function on 400 bits has `H_avg ≥ 2 ^ 40`. -/
example : ∃ f : BooleanFunction 400, ∃ S : ℕ, (2 : ℝ) ^ (40 : ℝ) ≤ S ∧
    ∀ g : BooleanFunction 400, complexity interpretation (single g) ≤ S →
      (#{x | g x = f x} : ℝ) / 2 ^ 400 < 1 / 2 + 1 / S := by
  obtain ⟨f, S, hS, hf⟩ := exists_forall_complexity_le_card_agree_lt (n := 400) le_rfl
  exact ⟨f, S, by norm_num at hS ⊢; exact hS, hf⟩

/-- The strict bound gives the library's non-strict average-case hardness predicate. -/
example {n : ℕ} (hn : 400 ≤ n) :
    ∃ f : BooleanFunction n, ∃ S : ℕ, (2 : ℝ) ^ ((n : ℝ) / 10) ≤ S ∧ IsAverageCaseHard f S := by
  obtain ⟨f, S, hS, hf⟩ := exists_forall_complexity_le_card_agree_lt hn
  exact ⟨f, S, hS, fun g hg => (hf g hg).le⟩
