/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Polylogarithms are eventually below the identity

`eventually_polylog_le C d`: eventually `(C·(log₂ N + 1))^d ≤ N`. Also
`log₂ N → ∞`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Polylog

open Filter

theorem eventually_poly_le_two_pow (C d : ℕ) : ∀ᶠ m : ℕ in atTop, (C * (m + 1)) ^ d ≤ 2 ^ m := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt d (by norm_num : (1 : ℝ) < 2)
  have hev := (h.eventually (gt_mem_nhds
      (show (0 : ℝ) < 1 / (2 * (C + 1) ^ d * 2 ^ d) by positivity)))
  filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_lt_iff₀ h2m] at hm
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have key : ((C * (m + 1) : ℕ) : ℝ) ^ d ≤ (2 : ℝ) ^ m := by
    push_cast
    have hle : (C : ℝ) * (m + 1) ≤ (C + 1) * 2 * m := by nlinarith
    calc ((C : ℝ) * (m + 1)) ^ d ≤ ((C + 1) * 2 * m) ^ d := by gcongr
      _ = (2 * (C + 1) ^ d * 2 ^ d) * (m ^ d) / 2 := by rw [mul_pow, mul_pow]; ring
      _ ≤ (2 * (C + 1) ^ d * 2 ^ d) * (1 / (2 * (C + 1) ^ d * 2 ^ d) * 2 ^ m) / 2 := by gcongr
      _ = 2 ^ m / 2 := by field_simp
      _ ≤ 2 ^ m := by linarith
  exact_mod_cast key

theorem tendsto_log2 : Tendsto (fun N : ℕ => N.log2) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨2 ^ b, fun N hN => ?_⟩
  exact (Nat.le_log2 (by have := Nat.one_le_two_pow (n := b); omega)).mpr hN

theorem eventually_polylog_le (C d : ℕ) : ∀ᶠ N : ℕ in atTop, (C * (N.log2 + 1)) ^ d ≤ N := by
  filter_upwards [tendsto_log2.eventually (eventually_poly_le_two_pow C d), eventually_ge_atTop 1]
    with N hN hN1
  exact hN.trans (Nat.log2_self_le (by omega))

end Cslib.Complexity.NtimeDspace.Polylog
