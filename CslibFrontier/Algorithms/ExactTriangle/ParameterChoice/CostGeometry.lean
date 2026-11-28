/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.ExactTriangle.ParameterChoice
public import CslibFrontier.Algorithms.ExactTriangle.Splitting
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite cost geometry of the integer box parameters

The nineteen-factor reservation gives the common `n^3/g` scale for actual preparation,
products, query/root control and scans. Group rounding supplies raw saving `2/1197`;
logarithmic factors remain to be absorbed by the complete native caller.
-/

public section

namespace Cslib.Algorithms.ExactTriangle.ParameterChoice

/-- Preparation's extra window and two group factors fit within nineteen reserved factors. -/
theorem window_mul_groups_sq_le {n : ℕ} (hn : 0 < n) :
    window n * groups n ^ 2 ≤ n := by
  have hg2 : groups n ^ 2 ≤ window n := by
    simp only [groups, window, level, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  calc window n * groups n ^ 2
    _ ≤ window n ^ 2 := (Nat.mul_le_mul_left _ hg2).trans_eq (sq _).symm
    _ ≤ window n ^ 19 := Nat.pow_le_pow_right (window_pos n) (by decide)
    _ ≤ n := geometry_nineteen hn

/-- The group-square bound for query control does not assume an exact square-root power. -/
theorem groups_sq_le_sqrt (n : ℕ) : (groups n : ℝ) ^ 2 ≤ Real.sqrt (window n : ℝ) := by
  have hnat : (groups n ^ 2) ^ 2 ≤ window n := by
    simp only [groups, window, level, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact (Real.le_sqrt (by positivity) (Nat.cast_nonneg _)).mpr (by exact_mod_cast hnat)

/-- Two group factors fit in the actual finite box product's fractional window saving. -/
theorem groups_sq_le_window_rpow (n : ℕ) :
    (groups n : ℝ) ^ 2 ≤ (window n : ℝ) ^ (8 / 125 : ℝ) := by
  have hnat : (groups n ^ 2) ^ 125 ≤ window n ^ 8 := by
    simp only [groups, window, level, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  refine le_of_pow_le_pow_left₀ (n := 125) (by decide) (by positivity) ?_
  rw [← Real.rpow_natCast ((window n : ℝ) ^ (8 / 125 : ℝ)), ← Real.rpow_mul (Nat.cast_nonneg _),
    show (8 / 125 : ℝ) * (125 : ℕ) = (8 : ℕ) by norm_num, Real.rpow_natCast]
  exact_mod_cast hnat

/-- The rounded group count gains an inverse input power with only a factor16 loss. -/
theorem rpow_lt_sixteen_mul_groups (n : ℕ) :
    (n : ℝ) ^ (2 / 1197 : ℝ) < 16 * groups n := by
  refine lt_of_pow_lt_pow_left₀ 1197 (by positivity) ?_
  rw [← Real.rpow_natCast ((n : ℝ) ^ (2 / 1197 : ℝ)), ← Real.rpow_mul (Nat.cast_nonneg n),
    show (2 / 1197 : ℝ) * (1197 : ℕ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
  simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using
    (Nat.cast_lt (α := ℝ)).mpr (size_sq_lt_groups_pow n)

/-- The original nineteen-factor reserve controls every nonnegative real window power. -/
theorem window_rpow_le_rpow {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    (window n : ℝ) ^ r ≤ (n : ℝ) ^ (r / 19) := by
  calc (window n : ℝ) ^ r
    _ = ((window n : ℝ) ^ 19) ^ (r / 19) := by
      rw [← Real.rpow_natCast_mul (by positivity)]
      congr 1
      push_cast; ring
    _ ≤ (n : ℝ) ^ (r / 19) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast geometry_nineteen hn) (by positivity)

/-- Explicit raw saving before logarithmic factors are absorbed. -/
theorem cubic_div_groups_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 3 / groups n ≤ 16 * (n : ℝ) ^ (3 - 2 / 1197 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ 3 = (n : ℝ) ^ (3 - 2 / 1197 : ℝ) * (n : ℝ) ^ (2 / 1197 : ℝ) := by
    rw [← Real.rpow_add hn0]; norm_num
  rw [div_le_iff₀ (by exact_mod_cast groups_pos n), hpow]
  nlinarith [mul_le_mul_of_nonneg_left (rpow_lt_sixteen_mul_groups n).le
    (Real.rpow_nonneg hn0.le (3 - 2 / 1197))]

/-- The one-time preparation term gains one inverse group factor. -/
theorem preparation_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 2 * window n * groups n ≤ (n : ℝ) ^ 3 / groups n := by
  rw [le_div_iff₀ (by exact_mod_cast groups_pos n)]
  have hscale : (window n : ℝ) * (groups n : ℝ) ^ 2 ≤ n := by
    exact_mod_cast window_mul_groups_sq_le hn
  nlinarith [mul_le_mul_of_nonneg_left hscale (sq_nonneg (n : ℝ))]

/-- Constant work per group fits the same common cost scale. -/
theorem group_work_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * groups n ≤ (n : ℝ) ^ 3 / groups n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ window n := by exact_mod_cast window_pos n
  calc (n : ℝ) * groups n
    _ ≤ (n : ℝ) ^ 2 * window n * groups n := by
      gcongr
      exact (le_self_pow₀ hn1 (by decide)).trans (le_mul_of_one_le_right (sq_nonneg _) hd1)
    _ ≤ (n : ℝ) ^ 3 / groups n := preparation_le hn

/-- Root setup per group also fits the common scale. -/
theorem root_work_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * groups n * Nat.sqrt (window n) ≤ (n : ℝ) ^ 3 / groups n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (Nat.sqrt (window n) : ℝ) ≤ window n := by exact_mod_cast Nat.sqrt_le_self _
  calc (n : ℝ) * groups n * Nat.sqrt (window n)
    _ = (n : ℝ) * (Nat.sqrt (window n) : ℝ) * groups n := by ring
    _ ≤ (n : ℝ) ^ 2 * window n * groups n := by
      gcongr
      exact le_self_pow₀ hn1 (by decide)
    _ ≤ (n : ℝ) ^ 3 / groups n := preparation_le hn

/-- The actual integer query capacity yields the same saving, without dropping rounding. -/
theorem query_work_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * groups n * queryCap n (window n) ≤ (n : ℝ) ^ 3 / groups n := by
  have hg : (0 : ℝ) < groups n := by exact_mod_cast groups_pos n
  have hs : (0 : ℝ) < Real.sqrt (window n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast window_pos n)
  have hQ : (queryCap n (window n) : ℝ) ≤ (n : ℝ) ^ 2 / Real.sqrt (window n) :=
    queryCap_eq_floor n (window n) ▸ Nat.floor_le (by positivity)
  calc (n : ℝ) * groups n * queryCap n (window n)
    _ ≤ (n : ℝ) * groups n * ((n : ℝ) ^ 2 / Real.sqrt (window n)) := by gcongr
    _ = (n : ℝ) ^ 3 * ((groups n : ℝ) / Real.sqrt (window n)) := by ring
    _ ≤ (n : ℝ) ^ 3 * (1 / groups n) := by
      refine mul_le_mul_of_nonneg_left ((div_le_div_iff₀ hs hg).mpr ?_) (by positivity)
      nlinarith only [groups_sq_le_sqrt n]
    _ = _ := by ring

/-- Product saving converts the additional group multiplier into one inverse group factor. -/
theorem product_work_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 3 * groups n * (window n : ℝ) ^ (-(8 / 125 : ℝ)) ≤
      (n : ℝ) ^ 3 / groups n := by
  have hg : (0 : ℝ) < groups n := by exact_mod_cast groups_pos n
  have hd : (0 : ℝ) < (window n : ℝ) ^ (8 / 125 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast window_pos n) _
  calc (n : ℝ) ^ 3 * groups n * (window n : ℝ) ^ (-(8 / 125 : ℝ))
    _ = (n : ℝ) ^ 3 * ((groups n : ℝ) / (window n : ℝ) ^ (8 / 125 : ℝ)) := by
      rw [Real.rpow_neg (Nat.cast_nonneg _)]; ring
    _ ≤ (n : ℝ) ^ 3 * (1 / groups n) := by
      refine mul_le_mul_of_nonneg_left ((div_le_div_iff₀ hd hg).mpr ?_) (by positivity)
      nlinarith only [groups_sq_le_window_rpow n]
    _ = _ := by ring

end Cslib.Algorithms.ExactTriangle.ParameterChoice
