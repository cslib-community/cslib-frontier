/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Window

/-!
# One step of the averaging of projections: the arithmetic

`Flag.step_num`: the numerical inequality behind one step of averaging projections over
windows, from *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Flag.Avg`.
-/

public section

open Finset

namespace Cslib.Circuits.Arithmetic.Separation.Flag

open Cslib.CAT0
open Cslib.SLTower (U SL2 lo hi x)

/-- One step of the averaging. -/
theorem step_num {X Y d L δ : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hL : 1 ≤ L) (hδ : 0 < δ)
    (h1 : Y ^ 2 ≤ (1 - δ / L) * X ^ 2) (h2 : L * d ^ 2 ≤ X ^ 2 - Y ^ 2) :
    d ≤ 2 / √δ * (X - Y) := by
  have hL0 : 0 < L := by linarith
  have h3 : δ * X ^ 2 ≤ L * (X ^ 2 - Y ^ 2) := by
    have h4 := mul_le_mul_of_nonneg_left h1 hL0.le
    have h5 : L * ((1 - δ / L) * X ^ 2) = L * X ^ 2 - δ * X ^ 2 := by field_simp
    linarith
  have hXY2 : 0 ≤ X ^ 2 - Y ^ 2 :=
    nonneg_of_mul_nonneg_right ((by positivity : 0 ≤ δ * X ^ 2).trans h3) hL0
  have hYX : Y ≤ X := (abs_le_of_sq_le_sq' (by linarith) hX).2
  have hs : 0 < √δ := Real.sqrt_pos.2 hδ
  rcases hX.eq_or_lt with rfl | hX0
  · obtain rfl : Y = 0 := le_antisymm hYX hY
    have hd0 : d ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right (by linarith) hL0
    rw [pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hd0 (sq_nonneg _))]
    simp
  · have h4 : δ * X ^ 2 * (L * d ^ 2) ≤ L * (4 * X ^ 2 * (X - Y) ^ 2) := calc
      δ * X ^ 2 * (L * d ^ 2) ≤ (L * (X ^ 2 - Y ^ 2)) * (X ^ 2 - Y ^ 2) :=
          mul_le_mul h3 h2 (by positivity) (by positivity)
      _ = L * ((X + Y) ^ 2 * (X - Y) ^ 2) := by ring
      _ ≤ L * (4 * X ^ 2 * (X - Y) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)) hL0.le
    have h5 : δ * d ^ 2 ≤ 4 * (X - Y) ^ 2 :=
      le_of_mul_le_mul_left (a := L * X ^ 2) (by linarith) (by positivity)
    have h6 : (√δ * d) ^ 2 ≤ (2 * (X - Y)) ^ 2 := by rw [mul_pow, Real.sq_sqrt hδ.le]; linarith
    have := (abs_le_of_sq_le_sq' h6 (by linarith)).2
    rw [div_mul_eq_mul_div, le_div_iff₀ hs]; linarith

end Cslib.Circuits.Arithmetic.Separation.Flag
