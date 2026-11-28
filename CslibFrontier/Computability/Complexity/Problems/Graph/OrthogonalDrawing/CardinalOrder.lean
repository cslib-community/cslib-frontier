/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.RotationCertificate
public import CslibFrontier.Foundations.Geometry.Orthogonal.Polygonal
import CslibFrontier.Foundations.Geometry.Polygonal.AngleOrder

/-!
# The executed cardinal ranks have the literal clockwise angle order

The four finite integer-direction cases are compared with the complex argument of the actual
segment vector. East, south, west, north have representatives `0,-π/2,-π,-3π/2` in one turn.
Thus the executed integer ranks preserve orientation rather than permitting reflection.
The angle-order comparison reuses the existing arbitrary-cut circular-order theorem.

These coordinate and finite-order lemmas are original.
-/

public section

namespace Cslib.Complexity.Graph.OrthogonalDrawing

open Cslib.Orthogonal

/-- A proper integer axis segment has exactly the complex angle represented by its
executed clockwise rank. This identifies the actual outgoing vector, not an idealized ray. -/
theorem arg_eq_clockwiseRank {a b : Point} (hab : AxisAligned a b) :
    ((complexPoint b - complexPoint a).arg : Real.Angle) =
      ((-(clockwiseRank a b : ℝ) * Real.pi / 2 : ℝ) : Real.Angle) := by
  have hre : (complexPoint b - complexPoint a).re = (b.1 : ℝ) - a.1 := by
    simp [complexPoint, realPoint, Complex.equivRealProdCLM_symm_apply]
  have him : (complexPoint b - complexPoint a).im = (b.2 : ℝ) - a.2 := by
    simp [complexPoint, realPoint, Complex.equivRealProdCLM_symm_apply]
  rcases hab with ⟨hx | hy, hne⟩
  · have hn₁ : ¬a.1 < b.1 := by omega
    have hn₂ : ¬b.1 < a.1 := by omega
    have hyne : a.2 ≠ b.2 := fun h => hne (Prod.ext hx h)
    by_cases hp : a.2 < b.2
    · have harg : (complexPoint b - complexPoint a).arg = Real.pi / 2 :=
        Complex.arg_eq_pi_div_two_iff.mpr
          ⟨by rw [hre, hx, sub_self], him ▸ sub_pos.mpr (mod_cast hp)⟩
      have hrank : clockwiseRank a b = 3 := by simp [clockwiseRank, direction, hn₁, hn₂, hp]
      rw [harg, hrank, Nat.cast_ofNat,
        show -(3 : ℝ) * Real.pi / 2 = Real.pi / 2 - 2 * Real.pi by ring,
        Real.Angle.coe_sub, Real.Angle.coe_two_pi, sub_zero]
    · have hlt : b.2 < a.2 := by omega
      have harg : (complexPoint b - complexPoint a).arg = -(Real.pi / 2) :=
        Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨by rw [hre, hx, sub_self],
          him ▸ sub_neg.mpr (mod_cast hlt)⟩
      have hrank : clockwiseRank a b = 1 := by simp [clockwiseRank, direction, hn₁, hn₂, hp]
      rw [harg, hrank]
      congr 1
      ring
  · have hn : a.1 ≠ b.1 := fun h => hne (Prod.ext h hy)
    by_cases hp : a.1 < b.1
    · have harg : (complexPoint b - complexPoint a).arg = 0 :=
        Complex.arg_eq_zero_iff.mpr
          ⟨hre ▸ (sub_pos.mpr (mod_cast hp)).le, by rw [him, hy, sub_self]⟩
      simp [harg, clockwiseRank, direction, hp]
    · have hlt : b.1 < a.1 := by omega
      have harg : (complexPoint b - complexPoint a).arg = Real.pi :=
        Complex.arg_eq_pi_iff.mpr ⟨hre ▸ sub_neg.mpr (mod_cast hlt), by rw [him, hy, sub_self]⟩
      have hrank : clockwiseRank a b = 2 := by simp [clockwiseRank, direction, hp, hlt]
      rw [harg, hrank, Nat.cast_ofNat, show -(2 : ℝ) * Real.pi / 2 = -Real.pi by ring,
        Real.Angle.coe_neg, Real.Angle.neg_coe_pi]

/-- The strict clockwise circular order of three distinct occupied cardinal ranks is
their strict cyclic integer order. The start of the turn is not part of the conclusion. -/
theorem sbtw_clockwiseRanks_iff {a b c : ℕ} (ha : a < 4) (hb : b < 4) (hc : c < 4)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw ((-(c : ℝ) * Real.pi / 2 : ℝ) : Real.Angle)
      ((-(b : ℝ) * Real.pi / 2 : ℝ) : Real.Angle)
      ((-(a : ℝ) * Real.pi / 2 : ℝ) : Real.Angle) ↔
      (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) := by
  have bound (n : ℕ) (hn : n < 4) :
      -(n : ℝ) * Real.pi / 2 ∈ Set.Ioo (-(7 : ℝ) * Real.pi / 4)
        (-(7 : ℝ) * Real.pi / 4 + 2 * Real.pi) := by
    have hn' : (n : ℝ) ≤ 3 := mod_cast (by omega : n ≤ 3)
    constructor <;> linarith [Real.pi_pos,
      mul_le_mul_of_nonneg_right hn' Real.pi_pos.le, mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le]
  have ne (i j : ℕ) (hij : i ≠ j) : -(i : ℝ) * Real.pi / 2 ≠ -(j : ℝ) * Real.pi / 2 :=
    fun he => hij (Nat.cast_injective (R := ℝ)
      (mul_right_cancel₀ Real.pi_ne_zero (by linarith)))
  rw [Cslib.Polygonal.sbtw_angle_iff_cyclic_lt (bound c hc) (bound b hb) (bound a ha)
    (ne c b hbc.symm) (ne b a hab.symm) (ne c a hac.symm)]
  have lt (i j : ℕ) : -(i : ℝ) * Real.pi / 2 < -(j : ℝ) * Real.pi / 2 ↔ j < i := by
    rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
    simp only [neg_mul, neg_lt_neg_iff, mul_lt_mul_iff_left₀ Real.pi_pos, Nat.cast_lt]
  simp only [lt]; tauto

end Cslib.Complexity.Graph.OrthogonalDrawing
