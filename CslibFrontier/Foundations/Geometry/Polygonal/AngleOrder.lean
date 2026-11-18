/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Circular order within one real turn

Increasing real representatives whose span is less than a full turn retain their strict
circular order as angles. This graph-free fact supports horizontal ports and moving fans
without requiring the same argument cut.
-/

public section

namespace Cslib.Polygonal

/-- Increasing real representatives with span less than a full turn give the literal
counterclockwise strict angle order, without a principal-argument cut restriction. -/
theorem sbtw_angle_of_lt_of_span_lt {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hspan : c - a < 2 * Real.pi) :
    sbtw (a : Real.Angle) (b : Real.Angle) (c : Real.Angle) := by
  have hp := Real.two_pi_pos
  let : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨hp⟩
  rw [sbtw_iff_not_btw]
  change ¬btw (c : ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))
    (b : ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))
    (a : ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))
  rw [QuotientAddGroup.btw_coe_iff]
  have hb : toIcoMod hp c b = b + 2 * Real.pi := by
    apply (toIcoMod_eq_iff hp).mpr
    refine ⟨⟨by linarith, by linarith⟩, -1, ?_⟩
    simp only [neg_one_zsmul]
    ring
  have ha : toIocMod hp c a = a + 2 * Real.pi := by
    apply (toIocMod_eq_iff hp).mpr
    refine ⟨⟨by linarith, by linarith⟩, -1, ?_⟩
    simp only [neg_one_zsmul]
    ring
  rw [hb, ha]
  linarith

/-- Three distinct real representatives in any one turn have exactly their cyclic
linear order as angles. In particular the cut may cross the principal argument branch. -/
theorem sbtw_angle_iff_cyclic_lt {cut a b c : ℝ}
    (ha : a ∈ Set.Ioo cut (cut + 2 * Real.pi))
    (hb : b ∈ Set.Ioo cut (cut + 2 * Real.pi))
    (hc : c ∈ Set.Ioo cut (cut + 2 * Real.pi))
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw (a : Real.Angle) (b : Real.Angle) (c : Real.Angle) ↔
      (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) := by
  have forward {a b c : ℝ} (ha : a ∈ Set.Ioo cut (cut + 2 * Real.pi))
      (hb : b ∈ Set.Ioo cut (cut + 2 * Real.pi))
      (hc : c ∈ Set.Ioo cut (cut + 2 * Real.pi))
      (h : (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b)) :
      sbtw (a : Real.Angle) (b : Real.Angle) (c : Real.Angle) := by
    rcases h with ⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩
    · exact sbtw_angle_of_lt_of_span_lt hab hbc (by linarith [ha.1, hc.2])
    · exact (sbtw_angle_of_lt_of_span_lt hbc hca (by linarith [hb.1, ha.2])).cyclic_right
    · exact (sbtw_angle_of_lt_of_span_lt hca hab (by linarith [hc.1, hb.2])).cyclic_left
  refine ⟨fun h => ?_, forward ha hb hc⟩
  by_contra hn
  have hrev : (c < b ∧ b < a) ∨ (b < a ∧ a < c) ∨ (a < c ∧ c < b) := by
    rcases lt_or_gt_of_ne hab with h | h <;>
      rcases lt_or_gt_of_ne hbc with k | k <;>
      rcases lt_or_gt_of_ne hac with l | l <;> tauto
  exact h.not_sbtw (forward hc hb ha hrev)

end Cslib.Polygonal
