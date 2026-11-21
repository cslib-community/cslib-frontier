/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial root tests)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Sign.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
# Bounded shifts for polynomial root labels

Scaling a real label by `-4 * D` reverses its sign, and adding a natural
number at most `D` preserves the reversed sign when the label has magnitude
at least one half. A shift in this range avoids zero on the enumerated roots
of a source polynomial of degree at most `D`.

Adapted from `ShiftedRootTests` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open Finset

/-- A root test formed by scaling a label by `-4 * D` and adding a constant shift. -/
@[expose] noncomputable def shiftedRootLabel {R : Type*} [Ring R] (D e : ℕ)
    (g : Polynomial R) : Polynomial R :=
  C (-(4 * (D : R))) * g + C (e : R)

/-- Among `D + 1` natural shifts, some shifted label is nonzero on `p.aroots A`
when `p` has degree at most `D` and `A` is a characteristic-zero domain. -/
theorem exists_aeval_shiftedRootLabel_ne_zero {R A : Type*} [CommRing R] [CommRing A]
    [IsDomain A] [CharZero A] [Algebra R A] (p g : Polynomial R) {D : ℕ}
    (hD : p.natDegree ≤ D) :
    ∃ e : ℕ, e ≤ D ∧ ∀ z ∈ p.aroots A, aeval z (shiftedRootLabel D e g) ≠ 0 := by
  classical
  let roots := (p.aroots A).toFinset
  let base (z : A) := aeval z (C (-(4 * (D : R))) * g)
  let forbidden := roots.image fun z => -base z
  let candidates := (range (D + 1)).image (Nat.cast : ℕ → A)
  have hroots : roots.card ≤ D := (Multiset.toFinset_card_le _).trans
    ((card_roots' _).trans (natDegree_map_le.trans hD))
  have hcount : forbidden.card < candidates.card := by
    rw [card_image_of_injective _ Nat.cast_injective, card_range]
    exact Nat.lt_succ_of_le (card_image_le.trans hroots)
  obtain ⟨a, ha, hnot⟩ := exists_mem_notMem_of_card_lt_card hcount
  change a ∈ (range (D + 1)).image (Nat.cast : ℕ → A) at ha
  obtain ⟨e, he, rfl⟩ := mem_image.mp ha
  refine ⟨e, Nat.le_of_lt_succ (mem_range.mp he), fun z hz hz0 => hnot ?_⟩
  have heq : base z + (e : A) = 0 := by
    simpa only [shiftedRootLabel, map_add, aeval_C, map_natCast, base] using hz0
  exact mem_image.mpr ⟨z, Multiset.mem_toFinset.mpr hz, (eq_neg_of_add_eq_zero_right heq).symm⟩

/-- A bounded shift reverses the sign of a real root label with magnitude at least one half. -/
theorem sign_eval_shiftedRootLabel {D e : ℕ} (hD : 0 < D) (he : e ≤ D)
    {g : Polynomial ℝ} {x : ℝ}
    (hm : (1 : ℝ) / 2 ≤ g.eval x ∨ g.eval x ≤ -(1 : ℝ) / 2) :
    SignType.sign ((shiftedRootLabel D e g).eval x) = -SignType.sign (g.eval x) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have he' : (e : ℝ) ≤ D := by exact_mod_cast he
  have he₀ : 0 ≤ (e : ℝ) := Nat.cast_nonneg _
  simp only [shiftedRootLabel, eval_add, eval_mul, eval_C]
  rcases hm with hm | hm
  · have hneg : -(4 * (D : ℝ)) * g.eval x + e < 0 := by
      nlinarith [mul_nonneg hD'.le (sub_nonneg.mpr hm)]
    rw [sign_neg hneg, sign_pos (by linarith : 0 < g.eval x)]
  · have hpos : 0 < -(4 * (D : ℝ)) * g.eval x + e := by
      nlinarith [mul_nonneg hD'.le (sub_nonneg.mpr hm)]
    rw [sign_pos hpos, sign_neg (by linarith : g.eval x < 0), neg_neg]

end Polynomial
