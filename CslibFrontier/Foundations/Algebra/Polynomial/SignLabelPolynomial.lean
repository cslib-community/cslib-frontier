/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial approximation)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.DyadicSignProduct
public import Mathlib.Basic.Sign.Basic
import CslibFrontier.Foundations.Algebra.Polynomial.DyadicSignApproximation
import CslibFrontier.Foundations.Analysis.SignLabelScore
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# An integer polynomial recognizing a family of sign tests

Clearing the positive denominators in the squared-error score gives a single
integer polynomial. At a point where every test value is zero or in the
advertised dyadic range in magnitude, the polynomial is positive exactly
when all target signs hold. The value has a uniform margin from zero.

Adapted from `ClearedSignTests` and `RootLabelPolynomial` in lean-canny at
commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open Finset

/-- The integer polynomial for the score with denominators cleared. Each
deviation is multiplied by all the other denominators before squaring. -/
@[expose] noncomputable def signLabelPolynomial {m : ℕ} (B : ℕ) (g : Fin m → ℤ[X])
    (target : Fin m → SignType) : ℤ[X] :=
  let p := dyadicSignProduct B (m + 1)
  let a (i : Fin m) := p.comp (g i)
  let b (i : Fin m) := p.comp (-g i)
  let d (i : Fin m) := a i + b i
  (∏ i, d i) ^ 2 - C (4 : ℤ) *
    ∑ i, ((a i - b i - C (target i : ℤ) * d i) * ∏ j ∈ univ.erase i, d j) ^ 2

private theorem eval₂_signLabelPolynomial {m : ℕ} (B : ℕ) (g : Fin m → ℤ[X])
    (target : Fin m → SignType) (x : ℝ) :
    let v (i : Fin m) := (g i).eval₂ (Int.castRingHom ℝ) x
    let p := dyadicSignProduct B (m + 1)
    let d (i : Fin m) := p.eval₂ (Int.castRingHom ℝ) (v i) + p.eval₂ (Int.castRingHom ℝ) (-v i)
    (signLabelPolynomial B g target).eval₂ (Int.castRingHom ℝ) x =
      (∏ i, d i) ^ 2 * SignType.labelScore (fun i => dyadicSignApprox B (m + 1) (v i)) target := by
  intro v p d
  let a (i : Fin m) := p.eval₂ (Int.castRingHom ℝ) (v i)
  let b (i : Fin m) := p.eval₂ (Int.castRingHom ℝ) (-v i)
  let D := ∏ i, d i
  have hd (i : Fin m) : d i ≠ 0 :=
    (zero_lt_one.trans_le (one_le_eval₂_dyadicSignProduct_add_neg B (m + 1) (v i))).ne'
  have hclear (i : Fin m) :
      (a i - b i - (target i : ℝ) * d i) * (∏ j ∈ univ.erase i, d j) =
        D * (dyadicSignApprox B (m + 1) (v i) - (target i : ℝ)) := by
    rw [show D = d i * ∏ j ∈ univ.erase i, d j from
      (mul_prod_erase _ _ (mem_univ i)).symm]
    change (a i - b i - (target i : ℝ) * d i) * (∏ j ∈ univ.erase i, d j) =
      (d i * ∏ j ∈ univ.erase i, d j) * ((a i - b i) / d i - (target i : ℝ))
    field_simp [hd i]
  simp only [signLabelPolynomial, eval₂_sub, eval₂_pow, eval₂_mul, eval₂_C, eval₂_finsetSum,
    eval₂_finsetProd, eval₂_add, eval₂_comp, eval₂_neg, Int.coe_castRingHom, Int.cast_ofNat,
    SignType.intCast_cast]
  change D ^ 2 - 4 * ∑ i, ((a i - b i - (target i : ℝ) * d i) *
    ∏ j ∈ univ.erase i, d j) ^ 2 = _
  simp_rw [hclear, mul_pow, ← Finset.mul_sum]
  unfold SignType.labelScore
  ring

/-- If every real test value is zero or has magnitude in the dyadic range, the
label has margin at least one half and is positive exactly on agreement. -/
theorem eval₂_signLabelPolynomial_margin {m : ℕ} (B : ℕ) (g : Fin m → ℤ[X])
    (target : Fin m → SignType) (x : ℝ)
    (hvalues : ∀ i, let v := (g i).eval₂ (Int.castRingHom ℝ) x
      v = 0 ∨ (((2 : ℝ) ^ B)⁻¹ ≤ |v| ∧ |v| ≤ (2 : ℝ) ^ B)) :
    let y := (signLabelPolynomial B g target).eval₂ (Int.castRingHom ℝ) x
    ((1 : ℝ) / 2 ≤ y ∨ y ≤ -(1 : ℝ) / 2) ∧
      (0 < y ↔ ∀ i, SignType.sign ((g i).eval₂ (Int.castRingHom ℝ) x) = target i) := by
  dsimp only
  rw [eval₂_signLabelPolynomial]
  let v (i : Fin m) := (g i).eval₂ (Int.castRingHom ℝ) x
  let p := dyadicSignProduct B (m + 1)
  let D := ∏ i, (p.eval₂ (Int.castRingHom ℝ) (v i) + p.eval₂ (Int.castRingHom ℝ) (-v i))
  let a (i : Fin m) := dyadicSignApprox B (m + 1) (v i)
  let score := SignType.labelScore a target
  change ((1 : ℝ) / 2 ≤ D ^ 2 * score ∨ D ^ 2 * score ≤ -(1 : ℝ) / 2) ∧ _
  have hD : 1 ≤ D :=
    one_le_prod₀ fun i _ => one_le_eval₂_dyadicSignProduct_add_neg B (m + 1) (v i)
  have hD₂ : 1 ≤ D ^ 2 := one_le_pow₀ hD
  obtain ⟨hmargin, hpos⟩ := SignType.labelScore_margin a (fun i => SignType.sign (v i)) target
    (fun i => abs_dyadicSignApprox_sub_sign_le_inv_four_mul_succ B m (hvalues i))
  refine ⟨?_, (mul_pos_iff_of_pos_left (zero_lt_one.trans_le hD₂)).trans hpos⟩
  rcases hmargin with h | h
  · have hnonneg : 0 ≤ score := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans h
    exact Or.inl (h.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hD₂ hnonneg))
  · have hnonpos : score ≤ 0 := h.trans (by norm_num)
    have hscaled : D ^ 2 * score ≤ score := by
      simpa only [one_mul] using mul_le_mul_of_nonpos_right hD₂ hnonpos
    exact Or.inr (hscaled.trans h)

end Polynomial
