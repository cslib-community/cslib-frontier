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

The weighted fingerprint label uses the same denominators to test an integer
sum of signs together with a qualifying positive test.

Adapted from `ClearedSignTests`, `RootLabelPolynomial` and `FingerprintLabelPolynomial`
in lean-canny at
commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open Finset

private theorem clear_dyadicSignApprox {m : ℕ} (B s : ℕ) (v : Fin m → ℝ) (i : Fin m) :
    let p := dyadicSignProduct B s
    let a (j : Fin m) := p.eval₂ (Int.castRingHom ℝ) (v j)
    let b (j : Fin m) := p.eval₂ (Int.castRingHom ℝ) (-v j)
    let d (j : Fin m) := a j + b j
    (a i - b i) * (∏ j ∈ univ.erase i, d j) =
      (∏ j, d j) * dyadicSignApprox B s (v i) := by
  intro p a b d
  have hd : d i ≠ 0 :=
    (zero_lt_one.trans_le (one_le_eval₂_dyadicSignProduct_add_neg B s (v i))).ne'
  change (a i - b i) * (∏ j ∈ univ.erase i, d j) = (∏ j, d j) * ((a i - b i) / d i)
  rw [← mul_prod_erase _ _ (mem_univ i)]
  field_simp [hd]

private theorem scale_signLabelMargin {D score : ℝ} {P : Prop}
    (hD : 1 ≤ D) (h : ((1 : ℝ) / 2 ≤ score ∨ score ≤ -(1 : ℝ) / 2) ∧ (0 < score ↔ P)) :
    ((1 : ℝ) / 2 ≤ D ^ 2 * score ∨ D ^ 2 * score ≤ -(1 : ℝ) / 2) ∧
      (0 < D ^ 2 * score ↔ P) := by
  have hD₂ : 1 ≤ D ^ 2 := one_le_pow₀ hD
  refine ⟨?_, (mul_pos_iff_of_pos_left (zero_lt_one.trans_le hD₂)).trans h.2⟩
  rcases h.1 with hpos | hneg
  · have hnonneg : 0 ≤ score := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hpos
    exact Or.inl (hpos.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hD₂ hnonneg))
  · have hnonpos : score ≤ 0 := hneg.trans (by norm_num)
    have hscaled : D ^ 2 * score ≤ score := by
      simpa only [one_mul] using mul_le_mul_of_nonpos_right hD₂ hnonpos
    exact Or.inr (hscaled.trans hneg)

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
  have hclear (i : Fin m) :
      (a i - b i - (target i : ℝ) * d i) * (∏ j ∈ univ.erase i, d j) =
        D * (dyadicSignApprox B (m + 1) (v i) - (target i : ℝ)) := by
    have happrox : (a i - b i) * (∏ j ∈ univ.erase i, d j) =
        D * dyadicSignApprox B (m + 1) (v i) := clear_dyadicSignApprox B (m + 1) v i
    rw [sub_mul, happrox]
    rw [show D = d i * ∏ j ∈ univ.erase i, d j from
      (mul_prod_erase _ _ (mem_univ i)).symm]
    ring
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
  exact scale_signLabelMargin hD (SignType.labelScore_margin a
    (fun i => SignType.sign (v i)) target
    (fun i => abs_dyadicSignApprox_sub_sign_le_inv_four_mul_succ B m (hvalues i)))

/-- The integer fingerprint label with the dyadic denominators cleared. Slot zero
qualifies the point. The subsequent slots contribute to the weighted fingerprint.
The dyadic product uses `M + 1` repetitions, where `M` bounds the total weight. -/
@[expose] noncomputable def fingerprintLabelPolynomial {m : ℕ} (B M : ℕ)
    (g : Fin (m + 1) → ℤ[X]) (w : Fin m → ℕ) (target : ℤ) : ℤ[X] :=
  let p := dyadicSignProduct B (M + 1)
  let a (i : Fin (m + 1)) := p.comp (g i)
  let b (i : Fin (m + 1)) := p.comp (-g i)
  let d (i : Fin (m + 1)) := a i + b i
  let D := ∏ i, d i
  let T (i : Fin (m + 1)) := (a i - b i) * ∏ j ∈ univ.erase i, d j
  D ^ 2 - C (4 : ℤ) *
    (((∑ i, C (w i : ℤ) * T i.succ) - C target * D) ^ 2 + (T 0 - D) ^ 2)

private theorem eval₂_fingerprintLabelPolynomial {m : ℕ} (B M : ℕ)
    (g : Fin (m + 1) → ℤ[X]) (w : Fin m → ℕ) (target : ℤ) (x : ℝ) :
    let v (i : Fin (m + 1)) := (g i).eval₂ (Int.castRingHom ℝ) x
    let p := dyadicSignProduct B (M + 1)
    let d (i : Fin (m + 1)) :=
      p.eval₂ (Int.castRingHom ℝ) (v i) + p.eval₂ (Int.castRingHom ℝ) (-v i)
    let A (i : Fin (m + 1)) := dyadicSignApprox B (M + 1) (v i)
    (fingerprintLabelPolynomial B M g w target).eval₂ (Int.castRingHom ℝ) x =
      (∏ i, d i) ^ 2 * SignType.fingerprintScore (∑ i, (w i : ℝ) * A i.succ) (A 0) target := by
  intro v p d A
  let a (i : Fin (m + 1)) := p.eval₂ (Int.castRingHom ℝ) (v i)
  let b (i : Fin (m + 1)) := p.eval₂ (Int.castRingHom ℝ) (-v i)
  let D := ∏ i, d i
  let T (i : Fin (m + 1)) := (a i - b i) * ∏ j ∈ univ.erase i, d j
  have hclear (i : Fin (m + 1)) : T i = D * A i := clear_dyadicSignApprox B (M + 1) v i
  have hsum : (∑ i, (w i : ℝ) * (D * A i.succ)) = D * ∑ i, (w i : ℝ) * A i.succ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => mul_left_comm _ _ _)
  simp only [fingerprintLabelPolynomial, eval₂_sub, eval₂_pow, eval₂_mul, eval₂_C, eval₂_finsetSum,
    eval₂_finsetProd, eval₂_add, eval₂_comp, eval₂_neg, Int.coe_castRingHom, Int.cast_ofNat,
    Int.cast_natCast]
  change D ^ 2 - 4 * (((∑ i, (w i : ℝ) * T i.succ) - (target : ℝ) * D) ^ 2 +
    (T 0 - D) ^ 2) = D ^ 2 * SignType.fingerprintScore _ _ _
  simp only [hclear, hsum, SignType.fingerprintScore]
  ring

/-- If the total weight is at most `M` and the test values are zero or within the dyadic
range in magnitude, the label has margin at least one half. It is positive exactly when
the weighted integer signs match the target and the qualifying test is positive. -/
theorem eval₂_fingerprintLabelPolynomial_margin {m : ℕ} (B M : ℕ)
    (g : Fin (m + 1) → ℤ[X]) (w : Fin m → ℕ) (target : ℤ) (x : ℝ)
    (hw : ∑ i, w i ≤ M)
    (hvalues : ∀ i, let v := (g i).eval₂ (Int.castRingHom ℝ) x
      v = 0 ∨ (((2 : ℝ) ^ B)⁻¹ ≤ |v| ∧ |v| ≤ (2 : ℝ) ^ B)) :
    let v (i : Fin (m + 1)) := (g i).eval₂ (Int.castRingHom ℝ) x
    let y := (fingerprintLabelPolynomial B M g w target).eval₂ (Int.castRingHom ℝ) x
    ((1 : ℝ) / 2 ≤ y ∨ y ≤ -(1 : ℝ) / 2) ∧
      (0 < y ↔ (∑ i, (w i : ℤ) * (SignType.sign (v i.succ) : ℤ)) = target ∧ 0 < v 0) := by
  intro v y
  dsimp only [y]
  rw [eval₂_fingerprintLabelPolynomial]
  let p := dyadicSignProduct B (M + 1)
  let D := ∏ i, (p.eval₂ (Int.castRingHom ℝ) (v i) + p.eval₂ (Int.castRingHom ℝ) (-v i))
  let A (i : Fin (m + 1)) := dyadicSignApprox B (M + 1) (v i)
  have hD : 1 ≤ D :=
    one_le_prod₀ fun i _ => one_le_eval₂_dyadicSignProduct_add_neg B (M + 1) (v i)
  have hA (i : Fin (m + 1)) : |A i - (SignType.sign (v i) : ℝ)| ≤ (4 * ((M : ℝ) + 1))⁻¹ :=
    abs_dyadicSignApprox_sub_sign_le_inv_four_mul_succ B M (hvalues i)
  have hδ : (4 * ((M : ℝ) + 1))⁻¹ ≤ (1 : ℝ) / 4 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num)
      (le_mul_of_one_le_right (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg M)))
  have h := SignType.fingerprintScore_margin w (fun i => A i.succ)
    (fun i => SignType.sign (v i.succ)) (A 0) (SignType.sign (v 0)) target hw
    (fun i => hA i.succ) ((hA 0).trans hδ)
  simpa only [sign_eq_one_iff] using scale_signLabelMargin hD h

end Polynomial
