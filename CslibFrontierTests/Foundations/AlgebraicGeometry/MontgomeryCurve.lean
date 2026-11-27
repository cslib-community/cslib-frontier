/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (unit tests for EllipticCurve.Montgomery)

public import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.Montgomery
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Montgomery curve tests

Client tests over `ZMod 7`, `ZMod 3`, `GaloisField 3 2`, and `ZMod 2`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Montgomery

open WeierstrassCurve _root_.MontgomeryCurve

section ZMod7

private local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private local instance : Invertible (2 : ZMod 7) := ⟨4, by decide, by decide⟩
private local instance : Invertible (3 : ZMod 7) := ⟨5, by decide, by decide⟩

private lemma ringChar_zmod_seven : ringChar (ZMod 7) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  decide

private def testM7 : MontgomeryCurve (ZMod 7) where
  A := 3
  B := 1
  nondegenerate := by decide

-- `toWeierstrass` coincides with a quadratic twist of `Y² = X³ + A X² + X`.
example : testM7.toWeierstrass = (ofCubic testM7.A 1 0).quadraticTwist testM7.B⁻¹ :=
  testM7.toWeierstrass_eq_quadraticTwist

-- `toWeierstrassEquiv` maps `.zero` to `0` and affine points to `(u / B, v / B)`.
example : testM7.toWeierstrassEquiv (by decide) .zero = 0 :=
  testM7.toWeierstrassEquiv_zero (by decide)

example :
    let h21 : testM7.Equation 2 1 := by decide
    testM7.toWeierstrassEquiv (by decide) (.some 2 1 h21) =
      .some (2 / testM7.B) (1 / testM7.B)
        (testM7.toWeierstrass_nonsingular_div (by decide) h21) := by
  intro h21
  exact testM7.toWeierstrassEquiv_some (by decide) h21

-- `toShortWeierstrass` puts `testM7` in short normal form and agrees with `toShortNF`.
example : testM7.toShortWeierstrass.IsShortNF :=
  testM7.isShortNF_toShortWeierstrass (by decide)

example : testM7.toShortWeierstrass = testM7.toWeierstrass.toShortNF • testM7.toWeierstrass :=
  testM7.toShortWeierstrass_eq_toShortNF

example : Nonempty (testM7.Point ≃ testM7.toShortWeierstrass.toAffine.Point) := by
  refine ⟨(testM7.toWeierstrassEquiv (by decide)).trans ?_⟩
  rw [testM7.toShortWeierstrass_eq_toShortNF]
  exact (variableChangePointEquiv _ testM7.toWeierstrass).symm.toEquiv

example : 4 ∣ Nat.card testM7.Point :=
  testM7.four_dvd_natCard_point ringChar_zmod_seven

example : 4 ∣ Nat.card testM7.toWeierstrass.toAffine.Point :=
  testM7.four_dvd_natCard_toWeierstrass_point ringChar_zmod_seven

-- An odd-order Weierstrass curve (`y² = x³ + 2`, order 9 over `ZMod 7`) cannot come from a
-- Montgomery curve via a point bijection or admissible change of variables.
private def oddW7 : WeierstrassCurve (ZMod 7) :=
  ⟨0, 0, 0, 0, 2⟩

private lemma oddW7_card : Nat.card oddW7.toAffine.Point = 9 := by
  have hΔ : oddW7.Δ ≠ 0 := by decide
  rw [Affine.natCard_point_eq_one_add_equation oddW7.toAffine hΔ,
    Nat.card_congr (Equiv.subtypeEquivRight fun xy : ZMod 7 × ZMod 7 ↦
      Affine.equation_iff (W := oddW7.toAffine) xy.1 xy.2),
    Nat.card_eq_fintype_card]
  decide

example (M : MontgomeryCurve (ZMod 7)) : IsEmpty (M.Point ≃ oddW7.toAffine.Point) := by
  refine ⟨fun e ↦ ?_⟩
  have h4 := M.four_dvd_natCard_point ringChar_zmod_seven
  rw [Nat.card_congr e, oddW7_card] at h4
  exact absurd h4 (by decide)

example (M : MontgomeryCurve (ZMod 7)) (C : VariableChange (ZMod 7)) :
    C • M.toWeierstrass ≠ oddW7 :=
  M.not_variableChange_of_odd ringChar_zmod_seven (by rw [oddW7_card]; decide) C

end ZMod7

section CharThree

private local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- Characteristic 3: `equation_iff_toShortWeierstrass` holds without `3 ≠ 0`, while
-- `toShortWeierstrass.IsShortNF` fails when `A ≠ 0` (witnessed over `GF(9)`, since `ZMod 3`
-- forces `A = 0`).
example {F : Type*} [Field F] [CharP F 3] (M : MontgomeryCurve F) (hA : M.A ≠ 0) :
    ¬ M.toShortWeierstrass.IsShortNF :=
  M.not_isShortNF_toShortWeierstrass (CharP.cast_eq_zero F 3) hA

example (M : MontgomeryCurve (ZMod 3)) : M.A = 0 := by
  have h := M.discr_ne_zero
  rcases (by decide : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2) M.A with hA | hA | hA
  · exact hA
  · exact absurd (by rw [hA]; decide) h
  · exact absurd (by rw [hA]; decide) h

private abbrev GF9 := GaloisField 3 2

example : ∃ M : MontgomeryCurve GF9, ¬ M.toShortWeierstrass.IsShortNF := by
  classical
  let _ : Fintype GF9 := Fintype.ofFinite GF9
  have hne : ({0, 1, -1} : Finset GF9) ≠ Finset.univ := by
    intro h
    have hle : (Finset.univ : Finset GF9).card ≤ 3 := by
      rw [← h]
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_le_two)
    rw [Finset.card_univ, Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)] at hle
    omega
  obtain ⟨A, -, hAn⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hAn
  rcases hAn with ⟨hA0, hA1, hAm1⟩
  have hdiscr : A ^ 2 - 4 ≠ 0 := by
    have h4 : (4 : GF9) = 1 := by
      have : (3 : GF9) = 0 := CharP.cast_eq_zero GF9 3
      linear_combination this
    rw [h4, show A ^ 2 - 1 = (A - 1) * (A + 1) by ring]
    exact mul_ne_zero (sub_ne_zero.mpr hA1) (fun h ↦ hAm1 (eq_neg_of_add_eq_zero_left h))
  let M : MontgomeryCurve GF9 := ⟨A, 1, mul_ne_zero one_ne_zero hdiscr⟩
  exact ⟨M, M.not_isShortNF_toShortWeierstrass (CharP.cast_eq_zero GF9 3) hA0⟩

example (M : MontgomeryCurve GF9) (x y : GF9) :
    M.Equation (M.B * x - M.A / 3) (M.B * y) ↔ M.toShortWeierstrass.toAffine.Equation x y :=
  M.equation_iff_toShortWeierstrass x y

end CharThree

section CharTwo

private local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

-- Characteristic 2 breaks Montgomery non-singularity and 4-divisibility: over `ZMod 2` the
-- equation of `badM2` is `v = u`, so its points are infinity, `(0, 0)` and `(1, 1)`, and
-- `natCard_point_eq_one_add` counts three.
private def badM2 : MontgomeryCurve (ZMod 2) where
  A := 1
  B := 1
  nondegenerate := by decide

example : badM2.toWeierstrass.Δ = 0 ∧ Nat.card badM2.Point = 3 := by
  refine ⟨?_, ?_⟩
  · rw [badM2.toWeierstrass_Δ, show (16 : ZMod 2) = 0 by decide, zero_mul, zero_div]
  · rw [badM2.natCard_point_eq_one_add, Nat.card_eq_fintype_card]
    decide

end CharTwo

end CslibFrontierTests.Montgomery
