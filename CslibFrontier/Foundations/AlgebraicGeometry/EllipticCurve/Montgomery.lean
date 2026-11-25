/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/AlgebraicGeometry/EllipticCurve/Montgomery.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.QuadraticTwist
public import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.GroupTheory.OrderOfElement

/-!
# Montgomery elliptic curves

A Montgomery curve over a commutative ring `R` is given by `B v² = u³ + A u² + u` with
`B (A² - 4) ≠ 0` ([BonehShoup2023], Section 15.2.1, p. 619). Over a field `F`, the coordinate
substitution `(u, v) = (B x, B y)` transforms this equation into the Weierstrass curve
`M.toWeierstrass` (`Y² = X³ + (A/B) X² + (1/B²) X`), which is the quadratic twist
`(ofCubic M.A 1 0).quadraticTwist M.B⁻¹`. When `2 ≠ 0` in `F`, `M.toWeierstrass` is elliptic and
`M.toWeierstrassEquiv` identifies `M.Point` with `M.toWeierstrass.toAffine.Point`. Over a finite
field of characteristic `≠ 2`, `4` divides `#M.Point`, so no Montgomery curve is related by a
change of variables to a Weierstrass curve of odd order.

## Main definitions

* `MontgomeryCurve R`: a Montgomery curve `B v² = u³ + A u² + u` with `B (A² - 4) ≠ 0`.
* `MontgomeryCurve.Equation M u v`: the affine curve equation `B v² = u³ + A u² + u`.
* `MontgomeryCurve.Point M`: the point at infinity `.zero` together with affine solutions
  `.some u v h`.
* `MontgomeryCurve.pointEquivOption`: bijection between `M.Point` and `Option` of the affine
  solution subtype.
* `MontgomeryCurve.toWeierstrass M`: the Weierstrass model `ofCubic (M.A / M.B) (1 / M.B ^ 2) 0`.
* `MontgomeryCurve.toWeierstrassEquiv`: bijection `M.Point ≃ M.toWeierstrass.toAffine.Point`
  when `2 ≠ 0`.
* `MontgomeryCurve.toShortWeierstrass M`: the shifted curve eliminating the quadratic term when
  `3 ≠ 0`.

## Main results

* `MontgomeryCurve.natCard_point_eq_one_add`: over a finite field of any characteristic,
  `Nat.card M.Point = 1 + Nat.card {uv : F × F // M.Equation uv.1 uv.2}`.
* `MontgomeryCurve.toWeierstrass_eq_quadraticTwist`:
  `M.toWeierstrass = (ofCubic M.A 1 0).quadraticTwist M.B⁻¹`.
* `MontgomeryCurve.toWeierstrass_Δ`, `MontgomeryCurve.isElliptic_toWeierstrass`,
  `MontgomeryCurve.equation_iff_toWeierstrass`: discriminant, ellipticity (`2 ≠ 0`), and affine
  equation equivalence for `M.toWeierstrass`, derived through `QuadraticTwist`.
* `MontgomeryCurve.isShortNF_toShortWeierstrass`,
  `MontgomeryCurve.not_isShortNF_toShortWeierstrass`,
  `MontgomeryCurve.toShortWeierstrass_eq_toShortNF`,
  `MontgomeryCurve.equation_iff_toShortWeierstrass`: short Weierstrass reduction (`3 ≠ 0` for
  `IsShortNF`, comparison with `WeierstrassCurve.toShortNF` when `2` and `3` are invertible,
  failure in characteristic `3` when `A ≠ 0`, and equation equivalence without `3 ≠ 0`).
* `MontgomeryCurve.four_dvd_natCard_toWeierstrass_point`,
  `MontgomeryCurve.four_dvd_natCard_point`, `MontgomeryCurve.not_variableChange_of_odd`: over a
  finite field of characteristic `≠ 2`, `4` divides the order of `M`, ruling out any admissible
  change of variables to an odd-order Weierstrass curve.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 15.2.1
  (p. 619).
-/

public section

open WeierstrassCurve

/-- A Montgomery elliptic curve `B v² = u³ + A u² + u` over a commutative ring `R`, with
non-degeneracy condition `B (A² - 4) ≠ 0` ([BonehShoup2023], Section 15.2.1, p. 619). -/
structure MontgomeryCurve (R : Type*) [CommRing R] where
  /-- The quadratic coefficient `A` in `B v² = u³ + A u² + u`. -/
  A : R
  /-- The twist coefficient `B` in `B v² = u³ + A u² + u`. -/
  B : R
  /-- Non-degeneracy: `B (A² - 4) ≠ 0`, avoiding singular curves when `2 ≠ 0`. -/
  nondegenerate : B * (A ^ 2 - 4) ≠ 0

namespace MontgomeryCurve

section Basic

variable {F : Type*} [Field F] (M : MontgomeryCurve F)

/-- The twist coefficient `M.B` is nonzero. -/
theorem B_ne_zero : M.B ≠ 0 :=
  left_ne_zero_of_mul M.nondegenerate

/-- The Montgomery discriminant factor `M.A ^ 2 - 4` is nonzero. -/
theorem discr_ne_zero : M.A ^ 2 - 4 ≠ 0 :=
  right_ne_zero_of_mul M.nondegenerate

/-- The affine Montgomery curve equation `B v² = u³ + A u² + u`. -/
@[expose] def Equation (u v : F) : Prop :=
  M.B * v ^ 2 = u ^ 3 + M.A * u ^ 2 + u

instance [DecidableEq F] (u v : F) : Decidable (M.Equation u v) :=
  inferInstanceAs (Decidable (_ = _))

/-- Points of a Montgomery curve `M`: the point at infinity `.zero` or an affine solution
`.some u v h`. -/
inductive Point
  | zero
  | some (u v : F) (h : M.Equation u v)
  deriving DecidableEq

/-- The points of a Montgomery curve `M` are equivalent to `Option` of the affine solutions of
`M.Equation`. -/
def pointEquivOption :
    M.Point ≃ Option {uv : F × F // M.Equation uv.1 uv.2} where
  toFun
    | .zero => none
    | .some u v h => some ⟨(u, v), h⟩
  invFun
    | none => .zero
    | some ⟨uv, h⟩ => .some uv.1 uv.2 h
  left_inv
    | .zero => rfl
    | .some _ _ _ => rfl
  right_inv
    | none => rfl
    | some ⟨⟨_, _⟩, _⟩ => rfl

/-- Over a finite field, the number of points on `M` is one (the point at infinity) plus the number
of affine solutions of `M.Equation`. -/
theorem natCard_point_eq_one_add [Finite F] :
    Nat.card M.Point = 1 + Nat.card {uv : F × F // M.Equation uv.1 uv.2} := by
  rw [Nat.card_congr M.pointEquivOption, add_comm]
  exact Finite.card_option

/-- The Weierstrass model `Y² = X³ + (A/B) X² + (1/B²) X` of `M`, obtained by substituting
`(u, v) = (B X, B Y)`. This coincides with the quadratic twist
`(ofCubic M.A 1 0).quadraticTwist M.B⁻¹`. The change of variables of [BonehShoup2023],
Section 15.2.1, p. 619, `u := B x - A/3` and `v := B y`, also removes the quadratic term; it is
`toShortWeierstrass`. -/
def toWeierstrass : WeierstrassCurve F :=
  ofCubic (M.A / M.B) (1 / M.B ^ 2) 0

/-- `M.toWeierstrass` is the quadratic twist of `Y² = X³ + A X² + X` by `B⁻¹`. -/
theorem toWeierstrass_eq_quadraticTwist :
    M.toWeierstrass = (ofCubic M.A 1 0).quadraticTwist M.B⁻¹ := by
  ext <;> simp only [toWeierstrass, quadraticTwist, ofCubic_a₁, ofCubic_a₂, ofCubic_a₃,
    ofCubic_a₄, ofCubic_a₆] <;> ring

/-- The discriminant of `M.toWeierstrass` is `16 (A² - 4) / B⁶`. -/
theorem toWeierstrass_Δ :
    M.toWeierstrass.Δ = 16 * (M.A ^ 2 - 4) / M.B ^ 6 := by
  rw [toWeierstrass_eq_quadraticTwist, quadraticTwist_Δ, Δ_of_isCharNeTwoNF]
  simp only [ofCubic_a₂, ofCubic_a₄, ofCubic_a₆]
  rw [div_eq_mul_inv, inv_pow]
  ring

/-- When `2 ≠ 0` in `F`, `M.toWeierstrass` is an elliptic curve. -/
theorem isElliptic_toWeierstrass (h2 : (2 : F) ≠ 0) : M.toWeierstrass.IsElliptic := by
  have h16 : (16 : F) ≠ 0 := by
    rw [show (16 : F) = 2 ^ 4 by norm_num]
    exact pow_ne_zero 4 h2
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [toWeierstrass_Δ]
  exact div_ne_zero (mul_ne_zero h16 M.discr_ne_zero) (pow_ne_zero 6 M.B_ne_zero)

/-- Affine solutions `(B x, B y)` of `M.Equation` correspond to affine solutions `(x, y)` of
`M.toWeierstrass`. -/
theorem equation_iff_toWeierstrass (x y : F) :
    M.Equation (M.B * x) (M.B * y) ↔ M.toWeierstrass.toAffine.Equation x y := by
  have hB : M.B ≠ 0 := M.B_ne_zero
  have hq := (ofCubic M.A 1 0).quadraticTwist_equation_iff (inv_ne_zero hB) (M.B * x) (M.B ^ 2 * y)
  have hy : M.B⁻¹ ^ 2 * (M.B ^ 2 * y) = y := by
    rw [inv_pow, inv_mul_cancel_left₀ (pow_ne_zero 2 hB)]
  have heq : M.B⁻¹ * (M.B ^ 2 * y) ^ 2 = M.B * (M.B * y) ^ 2 := by field_simp
  rw [← toWeierstrass_eq_quadraticTwist, inv_mul_cancel_left₀ hB, hy] at hq
  rw [hq, heq, Equation]
  simp only [ofCubic_a₂, ofCubic_a₄, ofCubic_a₆]
  rw [show (M.B * x) ^ 3 + M.A * (M.B * x) ^ 2 + 1 * (M.B * x) + 0 =
    (M.B * x) ^ 3 + M.A * (M.B * x) ^ 2 + M.B * x by ring]

/-- An affine point `(u, v)` on `M` maps to an affine solution `(u / B, v / B)` of
`M.toWeierstrass`. -/
theorem toWeierstrass_equation_div {u v : F} (h : M.Equation u v) :
    M.toWeierstrass.toAffine.Equation (u / M.B) (v / M.B) :=
  (M.equation_iff_toWeierstrass (u / M.B) (v / M.B)).mp (by
    simpa [mul_div_cancel₀ _ M.B_ne_zero] using h)

/-- When `2 ≠ 0`, an affine point `(u, v)` on `M` maps to a nonsingular point `(u / B, v / B)` on
`M.toWeierstrass`. -/
theorem toWeierstrass_nonsingular_div (h2 : (2 : F) ≠ 0) {u v : F} (h : M.Equation u v) :
    M.toWeierstrass.toAffine.Nonsingular (u / M.B) (v / M.B) :=
  letI := M.isElliptic_toWeierstrass h2
  Affine.equation_iff_nonsingular.mp (M.toWeierstrass_equation_div h)

/-- Equivalence between `M.Point` and the affine points of `M.toWeierstrass` when `2 ≠ 0`
([BonehShoup2023], Section 15.2.1, p. 619). -/
noncomputable def toWeierstrassEquiv (h2 : (2 : F) ≠ 0) :
    M.Point ≃ M.toWeierstrass.toAffine.Point where
  toFun
    | .zero => 0
    | .some u v h => .some (u / M.B) (v / M.B) (M.toWeierstrass_nonsingular_div h2 h)
  invFun
    | 0 => .zero
    | .some x y h => .some (M.B * x) (M.B * y) ((M.equation_iff_toWeierstrass x y).mpr h.1)
  left_inv := by
    rintro (_ | ⟨u, v, h⟩)
    · rfl
    · simp [mul_div_cancel₀ _ M.B_ne_zero]
  right_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · simp [mul_div_cancel_left₀ _ M.B_ne_zero]

/-- `M.toWeierstrassEquiv` maps `.zero` to `0`. -/
@[simp] theorem toWeierstrassEquiv_zero (h2 : (2 : F) ≠ 0) :
    M.toWeierstrassEquiv h2 .zero = 0 := by
  rfl

/-- `M.toWeierstrassEquiv` maps an affine point `.some u v h` to `.some (u / M.B) (v / M.B)`. -/
@[simp] theorem toWeierstrassEquiv_some (h2 : (2 : F) ≠ 0) {u v : F} (h : M.Equation u v) :
    M.toWeierstrassEquiv h2 (.some u v h) =
      .some (u / M.B) (v / M.B) (M.toWeierstrass_nonsingular_div h2 h) := by
  rfl

/-- `(M.toWeierstrassEquiv h2).symm` maps `0` to `.zero`. -/
@[simp] theorem toWeierstrassEquiv_symm_zero (h2 : (2 : F) ≠ 0) :
    (M.toWeierstrassEquiv h2).symm 0 = .zero := by
  rfl

/-- `(M.toWeierstrassEquiv h2).symm` maps `.some x y h` to `.some (M.B * x) (M.B * y)`. -/
@[simp] theorem toWeierstrassEquiv_symm_some (h2 : (2 : F) ≠ 0) {x y : F}
    (h : M.toWeierstrass.toAffine.Nonsingular x y) :
    (M.toWeierstrassEquiv h2).symm (.some x y h) =
      .some (M.B * x) (M.B * y) ((M.equation_iff_toWeierstrass x y).mpr h.1) := by
  rfl

/-- Shift `X ↦ X - A / (3 B)` transforming `M.toWeierstrass` into short Weierstrass form when
`3 ≠ 0` ([BonehShoup2023], Section 15.2.1, p. 619). -/
noncomputable def toShortWeierstrass : WeierstrassCurve F :=
  VariableChange.mk 1 (-M.A / (3 * M.B)) 0 0 • M.toWeierstrass

/-- When `2` and `3` are invertible in `F`, `M.toShortWeierstrass` equals the curve obtained from
`M.toWeierstrass` via Mathlib's `WeierstrassCurve.toShortNF`. -/
theorem toShortWeierstrass_eq_toShortNF [Invertible (2 : F)] [Invertible (3 : F)] :
    M.toShortWeierstrass = M.toWeierstrass.toShortNF • M.toWeierstrass := by
  have hC : (VariableChange.mk 1 (-M.A / (3 * M.B)) 0 0 : VariableChange F) =
      M.toWeierstrass.toShortNF := by
    rw [WeierstrassCurve.toShortNF]
    have h2nf : M.toWeierstrass.toCharNeTwoNF = 1 := by
      rw [WeierstrassCurve.toCharNeTwoNF]
      simp only [toWeierstrass, ofCubic_a₁, ofCubic_a₃, neg_zero, mul_zero]
      rfl
    rw [h2nf, mul_one, one_smul]
    congr 1
    simp only [toWeierstrass, ofCubic_a₂, invOf_eq_inv]
    ring
  rw [toShortWeierstrass, hC]

/-- When `3 ≠ 0`, `M.toShortWeierstrass` is in short Weierstrass normal form (`a₁ = a₂ = a₃ = 0`).
-/
theorem isShortNF_toShortWeierstrass (h3 : (3 : F) ≠ 0) : M.toShortWeierstrass.IsShortNF := by
  have hB : M.B ≠ 0 := M.B_ne_zero
  constructor <;> simp only [toShortWeierstrass, toWeierstrass, variableChange_a₁,
    variableChange_a₂, variableChange_a₃, ofCubic_a₁, ofCubic_a₂, ofCubic_a₃, inv_one,
    Units.val_one]
  · ring
  · field_simp
    ring
  · ring

/-- In characteristic three (`3 = 0` in `F`), if `M.A ≠ 0` then `M.toShortWeierstrass` is not in
short normal form, since `a₂ = A / B ≠ 0`. -/
theorem not_isShortNF_toShortWeierstrass (h3 : (3 : F) = 0) (hA : M.A ≠ 0) :
    ¬ M.toShortWeierstrass.IsShortNF := by
  intro hnf
  have ha2 : M.toShortWeierstrass.a₂ = M.A / M.B := by
    simp only [toShortWeierstrass, toWeierstrass, variableChange_a₂, ofCubic_a₁, ofCubic_a₂,
      inv_one, Units.val_one]
    rw [h3]
    ring
  have h0 : M.A / M.B = 0 := ha2.symm.trans hnf.a₂
  exact hA (div_eq_zero_iff.mp h0 |>.resolve_right M.B_ne_zero)

/-- Affine solutions `(B x - A / 3, B y)` of `M.Equation` correspond to affine solutions `(x, y)`
of `M.toShortWeierstrass`, without requiring `3 ≠ 0`. -/
theorem equation_iff_toShortWeierstrass (x y : F) :
    M.Equation (M.B * x - M.A / 3) (M.B * y) ↔ M.toShortWeierstrass.toAffine.Equation x y := by
  have hB : M.B ≠ 0 := M.B_ne_zero
  rw [toShortWeierstrass, variableChange_equation_iff, ← equation_iff_toWeierstrass]
  have hx : M.B * ((1 : Fˣ) ^ 2 * x + -M.A / (3 * M.B)) = M.B * x - M.A / 3 := by
    by_cases h3 : (3 : F) = 0
    · simp [h3]
    · field_simp
      simp only [Units.val_one]
      ring
  have hy : M.B * ((1 : Fˣ) ^ 3 * y + (1 : Fˣ) ^ 2 * 0 * x + 0) = M.B * y := by simp
  rw [hx, hy]

end Basic

section DivFour

variable {F : Type*} [Field F]

private lemma toWeierstrass_negY (M : MontgomeryCurve F) (x y : F) :
    M.toWeierstrass.toAffine.negY x y = -y := by
  simp [Affine.negY, toWeierstrass]

private lemma four_dvd_of_twoTorsion (M : MontgomeryCurve F) (h2 : (2 : F) ≠ 0)
    (r : F) (hr : r ^ 2 = M.A ^ 2 - 4) :
    4 ∣ Nat.card M.toWeierstrass.toAffine.Point := by
  classical
  have := M.isElliptic_toWeierstrass h2
  have hB : M.B ≠ 0 := M.B_ne_zero
  have hr0 : r ≠ 0 := fun h ↦ M.discr_ne_zero (by rw [← hr, h]; norm_num)
  let x₁ : F := (-M.A + 1 * r) / (2 * M.B)
  let x₂ : F := (-M.A + -1 * r) / (2 * M.B)
  have hroot_ne (s : F) (hs : s ^ 2 = 1) : (-M.A + s * r) / (2 * M.B) ≠ 0 := by
    intro h
    have hA : M.A = s * r := by
      have hnum := (div_eq_zero_iff.mp h).resolve_right (mul_ne_zero h2 hB)
      linear_combination -hnum
    have h4 : (2 : F) * 2 = 0 := by
      have : M.A ^ 2 = s ^ 2 * r ^ 2 := by rw [hA]; ring
      rw [hs, one_mul, hr] at this
      linear_combination this
    exact mul_ne_zero h2 h2 h4
  have hx₁0 : x₁ ≠ 0 := hroot_ne 1 (one_pow 2)
  have hx₂0 : x₂ ≠ 0 := hroot_ne (-1) (by norm_num)
  have hx₁₂ : x₁ ≠ x₂ := by
    intro h
    have hmul : (2 : F) * r = 0 := by
      dsimp [x₁, x₂] at h
      have h' := congr_arg ((2 * M.B) * ·) h
      field_simp at h'
      linear_combination h'
    exact absurd (mul_eq_zero.mp hmul) (not_or.mpr ⟨h2, hr0⟩)
  have hEq0 : M.toWeierstrass.toAffine.Equation 0 0 := by
    rw [← M.equation_iff_toWeierstrass, Equation]
    simp
  have hEqs (s : F) (hs : s ^ 2 = 1) :
      M.toWeierstrass.toAffine.Equation ((-M.A + s * r) / (2 * M.B)) 0 := by
    rw [← M.equation_iff_toWeierstrass, Equation]
    have hBx : M.B * ((-M.A + s * r) / (2 * M.B)) = (-M.A + s * r) / 2 := by field_simp
    have hfac : ((-M.A + s * r) / 2) ^ 3 + M.A * ((-M.A + s * r) / 2) ^ 2 + (-M.A + s * r) / 2 =
        ((-M.A + s * r) / 8) * ((s * r) ^ 2 - (M.A ^ 2 - 4)) := by
      have h8 : (8 : F) ≠ 0 := by rw [show (8 : F) = 2 ^ 3 by ring]; exact pow_ne_zero 3 h2
      field_simp
      ring
    rw [hBx, mul_zero, zero_pow two_ne_zero, mul_zero, hfac, mul_pow, hs, one_mul,
      sub_eq_zero.mpr hr, mul_zero]
  have hEq1 : M.toWeierstrass.toAffine.Equation x₁ 0 := hEqs 1 (one_pow 2)
  have hEq2 : M.toWeierstrass.toAffine.Equation x₂ 0 := hEqs (-1) (by norm_num)
  let P₀ : M.toWeierstrass.toAffine.Point := Affine.Point.mk hEq0
  let P₁ : M.toWeierstrass.toAffine.Point := Affine.Point.mk hEq1
  let P₂ : M.toWeierstrass.toAffine.Point := Affine.Point.mk hEq2
  let H : AddSubgroup M.toWeierstrass.toAffine.Point :=
    { carrier := {P | P + P = 0}
      zero_mem' := zero_add 0
      add_mem' := fun {a b} ha hb ↦ by
        change (a + b) + (a + b) = 0
        rw [add_add_add_comm, ha, hb, zero_add]
      neg_mem' := fun {a} ha ↦ by
        change -a + -a = 0
        rw [← neg_add, ha, neg_zero] }
  have hHP0 : P₀ ∈ H := Affine.Point.add_of_Y_eq rfl (by rw [toWeierstrass_negY, neg_zero])
  have hHP1 : P₁ ∈ H := Affine.Point.add_of_Y_eq rfl (by rw [toWeierstrass_negY, neg_zero])
  have hHP2 : P₂ ∈ H := Affine.Point.add_of_Y_eq rfl (by rw [toWeierstrass_negY, neg_zero])
  have hSet : (H : Set M.toWeierstrass.toAffine.Point) = {0, P₀, P₁, P₂} := by
    ext P
    refine ⟨fun hP ↦ ?_, fun hP ↦ ?_⟩
    · rcases P with _ | ⟨x, y, h⟩
      · left; rfl
      · have hy : y = M.toWeierstrass.toAffine.negY x y := by
          by_contra hne
          have hadd := Affine.Point.add_some (x₁ := x) (x₂ := x) (y₁ := y) (y₂ := y)
            (fun ⟨_, hy'⟩ ↦ hne hy') (h₁ := h) (h₂ := h)
          rw [show Affine.Point.some x y h + Affine.Point.some x y h = 0 from hP] at hadd
          exact Affine.Point.some_ne_zero _ hadd.symm
        have hy0 : y = 0 := by
          rw [toWeierstrass_negY] at hy
          have : 2 * y = 0 := by linear_combination hy
          exact (mul_eq_zero.mp this).resolve_left h2
        subst hy0
        have heq := (M.equation_iff_toWeierstrass x 0).mpr h.1
        rw [Equation] at heq
        have hfac : x * (x - x₁) * (x - x₂) = 0 := by
          have hsub : r ^ 2 - (M.A ^ 2 - 4) = 0 := sub_eq_zero.mpr hr
          have hzero : (M.B * x) ^ 3 + M.A * (M.B * x) ^ 2 + M.B * x = 0 := by
            linear_combination -heq
          have hid : 4 * M.B ^ 3 * (x * (x - x₁) * (x - x₂)) =
              4 * ((M.B * x) ^ 3 + M.A * (M.B * x) ^ 2 + M.B * x) -
                M.B * x * (r ^ 2 - (M.A ^ 2 - 4)) := by
            dsimp [x₁, x₂]
            field_simp
            ring
          rw [hzero, hsub, mul_zero, mul_zero, sub_zero] at hid
          have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 ^ 2 by ring]; exact pow_ne_zero 2 h2
          exact (mul_eq_zero.mp hid).resolve_left (mul_ne_zero h4 (pow_ne_zero 3 hB))
        simp only [mul_eq_zero, sub_eq_zero] at hfac
        rcases hfac with (rfl | rfl) | rfl <;> simp [P₀, P₁, P₂, Affine.Point.mk]
    · rcases hP with rfl | rfl | rfl | rfl
      exacts [H.zero_mem, hHP0, hHP1, hHP2]
  have hcard : Nat.card H = 4 := by
    have hp0 : P₀ ≠ 0 := Affine.Point.some_ne_zero _
    have hp1 : P₁ ≠ 0 := Affine.Point.some_ne_zero _
    have hp2 : P₂ ≠ 0 := Affine.Point.some_ne_zero _
    have hp01 : P₀ ≠ P₁ := fun h ↦ hx₁0 (Affine.Point.some.inj h).1.symm
    have hp02 : P₀ ≠ P₂ := fun h ↦ hx₂0 (Affine.Point.some.inj h).1.symm
    have hp12 : P₁ ≠ P₂ := fun h ↦ hx₁₂ (Affine.Point.some.inj h).1
    rw [← SetLike.coe_sort_coe, hSet, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem,
      Set.ncard_insert_of_notMem, Set.ncard_pair hp12] <;>
      simp [hp0.symm, hp1.symm, hp2.symm, hp01, hp02]
  rw [← hcard]
  exact AddSubgroup.card_addSubgroup_dvd_card H

private lemma four_dvd_of_fourTorsion (M : MontgomeryCurve F) (h2 : (2 : F) ≠ 0)
    (ε s : F) (hε : ε ^ 2 = 1) (hs : s ^ 2 = (M.A + 2 * ε) / M.B) :
    4 ∣ Nat.card M.toWeierstrass.toAffine.Point := by
  classical
  let _ : M.toWeierstrass.IsElliptic := M.isElliptic_toWeierstrass h2
  have hB : M.B ≠ 0 := M.B_ne_zero
  have hs' : M.B * s ^ 2 = M.A + 2 * ε := by rw [hs, mul_div_cancel₀ _ hB]
  have hAε : M.A + 2 * ε ≠ 0 := by
    intro h
    have hA : M.A = -2 * ε := by linear_combination h
    apply M.discr_ne_zero
    rw [hA]
    linear_combination 4 * hε
  have hs0 : s ≠ 0 := fun h ↦
    hAε (by linear_combination -hs' + M.B * (by rw [h]; ring : s ^ 2 = 0))
  have hEq0 : M.toWeierstrass.toAffine.Equation 0 0 := by
    rw [← M.equation_iff_toWeierstrass, Equation]
    simp
  have hEq : M.toWeierstrass.toAffine.Equation (ε / M.B) (s / M.B) := by
    rw [← M.equation_iff_toWeierstrass, mul_div_cancel₀ _ hB, mul_div_cancel₀ _ hB, Equation]
    linear_combination hs' - (ε + M.A) * hε
  let P₀ : M.toWeierstrass.toAffine.Point := Affine.Point.mk hEq0
  let P : M.toWeierstrass.toAffine.Point := Affine.Point.mk hEq
  have hP2 : P + P = P₀ := by
    have hne : s / M.B ≠ M.toWeierstrass.toAffine.negY (ε / M.B) (s / M.B) := by
      intro h
      rw [toWeierstrass_negY] at h
      have : 2 * (s / M.B) = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).elim h2 (div_ne_zero hs0 hB)
    dsimp [P, P₀, Affine.Point.mk]
    rw [Affine.Point.add_some (fun ⟨_, h⟩ ↦ hne h)]
    simp only [Affine.Point.some.injEq]
    have hslope : M.toWeierstrass.toAffine.slope (ε / M.B) (ε / M.B) (s / M.B) (s / M.B) =
        ε * s := by
      rw [Affine.slope_of_Y_ne rfl hne]
      change (3 * (ε / M.B) ^ 2 + 2 * (M.A / M.B) * (ε / M.B) + 1 / M.B ^ 2 - 0 * (s / M.B)) /
        (s / M.B - (-(s / M.B) - 0 * (ε / M.B) - 0)) = ε * s
      have hsub2 : s / M.B - (-(s / M.B) - 0 * (ε / M.B) - 0) = 2 * s / M.B := by ring
      have h2sB : 2 * s / M.B ≠ 0 := div_ne_zero (mul_ne_zero h2 hs0) hB
      rw [hsub2, div_eq_iff h2sB]
      apply mul_right_cancel₀ (pow_ne_zero 2 hB)
      have hLHS : (3 * (ε / M.B) ^ 2 + 2 * (M.A / M.B) * (ε / M.B) + 1 / M.B ^ 2 -
          0 * (s / M.B)) * M.B ^ 2 = 3 * ε ^ 2 + 2 * M.A * ε + 1 := by
        field_simp; ring
      have hRHS : ε * s * (2 * s / M.B) * M.B ^ 2 = 2 * ε * (M.B * s ^ 2) := by
        field_simp
      rw [hLHS, hRHS, hs']
      linear_combination -hε
    rw [hslope]
    simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY]
    change ((ε * s) ^ 2 + 0 * (ε * s) - M.A / M.B - ε / M.B - ε / M.B = 0) ∧
      (-(ε * s * (((ε * s) ^ 2 + 0 * (ε * s) - M.A / M.B - ε / M.B - ε / M.B) - ε / M.B) +
        s / M.B) - 0 * _ - 0 = 0)
    have hx0 : (ε * s) ^ 2 + 0 * (ε * s) - M.A / M.B - ε / M.B - ε / M.B = 0 := by
      field_simp
      linear_combination M.B * s ^ 2 * hε + hs'
    refine ⟨hx0, ?_⟩
    rw [hx0]
    field_simp
    linear_combination s * hε
  have hord : addOrderOf P = 4 := by
    refine (addOrderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_).trans (by norm_num)
    · rw [pow_one, two_nsmul, hP2]
      exact Affine.Point.some_ne_zero _
    · rw [show (2 ^ (1 + 1) : ℕ) • P = (P + P) + (P + P) by
        rw [show (2 ^ (1 + 1) : ℕ) = 2 + 2 by norm_num, add_nsmul, two_nsmul], hP2]
      exact Affine.Point.add_of_Y_eq rfl (by rw [toWeierstrass_negY, neg_zero])
  rw [← hord]
  exact addOrderOf_dvd_natCard P

/-- Over a finite field of characteristic `≠ 2`, `4 ∣ #M.toWeierstrass(F)` ([BonehShoup2023],
Section 15.2.1, p. 619). -/
theorem four_dvd_natCard_toWeierstrass_point (M : MontgomeryCurve F) [Finite F]
    (hF : ringChar F ≠ 2) : 4 ∣ Nat.card M.toWeierstrass.toAffine.Point := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  by_cases hsq : IsSquare (M.A ^ 2 - 4)
  · obtain ⟨r, hr⟩ := hsq
    exact four_dvd_of_twoTorsion M h2 r (by rw [sq, ← hr])
  · have hB : M.B ≠ 0 := M.B_ne_zero
    let _ : Fintype F := Fintype.ofFinite F
    let a := (M.A + 2) / M.B
    let b := (M.A - 2) / M.B
    have hab : a * b = (M.A ^ 2 - 4) / M.B ^ 2 := by dsimp [a, b]; ring
    have ha0 : a ≠ 0 :=
      div_ne_zero (fun h ↦ M.discr_ne_zero (by linear_combination (M.A - 2) * h)) hB
    have hb0 : b ≠ 0 :=
      div_ne_zero (fun h ↦ M.discr_ne_zero (by linear_combination (M.A + 2) * h)) hB
    have hns : ¬IsSquare (a * b) := by
      rw [hab]
      rintro ⟨u, hu⟩
      apply hsq
      refine ⟨M.B * u, ?_⟩
      field_simp at hu
      linear_combination hu
    have hχ : quadraticChar F (a * b) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hns
    rw [map_mul] at hχ
    rcases quadraticChar_dichotomy ha0 with hχa | hχa
    · obtain ⟨s, hs⟩ := (quadraticChar_one_iff_isSquare ha0).mp hχa
      exact four_dvd_of_fourTorsion M h2 1 s (by norm_num) (by rw [sq, ← hs]; dsimp [a]; ring)
    · have hχb : quadraticChar F b = 1 := by
        rw [hχa] at hχ
        omega
      obtain ⟨s, hs⟩ := (quadraticChar_one_iff_isSquare hb0).mp hχb
      exact four_dvd_of_fourTorsion M h2 (-1) s (by norm_num)
        (by rw [sq, ← hs]; dsimp [b]; ring)

/-- Over a finite field of characteristic `≠ 2`, the order of any Montgomery curve is divisible by
`4` ([BonehShoup2023], Section 15.2.1, p. 619). -/
theorem four_dvd_natCard_point (M : MontgomeryCurve F) [Finite F] (hF : ringChar F ≠ 2) :
    4 ∣ Nat.card M.Point := by
  rw [Nat.card_congr (M.toWeierstrassEquiv (Ring.two_ne_zero hF))]
  exact M.four_dvd_natCard_toWeierstrass_point hF

/-- No Montgomery curve over a finite field of characteristic `≠ 2` is related by a change of
variables to a Weierstrass curve of odd order. -/
theorem not_variableChange_of_odd {W : WeierstrassCurve F} [Finite F] (hF : ringChar F ≠ 2)
    (hodd : Odd (Nat.card W.toAffine.Point)) (M : MontgomeryCurve F) (C : VariableChange F) :
    C • M.toWeierstrass ≠ W := by
  classical
  intro hC
  have h4 := M.four_dvd_natCard_toWeierstrass_point hF
  have he : (C • M.toWeierstrass).toAffine.Point ≃+ M.toWeierstrass.toAffine.Point :=
    variableChangePointEquiv C M.toWeierstrass
  rw [hC] at he
  rw [← Nat.card_congr he.toEquiv] at h4
  exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)) hodd

end DivFour

end MontgomeryCurve
