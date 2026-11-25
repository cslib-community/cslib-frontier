/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`)

public import CslibFrontier.Init
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Change of variables on affine Weierstrass points

Relates affine equations, nonsingularity, and the affine group law under an admissible linear
change of variables `C : WeierstrassCurve.VariableChange F` over a field `F`, yielding the additive
group equivalence `(C • W).toAffine.Point ≃+ W.toAffine.Point`.

## Main definitions

* `WeierstrassCurve.variableChangePointEquiv`: additive group equivalence between the affine
  points of `C • W` and those of `W`, whose action on affine points is given by
  `WeierstrassCurve.variableChangePointEquiv_some`.

## Main results

* `WeierstrassCurve.variableChange_equation_iff`: characterizes `(C • W).toAffine.Equation x y`
  in terms of `W.toAffine.Equation` at `(C.u ^ 2 * x + C.r, C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)`.
* `WeierstrassCurve.variableChange_nonsingular_iff`: characterizes
  `(C • W).toAffine.Nonsingular x y` in terms of `W.toAffine.Nonsingular` at
  `(C.u ^ 2 * x + C.r, C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 15.2.1.
-/

public section

namespace WeierstrassCurve

variable {F : Type*} [Field F]

/-- An affine point `(x, y)` satisfies the equation of `C • W` if and only if
`(C.u ^ 2 * x + C.r, C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)` satisfies `W`. -/
theorem variableChange_equation_iff (C : VariableChange F) (W : WeierstrassCurve F)
    (x y : F) :
    (C • W).toAffine.Equation x y ↔
      W.toAffine.Equation (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [Affine.equation_iff]
  dsimp only [WeierstrassCurve.toAffine]
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, Units.val_inv_eq_inv_val]
  refine ⟨fun h => ?_, fun h => by field_simp; linear_combination h⟩
  have h6 := congr_arg ((C.u : F) ^ 6 * ·) h
  field_simp at h6; linear_combination h6

private lemma variableChange_polynomialY (C : VariableChange F) (W : WeierstrassCurve F)
    (x y : F) :
    (C • W).toAffine.polynomialY.evalEval x y =
      (C.u : F)⁻¹ ^ 3 *
        W.toAffine.polynomialY.evalEval (C.u ^ 2 * x + C.r)
          (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [Affine.evalEval_polynomialY]
  dsimp only [WeierstrassCurve.toAffine]
  simp only [variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp; ring

private lemma variableChange_polynomialX (C : VariableChange F) (W : WeierstrassCurve F)
    (x y : F) :
    (C • W).toAffine.polynomialX.evalEval x y =
      (C.u : F)⁻¹ ^ 4 *
        (W.toAffine.polynomialX.evalEval (C.u ^ 2 * x + C.r)
            (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) +
          C.s * W.toAffine.polynomialY.evalEval (C.u ^ 2 * x + C.r)
            (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [Affine.evalEval_polynomialX, Affine.evalEval_polynomialY]
  dsimp only [WeierstrassCurve.toAffine]
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp; ring

/-- An affine point `(x, y)` is nonsingular on `C • W` if and only if
`(C.u ^ 2 * x + C.r, C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)` is nonsingular on `W`. -/
theorem variableChange_nonsingular_iff (C : VariableChange F) (W : WeierstrassCurve F)
    (x y : F) :
    (C • W).toAffine.Nonsingular x y ↔
      W.toAffine.Nonsingular (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [Affine.Nonsingular, variableChange_equation_iff, variableChange_polynomialX,
    variableChange_polynomialY]
  refine and_congr_right fun _ ↦ ?_
  by_cases hY : W.toAffine.polynomialY.evalEval (↑C.u ^ 2 * x + C.r)
      (↑C.u ^ 3 * y + ↑C.u ^ 2 * C.s * x + C.t) = 0 <;> simp [hY]

private lemma variableChange_negY (C : VariableChange F) (W : WeierstrassCurve F) (x y : F) :
    C.u ^ 3 * (C • W).toAffine.negY x y + C.u ^ 2 * C.s * x + C.t =
      W.toAffine.negY (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  dsimp only [Affine.negY, WeierstrassCurve.toAffine]
  simp only [variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp; ring

private lemma variableChange_eq_and_negY_iff (C : VariableChange F) (W : WeierstrassCurve F)
    (x₁ x₂ y₁ y₂ : F) :
    (C.u ^ 2 * x₁ + C.r = C.u ^ 2 * x₂ + C.r ∧
        C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t =
          W.toAffine.negY (C.u ^ 2 * x₂ + C.r)
            (C.u ^ 3 * y₂ + C.u ^ 2 * C.s * x₂ + C.t)) ↔
      (x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  refine ⟨fun ⟨hx, hy⟩ => ?_, fun ⟨rfl, hy⟩ => ⟨rfl, by rw [hy, variableChange_negY]⟩⟩
  obtain rfl : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (add_right_cancel hx)
  exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero 3 hu)
    (add_right_cancel (add_right_cancel (hy.trans (variableChange_negY C W x₁ y₂).symm)))⟩

private lemma variableChange_slope [DecidableEq F] (C : VariableChange F) (W : WeierstrassCurve F)
    {x₁ x₂ y₁ y₂ : F} (h₁ : (C • W).toAffine.Equation x₁ y₁)
    (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope x₁ x₂ y₁ y₂ =
      C.u⁻¹ * (W.toAffine.slope (C.u ^ 2 * x₁ + C.r) (C.u ^ 2 * x₂ + C.r)
        (C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t)
        (C.u ^ 3 * y₂ + C.u ^ 2 * C.s * x₂ + C.t) - C.s) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hxy' := mt (variableChange_eq_and_negY_iff C W x₁ x₂ y₁ y₂).mp hxy
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ (C • W).toAffine.negY x₂ y₂ := fun h ↦ hxy ⟨hx, h⟩
    obtain ⟨rfl, rfl⟩ : x₁ = x₂ ∧ y₁ = y₂ := ⟨hx, Affine.Y_eq_of_Y_ne h₁ h₂ hx hy⟩
    have hy' : C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t ≠
        W.toAffine.negY (C.u ^ 2 * x₁ + C.r) (C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t) :=
      fun h ↦ hxy' ⟨rfl, h⟩
    rw [Affine.slope_of_Y_ne_eq_evalEval rfl hy, Affine.slope_of_Y_ne_eq_evalEval rfl hy',
      variableChange_polynomialX, variableChange_polynomialY, Units.val_inv_eq_inv_val]
    have hpy : W.toAffine.polynomialY.evalEval (C.u ^ 2 * x₁ + C.r)
        (C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t) ≠ 0 := fun h0 => hy' <| by
      rw [Affine.evalEval_polynomialY] at h0
      dsimp only [Affine.negY, WeierstrassCurve.toAffine] at h0 ⊢; linear_combination h0
    generalize W.toAffine.polynomialX.evalEval _ _ = px,
      W.toAffine.polynomialY.evalEval _ _ = py at hpy ⊢
    field_simp; ring
  · have hx' : (C.u : F) ^ 2 * x₁ + C.r ≠ C.u ^ 2 * x₂ + C.r :=
      fun h ↦ hx (mul_left_cancel₀ (pow_ne_zero 2 hu) (add_right_cancel h))
    rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx', Units.val_inv_eq_inv_val,
      show (↑C.u ^ 2 * x₁ + C.r) - (↑C.u ^ 2 * x₂ + C.r) = ↑C.u ^ 2 * (x₁ - x₂) by ring]
    have := sub_ne_zero_of_ne hx
    field_simp; ring

/-- The additive group equivalence `(C • W).toAffine.Point ≃+ W.toAffine.Point` sending
`(x, y) ↦ (C.u ^ 2 * x + C.r, C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)` and `0 ↦ 0`. -/
def variableChangePointEquiv [DecidableEq F] (C : VariableChange F) (W : WeierstrassCurve F) :
    (C • W).toAffine.Point ≃+ W.toAffine.Point where
  toFun
    | 0 => 0
    | .some x y h =>
      .some (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)
        ((variableChange_nonsingular_iff C W x y).mp h)
  invFun
    | 0 => 0
    | .some x y h =>
      .some (C.u⁻¹ ^ 2 * (x - C.r))
        (C.u⁻¹ ^ 3 * (y - C.u ^ 2 * C.s * (C.u⁻¹ ^ 2 * (x - C.r)) - C.t))
        ((variableChange_nonsingular_iff C W _ _).mpr <| by
          have hu : (C.u : F) ≠ 0 := C.u.ne_zero
          simp only [Units.val_inv_eq_inv_val]
          convert h using 2 <;> field_simp <;> ring)
  left_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · simp only [Affine.Point.some.injEq, Units.val_inv_eq_inv_val]
      have hu : (C.u : F) ≠ 0 := C.u.ne_zero
      constructor <;> field_simp <;> ring
  right_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · simp only [Affine.Point.some.injEq, Units.val_inv_eq_inv_val]
      have hu : (C.u : F) ≠ 0 := C.u.ne_zero
      constructor <;> field_simp <;> ring
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    · rfl
    · rfl
    · rfl
    · have hu : (C.u : F) ≠ 0 := C.u.ne_zero
      by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
      · rcases hxy with ⟨rfl, hy⟩
        rw [Affine.Point.add_of_Y_eq rfl hy]
        have hy' : C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t =
            W.toAffine.negY (C.u ^ 2 * x₁ + C.r) (C.u ^ 3 * y₂ + C.u ^ 2 * C.s * x₁ + C.t) := by
          rw [hy, variableChange_negY]
        exact (Affine.Point.add_of_Y_eq rfl hy').symm
      · have hxy' := mt (variableChange_eq_and_negY_iff C W x₁ x₂ y₁ y₂).mp hxy
        rw [Affine.Point.add_some hxy, Affine.Point.add_some hxy']
        simp only [Affine.Point.some.injEq]
        rw [variableChange_slope C W h₁.1 h₂.1 hxy]
        simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY]
        change (↑C.u ^ 2 * ((↑C.u⁻¹ * (W.toAffine.slope _ _ _ _ - C.s)) ^ 2 +
            (C • W).a₁ * (↑C.u⁻¹ * (W.toAffine.slope _ _ _ _ - C.s)) -
            (C • W).a₂ - x₁ - x₂) + C.r = _) ∧ _
        simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃,
          Units.val_inv_eq_inv_val]
        constructor <;> field_simp <;> ring

/-- Explicit coordinate formula for `WeierstrassCurve.variableChangePointEquiv` on affine
points. -/
theorem variableChangePointEquiv_some [DecidableEq F] (C : VariableChange F)
    (W : WeierstrassCurve F) {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    variableChangePointEquiv C W (.some x y h) =
      .some (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)
        ((variableChange_nonsingular_iff C W x y).mp h) := by
  rfl

end WeierstrassCurve
