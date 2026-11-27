/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (unit tests for EllipticCurve.VariableChange)

public import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.Decidable
public import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Variable change tests on affine Weierstrass points

Client tests for `WeierstrassCurve.variableChange_equation_iff`,
`WeierstrassCurve.variableChange_nonsingular_iff`, `WeierstrassCurve.variableChangePointEquiv`,
and `WeierstrassCurve.variableChangePointEquiv_some` generically over any field, over `ZMod 7`,
and on a singular nodal cubic over `ZMod 5`.
-/

namespace CslibFrontierTests.VariableChange

open WeierstrassCurve

public theorem generic_variableChange_map_add {F : Type*} [Field F] [DecidableEq F]
    (C : VariableChange F) (W : WeierstrassCurve F) {x₁ y₁ x₂ y₂ x₃ y₃ : F}
    (h₁ : (C • W).toAffine.Nonsingular x₁ y₁) (h₂ : (C • W).toAffine.Nonsingular x₂ y₂)
    (h₃' : W.toAffine.Nonsingular x₃ y₃)
    (hadd : (.some _ _ ((variableChange_nonsingular_iff C W x₁ y₁).mp h₁) : W.toAffine.Point) +
        .some _ _ ((variableChange_nonsingular_iff C W x₂ y₂).mp h₂) =
      .some x₃ y₃ h₃') :
    variableChangePointEquiv C W ((.some x₁ y₁ h₁ : (C • W).toAffine.Point) + .some x₂ y₂ h₂) =
      .some x₃ y₃ h₃' := by
  rw [map_add, variableChangePointEquiv_some, variableChangePointEquiv_some, hadd]

section ZMod7

private local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private abbrev baseCurve : WeierstrassCurve (ZMod 7) := ⟨0, 0, 0, 3, 3⟩

private abbrev testChange : VariableChange (ZMod 7) :=
  ⟨⟨3, 5, by decide, by decide⟩, 1, 2, 4⟩

private abbrev transformedCurve : WeierstrassCurve (ZMod 7) := testChange • baseCurve

-- Positive and negative `variableChange_equation_iff` checks.
example : transformedCurve.toAffine.Equation 0 4 := by decide

example :
    baseCurve.toAffine.Equation (testChange.u ^ 2 * 0 + testChange.r)
      (testChange.u ^ 3 * 4 + testChange.u ^ 2 * testChange.s * 0 + testChange.t) :=
  (variableChange_equation_iff testChange baseCurve 0 4).mp (by decide)

example : ¬transformedCurve.toAffine.Equation 0 0 := by decide

example :
    ¬baseCurve.toAffine.Equation (testChange.u ^ 2 * 0 + testChange.r)
        (testChange.u ^ 3 * 0 + testChange.u ^ 2 * testChange.s * 0 + testChange.t) := by
  rw [← variableChange_equation_iff testChange baseCurve 0 0]
  decide

private lemma hP1 : transformedCurve.toAffine.Nonsingular 0 4 := by decide
private lemma hP2 : transformedCurve.toAffine.Nonsingular 1 6 := by decide
private lemma hP3 : transformedCurve.toAffine.Nonsingular 5 6 := by decide
private lemma hP4 : transformedCurve.toAffine.Nonsingular 1 3 := by decide

private lemma hQ1 : baseCurve.toAffine.Nonsingular 1 0 := by decide
private lemma hQ2 : baseCurve.toAffine.Nonsingular 3 2 := by decide
private lemma hQ3 : baseCurve.toAffine.Nonsingular 4 4 := by decide
private lemma hQ4 : baseCurve.toAffine.Nonsingular 3 5 := by decide

private lemma map_some_eq {x y x' y' : ZMod 7}
    (hp : transformedCurve.toAffine.Nonsingular x y)
    (hq : baseCurve.toAffine.Nonsingular x' y')
    (hx : (testChange.u : ZMod 7) ^ 2 * x + testChange.r = x')
    (hy : (testChange.u : ZMod 7) ^ 3 * y + testChange.u ^ 2 * testChange.s * x +
      testChange.t = y') :
    variableChangePointEquiv testChange baseCurve (.some x y hp) = .some x' y' hq := by
  rw [variableChangePointEquiv_some, Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

private lemma map_P1 : variableChangePointEquiv testChange baseCurve (.some 0 4 hP1) =
    .some 1 0 hQ1 :=
  map_some_eq hP1 hQ1 (by decide) (by decide)

private lemma map_P2 : variableChangePointEquiv testChange baseCurve (.some 1 6 hP2) =
    .some 3 2 hQ2 :=
  map_some_eq hP2 hQ2 (by decide) (by decide)

private lemma map_P3 : variableChangePointEquiv testChange baseCurve (.some 5 6 hP3) =
    .some 4 4 hQ3 :=
  map_some_eq hP3 hQ3 (by decide) (by decide)

private lemma map_P4 : variableChangePointEquiv testChange baseCurve (.some 1 3 hP4) =
    .some 3 5 hQ4 :=
  map_some_eq hP4 hQ4 (by decide) (by decide)

example : variableChangePointEquiv testChange baseCurve 0 = 0 :=
  map_zero _

example :
    (variableChangePointEquiv testChange baseCurve).symm (.some 4 4 hQ3) = .some 5 6 hP3 :=
  (variableChangePointEquiv testChange baseCurve).symm_apply_eq.mpr map_P3.symm

-- Opposite-Y addition (`P₁ + P₁ = 0`).
example :
    variableChangePointEquiv testChange baseCurve
        ((.some 0 4 hP1 : transformedCurve.toAffine.Point) + .some 0 4 hP1) = 0 := by
  rw [map_add, map_P1, Affine.Point.add_of_Y_eq rfl (by decide)]

private lemma baseCurve_add_12 :
    (.some 1 0 hQ1 : baseCurve.toAffine.Point) + .some 3 2 hQ2 = .some 4 4 hQ3 := by
  rw [Affine.Point.add_some (by decide)]
  have hs : baseCurve.toAffine.slope 1 3 0 2 = 1 := by
    rw [Affine.slope_of_X_ne (by decide), div_eq_iff (by decide)]
    decide
  simp only [Affine.Point.some.injEq, Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, hs]
  constructor <;> decide

private lemma baseCurve_double_2 :
    (.some 3 2 hQ2 : baseCurve.toAffine.Point) + .some 3 2 hQ2 = .some 3 5 hQ4 := by
  rw [Affine.Point.add_some (by decide)]
  have hs : baseCurve.toAffine.slope 3 3 2 2 = 4 := by
    rw [Affine.slope_of_Y_ne_eq_evalEval rfl (by decide),
      Affine.evalEval_polynomialX, Affine.evalEval_polynomialY, div_eq_iff (by decide)]
    decide
  simp only [Affine.Point.some.injEq, Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, hs]
  constructor <;> decide

-- Tangent doubling (`P₂ + P₂ = P₄` transferred across `variableChangePointEquiv`).
example :
    variableChangePointEquiv testChange baseCurve
        ((.some 1 6 hP2 : transformedCurve.toAffine.Point) + .some 1 6 hP2) =
      variableChangePointEquiv testChange baseCurve (.some 1 3 hP4) := by
  rw [map_add, map_P2, map_P4, baseCurve_double_2]

-- Distinct-X addition (`P₁ + P₂ = P₃` via `Injective` of `variableChangePointEquiv`).
example :
    (.some 0 4 hP1 : transformedCurve.toAffine.Point) + .some 1 6 hP2 = .some 5 6 hP3 := by
  apply (variableChangePointEquiv testChange baseCurve).injective
  rw [map_add, map_P1, map_P2, map_P3, baseCurve_add_12]

end ZMod7

section NodalZMod5

private local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev nodalCurve : WeierstrassCurve (ZMod 5) := ⟨0, 1, 0, 0, 0⟩

private abbrev nodalChange : VariableChange (ZMod 5) :=
  ⟨⟨2, 3, by decide, by decide⟩, 3, 1, 4⟩

-- Singular node `(3, 3) ↦ (0, 0)`: satisfies `Equation` but fails `Nonsingular` on both curves.
example :
    nodalCurve.toAffine.Equation (nodalChange.u ^ 2 * 3 + nodalChange.r)
      (nodalChange.u ^ 3 * 3 + nodalChange.u ^ 2 * nodalChange.s * 3 + nodalChange.t) :=
  (variableChange_equation_iff nodalChange nodalCurve 3 3).mp (by decide)

example :
    ¬nodalCurve.toAffine.Nonsingular (nodalChange.u ^ 2 * 3 + nodalChange.r)
        (nodalChange.u ^ 3 * 3 + nodalChange.u ^ 2 * nodalChange.s * 3 + nodalChange.t) := by
  rw [← variableChange_nonsingular_iff]
  decide

-- Nonsingular point `(0, 4) ↦ (3, 1)` on the same nodal cubic.
example :
    nodalCurve.toAffine.Nonsingular (nodalChange.u ^ 2 * 0 + nodalChange.r)
      (nodalChange.u ^ 3 * 4 + nodalChange.u ^ 2 * nodalChange.s * 0 + nodalChange.t) :=
  (variableChange_nonsingular_iff nodalChange nodalCurve 0 4).mp (by decide)

end NodalZMod5

end CslibFrontierTests.VariableChange
