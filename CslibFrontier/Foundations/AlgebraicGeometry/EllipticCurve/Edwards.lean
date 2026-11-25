/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/AlgebraicGeometry/EllipticCurve/Edwards.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Even

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Edwards curves and their unified addition law

An Edwards curve over a commutative ring `R` is given by the affine equation
`x² + y² = 1 + d x² y²` with `d ≠ 0` and `d ≠ 1` ([BonehShoup2023], Section 15.2.1, p. 619).
Unlike Weierstrass form, the unified Edwards addition formula
`(x₁, y₁) + (x₂, y₂) =`
`((x₁ y₂ + x₂ y₁) / (1 + d x₁ x₂ y₁ y₂), (y₁ y₂ - x₁ x₂) / (1 - d x₁ x₂ y₁ y₂))`
requires no case split for doubling or adding the identity `(0, 1)`, and the inverse of `(x, y)`
is `(-x, y)`.

Over any field `F`, when `d` is a non-square (`¬ IsSquare E.d`), the addition denominators never
vanish (`EdwardsCurve.denom_ne_zero`), making `EdwardsCurve.add` total on `E.Point` with identity
`(0, 1)`, negation `(-x, y)`, commutativity, and inverse cancellation. Associativity and the
equivalence with Montgomery and Weierstrass models are left to follow-up modules.

## Main definitions

* `EdwardsCurve`: an Edwards curve `x² + y² = 1 + d x² y²` with `d ≠ 0` and `d ≠ 1`.
* `EdwardsCurve.Equation`: the curve equation `x ^ 2 + y ^ 2 = 1 + E.d * x ^ 2 * y ^ 2`.
* `EdwardsCurve.Point`: affine points `(x, y)` satisfying `E.Equation x y`.
* `EdwardsCurve.zero`: the identity point `(0, 1)`.
* `EdwardsCurve.neg`: the inverse map `(x, y) ↦ (-x, y)`.
* `EdwardsCurve.order4Point`: the point `(1, 0)` (which has order four when `(2 : F) ≠ 0`).
* `EdwardsCurve.add`: the unified Edwards addition law on `E.Point` when `¬ IsSquare E.d`.

## Main results

* `EdwardsCurve.equation_add`: closure of `E.Equation` under the unified addition formula.
* `EdwardsCurve.mul_xy_eq_zero_of_two_eq_zero`: in characteristic two, `¬ IsSquare E.d` forces
  `R.x * R.y = 0` for every point `R`.
* `EdwardsCurve.denom_ne_zero`: for `¬ IsSquare E.d`, `1 ± E.d * P.x * Q.x * P.y * Q.y ≠ 0`
  over any field.
* `EdwardsCurve.zero_add`, `EdwardsCurve.add_zero`, `EdwardsCurve.add_comm`,
  `EdwardsCurve.neg_add_cancel`: left/right identity, commutativity, and inverse cancellation for
  `E.add`.

## Implementation notes and deviations from the source

* [BonehShoup2023], Section 15.2.1 (p. 619) states only `d ≠ 0, 1` over `𝔽_p` when introducing
  the unified addition formula; `d ≠ 0, 1` alone does not keep the denominators
  `1 ± d x₁ x₂ y₁ y₂` nonzero on `E.Point` (see `d = 4` over `ZMod 11` in the test suite), and
  this module adds the hypothesis `¬ IsSquare E.d`, which is sufficient but not necessary.
* Over a field, `denom_ne_zero`, `add`, `zero_add`, `add_zero`, `add_comm`, and `neg_add_cancel`
  hold without assuming `(2 : F) ≠ 0`, because in characteristic two a non-square `d` forces
  `R.x * R.y = 0` for every point `R`, so the curve has only the points `(0, 1)` and `(1, 0)`; no
  finite field of characteristic two satisfies the hypothesis.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 15.2.1
  (p. 619).
-/

public section

/-- An Edwards curve `x² + y² = 1 + d x² y²` over a commutative ring `R`, with `d ≠ 0` and
`d ≠ 1` ([BonehShoup2023], Section 15.2.1, p. 619). -/
structure EdwardsCurve (R : Type*) [CommRing R] where
  /-- The curve parameter `d` in `x² + y² = 1 + d x² y²`. -/
  d : R
  /-- Non-degeneracy condition `d ≠ 0`. -/
  d_ne_zero : d ≠ 0
  /-- Non-degeneracy condition `d ≠ 1`. -/
  d_ne_one : d ≠ 1

namespace EdwardsCurve

section Basic

variable {R : Type*} [CommRing R] (E : EdwardsCurve R)

/-- The affine equation `x² + y² = 1 + d x² y²` defining `E`. -/
@[expose] def Equation (x y : R) : Prop :=
  x ^ 2 + y ^ 2 = 1 + E.d * x ^ 2 * y ^ 2

/-- Decidability of `E.Equation x y` when equality in `R` is decidable. -/
instance [DecidableEq R] (x y : R) : Decidable (E.Equation x y) :=
  inferInstanceAs (Decidable (_ = _))

/-- An affine point on the Edwards curve `E`. -/
@[ext]
structure Point where
  /-- The `x`-coordinate of the point. -/
  x : R
  /-- The `y`-coordinate of the point. -/
  y : R
  /-- Witness that `(x, y)` satisfies `E.Equation`. -/
  eq : E.Equation x y
  deriving DecidableEq

/-- The identity point `(0, 1)` on `E`. -/
def zero : E.Point := ⟨0, 1, by simp [Equation]⟩

/-- The `x`-coordinate of `E.zero` is `0`. -/
@[simp] theorem zero_x : E.zero.x = 0 := by rfl

/-- The `y`-coordinate of `E.zero` is `1`. -/
@[simp] theorem zero_y : E.zero.y = 1 := by rfl

/-- The Edwards negation `(x, y) ↦ (-x, y)`. -/
def neg (P : E.Point) : E.Point := ⟨-P.x, P.y, by simpa [Equation] using P.eq⟩

/-- The `x`-coordinate of `E.neg P` is `-P.x`. -/
@[simp] theorem neg_x (P : E.Point) : (E.neg P).x = -P.x := by rfl

/-- The `y`-coordinate of `E.neg P` is `P.y`. -/
@[simp] theorem neg_y (P : E.Point) : (E.neg P).y = P.y := by rfl

/-- Negation is involutive on `E.Point`. -/
@[simp] protected theorem neg_neg (P : E.Point) : E.neg (E.neg P) = P := by
  ext <;> simp

/-- The point `(1, 0)` on `E` (which has order four when `(2 : F) ≠ 0`). -/
def order4Point : E.Point := ⟨1, 0, by simp [Equation]⟩

/-- The `x`-coordinate of `E.order4Point` is `1`. -/
@[simp] theorem order4Point_x : E.order4Point.x = 1 := by rfl

/-- The `y`-coordinate of `E.order4Point` is `0`. -/
@[simp] theorem order4Point_y : E.order4Point.y = 0 := by rfl

/-- `1 - E.d ≠ 0` follows from `E.d ≠ 1`. -/
theorem one_sub_d_ne_zero : 1 - E.d ≠ 0 :=
  sub_ne_zero.mpr E.d_ne_one.symm

end Basic

section Field

variable {F : Type*} [Field F] (E : EdwardsCurve F)

private lemma equation_add_identity {R : Type*} [CommRing R] (d x₁ y₁ x₂ y₂ : R)
    (h₁ : x₁ ^ 2 + y₁ ^ 2 = 1 + d * x₁ ^ 2 * y₁ ^ 2)
    (h₂ : x₂ ^ 2 + y₂ ^ 2 = 1 + d * x₂ ^ 2 * y₂ ^ 2) :
    (1 - d * x₁ * x₂ * y₁ * y₂) ^ 2 * (x₁ * y₂ + x₂ * y₁) ^ 2 +
        (1 + d * x₁ * x₂ * y₁ * y₂) ^ 2 * (y₁ * y₂ - x₁ * x₂) ^ 2 =
      (1 + d * x₁ * x₂ * y₁ * y₂) ^ 2 * (1 - d * x₁ * x₂ * y₁ * y₂) ^ 2 +
        d * (x₁ * y₂ + x₂ * y₁) ^ 2 * (y₁ * y₂ - x₁ * x₂) ^ 2 := by
  linear_combination
    ((1 + (d * x₁ * x₂ * y₁ * y₂) ^ 2) * (x₂ ^ 2 + y₂ ^ 2) -
      d * x₂ ^ 2 * y₂ ^ 2 * (x₁ ^ 2 + y₁ ^ 2 + 1 + d * x₁ ^ 2 * y₁ ^ 2)) * h₁ +
    ((1 + (d * x₁ * x₂ * y₁ * y₂) ^ 2) * (1 + d * x₁ ^ 2 * y₁ ^ 2) -
      d * x₁ ^ 2 * y₁ ^ 2 * (x₂ ^ 2 + y₂ ^ 2 + 1 + d * x₂ ^ 2 * y₂ ^ 2)) * h₂

/-- The unified Edwards addition formula preserves `E.Equation` whenever both denominators are
nonzero. -/
theorem equation_add {x₁ y₁ x₂ y₂ : F} (h₁ : E.Equation x₁ y₁) (h₂ : E.Equation x₂ y₂)
    (hplus : 1 + E.d * x₁ * x₂ * y₁ * y₂ ≠ 0)
    (hminus : 1 - E.d * x₁ * x₂ * y₁ * y₂ ≠ 0) :
    E.Equation ((x₁ * y₂ + x₂ * y₁) / (1 + E.d * x₁ * x₂ * y₁ * y₂))
      ((y₁ * y₂ - x₁ * x₂) / (1 - E.d * x₁ * x₂ * y₁ * y₂)) := by
  simp only [Equation] at h₁ h₂ ⊢
  have hgoal := equation_add_identity E.d x₁ y₁ x₂ y₂ h₁ h₂
  have hplus' : 1 + x₁ * y₂ * x₂ * y₁ * E.d ≠ 0 := by convert hplus using 1; ring
  have hminus' : 1 - x₁ * y₂ * x₂ * y₁ * E.d ≠ 0 := by convert hminus using 1; ring
  field_simp [hplus', hminus']
  linear_combination hgoal

/-- In characteristic two, a non-square parameter forces `R.x * R.y = 0` for every point `R`. -/
lemma mul_xy_eq_zero_of_two_eq_zero (h2 : (2 : F) = 0) (hd : ¬IsSquare E.d)
    (R : E.Point) : R.x * R.y = 0 := by
  by_contra hxy
  have heq : R.x ^ 2 + R.y ^ 2 = 1 + E.d * R.x ^ 2 * R.y ^ 2 := R.eq
  refine hd ⟨(R.x + R.y + 1) / (R.x * R.y), ?_⟩
  rw [div_mul_div_comm, ← sq, ← sq, eq_div_iff (pow_ne_zero 2 hxy)]
  linear_combination -heq - (1 + R.x * R.y + R.x + R.y) * h2

private lemma add_denom_ne_zero_of_two_ne_zero (h2 : (2 : F) ≠ 0) (hd : ¬IsSquare E.d)
    (P Q : E.Point) :
    1 + E.d * P.x * Q.x * P.y * Q.y ≠ 0 := by
  set x₁ := P.x
  set y₁ := P.y
  set x₂ := Q.x
  set y₂ := Q.y
  set ε := E.d * x₁ * x₂ * y₁ * y₂
  have hL : (1 - ε) ^ 2 * (x₁ * y₂ + x₂ * y₁) ^ 2 + (1 + ε) ^ 2 * (y₁ * y₂ - x₁ * x₂) ^ 2 =
      (1 + ε) ^ 2 * (1 - ε) ^ 2 + E.d * (x₁ * y₂ + x₂ * y₁) ^ 2 * (y₁ * y₂ - x₁ * x₂) ^ 2 :=
    equation_add_identity E.d x₁ y₁ x₂ y₂ P.eq Q.eq
  intro hplus
  have hε : ε = -1 := by linear_combination hplus
  have h4 : 4 * (x₁ * y₂ + x₂ * y₁) ^ 2 =
      E.d * (x₁ * y₂ + x₂ * y₁) ^ 2 * (y₁ * y₂ - x₁ * x₂) ^ 2 := by
    rw [hε] at hL
    linear_combination hL
  by_cases hsum : x₁ * y₂ + x₂ * y₁ = 0
  · apply hd
    refine ⟨(x₁ * y₂)⁻¹, ?_⟩
    have hxy : x₂ * y₁ = -(x₁ * y₂) := by linear_combination hsum
    have hsq : E.d * (x₁ * y₂) ^ 2 = 1 := by
      linear_combination -hε + E.d * (x₁ * y₂) * hxy
    have hnz : x₁ * y₂ ≠ 0 := fun hz ↦ by rw [hz] at hsq; simp at hsq
    exact (eq_mul_inv_iff_mul_eq₀ hnz).mpr (eq_inv_of_mul_eq_one_left (by linear_combination hsq))
  · have h4' : E.d * (y₁ * y₂ - x₁ * x₂) ^ 2 = 4 := by
      apply mul_right_cancel₀ (pow_ne_zero 2 hsum)
      linear_combination -h4
    apply hd
    refine ⟨2 / (y₁ * y₂ - x₁ * x₂), ?_⟩
    have h4ne : (4 : F) ≠ 0 := by
      rw [show (4 : F) = 2 * 2 by ring]
      exact mul_ne_zero h2 h2
    have hnz : (y₁ * y₂ - x₁ * x₂) ^ 2 ≠ 0 := fun hz ↦
      h4ne (by rw [hz, mul_zero] at h4'; exact h4'.symm)
    rw [div_mul_div_comm, ← sq, ← sq, show (2 : F) ^ 2 = 4 by norm_num, eq_div_iff hnz]
    exact h4'

private lemma add_denom_ne_zero (hd : ¬IsSquare E.d) (P Q : E.Point) :
    1 + E.d * P.x * Q.x * P.y * Q.y ≠ 0 := by
  by_cases h2 : (2 : F) = 0
  · have h0 : E.d * P.x * Q.x * P.y * Q.y = 0 := by
      have h := E.mul_xy_eq_zero_of_two_eq_zero h2 hd P
      linear_combination E.d * Q.x * Q.y * h
    rw [h0]
    simp
  · exact E.add_denom_ne_zero_of_two_ne_zero h2 hd P Q

/-- For non-square `E.d`, both denominators `1 ± E.d * P.x * Q.x * P.y * Q.y` in the unified
Edwards addition formula are nonzero over any field `F`. -/
theorem denom_ne_zero (hd : ¬IsSquare E.d) (P Q : E.Point) :
    1 + E.d * P.x * Q.x * P.y * Q.y ≠ 0 ∧ 1 - E.d * P.x * Q.x * P.y * Q.y ≠ 0 := by
  refine ⟨E.add_denom_ne_zero hd P Q, ?_⟩
  rw [show 1 - E.d * P.x * Q.x * P.y * Q.y =
      1 + E.d * P.x * (E.neg Q).x * P.y * (E.neg Q).y by simp; ring]
  exact E.add_denom_ne_zero hd P (E.neg Q)

/-- The unified Edwards addition law `P ⊞ Q` on `E.Point` when `¬ IsSquare E.d`. -/
def add (hd : ¬IsSquare E.d) (P Q : E.Point) : E.Point where
  x := (P.x * Q.y + Q.x * P.y) / (1 + E.d * P.x * Q.x * P.y * Q.y)
  y := (P.y * Q.y - P.x * Q.x) / (1 - E.d * P.x * Q.x * P.y * Q.y)
  eq := E.equation_add P.eq Q.eq (E.denom_ne_zero hd P Q).1 (E.denom_ne_zero hd P Q).2

/-- The `x`-coordinate of `E.add hd P Q`. -/
@[simp] theorem add_x (hd : ¬IsSquare E.d) (P Q : E.Point) :
    (E.add hd P Q).x = (P.x * Q.y + Q.x * P.y) / (1 + E.d * P.x * Q.x * P.y * Q.y) := by rfl

/-- The `y`-coordinate of `E.add hd P Q`. -/
@[simp] theorem add_y (hd : ¬IsSquare E.d) (P Q : E.Point) :
    (E.add hd P Q).y = (P.y * Q.y - P.x * Q.x) / (1 - E.d * P.x * Q.x * P.y * Q.y) := by rfl

/-- Left identity for `E.add`. -/
protected theorem zero_add (hd : ¬IsSquare E.d) (P : E.Point) :
    E.add hd E.zero P = P := by
  ext <;> simp

/-- Right identity for `E.add`. -/
protected theorem add_zero (hd : ¬IsSquare E.d) (P : E.Point) :
    E.add hd P E.zero = P := by
  ext <;> simp

/-- Commutativity of `E.add`. -/
protected theorem add_comm (hd : ¬IsSquare E.d) (P Q : E.Point) :
    E.add hd P Q = E.add hd Q P := by
  ext <;> simp <;> ring

/-- Left inverse cancellation for `E.add`. -/
protected theorem neg_add_cancel (hd : ¬IsSquare E.d) (P : E.Point) :
    E.add hd (E.neg P) P = E.zero := by
  have hden := (E.denom_ne_zero hd (E.neg P) P).2
  have heq : P.x ^ 2 + P.y ^ 2 = 1 + E.d * P.x ^ 2 * P.y ^ 2 := P.eq
  simp only [neg_x, neg_y] at hden
  ext <;> simp only [add_x, add_y, neg_x, neg_y, zero_x, zero_y]
  · ring
  · rw [div_eq_one_iff_eq hden]
    linear_combination heq

end Field

end EdwardsCurve
