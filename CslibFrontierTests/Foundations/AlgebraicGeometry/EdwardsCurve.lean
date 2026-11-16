/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.Edwards
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Parity

/-!
# Edwards curves and their unified addition law: checked instances

Checks for `CslibFrontier/Foundations/AlgebraicGeometry/EllipticCurve/Edwards.lean`:

* Positive checks on `x² + y² = 1 + 3 x² y²` and `x² + y² = 1 + 5 x² y²` over `ZMod 7`,
  including nontrivial denominators `(3, 2) + (3, 2) = (2, 3)` and `zero_add`, `add_zero`,
  `add_comm`, `neg_add_cancel`, `add_equation`, and `denom_ne_zero`.
* Characteristic-two compatibility: `denom_ne_zero`, `add`, and its laws apply without assuming
  `(2 : F) ≠ 0`.
* Counterexample `(a)`: when `d` is a square (`d = 4 = 2²` in `ZMod 11`), addition denominators can
  vanish on curve points `(2, 3)` and `(8, 2)`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Foundations.AlgebraicGeometry.EdwardsCurve

section TestZMod7

private local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def testE7 : EdwardsCurve (ZMod 7) where
  d := 3
  d_ne_zero := by decide
  d_ne_one := by decide

example (P Q : testE7.Point) :
    1 + testE7.d * P.x * Q.x * P.y * Q.y ≠ 0 ∧
      1 - testE7.d * P.x * Q.x * P.y * Q.y ≠ 0 :=
  testE7.denom_ne_zero (by decide) P Q

example (P : testE7.Point) : testE7.add (by decide) testE7.zero P = P :=
  testE7.zero_add (by decide) P

example (P : testE7.Point) : testE7.add (by decide) P testE7.zero = P :=
  testE7.add_zero (by decide) P

example (P Q : testE7.Point) : testE7.add (by decide) P Q = testE7.add (by decide) Q P :=
  testE7.add_comm (by decide) P Q

example (P : testE7.Point) : testE7.add (by decide) (testE7.neg P) P = testE7.zero :=
  testE7.neg_add_cancel (by decide) P

example :
    testE7.add (by decide) testE7.order4Point testE7.order4Point = ⟨0, -1, by decide⟩ := by
  ext <;> simp

example : testE7.neg testE7.order4Point = ⟨-1, 0, by decide⟩ := by
  ext <;> simp

private def testE7' : EdwardsCurve (ZMod 7) where
  d := 5
  d_ne_zero := by decide
  d_ne_one := by decide

private def testP7' : testE7'.Point := ⟨3, 2, by decide⟩

example : testE7'.add (by decide) testP7' testP7' = ⟨2, 3, by decide⟩ := by
  ext
  · rw [EdwardsCurve.add_x]
    simp only [testP7', testE7']
    rw [div_eq_iff (by decide)]
    decide
  · rw [EdwardsCurve.add_y]
    simp only [testP7', testE7']
    rw [div_eq_iff (by decide)]
    decide

example :
    testE7'.Equation ((3 * 2 + 3 * 2) / (1 + testE7'.d * 3 * 3 * 2 * 2))
      ((2 * 2 - 3 * 3) / (1 - testE7'.d * 3 * 3 * 2 * 2)) :=
  testE7'.add_equation (by decide) (by decide) (by decide) (by decide)

end TestZMod7

section CharTwo

-- `(2 : F) ≠ 0` is not required for `denom_ne_zero`, `add`, or its algebraic laws.
example {F : Type*} [Field F] (_ : (2 : F) = 0) (E : EdwardsCurve F) (hd : ¬IsSquare E.d)
    (P Q : E.Point) :
    (1 + E.d * P.x * Q.x * P.y * Q.y ≠ 0 ∧ 1 - E.d * P.x * Q.x * P.y * Q.y ≠ 0) ∧
      E.add hd P Q = E.add hd Q P :=
  ⟨E.denom_ne_zero hd P Q, E.add_comm hd P Q⟩

end CharTwo

section CounterexampleA

private local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

-- Counterexample (a): square `d = 4` in `ZMod 11` gives zero addition denominators on curve points.
private def badE11 : EdwardsCurve (ZMod 11) where
  d := 4
  d_ne_zero := by decide
  d_ne_one := by decide

private def badP11 : badE11.Point := ⟨2, 3, by decide⟩
private def badQ11 : badE11.Point := ⟨8, 2, by decide⟩

example : IsSquare badE11.d ∧
    1 - badE11.d * badP11.x * badP11.x * badP11.y * badP11.y = 0 ∧
    1 + badE11.d * badP11.x * badQ11.x * badP11.y * badQ11.y = 0 :=
  ⟨⟨2, by decide⟩, by decide, by decide⟩

end CounterexampleA

end CslibFrontierTests.Foundations.AlgebraicGeometry.EdwardsCurve
