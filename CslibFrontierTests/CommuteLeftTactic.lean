/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Tactic.CommuteLeft

/-! # `commute_left`

Equations of products up to quantified and unquantified commutations, as in the chains of
rigidity arguments.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.CommuteLeftTactic

variable {A ι : Type} [Monoid A] (X Z X' Z' : ι → A)

/-- One player's operator moves in front of a product of the other's. -/
example (hXZ' : ∀ a b, Commute (X a) (Z' b)) (hZZ' : ∀ b b', Commute (Z b) (Z' b')) (a c d : ι) :
    X a * Z c * Z' d = Z' d * (X a * Z c) := by
  commute_left [hXZ', hZZ']

/-- Two operators of one player move in front of two of the other's. -/
example (hXZ' : ∀ a b, Commute (X a) (Z' b)) (hZZ' : ∀ b b', Commute (Z b) (Z' b'))
    (hZX' : ∀ b a, Commute (Z b) (X' a)) (hXX' : ∀ a b, Commute (X a) (X' b)) (a c d : ι) :
    Z c * X a * Z' d * X' a = Z' d * X' a * (Z c * X a) := by
  commute_left [hXZ', hZZ', hZX', hXX']

/-- An unquantified commutation. -/
example {u v w : A} (huv : Commute u v) (hwv : Commute w v) : u * w * v = v * u * w := by
  commute_left [huv, hwv]

/-- Mixed explicit and implicit binders (regression). -/
example (hXZ' : ∀ (a : ι) {b : ι}, Commute (X a) (Z' b)) (a d : ι) :
    X a * Z' d = Z' d * X a := by
  commute_left [hXZ']

/-- The tactic fails, rather than leaving a goal, when the commutations do not suffice. -/
example (u v w : A) (h : (u * v) * w = w * (u * v)) : (u * v) * w = w * (u * v) := by
  fail_if_success commute_left []
  exact h

end CslibFrontierTests.CommuteLeftTactic
