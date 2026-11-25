/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.NetworkProjection

/-! Tests of the network polynomial in the flat case, as a client that sees only the public
statements.

* What the node `0` of two nodes sees, a variable of the network polynomial on the views; circuits
  for that polynomial are circuits for the network polynomial.
* Lemma E.3: the network polynomial on two nodes with one bit is an affine projection of the
  Hamiltonian cycle polynomial, so circuits for that family give circuits for it; and a circuit
  for a permanent gives one with five times as many nodes. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationFlatCase

open Finset MvPolynomial Cslib Cslib.Circuits.Arithmetic
  Cslib.Circuits.Arithmetic.Separation.Flat

/-- The node `0` sees the string `true` on its wire to the node `1`. -/
example : NodeView 2 1 := ⟨0, ![fun _ => false, fun _ => true], rfl⟩

/-- A circuit for the network polynomial on the views is one for the network polynomial. -/
example {s : ℕ} (h : ComputedWithin (networkPolynomialOnViews ℚ 2 1) s) :
    ComputedWithin (networkPolynomial ℚ 2 1) s :=
  rename_networkPolynomialOnViews ℚ ▸ h.rename _

/-- Lemma E.3 with the Hamiltonian cycle polynomial, which is complete for grid sums with blow-up
`40`: `f_{2,1}` is an affine projection of the Hamiltonian cycle polynomial on
`40 · 2³ · 1 · 2² = 1280` vertices. -/
example : IsAffineProjection (networkPolynomial ℚ 2 1) ((hcFamily ℚ).poly 1280) :=
  isAffineProjection_networkPolynomial gridComplete_hcFamily le_rfl le_rfl le_rfl

/-- A circuit for the Hamiltonian cycle polynomial on `1280` vertices gives one for `f_{2,1}`
with five times as many nodes. -/
example {s : ℕ} (hs : ComputedWithin ((hcFamily ℚ).poly 1280) s) :
    ComputedWithin (networkPolynomial ℚ 2 1) (5 * s) :=
  hs.of_isAffineProjection
    (isAffineProjection_networkPolynomial gridComplete_hcFamily le_rfl le_rfl le_rfl)

/-- Lemma E.3: over `ℚ`, a circuit for `PERM_96` gives one for `f_{2,1}`, since
`3 · 2³ · 1 · 2² = 96`. -/
example {s : ℕ} (hs : ComputedWithin ((permFamily ℚ).poly 96) s) :
    ComputedWithin (networkPolynomial ℚ 2 1) (5 * s) :=
  computedWithin_networkPolynomial two_ne_zero le_rfl le_rfl le_rfl hs

end CslibFrontierTests.SeparationFlatCase
