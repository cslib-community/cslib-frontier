/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.BoundedPolynomial
public import CslibFrontier.Foundations.Quantum.Algebra.CompletedMeasurement

/-!
# Evaluating polynomial measurements

Postprocess each successful polynomial outcome by evaluation at a point. The
failure effect and total successful effect are preserved. Each successful
value pools the effects of precisely the polynomials taking that value.

## Main definitions

* `Cslib.PCP.LowIndividualDegree.evaluatePolynomialMeasurement`: point
  evaluation of a polynomial measurement with failure.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset MvPolynomial

variable {F A : Type*} {m d : ℕ} [Field F] [Fintype F] [DecidableEq F]

section OrderedRing

variable [Ring A] [PartialOrder A] [IsOrderedAddMonoid A]

/-- Evaluate the polynomial outcomes of a measurement at a point, preserving failure. -/
@[expose] noncomputable def evaluatePolynomialMeasurement
    (M : Measurement (Option (BoundedPolynomial F m d)) A) (u : Fin m → F) :
    Measurement (Option F) A :=
  M.map (Option.map fun q => eval u q.val)

@[simp] theorem evaluatePolynomialMeasurement_effect_none
    (M : Measurement (Option (BoundedPolynomial F m d)) A) (u : Fin m → F) :
    (evaluatePolynomialMeasurement M u).effect none = M.effect none := by
  classical
  rw [evaluatePolynomialMeasurement, Measurement.map_effect, sum_filter, Fintype.sum_option]
  simp

/-- The effect of a successful value sums precisely the polynomials evaluating to it. -/
theorem evaluatePolynomialMeasurement_effect_some
    (P : Measurement (Option (BoundedPolynomial F m d)) A) (u : Fin m → F) (b : F) :
    (evaluatePolynomialMeasurement P u).effect (some b) =
      ∑ g with eval u g.val = b, P.effect (some g) :=
  P.map_option_effect_some (fun g => eval u g.val) b

end OrderedRing

variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Evaluating the polynomial outcome does not change the total successful effect. -/
theorem evaluatePolynomialMeasurement_successfulEffect
    (P : Measurement (Option (BoundedPolynomial F m d)) A) (u : Fin m → F) :
    (evaluatePolynomialMeasurement P u).successfulEffect = P.successfulEffect := by
  have hh := congrArg (fun x : A => 1 - x) (evaluatePolynomialMeasurement_effect_none P u)
  simpa only [Measurement.effect_none_eq_one_sub_successfulEffect, sub_sub_cancel] using hh

end Cslib.PCP.LowIndividualDegree
