/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.BoundedPolynomial
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.MvPolynomial.SchwartzZippel

/-!
# Collisions under polynomial evaluation

Schwartz–Zippel bounds the fraction of points where distinct bounded
polynomials agree by the total degree bound divided by the field size.

## Main results

* `Cslib.PCP.LowIndividualDegree.expect_evaluation_collision_le`.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset MvPolynomial
open scoped BigOperators

variable {F : Type*} {m d : ℕ} [Field F] [Fintype F] [DecidableEq F]

/-- The fraction of points where distinct bounded polynomials agree is at
most their total degree bound divided by the field size. -/
theorem expect_evaluation_collision_le (g h : BoundedPolynomial F m d) (hne : g ≠ h) :
    (𝔼 u : Fin m → F, if eval u h.val = eval u g.val then (1 : ℝ) else 0) ≤
      (m : ℝ) * d / Fintype.card F := by
  have hcard := card_filter_eval_eq_mul_card_le (fun h' => hne.symm (Subtype.ext h')) h.prop g.prop
  rw [Fintype.expect_eq_sum_div_card, sum_boole, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  refine (div_le_div_iff₀ (pow_pos (by exact_mod_cast Fintype.card_pos) _)
    (by exact_mod_cast Fintype.card_pos)).mpr ?_
  exact_mod_cast hcard

end Cslib.PCP.LowIndividualDegree
