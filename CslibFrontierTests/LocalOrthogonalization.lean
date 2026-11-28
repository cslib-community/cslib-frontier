/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.LocalOrthogonalization

/-! # Local orthogonalization

Checked clients: pulling a joint state back to a party, simultaneous local orthogonalization with
commuting results, and the local character corollary. A zero-defect client: a projective local
measurement satisfies the hypothesis with defect `0` in every joint state, so it has a projective
partner at zero distance in the joint state's seminorm.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LocalOrthogonalization

open Matrix Cslib Cslib.Quantum Finset
open scoped Kronecker MatrixOrder ComplexOrder BigOperators Matrix.Norms.L2Operator

variable {ι κ α β : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype α]
  [Fintype β]

/-- The pulled-back state evaluates the first party's observable as `M ⊗ 1`. -/
example (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ)) (M : Matrix ι ι ℂ) :
    φ.comap kroneckerOne (OrderHomClass.mono _) M = φ (M ⊗ₖ 1) :=
  rfl

/-- **Simultaneous local orthogonalization**, with commuting results. -/
example (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ)) (M : Measurement α (Matrix ι ι ℂ))
    (N : Measurement β (Matrix κ κ ℂ)) {ε ε' : ℝ}
    (hε : 1 - ε ≤ ∑ a, (φ ((M.effect a * M.effect a) ⊗ₖ 1)).re)
    (hε' : 1 - ε' ≤ ∑ b, (φ (1 ⊗ₖ (N.effect b * N.effect b))).re) :
    ∃ (P : Measurement α (Matrix ι ι ℂ)) (R : Measurement β (Matrix κ κ ℂ)),
      P.IsProjective ∧ R.IsProjective ∧
      ∑ a, φ.norm ((M.effect a - P.effect a) ⊗ₖ 1) ^ 2 ≤ 9 * ε ∧
      ∑ b, φ.norm (1 ⊗ₖ (N.effect b - R.effect b)) ^ 2 ≤ 9 * ε' ∧
      ∀ a b, Commute (P.effect a ⊗ₖ (1 : Matrix κ κ ℂ)) ((1 : Matrix ι ι ℂ) ⊗ₖ R.effect b) :=
  Measurement.exists_isProjective_local φ M N hε hε'

/-- **Local character observables.** -/
example {n : Type} [Fintype n] [DecidableEq n] (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ))
    (M : Measurement (n → Bool) (Matrix ι ι ℂ)) {ε : ℝ}
    (hε : 1 - ε ≤ ∑ x, (φ ((M.effect x * M.effect x) ⊗ₖ 1)).re) :
    ∃ P : Measurement (n → Bool) (Matrix ι ι ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix ι ι ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm ((M.charObs a - P.charObs a) ⊗ₖ 1) ^ 2 ≤ 9 * ε :=
  Measurement.exists_isProjective_charObs_kroneckerOne φ M hε

/-- **Zero defect.** A projective measurement of the first party has defect `0` in every joint
state, so local orthogonalization gives a projective measurement at zero distance in the joint
state's seminorm. -/
example (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ)) (M : Measurement α (Matrix ι ι ℂ))
    (hM : M.IsProjective) :
    ∃ P : Measurement α (Matrix ι ι ℂ), P.IsProjective ∧
      ∑ a, φ.norm (kroneckerOne (κ := κ) (M.effect a - P.effect a)) ^ 2 ≤ 0 := by
  have h1 : 1 - 0 ≤ ∑ a, (φ (kroneckerOne (κ := κ) (M.effect a * M.effect a))).re := by
    simp_rw [hM _]
    rw [← Complex.re_sum, ← map_sum, ← map_sum, M.sum_effect, map_one, φ.map_one, sub_zero,
      Complex.one_re]
  simpa using Measurement.exists_isProjective_sum_norm_map_sub_sq_le φ kroneckerOne M h1

end CslibFrontierTests.LocalOrthogonalization
