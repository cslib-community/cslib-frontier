/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.Linearity

/-! # The two-player linearity test

Checked clients: the acceptance probability as an average of correlations, and linearity of the
point player's observables from acceptance. Two concrete instances:

* completeness: the honest answers of a linear function pass every check, for two-bit queries;
* the sampled check (regression for coinciding queries): the constant answers `γ = α = β = true`
  pass the two consistency checks and fail the linearity check, so they are accepted with
  probability exactly `2/3`, also when the queries coincide. A verifier that ran every applicable
  check would reject them whenever `c = a = b`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LinearityGame

open Cslib Cslib.PCP Cslib.Quantum Finset Matrix
open scoped BigOperators MatrixOrder

/-- The acceptance probability as an average of correlations. -/
example {n 𝒜 : Type} [Fintype n] [DecidableEq n] [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [Algebra ℂ 𝒜]
    (S : CommutingStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) 𝒜) :
    S.linearityTestProb = 𝔼 k : Fin 3, 𝔼 a, 𝔼 b,
      (1 + (S.state ((S.alice (linearityQuery k a b)).observable *
        ((S.bob (a, b)).map (linearityCheck k)).observable)).re) / 2 :=
  CommutingStrategy.linearityTestProb_eq S

/-- **Passing the linearity test** makes the point player's observables linear on average. -/
example {n 𝒜 : Type} [Fintype n] [DecidableEq n] [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜]
    (S : CommutingStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) 𝒜)
    (hA : ∀ c, (S.alice c).IsProjective) (hB : ∀ q, (S.bob q).IsProjective) {ε : ℝ}
    (hε : 1 - ε ≤ S.linearityTestProb) :
    1 - 6 * ε - √(12 * ε) - √(12 * ε) ≤
      𝔼 a, 𝔼 b, (S.state ((S.alice a).observable * (S.alice b).observable *
        (S.alice (a + b)).observable)).re :=
  CommutingStrategy.one_sub_le_expect_re_apply_mul_mul_of_linearityTest S hA hB hε

/-- **Completeness for linear functions** (concrete, two bits): the honest answers of the linear
function `c ↦ s·c` pass every check. -/
example : ∀ s a b : Fin 2 → Bool, ∀ k : Fin 3,
    s ⬝ᵥ linearityQuery k a b = linearityCheck k (s ⬝ᵥ a, s ⬝ᵥ b) := by
  decide

/-- The constant strategy answering `true` to every question, in any state of `M₁(ℂ)`. -/
noncomputable def constTrue (φ : AlgState (Matrix (Fin 1) (Fin 1) ℂ)) :
    CommutingStrategy (Fin 1 → Bool) ((Fin 1 → Bool) × (Fin 1 → Bool)) Bool (Bool × Bool)
      (Matrix (Fin 1) (Fin 1) ℂ) where
  state := φ
  alice _ := Measurement.const true
  bob _ := Measurement.const (true, true)
  commute _ _ a b := by
    simp only [Measurement.const]
    split_ifs <;> simp [Commute, SemiconjBy]

/-- **Regression for coinciding queries**: the verifier runs only the sampled check, so the constant
answers are accepted with probability `2/3` on one-bit queries. -/
example (φ : AlgState (Matrix (Fin 1) (Fin 1) ℂ)) : (constTrue φ).linearityTestProb = 2 / 3 := by
  simp only [CommutingStrategy.linearityTestProb, CommutingStrategy.prob, constTrue,
    Measurement.const, Fintype.sum_bool, Fintype.sum_prod_type, linearityCheck]
  simp [Fintype.expect_eq_sum_div_card, φ.map_one]
  norm_cast

end CslibFrontierTests.LinearityGame
