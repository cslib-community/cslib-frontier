/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingLinearity
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Order

/-! # The two-player linearity test

Checked clients: the acceptance probability as an average of correlations, and linearity of the
point player's observables from acceptance. Two concrete instances:

* completeness: the honest answers of a linear function pass every check, for two-bit queries;
* the sampled check (regression for coinciding queries): the constant answers `γ = α = β = true`
  pass the two consistency checks and fail the linearity check, so they are accepted with
  probability exactly `2/3`, also when the queries coincide. A verifier that ran every applicable
  check would reject them whenever `c = a = b`;
* the symmetric verifier sorts and decodes both questions and handles either role assignment.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LinearityGame

open Cslib Cslib.PCP Cslib.Quantum Finset Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

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
    (hB : ∀ q, (S.bob q).IsProjective) {ε : ℝ}
    (hε : 1 - ε ≤ S.linearityTestProb) :
    1 - 6 * ε - √(12 * ε) - √(12 * ε) ≤
      𝔼 a, 𝔼 b, (S.state ((S.alice a).observable * (S.alice b).observable *
        (S.alice (a + b)).observable)).re :=
  CommutingStrategy.one_sub_le_expect_re_apply_mul_mul_of_linearityTest S hB hε

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

/-- The linearity test as a seeded game wins with the acceptance probability of the test. -/
example {n 𝒜 : Type} [Fintype n] [DecidableEq n] [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜]
    (S : CommutingStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) 𝒜) :
    (linearityGame n).commutingWinProb S = S.linearityTestProb :=
  commutingWinProb_linearityGame S

/-- At `a = b = 0`, all three seeds produce the same questions. The first two accept the
all-true answers and the third rejects them. -/
example :
    let G := linearityGame (Fin 1)
    G.query (0, 0, 0) = G.query (1, 0, 0) ∧
      G.query (0, 0, 0) = G.query (2, 0, 0) ∧
      G.accepts (0, 0, 0) true (true, true) ∧
      G.accepts (1, 0, 0) true (true, true) ∧
      ¬ G.accepts (2, 0, 0) true (true, true) := by
  decide

/-- The constant all-true strategy wins the seeded linearity game with probability `2/3`. -/
example (φ : AlgState (Matrix (Fin 1) (Fin 1) ℂ)) :
    (linearityGame (Fin 1)).commutingWinProb (constTrue φ) = 2 / 3 := by
  rw [commutingWinProb_linearityGame]
  simp only [CommutingStrategy.linearityTestProb, CommutingStrategy.prob, constTrue,
    Measurement.const, Fintype.sum_bool, Fintype.sum_prod_type, linearityCheck]
  simp [Fintype.expect_eq_sum_div_card, φ.map_one]
  norm_cast

/-- Both questions arrive in sorted order, with their order across players determined by the
sampled roles. The checked coordinate is the second in both questions. -/
example :
    let G := symmetricLinearityGame 2
    let high : Fin 2 → Bool := fun i => decide (i = 0)
    let low : Fin 2 → Bool := fun i => decide (i = 1)
    let dummy : Fin 2 → Bool := fun _ => false
    let seed : SymmetricLinearitySeed 2 :=
      { swapRoles := false, check := 0, first := high, second := low, dummy := dummy }
    let swapped := { seed with swapRoles := true }
    G.query seed = ((low, high), (dummy, high)) ∧
      G.query swapped = ((dummy, high), (low, high)) ∧
      G.accepts seed (false, true) (true, true) ∧
      G.accepts swapped (true, true) (false, true) ∧
      ¬ G.accepts seed (false, true) (true, false) := by
  decide

/-- Even with identical visible queries, the sampled xor check can reject answers that pass
the equality check. -/
example :
    let G := symmetricLinearityGame 1
    let zero : Fin 1 → Bool := fun _ => false
    G.query ⟨false, 0, zero, zero, zero⟩ = G.query ⟨false, 2, zero, zero, zero⟩ ∧
      G.accepts ⟨false, 0, zero, zero, zero⟩ (true, true) (true, true) ∧
      ¬ G.accepts ⟨false, 2, zero, zero, zero⟩ (true, true) (true, true) := by
  decide

private abbrev String₁ := Fin 1 → Bool

private def dummyAnswer (q : String₁ × String₁) : Bool × Bool :=
  let bit := decide (q.1 ≠ q.2)
  (bit, bit)

private noncomputable def dummyDependent (φ : AlgState (Matrix (Fin 1) (Fin 1) ℂ)) :
    CommutingStrategy (String₁ × String₁) (String₁ × String₁)
      (Bool × Bool) (Bool × Bool) (Matrix (Fin 1) (Fin 1) ℂ) where
  state := φ
  alice q := Measurement.const (dummyAnswer q)
  bob q := Measurement.const (dummyAnswer q)
  commute _ _ a b := by
    simp only [Measurement.const]
    split_ifs <;> simp [Commute, SemiconjBy]

/-- The width-one matrix strategy participates in the score identity for both assignments. -/
example (φ : AlgState (Matrix (Fin 1) (Fin 1) ℂ)) :
    let S := dummyDependent φ
    (symmetricLinearityGame 1).commutingWinProb S =
      𝔼 roles : Bool, (cond roles S S.swap).asymmetricLinearity.linearityTestProb :=
  (dummyDependent φ).commutingWinProb_symmetricLinearityGame

/-- Both strategies answer projectively on every visible pair. On point zero, the uniform
dummy leads to both possible decoded point answers, so the averaged measurement is a POVM
with zero observable. -/
example (φ : AlgState (Matrix (Fin 1) (Fin 1) ℂ)) :
    let S := dummyDependent φ
    (∀ q, (S.alice q).IsProjective ∧ (S.bob q).IsProjective) ∧
      ¬ (S.asymmetricLinearity.alice 0).IsProjective := by
  intro S
  refine ⟨fun q => ⟨Measurement.isProjective_const _, Measurement.isProjective_const _⟩, ?_⟩
  have hobs : (S.asymmetricLinearity.alice 0).observable = 0 := by
    rw [CommutingStrategy.observable_asymmetricLinearity]
    simp only [Cslib.BitString.lexSwap_zero_left, Bool.cond_false, id_eq]
    let O (d : String₁) := ((S.alice (0, d)).map Prod.fst).observable
    change (𝔼 d, O d) = 0
    have he := Fintype.expect_equiv (Equiv.funUnique (Fin 1) Bool) O
      (fun b => O (fun _ => b)) (fun d => congrArg O (funext fun i =>
        congrArg d (Subsingleton.elim i default)))
    have hfalse : dummyAnswer (0, fun _ => false) = (false, false) := by decide
    have htrue : dummyAnswer (0, fun _ => true) = (true, true) := by decide
    rw [he, Finset.expect, Fintype.sum_bool]
    simp [O, S, dummyDependent, hfalse, htrue, Measurement.observable, Measurement.map_effect,
      Measurement.const]
  intro h
  have hsquare := Measurement.observable_mul_self h
  rw [hobs, zero_mul] at hsquare
  exact zero_ne_one hsquare

/-- The width-one Pauli bound instantiates in the usual matrix order for either basis and role. -/
example
    (S : CommutingStrategy (PauliBraidingQuestion 1 Bool) (PauliBraidingQuestion 1 Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) (Matrix (Fin 1) (Fin 1) ℂ))
    (hA : ∀ basis q, (S.alice (.basis basis q)).IsProjective)
    (hB : ∀ basis q, (S.bob (.basis basis q)).IsProjective)
    (basis roles : Bool) {ε : ℝ}
    (hwin : 1 - ε ≤ (pauliBraidingBranchGame 1 TwoProverGame.chsh id
      (fun _ => id) 0).commutingWinProb S) :
    let R := pauliBraidingLinearityStrategy basis S
    let T := (cond roles R R.swap).asymmetricLinearity
    1 - 24 * ε - √(48 * ε) - √(48 * ε) ≤
      𝔼 a, 𝔼 b, (T.state ((T.alice a).observable * (T.alice b).observable *
        (T.alice (a + b)).observable)).re :=
  one_sub_le_expect_re_apply_mul_mul_of_pauliBraidingLinearity
    TwoProverGame.chsh id (fun _ => id) S hA hB hwin basis roles

end CslibFrontierTests.LinearityGame
