/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Seeded
public import CslibFrontier.Foundations.Quantum.Algebra.LinearityTest
public import CslibFrontier.Foundations.Quantum.Algebra.CStar
public import CslibFrontier.Foundations.Data.BitString.Sign

/-!
# The two-player linearity test

In the **linearity test** the verifier draws `k ∈ {0, 1, 2}` and `a, b ∈ {0,1}ⁿ` uniformly, sends
the pair `(a, b)` to the *pair player* (Bob), and sends the point `c = a`, `b` or `a + b`
(`Cslib.PCP.linearityQuery`), according to `k`, to the *point player* (Alice). Alice answers a bit
`γ`, Bob answers bits `(α, β)`, and the verifier runs the single check selected by `k`:
`γ = α`, `γ = β` or `γ = α ⊕ β` (`Cslib.PCP.linearityCheck`). The verifier's choice `k` is private,
and when the queries coincide (for instance `a = b`) several values of `k` produce the same
questions but different checks. So the test is a seeded game (`Cslib.PCP.linearityGame`, a
`Cslib.PCP.SeededGame`) rather than a `Cslib.PCP.TwoProverGame`, whose acceptance predicate sees
only the questions. Its winning probability is the acceptance probability with the sampled check
(`Cslib.PCP.CommutingStrategy.linearityTestProb`, `Cslib.PCP.commutingWinProb_linearityGame`).

The acceptance probability is an average of correlations
(`Cslib.PCP.CommutingStrategy.linearityTestProb_eq`), by
`Cslib.PCP.CommutingStrategy.sum_ite_prob_eq`. When a strategy with projective pair measurements
is accepted with probability `1 - ε`, Alice's observables `A(c)` are linear on average
(`Cslib.PCP.CommutingStrategy.one_sub_le_expect_re_apply_mul_mul_of_linearityTest`):

`E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - 6ε - 2√(12ε)`.

Each check passes with probability at least `1 - 3ε`. The consistency checks bound the distances
between Alice's observables and the marginals of Bob's, and the linearity check bounds the
correlation of `A(a + b)` with the product of Bob's marginals, which for a projective measurement
is the parity observable. Linearity from consistency
(`Cslib.Quantum.one_sub_le_expect_re_apply_mul_mul`) then gives the bound.

This is the test of [Natarajan and Vidick, §3, Figure 1][NatarajanVidick2017]
(arXiv:1610.03574v1) in an **asymmetric variant**, and the estimate is the commuting-operator,
point-player form of their Theorem 11. The variant differs from the source in three ways:

* one player always gets the point and the other the pair, whereas the source labels the players
  at random and sends Bob a second, uniformly random query so that symmetric strategies apply;
* the pair is sent in sampled order `(a, b)`. Figure 1 sends it in lexicographic order, so
  a strategy for this variant can distinguish the two sampled orders;
* the conclusion concerns the point player's own observables, whereas the source rounds the
  Naimark dilation of the averaged pair marginals.

As in the source, the strategy's measurements are assumed projective here. The
`CslibFrontier.Computability.PCP.TwoProverGame.SymmetricLinearity` module defines the source's
symmetric verifier as `Cslib.PCP.symmetricLinearityGame`. Its seed also assigns the players' roles
and samples the dummy query. Quantum soundness of the symmetric verifier and the remaining steps
toward Pauli rigidity are tracked in #6149.

## Main definitions

* `Cslib.PCP.linearityQuery`, `Cslib.PCP.linearityCheck`: the point query and the check of each
  test.
* `Cslib.PCP.CommutingStrategy.linearityTestProb`: the probability that the verifier accepts.
* `Cslib.PCP.linearityGame`: the linearity test as a seeded game.

## Main results

* `Cslib.PCP.CommutingStrategy.linearityTestProb_eq`: the acceptance probability as an average of
  correlations.
* `Cslib.PCP.commutingWinProb_linearityGame`: it is the winning probability of the seeded game.
* `Cslib.PCP.CommutingStrategy.one_sub_le_expect_re_apply_mul_mul_of_linearityTest`: acceptance
  makes the point player's observables linear on average.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

@[expose] public section

namespace Cslib.PCP

open Finset Quantum
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The point sent to the point player in each of the three tests: `a`, `b` or `a + b`. -/
def linearityQuery (k : Fin 3) (a b : n → Bool) : n → Bool :=
  if k = 0 then a else if k = 1 then b else a + b

/-- The function of the pair player's bits that the point player's bit must match in each of the
three tests: `α`, `β` or `α ⊕ β`. -/
def linearityCheck (k : Fin 3) : Bool × Bool → Bool :=
  if k = 0 then Prod.fst else if k = 1 then Prod.snd else fun r => r.1 ^^ r.2

namespace CommutingStrategy

variable {𝒜 : Type*}

section Ring

variable [Ring 𝒜] [PartialOrder 𝒜] [Algebra ℂ 𝒜]

/-- The probability that the linearity-test verifier accepts the strategy `S`: it draws
`k ∈ {0, 1, 2}` and `a, b` uniformly, asks `linearityQuery k a b` and `(a, b)`, and accepts when the
point player's bit equals `linearityCheck k` of the pair player's bits. -/
noncomputable def linearityTestProb
    (S : CommutingStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) 𝒜) : ℝ :=
  𝔼 k : Fin 3, 𝔼 a, 𝔼 b, ∑ γ, ∑ r,
    if γ = linearityCheck k r then S.prob (linearityQuery k a b) (a, b) γ r else 0

end Ring

section Star

variable [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜]

/-- The acceptance probability of the linearity test is the average of
`(1 + Re φ(A(c) N_k(a, b))) / 2`, for the point player's observable `A(c)` and the observable
`N_k(a, b)` of the pair player's checked bit. -/
theorem linearityTestProb_eq
    (S : CommutingStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) 𝒜) :
    S.linearityTestProb = 𝔼 k : Fin 3, 𝔼 a, 𝔼 b,
      (1 + (S.state ((S.alice (linearityQuery k a b)).observable *
        ((S.bob (a, b)).map (linearityCheck k)).observable)).re) / 2 := by
  simp only [linearityTestProb, sum_ite_prob_eq]

end Star

section CStar

variable [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **Passing the linearity test makes the point player's observables linear.** A
commuting-operator strategy with projective pair measurements accepted by the linearity-test
verifier with probability at least `1 - ε` has
`E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - 6ε - 2√(12ε)` for the point observables `A(c)`. -/
theorem one_sub_le_expect_re_apply_mul_mul_of_linearityTest
    (S : CommutingStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) 𝒜)
    (hB : ∀ q, (S.bob q).IsProjective) {ε : ℝ}
    (hε : 1 - ε ≤ S.linearityTestProb) :
    1 - 6 * ε - √(12 * ε) - √(12 * ε) ≤
      𝔼 a, 𝔼 b, (S.state ((S.alice a).observable * (S.alice b).observable *
        (S.alice (a + b)).observable)).re := by
  classical
  set φ := S.state
  let A : (n → Bool) → 𝒜 := fun c => (S.alice c).observable
  let N : Fin 3 → (n → Bool) → (n → Bool) → 𝒜 := fun k a b =>
    ((S.bob (a, b)).map (linearityCheck k)).observable
  let C : Fin 3 → (n → Bool) → (n → Bool) → ℝ := fun k a b =>
    (φ (A (linearityQuery k a b) * N k a b)).re
  have hA c : star (A c) * A c ≤ 1 := (S.alice c).star_observable_mul_self_le_one
  have hN k a b : star (N k a b) * N k a b ≤ 1 :=
    ((S.bob (a, b)).map (linearityCheck k)).star_observable_mul_self_le_one
  have hdist (k : Fin 3) (a b : n → Bool) :
      φ.norm (A (linearityQuery k a b) - N k a b) ^ 2 ≤ 2 - 2 * C k a b := by
    let c := linearityQuery k a b
    have ha := φ.norm_sq_le_of_star_mul_le (hA c)
    have hb := φ.norm_sq_le_of_star_mul_le (hN k a b)
    rw [AlgState.map_one, Complex.one_re] at ha hb
    change ‖φ.toPreGNS (A c - N k a b)‖ ^ 2 ≤ 2 - 2 * C k a b
    rw [map_sub, norm_sub_sq (𝕜 := ℂ), AlgState.inner_toPreGNS,
      (S.alice c).isSelfAdjoint_observable.star_eq, RCLike.re_to_complex]
    change φ.norm (A c) ^ 2 - 2 * C k a b + φ.norm (N k a b) ^ 2 ≤ _
    linarith
  have hC1 (k : Fin 3) (a b : n → Bool) : C k a b ≤ 1 := by
    linarith [hdist k a b, sq_nonneg (φ.norm (A (linearityQuery k a b) - N k a b))]
  have hwin : S.linearityTestProb =
      1 / 2 + (𝔼 a, 𝔼 b, C 0 a b + 𝔼 a, 𝔼 b, C 1 a b + 𝔼 a, 𝔼 b, C 2 a b) / 6 := by
    rw [linearityTestProb_eq]
    simp only [Fintype.expect_eq_sum_div_card, Fin.sum_univ_three, Fintype.card_fin, ← sum_div,
      add_div, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
    have hK : (Fintype.card (n → Bool) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hE (k : Fin 3) : 𝔼 a, 𝔼 b, C k a b ≤ 1 :=
    (expect_le_expect fun a _ => expect_le_expect fun b _ => hC1 k a b).trans_eq
      (by simp only [Fintype.expect_const])
  have hc : ∀ k a b c, Commute (N k a b) (A c) := fun k a b c => S.commute_observable_map _ _ _
  have hdistE (k : Fin 3) :
      𝔼 a, 𝔼 b, φ.norm (A (linearityQuery k a b) - N k a b) ^ 2 ≤
        2 - 2 * 𝔼 a, 𝔼 b, C k a b := by
    have h := expect_le_expect (s := (univ : Finset (n → Bool))) fun a _ =>
      expect_le_expect (s := (univ : Finset (n → Bool))) fun b _ => hdist k a b
    simpa only [expect_sub_distrib, ← mul_expect, Fintype.expect_const] using h
  have hL : 1 - 6 * ε ≤ 𝔼 a, 𝔼 b, (φ (N 0 a b * N 1 a b * A (a + b))).re := by
    have e : ∀ a b, (φ (N 0 a b * N 1 a b * A (a + b))).re = C 2 a b := fun a b => by
      simp only [C, N, linearityCheck, linearityQuery, Fin.reduceEq, ite_true, ite_false,
        (hB (a, b)).observable_map_mul_observable_map Prod.fst Prod.snd]
      rw [(S.commute_observable_map _ (a + b) (a, b)).eq]
    simp only [e]
    linarith [hE 0, hE 1, hE 2]
  have h₁ : 𝔼 a, 𝔼 b, φ.norm (A a - N 0 a b) ^ 2 ≤ 12 * ε := by
    have := hdistE 0
    simp only [linearityQuery, ite_true] at this
    linarith [hE 0, hE 1, hE 2]
  have h₂ : 𝔼 a, 𝔼 b, φ.norm (A b - N 1 a b) ^ 2 ≤ 12 * ε := by
    have := hdistE 1
    simp only [linearityQuery, Fin.reduceEq, ite_true, ite_false] at this
    linarith [hE 0, hE 1, hE 2]
  exact one_sub_le_expect_re_apply_mul_mul φ A (N 0) (N 1) hA (hN 0) (hc 0) (hc 1) hL h₁ h₂

end CStar

end CommutingStrategy

/-- The **two-player linearity test as a seeded game**: the verifier's seed `(k, a, b)` is uniform,
the questions are `linearityQuery k a b` and `(a, b)`, and the verifier accepts when the point
player's bit equals `linearityCheck k` of the pair player's bits. The seed `k` stays private. -/
noncomputable def linearityGame (n : Type*) [Fintype n] [DecidableEq n] :
    SeededGame (Fin 3 × (n → Bool) × (n → Bool)) (n → Bool) ((n → Bool) × (n → Bool)) Bool
      (Bool × Bool) where
  seed := Probability.PMF.uniformOfFintype _
  query | (k, a, b) => (linearityQuery k a b, (a, b))
  accepts | (k, _, _), γ, r => γ = linearityCheck k r

instance (s : Fin 3 × (n → Bool) × (n → Bool)) (γ : Bool) (r : Bool × Bool) :
    Decidable ((linearityGame n).accepts s γ r) :=
  inferInstanceAs (Decidable (γ = _))

/-- The winning probability of the seeded linearity game is the acceptance probability of the
linearity test. -/
theorem commutingWinProb_linearityGame {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
    [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]
    (S : CommutingStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) 𝒜) :
    (linearityGame n).commutingWinProb S = S.linearityTestProb := by
  rw [SeededGame.commutingWinProb_eq_expect_of_uniform _ rfl, CommutingStrategy.linearityTestProb]
  simp only [Fintype.expect_prod_type, linearityGame]
  refine expect_congr rfl fun k _ => expect_congr rfl fun a _ => expect_congr rfl fun b _ =>
    sum_congr rfl fun γ _ => sum_congr rfl fun r _ => ?_
  by_cases h : γ = linearityCheck k r <;> simp only [h, ite_true, ite_false]

end Cslib.PCP
