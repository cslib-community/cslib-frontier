/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
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
questions but different checks. The acceptance probability of a commuting-operator strategy is
therefore defined with the sampled check (`Cslib.PCP.CommutingStrategy.linearityTestProb`) rather
than as a `Cslib.PCP.TwoProverGame`, whose acceptance predicate sees only the questions; extending
that structure with private verifier randomness is tracked in
cslib-community/cslib-frontier#6149.

The acceptance probability is an average of correlations
(`Cslib.PCP.CommutingStrategy.linearityTestProb_eq`), by
`Cslib.PCP.CommutingStrategy.sum_ite_prob_eq`. A strategy with projective measurements that is
accepted with probability `1 - ε` therefore makes Alice's observables `A(c)` linear on average
(`Cslib.PCP.CommutingStrategy.one_sub_le_expect_re_apply_mul_mul_of_linearityTest`):

`E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - 6ε - 2√(12ε)`.

Each check passes with probability at least `1 - 3ε`. The consistency checks bound the distances
between Alice's observables and the marginals of Bob's, and the linearity check bounds the
correlation of `A(a + b)` with the product of Bob's marginals, which for a projective measurement
is the parity observable. Linearity from consistency
(`Cslib.Quantum.one_sub_le_expect_re_apply_mul_mul`) then gives the bound.

This is the test of [Natarajan and Vidick, §3, Figure 1][NatarajanVidick2017]
(arXiv:1610.03574v1) in an **asymmetric variant**, and the estimate is the commuting-operator,
point-player form of their Theorem 11. The variant differs from the source in two ways:

* one player always gets the point and the other the pair, whereas the source labels the players
  at random and sends Bob a second, uniformly random query so that symmetric strategies apply;
* the conclusion concerns the point player's own observables, whereas the source rounds the
  Naimark dilation of the averaged pair marginals.

As in the source, the strategy's measurements are assumed projective here. The source's symmetric
game and the remaining steps toward Pauli rigidity are tracked in #6149.

## Main definitions

* `Cslib.PCP.linearityQuery`, `Cslib.PCP.linearityCheck`: the point query and the check of each
  test.
* `Cslib.PCP.CommutingStrategy.linearityTestProb`: the probability that the verifier accepts.

## Main results

* `Cslib.PCP.CommutingStrategy.linearityTestProb_eq`: the acceptance probability as an average of
  correlations.
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

private theorem observable_mem_unitary {M : Measurement Bool 𝒜} (hM : M.IsProjective) :
    M.observable ∈ unitary 𝒜 := by
  rw [Unitary.mem_iff, M.isSelfAdjoint_observable.star_eq]
  exact ⟨Measurement.observable_mul_self hM, Measurement.observable_mul_self hM⟩

private theorem commute_observable {X Y B : Type*} [Fintype B]
    (S : CommutingStrategy X Y Bool B 𝒜) (g : B → Bool) (x : X) (y : Y) :
    Commute (((S.bob y).map g).observable) ((S.alice x).observable) := by
  classical
  simp only [Measurement.observable, Measurement.map_effect]
  refine (Commute.sub_left ?_ ?_) <;> refine Commute.sum_left _ _ _ fun r _ => ?_ <;>
    exact ((S.commute x y false r).sub_left (S.commute x y true r)).symm

private theorem norm_sub_sq_eq (φ : AlgState 𝒜) {U V : 𝒜} (hU : IsSelfAdjoint U)
    (hV : IsSelfAdjoint V) (hU2 : U * U = 1) (hV2 : V * V = 1) (hc : Commute V U) :
    φ.norm (U - V) ^ 2 = 2 - 2 * (φ (U * V)).re := by
  have e : (U - V) * (U - V) = (1 + 1) - (U * V + U * V) := by
    rw [sub_mul, mul_sub, mul_sub, hU2, hV2, hc.eq]; abel
  rw [φ.norm_sq, star_sub, hU.star_eq, hV.star_eq, e, map_sub, map_add, map_add, φ.map_one,
    Complex.sub_re, Complex.add_re, Complex.add_re, Complex.one_re]
  ring

/-- The product of the observables of two bits of a projective measurement is the observable of
their parity. -/
private theorem observable_map_fst_mul_snd {M : Measurement (Bool × Bool) 𝒜}
    (hM : M.IsProjective) :
    (M.map Prod.fst).observable * (M.map Prod.snd).observable =
      (M.map fun r => r.1 ^^ r.2).observable := by
  rw [Measurement.observable_map, Measurement.observable_map, Measurement.observable_map,
    hM.sum_smul_mul_sum_smul]
  refine sum_congr rfl fun r _ => ?_
  rw [BitString.signVal_xor, Complex.ofReal_mul]

/-- **Passing the linearity test makes the point player's observables linear.** A
commuting-operator strategy with projective measurements that the linearity-test verifier accepts
with probability at least `1 - ε` has `E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - 6ε - 2√(12ε)` for
the observables `A(c)` of the point player. -/
theorem one_sub_le_expect_re_apply_mul_mul_of_linearityTest
    (S : CommutingStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) 𝒜)
    (hA : ∀ c, (S.alice c).IsProjective) (hB : ∀ q, (S.bob q).IsProjective) {ε : ℝ}
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
  have hAu : ∀ c, A c ∈ unitary 𝒜 := fun c => observable_mem_unitary (hA c)
  have hNu : ∀ k a b, N k a b ∈ unitary 𝒜 := fun k a b => observable_mem_unitary ((hB _).map _)
  have hC1 : ∀ k a b, C k a b ≤ 1 := fun k a b =>
    (Complex.re_le_norm _).trans ((φ.norm_apply_le_norm _).trans (φ.norm_le_one
      (Unitary.star_mul_self_of_mem (mul_mem (hAu _) (hNu k a b))).le))
  have hwin : S.linearityTestProb =
      1 / 2 + (𝔼 a, 𝔼 b, C 0 a b + 𝔼 a, 𝔼 b, C 1 a b + 𝔼 a, 𝔼 b, C 2 a b) / 6 := by
    rw [linearityTestProb_eq]
    simp only [Fintype.expect_eq_sum_div_card, Fin.sum_univ_three, Fintype.card_fin, ← sum_div,
      add_div, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
    have hK : (Fintype.card (n → Bool) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hE : ∀ k, 𝔼 a, 𝔼 b, C k a b ≤ 1 := fun k => by
    calc 𝔼 a, 𝔼 b, C k a b ≤ 𝔼 _a : n → Bool, 𝔼 _b : n → Bool, (1 : ℝ) :=
          expect_le_expect fun a _ => expect_le_expect fun b _ => hC1 k a b
      _ = 1 := by simp only [Fintype.expect_const]
  have hc : ∀ k a b c, Commute (N k a b) (A c) := fun k a b c => commute_observable S _ _ _
  have hNsa : ∀ k a b, IsSelfAdjoint (N k a b) := fun k a b =>
    Measurement.isSelfAdjoint_observable _
  have hN2 : ∀ k a b, N k a b * N k a b = 1 := fun k a b =>
    Measurement.observable_mul_self ((hB _).map _)
  have hdist : ∀ k a b, φ.norm (A (linearityQuery k a b) - N k a b) ^ 2 = 2 - 2 * C k a b :=
    fun k a b => norm_sub_sq_eq φ (S.alice _).isSelfAdjoint_observable (hNsa k a b)
      (Measurement.observable_mul_self (hA _)) (hN2 k a b) (hc k a b _)
  have hdistE : ∀ k, 𝔼 a, 𝔼 b, φ.norm (A (linearityQuery k a b) - N k a b) ^ 2 =
      2 - 2 * 𝔼 a, 𝔼 b, C k a b := fun k => by
    simp only [hdist, expect_sub_distrib, ← mul_expect, Fintype.expect_const]
  have hL : 1 - 6 * ε ≤ 𝔼 a, 𝔼 b, (φ (N 0 a b * N 1 a b * A (a + b))).re := by
    have e : ∀ a b, (φ (N 0 a b * N 1 a b * A (a + b))).re = C 2 a b := fun a b => by
      simp only [C, N, linearityCheck, linearityQuery, Fin.reduceEq, ite_true, ite_false,
        observable_map_fst_mul_snd (hB (a, b))]
      rw [(commute_observable S _ (a + b) (a, b)).eq]
    simp only [e]
    linarith [hE 0, hE 1, hE 2]
  have h₁ : 𝔼 a, 𝔼 b, φ.norm (A a - N 0 a b) ^ 2 ≤ 12 * ε := by
    have := hdistE 0
    simp only [linearityQuery, ite_true] at this
    rw [this]
    linarith [hE 0, hE 1, hE 2]
  have h₂ : 𝔼 a, 𝔼 b, φ.norm (A b - N 1 a b) ^ 2 ≤ 12 * ε := by
    have := hdistE 1
    simp only [linearityQuery, Fin.reduceEq, ite_true, ite_false] at this
    rw [this]
    linarith [hE 0, hE 1, hE 2]
  exact one_sub_le_expect_re_apply_mul_mul φ A (N 0) (N 1) hAu (hNu 0) (hc 0) (hc 1) hL h₁ h₂

end CStar

end CommutingStrategy

end Cslib.PCP
