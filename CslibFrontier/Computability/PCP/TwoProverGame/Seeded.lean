/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
import CslibFrontier.Probability.PMF.Event

/-!
# Two-prover games with private verifier randomness

In a `Cslib.PCP.TwoProverGame` the verifier's decision depends only on the questions and the
answers. Many verifiers keep randomness of their own: the linearity test selects which check to
run, the Pauli braiding test selects a subtest and a role for each player, and when two choices of
the private randomness produce the same questions, the verifier may still decide differently. A
**seeded game** (`Cslib.PCP.SeededGame`) records this: the verifier draws a seed `r ∼ seed`, sends
the questions `query r`, and accepts the answers `(a, b)` when `accepts r a b`. The players see
only the questions.

The winning probability of answer distributions `ans x y` (`Cslib.PCP.SeededGame.answersWinProb`),
and so of tensor-product and commuting-operator strategies
(`Cslib.PCP.SeededGame.quantumWinProb`, `Cslib.PCP.SeededGame.commutingWinProb`), is the
probability that the verifier accepts; for finite seeds and answers it is
`∑_r Pr[r] ∑_{a,b} [accepts r a b] Pr[(a, b) | query r]`
(`Cslib.PCP.SeededGame.answersWinProb_eq_sum`, `Cslib.PCP.SeededGame.commutingWinProb_eq_sum`).
Every two-prover game is a seeded game with the questions as the seed
(`Cslib.PCP.TwoProverGame.toSeeded`), with the same winning probabilities
(`Cslib.PCP.TwoProverGame.answersWinProb_toSeeded`).

## Main definitions

* `Cslib.PCP.SeededGame`: a two-prover game with private verifier randomness.
* `Cslib.PCP.SeededGame.answersWinProb`, `Cslib.PCP.SeededGame.quantumWinProb`,
  `Cslib.PCP.SeededGame.commutingWinProb`: winning probabilities.
* `Cslib.PCP.TwoProverGame.toSeeded`: a two-prover game as a seeded game.

## Main results

* `Cslib.PCP.SeededGame.answersWinProb_eq_sum`: the winning probability as a sum.
* `Cslib.PCP.SeededGame.commutingWinProb_toCommuting`: converting a tensor-product strategy
  to a commuting-operator strategy preserves its winning probability.
-/

@[expose] public section

namespace Cslib.PCP

open Finset Quantum
open scoped BigOperators

namespace SeededGame

variable {R X Y A B : Type*} (G : SeededGame R X Y A B)

/-- The probability that the tensor-product strategy `S` wins `G`. -/
noncomputable def quantumWinProb [Fintype A] [Fintype B] {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (S : QuantumStrategy X Y A B ι κ) : ℝ :=
  G.answersWinProb S.answers

section Commuting

variable {𝒜 : Type*} [Fintype A] [Fintype B] [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
  [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]

/-- The probability that the commuting-operator strategy `S` wins `G`. -/
noncomputable def commutingWinProb (S : CommutingStrategy X Y A B 𝒜) : ℝ :=
  G.answersWinProb S.answers

/-- The winning probability of a commuting-operator strategy:
`∑_r Pr[r] ∑_{a,b} [accepts r a b] Re φ(P_x^a Q_y^b)` with `(x, y) = query r`. -/
theorem commutingWinProb_eq_sum [Fintype R] [∀ r a b, Decidable (G.accepts r a b)]
    (S : CommutingStrategy X Y A B 𝒜) :
    G.commutingWinProb S = ∑ r, (G.seed r).toReal * ∑ a, ∑ b,
      if G.accepts r a b then S.prob (G.query r).1 (G.query r).2 a b else 0 := by
  rw [commutingWinProb, answersWinProb_eq_sum]
  simp only [S.answers_apply, ENNReal.toReal_ofReal (S.prob_nonneg _ _ _ _)]

/-- With a uniform private seed, the winning probability is the average of the conditional
acceptance probabilities. -/
theorem commutingWinProb_eq_expect_of_uniform [Fintype R] [Nonempty R]
    [∀ r a b, Decidable (G.accepts r a b)]
    (h : G.seed = Cslib.Probability.PMF.uniformOfFintype R) (S : CommutingStrategy X Y A B 𝒜) :
    G.commutingWinProb S = 𝔼 r, ∑ a, ∑ b,
      if G.accepts r a b then S.prob (G.query r).1 (G.query r).2 a b else 0 := by
  rw [commutingWinProb_eq_sum, Fintype.expect_eq_sum_div_card, div_eq_inv_mul, mul_sum]
  simp only [h, Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

/-- Rejection at a specified private seed is the sum of the probability of every rejected
answer pair on that seed's questions. -/
theorem one_sub_commutingWinProb_pure_seed (r : R)
    [∀ a b, Decidable (G.accepts r a b)] (S : CommutingStrategy X Y A B 𝒜) :
    1 - ({ G with seed := PMF.pure r }).commutingWinProb S =
      ∑ a, ∑ b, if G.accepts r a b then 0 else S.prob (G.query r).1 (G.query r).2 a b := by
  have hwin : ({ G with seed := PMF.pure r }).commutingWinProb S =
      ∑ a, ∑ b, if G.accepts r a b then S.prob (G.query r).1 (G.query r).2 a b else 0 := by
    unfold commutingWinProb answersWinProb
    rw [PMF.pure_bind, PMF.toOuterMeasure_map_apply,
      Cslib.Probability.PMF.toOuterMeasure_apply_toReal, Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, AcceptsRound, S.answers_apply,
      ENNReal.toReal_ofReal (S.prob_nonneg _ _ _ _)]
  rw [hwin, ← S.sum_prob (G.query r).1 (G.query r).2]
  simp only [← sum_sub_distrib]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

end Commuting

open scoped MatrixOrder ComplexOrder in
/-- A tensor-product strategy and its commuting-operator form win with the same probability. -/
theorem commutingWinProb_toCommuting [Fintype A] [Fintype B] {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (S : QuantumStrategy X Y A B ι κ) :
    G.commutingWinProb S.toCommuting = G.quantumWinProb S := by
  rw [commutingWinProb, quantumWinProb]
  congr 1
  funext x y
  exact S.answers_toCommuting x y

end SeededGame

namespace TwoProverGame

variable {X Y A B : Type*} (G : TwoProverGame X Y A B)

/-- A two-prover game and its seeded form have the same winning probabilities. -/
theorem answersWinProb_toSeeded (ans : X → Y → PMF (A × B)) :
    G.toSeeded.answersWinProb ans = G.answersWinProb ans :=
  rfl

end TwoProverGame

end Cslib.PCP
