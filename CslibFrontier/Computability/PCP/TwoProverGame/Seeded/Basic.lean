/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.ToReal

/-!
# Two-prover games with private verifier randomness

A `SeededGame` samples a seed, sends each prover its question, and checks the answers against
the sampled seed. An ordinary `TwoProverGame` is the special case where the seed is the question
pair. The answer distributions depend only on the questions.

## Main definitions

* `Cslib.PCP.SeededGame`: the verifier and its private randomness.
* `Cslib.PCP.SeededGame.answersWinProb`: winning probability for an answer kernel.
* `Cslib.PCP.TwoProverGame.toSeeded`: an ordinary game as a seeded game.

## Main results

* `Cslib.PCP.SeededGame.answersWinProb_eq_sum`: the winning probability as a finite sum.
-/

@[expose] public section

namespace Cslib.PCP

/-- A **two-prover game with private verifier randomness**: the verifier draws a seed `r` from
`seed`, sends the questions `query r`, and accepts the answers `(a, b)` when `accepts r a b`. -/
structure SeededGame (R X Y A B : Type*) where
  /-- The distribution of the verifier's seed. -/
  seed : PMF R
  /-- The questions sent on the seed `r`. -/
  query : R → X × Y
  /-- The verifier's decision on the seed `r` and the answers. -/
  accepts : R → A → B → Prop

namespace SeededGame

variable {R X Y A B : Type*} (G : SeededGame R X Y A B)

/-- The verdict of `G` on a seed and answers. -/
def AcceptsRound : R × A × B → Prop
  | (r, (a, b)) => G.accepts r a b

/-- The probability of winning `G` when the answers to questions `(x, y)` are drawn from
`ans x y`. -/
noncomputable def answersWinProb (ans : X → Y → PMF (A × B)) : ℝ :=
  ((G.seed.bind fun r => (ans (G.query r).1 (G.query r).2).map fun ab => (r, ab)).toOuterMeasure
    {z | G.AcceptsRound z}).toReal

theorem answersWinProb_nonneg (ans : X → Y → PMF (A × B)) : 0 ≤ G.answersWinProb ans :=
  ENNReal.toReal_nonneg

theorem answersWinProb_le_one (ans : X → Y → PMF (A × B)) : G.answersWinProb ans ≤ 1 :=
  Cslib.Probability.PMF.toOuterMeasure_toReal_le_one _ _

/-- The winning probability `∑_r Pr[r] ∑_{a,b} [accepts r a b] Pr[(a, b) | query r]`. -/
theorem answersWinProb_eq_sum [Fintype R] [Fintype A] [Fintype B]
    [∀ r a b, Decidable (G.accepts r a b)] (ans : X → Y → PMF (A × B)) :
    G.answersWinProb ans = ∑ r, (G.seed r).toReal * ∑ a, ∑ b,
      if G.accepts r a b then (ans (G.query r).1 (G.query r).2 (a, b)).toReal else 0 := by
  rw [answersWinProb, Cslib.Probability.PMF.toOuterMeasure_bind_toReal]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [PMF.toOuterMeasure_map_apply,
    Cslib.Probability.PMF.toOuterMeasure_apply_toReal, ← Finset.univ_product_univ,
    Finset.sum_product]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, AcceptsRound]

end SeededGame

namespace TwoProverGame

variable {X Y A B : Type*} (G : TwoProverGame X Y A B)

/-- A two-prover game as a seeded game: the seed is the pair of questions. -/
def toSeeded : SeededGame (X × Y) X Y A B where
  seed := G.questions
  query := id
  accepts q a b := G.accepts q.1 q.2 a b

end TwoProverGame

end Cslib.PCP
