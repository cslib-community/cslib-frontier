/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting

/-!
# The three linearity checks on a diagonal pair

When the pair player receives two copies of the same string, the first and second
checks ask the point player for the same bit. If the two pair bits disagree, at least
one of those checks rejects. The parity check then asks for the zero string. The
pair player's marginal is independent of the point question, so a true zero bit
costs either a parity-check rejection or a disagreement in the first two checks.

## Main results

* `Cslib.PCP.CommutingStrategy.prob_true_le_diagonal_linearity`: the three rejection
  probabilities bound the marginal probability of decoding a true zero answer.
-/

public section

namespace Cslib.PCP.CommutingStrategy

open Finset Quantum

variable {X Y A B 𝒜 : Type*} [Fintype A] [Fintype B] [Ring 𝒜] [StarRing 𝒜]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [TopologicalSpace 𝒜]
  [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]

/-- On a diagonal round, rejection of the two coordinate checks and the parity check
controls the probability of a true decoded answer at zero. The pair player's question
and decoder are the same in all three checks. -/
theorem prob_true_le_diagonal_linearity
    (S : CommutingStrategy X Y A B 𝒜) (x : X) (point zero : Y)
    (pair : A → Bool × Bool) (readPoint readZero : B → Bool) :
    let loss (y : Y) (read : B → Bool) (check : Bool × Bool → Bool) :=
      ∑ a, ∑ b, if read b = check (pair a) then 0 else S.prob x y a b
    ((S.bob zero).map readZero).prob S.state true ≤
      loss point readPoint Prod.fst + loss point readPoint Prod.snd +
        loss zero readZero (fun bits => bits.1 ^^ bits.2) := by
  intro loss
  let parity (a : A) := (pair a).1 ^^ (pair a).2
  let pairBad := ((S.alice x).map parity).prob S.state true
  have hpair (y : Y) :
      pairBad = ∑ a, ∑ b, if parity a = true then S.prob x y a b else 0 := by
    simp only [pairBad, Measurement.prob_map, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    split_ifs
    · exact (S.sum_prob_bob x y a).symm
    · simp
  have hpoint :
      ((S.bob zero).map readZero).prob S.state true =
        ∑ a, ∑ b, if readZero b = true then S.prob x zero a b else 0 := by
    rw [Measurement.prob_map, sum_filter, sum_comm]
    refine sum_congr rfl fun b _ => ?_
    split_ifs
    · exact (S.sum_prob_alice x zero b).symm
    · simp
  have hcoordinates : pairBad ≤ loss point readPoint Prod.fst + loss point readPoint Prod.snd := by
    rw [hpair point]
    simp only [loss, ← sum_add_distrib]
    refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
    have h (first second answer : Bool) (p : ℝ) (hp : 0 ≤ p) :
        (if (first ^^ second) = true then p else 0) ≤
          (if answer = first then 0 else p) + (if answer = second then 0 else p) := by
      cases first <;> cases second <;> cases answer <;> simp [hp]
    exact h (pair a).1 (pair a).2 (readPoint b) _ (S.prob_nonneg x point a b)
  have hparity :
      ((S.bob zero).map readZero).prob S.state true ≤
        pairBad + loss zero readZero (fun bits => bits.1 ^^ bits.2) := by
    rw [hpoint, hpair zero]
    simp only [loss, parity, ← sum_add_distrib]
    refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
    have h (expected answer : Bool) (p : ℝ) (hp : 0 ≤ p) :
        (if answer = true then p else 0) ≤
          (if expected = true then p else 0) + (if answer = expected then 0 else p) := by
      cases expected <;> cases answer <;> simp [hp]
    exact h (parity a) (readZero b) _ (S.prob_nonneg x zero a b)
  linarith

end Cslib.PCP.CommutingStrategy
