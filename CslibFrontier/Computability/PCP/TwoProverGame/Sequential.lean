/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import CslibFrontier.Foundations.Quantum.Algebra.SequentialDisturbance
public import Mathlib.Algebra.BigOperators.Expect
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.PMF.Event

/-!
# Sequential questions to one player

A commuting strategy with projective Alice measurements can accept a tuple of Alice questions
and return the full sequential transcript. The probability of an event involving one coordinate
of that transcript and Bob's answer increases by at most twice the square root of Alice's
prefix commutator defect.
-/

public section

namespace Cslib.PCP.CommutingStrategy

open Finset Cslib.Quantum
open scoped BigOperators Real

variable {A X Y α β : Type*} [Fintype α] [Fintype β] [Ring A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [Algebra ℂ A]

/-- Ask Alice all the questions of the input tuple in order, and ask Bob his original question. -/
@[expose] noncomputable def sequential (S : CommutingStrategy X Y α β A) (k : ℕ)
    (hM : ∀ x, (S.alice x).IsProjective) : CommutingStrategy (Fin k → X) Y (Fin k → α) β A where
  state := S.state
  alice xs := Measurement.sequentialProjective (fun j => S.alice (xs j)) (fun j => hM (xs j))
  bob := S.bob
  commute xs y g b :=
    Measurement.sequentialProjective_commute _ _ _ (fun j a => S.commute (xs j) y a b) g

variable [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

private noncomputable def eventWeight (B : Measurement β A) (p : α → β → Prop) (a : α) : A := by
  classical
  exact ∑ b with p a b, B.effect b

private theorem event_prob_eq (S : CommutingStrategy X Y α β A) (x : X) (y : Y)
    (p : α → β → Prop) :
    ((S.answers x y).toOuterMeasure {ab | p ab.1 ab.2}).toReal =
      ∑ a, (S.state ((S.alice x).effect a * eventWeight (S.bob y) p a)).re := by
  classical
  rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  simp only [Set.mem_ofPred_eq, S.answers_apply,
    ENNReal.toReal_ofReal (S.prob_nonneg x y a _), eventWeight, sum_filter, mul_sum,
    Complex.re_sum, map_sum]
  refine sum_congr rfl fun b _ => ?_
  by_cases h : p a b <;> simp [h, prob]

variable [StarModule ℂ A] [SelfAdjointDecompose A]

/-- Compare an event testing coordinate `i` of Alice's transcript and Bob's answer
with the same event when only the `i`-th question is asked. -/
theorem sequential_event_le (S : CommutingStrategy X Y α β A) {k : ℕ}
    (hM : ∀ x, (S.alice x).IsProjective) (xs : Fin k → X) (i : Fin k) (y : Y)
    (p : α → β → Prop) :
    (((S.sequential k hM).answers xs y).toOuterMeasure {ab | p (ab.1 i) ab.2}).toReal ≤
      ((S.answers (xs i) y).toOuterMeasure {ab | p ab.1 ab.2}).toReal +
        2 * √(Measurement.prefixCommutatorDefect S.state (fun j => S.alice (xs j)) i) := by
  classical
  rw [event_prob_eq (S.sequential k hM) xs y (fun g b => p (g i) b),
    event_prob_eq S (xs i) y p]
  unfold sequential
  let W := eventWeight (S.bob y) p
  change (∑ g, (S.state
    ((Measurement.sequentialProjective (fun j => S.alice (xs j)) (fun j => hM (xs j))).effect g *
      W (g i))).re) ≤
      (∑ a, (S.state ((S.alice (xs i)).effect a * W a)).re) + _
  refine Measurement.sequentialProjective_weighted_le _ _ _ _ W (fun a => ?_) ?_
  · have h0 : 0 ≤ W a := sum_nonneg fun b _ => (S.bob y).nonneg b
    have h1 : W a ≤ 1 := by
      rw [← (S.bob y).sum_effect]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun b _ _ => (S.bob y).nonneg b
    calc
      star (W a) * W a = W a * W a := by rw [h0.isSelfAdjoint.star_eq]
      _ ≤ W a := by
        have hc : Commute (W a) (1 - W a) := (Commute.one_right _).sub_right (Commute.refl _)
        have h := Commute.mul_nonneg h0 (sub_nonneg.mpr h1) hc
        rwa [mul_sub, mul_one, sub_nonneg] at h
      _ ≤ 1 := h1
  · intro j b a
    exact (Commute.sum_left _ _ _ fun q _ => (S.commute (xs j) y b q).symm).symm

/-- Under independent uniform questions, the average transcript error is bounded by
the isolated error plus twice the square root of the average prefix defect. -/
theorem average_sequential_event_le [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (S : CommutingStrategy X Y α β A) {k : ℕ}
    (hM : ∀ x, (S.alice x).IsProjective) (i : Fin k) (p : X → Y → α → β → Prop) :
    (𝔼 y, 𝔼 xs : Fin k → X,
      (((S.sequential k hM).answers xs y).toOuterMeasure
        {ab | p (xs i) y (ab.1 i) ab.2}).toReal) ≤
      (𝔼 y, 𝔼 x, ((S.answers x y).toOuterMeasure {ab | p x y ab.1 ab.2}).toReal) +
        2 * √(𝔼 xs : Fin k → X, Measurement.prefixCommutatorDefect S.state
          (fun j => S.alice (xs j)) i) := by
  let base x y := ((S.answers x y).toOuterMeasure {ab | p x y ab.1 ab.2}).toReal
  let defect (xs : Fin k → X) :=
    Measurement.prefixCommutatorDefect S.state (fun j => S.alice (xs j)) i
  have hbase (y : Y) : (𝔼 xs : Fin k → X, base (xs i) y) = 𝔼 x, base x y := by
    rw [← Fintype.expect_expect_update (fun xs : Fin k → X => base (xs i) y) i]
    simp only [Function.update_self, Fintype.expect_const]
  have hjensen : (𝔼 xs, √(defect xs)) ≤ √(𝔼 xs, defect xs) := by
    have h := Real.expect_mul_le_sqrt_mul_sqrt univ (fun xs => √(defect xs)) (fun _ => 1)
    have hnn (xs : Fin k → X) : 0 ≤ defect xs := Measurement.prefixCommutatorDefect_nonneg _ _ _
    simpa only [Real.sq_sqrt (hnn _), mul_one, one_pow, Fintype.expect_const, Real.sqrt_one] using h
  calc
    _ ≤ 𝔼 y, 𝔼 xs : Fin k → X, (base (xs i) y + 2 * √(defect xs)) :=
      Finset.expect_le_expect fun y _ => Finset.expect_le_expect fun xs _ =>
        S.sequential_event_le hM xs i y (p (xs i) y)
    _ = (𝔼 y, 𝔼 x, base x y) + 2 * (𝔼 xs, √(defect xs)) := by
      simp only [Finset.expect_add_distrib, hbase, Fintype.expect_const, ← Finset.mul_expect]
    _ ≤ _ := by gcongr

end Cslib.PCP.CommutingStrategy
