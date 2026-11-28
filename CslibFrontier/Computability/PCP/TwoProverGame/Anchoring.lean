/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Quantum
public import CslibFrontier.Probability.PMF.AnchorPair
import CslibFrontier.Probability.PMF.EventBind

/-!
# Anchoring a two-prover game

In the anchoring transformation [Bavarian, Vidick and Yuen, Definition 1.1][BavarianVidickYuen2022],
the verifier replaces each question independently by an anchor symbol with probability `α`.
It accepts automatically if either player received an anchor. We use `Option` to add the anchor
and sample the two independent replacement flags before the original question pair.

The probability of neither anchor is `(1 - α)^2`. On that branch the players face the original
game with their original measurements. The strategy maps preserve each player's local space,
including for asymmetric strategies. Taking the two suprema gives the value identities of
[Bavarian, Vidick and Yuen, Lemma 1.2][BavarianVidickYuen2022].

The source locators refer to arXiv:1509.07466v2. The identities also hold for `α = 0` and
`α = 1`.

## Main definitions

* `Cslib.PCP.TwoProverGame.anchored`: the anchoring transformation.

## Main results

* `Cslib.PCP.TwoProverGame.quantumValue_anchored` and
  `Cslib.PCP.TwoProverGame.value_anchored`: the exact entangled and classical values.
-/

public section

open scoped unitInterval

namespace Cslib.PCP.TwoProverGame

variable {X Y A B : Type*} (G : TwoProverGame X Y A B)

/-- Independently replace each question by an anchor with probability `α`. Whenever a
question is replaced, the verifier accepts every answer. This is Definition 1.1 of
[Bavarian, Vidick and Yuen][BavarianVidickYuen2022]. -/
noncomputable def anchored (α : I) : TwoProverGame (Option X) (Option Y) A B where
  questions := Probability.PMF.anchorPair G.questions α α
  accepts
    | some x, some y, a, b => G.accepts x y a b
    | _, _, _, _ => True

/-- The anchored question law uses the same replacement rate for each player. -/
theorem anchored_questions (α : I) :
    (G.anchored α).questions = Probability.PMF.anchorPair G.questions α α := by
  unfold anchored
  rfl

/-- If only one question is retained, its law is the corresponding original marginal.
The two anchor flags contribute their independent masses in each case. -/
theorem anchored_questions_apply (α : I) (x : Option X) (y : Option Y) :
    (G.anchored α).questions (x, y) =
      match x, y with
      | none, none => ENNReal.ofReal (α : ℝ) ^ 2
      | some x, none =>
        ENNReal.ofReal (1 - (α : ℝ)) * ENNReal.ofReal (α : ℝ) * (G.questions.map Prod.fst) x
      | none, some y =>
        ENNReal.ofReal (α : ℝ) * ENNReal.ofReal (1 - (α : ℝ)) * (G.questions.map Prod.snd) y
      | some x, some y => ENNReal.ofReal (1 - (α : ℝ)) ^ 2 * G.questions (x, y) := by
  cases x <;> cases y <;>
    simpa only [anchored, pow_two] using Probability.PMF.anchorPair_apply G.questions α α _ _

variable {α : I}

/-- The game incurs the original loss only when both questions are retained. -/
theorem answersWinProb_anchored (ans : Option X → Option Y → PMF (A × B)) :
    (G.anchored α).answersWinProb ans =
      1 - (1 - (α : ℝ)) ^ 2 * (1 - G.answersWinProb (fun x y => ans (some x) (some y))) := by
  let coin := Probability.PMF.coin α
  let H := G.anchored α
  let R (i j : Bool) := G.questions.bind fun q =>
    let q' := (if i then none else some q.1, if j then none else some q.2)
    (ans q'.1 q'.2).map (q', ·)
  let event : Set ((Option X × Option Y) × A × B) := {z | H.AcceptsRound z}
  have he (i j : Bool) :
      ((R i j).toOuterMeasure event).toReal = if i || j then 1 else
        G.answersWinProb (fun x y => ans (some x) (some y)) := by
    split_ifs with h
    · have hq (q : X × Y) :
          let q' := (if i then none else some q.1, if j then none else some q.2)
          ((ans q'.1 q'.2).map (q', ·)).toOuterMeasure event = 1 := by
        dsimp only
        rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_eq_one_iff]
        intro ab _
        cases i <;> cases j <;> first | contradiction | trivial
      dsimp only [R]
      rw [PMF.toOuterMeasure_bind_apply]
      simp only [hq, mul_one, PMF.tsum_coe, ENNReal.toReal_one]
    · obtain ⟨rfl, rfl⟩ : i = false ∧ j = false := by simpa using h
      let e := fun z : (X × Y) × A × B => ((some z.1.1, some z.1.2), z.2)
      have hr : R false false =
          (G.questions.bind fun q => (ans (some q.1) (some q.2)).map (q, ·)).map e := by
        simp only [R, Bool.false_eq_true, ite_false, PMF.map_bind, PMF.map_comp]
        rfl
      rw [hr, PMF.toOuterMeasure_map_apply]
      rfl
  change ((H.questions.bind fun q => (ans q.1 q.2).map (q, ·)).toOuterMeasure event).toReal = _
  have hr : (H.questions.bind fun q => (ans q.1 q.2).map (q, ·)) =
      coin.bind fun i => coin.bind fun j => R i j := by
    simp only [H, anchored, Probability.PMF.anchorPair, PMF.bind_bind, PMF.bind_map,
      Function.comp_def, R, coin]
  rw [hr, Probability.PMF.toOuterMeasure_bind_toReal, Fintype.sum_bool]
  simp_rw [Probability.PMF.toOuterMeasure_bind_toReal, Fintype.sum_bool, he]
  simp only [Bool.or_false, Bool.or_true, Bool.false_eq_true, ite_false, ite_true,
    coin, Probability.PMF.coin_apply_toReal]
  ring

section Quantum

variable [Fintype A] [Fintype B]

private def restrictStrategy {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (S : QuantumStrategy (Option X) (Option Y) A B ι κ) : QuantumStrategy X Y A B ι κ where
  state := S.state
  norm_state := S.norm_state
  alice x := S.alice (some x)
  bob y := S.bob (some y)

private noncomputable def extendStrategy {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [DecidableEq A] [DecidableEq B]
    (S : QuantumStrategy X Y A B ι κ) (a : A) (b : B) :
    QuantumStrategy (Option X) (Option Y) A B ι κ where
  state := S.state
  norm_state := S.norm_state
  alice := fun x => x.elim (Quantum.POVM.const a) S.alice
  bob := fun y => y.elim (Quantum.POVM.const b) S.bob

private theorem quantumWinProb_anchored {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (S : QuantumStrategy (Option X) (Option Y) A B ι κ) :
    (G.anchored α).quantumWinProb S =
      1 - (1 - (α : ℝ)) ^ 2 * (1 - G.quantumWinProb (restrictStrategy S)) := by
  rw [quantumWinProb, answersWinProb_anchored]
  rfl

/-- The exact entangled value of the anchored game, allowing endpoint probabilities.
This is the entangled-value identity of [Bavarian, Vidick and Yuen, Lemma 1.2]
[BavarianVidickYuen2022]. The supremum need not be attained. -/
theorem quantumValue_anchored [Nonempty A] [Nonempty B] :
    (G.anchored α).quantumValue = 1 - (1 - (α : ℝ)) ^ 2 * (1 - G.quantumValue) := by
  classical
  let H := G.anchored α
  let c := (1 - (α : ℝ)) ^ 2
  have hc : 0 ≤ c := sq_nonneg _
  have hc₁ : c ≤ 1 := by
    dsimp [c]
    nlinarith [mul_nonneg α.2.1 (sub_nonneg.mpr α.2.2)]
  have hlower {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (S : QuantumStrategy X Y A B ι κ) : 1 - c * (1 - G.quantumWinProb S) ≤ H.quantumValue := by
    simpa only [H, c, quantumWinProb_anchored, restrictStrategy, extendStrategy,
      Option.elim_some] using H.quantumWinProb_le_quantumValue
        (extendStrategy S (Classical.choice ‹Nonempty A›) (Classical.choice ‹Nonempty B›))
  let S₀ := QuantumStrategy.ofDeterministic (fun _ : X => Classical.choice ‹Nonempty A›)
    (fun _ : Y => Classical.choice ‹Nonempty B›)
  change H.quantumValue = 1 - c * (1 - G.quantumValue)
  refine le_antisymm (H.quantumValue_le ?_ ?_) ?_
  · nlinarith [mul_nonneg hc G.quantumValue_nonneg]
  · intro ι κ _ _ _ _ S
    rw [quantumWinProb_anchored]
    gcongr; exact G.quantumWinProb_le_quantumValue _
  · rcases hc.eq_or_lt with hzero | hpos
    · simpa only [← hzero, zero_mul, sub_zero] using hlower S₀
    · have hthreshold : 0 ≤ (H.quantumValue - (1 - c)) / c := by
        apply div_nonneg _ hc
        linarith [hlower S₀, mul_nonneg hc (G.quantumWinProb_nonneg S₀)]
      have hs : G.quantumValue ≤ (H.quantumValue - (1 - c)) / c :=
        G.quantumValue_le hthreshold fun S => (le_div_iff₀ hpos).mpr (by linarith [hlower S])
      linarith [(le_div_iff₀ hpos).mp hs]

/-- An anchoring probability below one preserves entangled value one in both directions. -/
theorem quantumValue_anchored_eq_one_iff [Nonempty A] [Nonempty B] (hα : (α : ℝ) < 1) :
    (G.anchored α).quantumValue = 1 ↔ G.quantumValue = 1 := by
  rw [quantumValue_anchored, sub_eq_self, mul_eq_zero,
    or_iff_right (pow_ne_zero _ (sub_pos.mpr hα).ne'), sub_eq_zero, eq_comm]

end Quantum

/-- The score of deterministic provers is transformed by the same loss factor. -/
theorem winProb_anchored (a : Option X → A) (b : Option Y → B) :
    (G.anchored α).winProb a b = 1 - (1 - (α : ℝ)) ^ 2 *
      (1 - G.winProb (fun x => a (some x)) (fun y => b (some y))) := by
  rw [← (G.anchored α).answersWinProb_pure a b, answersWinProb_anchored]
  rw [G.answersWinProb_pure (fun x => a (some x)) (fun y => b (some y))]

/-- The classical value obeys the same anchoring identity
[Bavarian, Vidick and Yuen, Lemma 1.2][BavarianVidickYuen2022]. -/
theorem value_anchored [Finite X] [Finite Y] [Finite A] [Finite B] [Nonempty A] [Nonempty B] :
    (G.anchored α).value = 1 - (1 - (α : ℝ)) ^ 2 * (1 - G.value) := by
  classical
  let H := G.anchored α
  obtain ⟨a, b, hab⟩ := H.exists_winProb_eq_value
  obtain ⟨p, q, hpq⟩ := G.exists_winProb_eq_value
  change H.value = _
  refine le_antisymm ?_ ?_
  · rw [← hab, winProb_anchored]
    gcongr
    exact G.winProb_le_value _ _
  · simpa only [H, winProb_anchored, Option.elim_some, hpq] using H.winProb_le_value
      (fun x => x.elim (Classical.choice ‹Nonempty A›) p)
      (fun y => y.elim (Classical.choice ‹Nonempty B›) q)

end Cslib.PCP.TwoProverGame
