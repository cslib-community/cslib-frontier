/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredCoordinateTraceDistance
public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredTranscriptDistance
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.StatisticalDistance.Event
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Trace deviation under an independent selected trial

Keep the states conditioned under the winning law. Draw the selected question pair and
its tagged message from the prior, independently of the winning remaining transcript.
The sum of squared trace deviations under this experiment is bounded by its value
under the winning law plus four times the summed statistical-distance cost. This is
the prior-draw and anchor comparisons used around equations (49)–(54) of
[Bavarian, Vidick and Yuen][BavarianVidickYuen2022] (arXiv:1509.07466v2, §5.2, printed pp. 26–27).
The density families are kept fixed, including the chosen defaults at null observations.

## Main results

* `priorConditionalTraceNormSq_le`: the cost of changing the averaging law.
* `leftTaggedPairConditionalTraceNormSq_le` and `rightTaggedPairConditionalTraceNormSq_le`:
  select the message tag and replace its value by the corresponding question.
* `leftTaggedPairAnchorTraceNormSq_le` and `rightTaggedPairAnchorTraceNormSq_le`:
  compare the opposite player’s question with its anchor value.
* `leftTaggedPairAnchorMissMass_le` and `rightTaggedPairAnchorMissMass_le`: the same
  statistical-distance cost bounds missing winning support at the sampled or anchored question.
-/

public section

namespace Cslib.PCP.AnchoredDependency

open Cslib.Probability.PMF
open Quantum Matrix Finset
open ParallelRepetition (Revealed Shared)
open scoped unitInterval Cslib.Probability.PMF

variable {X Y A B ι κ D U : Type*} {n m : ℕ}
variable [Fintype D] [DecidableEq D]
variable (C : Finset (Fin n))

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Info" => Revealed (Option X) (Option Y) C
local notation "Answer" => ((C → A) × (C → B))
local notation "Label" => (Info × Answer)
local notation "PairQ" => (Option X × Option Y)
local notation "Message" => (Option X ⊕ Option Y)
local notation "Rest" => Shared (Option X) (Option Y) A B C
local notation "Transcript" => ((Info × (C → A × B)) × (Free → PairQ))
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ

/-- Restore the full checked transcript by inserting the selected noisy message. -/
@[expose] def restoreCheckedTranscript (j : Free) (r : Rest j) (msg : Message) : Label :=
  (⟨r.questions, fun i => if hi : i = j then msg else r.halves ⟨i, hi⟩⟩,
    (Prod.fst ∘ r.answers, Prod.snd ∘ r.answers))

private theorem restoreCheckedTranscript_restTranscript (j : Free) (z : Transcript) :
    restoreCheckedTranscript C j (restTranscript C j z) (freeTrials C z j).1 =
      (let ((t, a), _) := z
       (t, (Prod.fst ∘ a, Prod.snd ∘ a))) := by
  rcases z with ⟨⟨⟨qs, msgs⟩, a⟩, u⟩
  have h : (fun i => if hi : i = j then msgs j
      else msgs (⟨i, hi⟩ : {k : Free // k ≠ j}).1) = msgs := by
    funext i
    by_cases hi : i = j <;> simp [hi]
  exact congrArg (fun msgs' => ((⟨qs, msgs'⟩ : Info), (Prod.fst ∘ a, Prod.snd ∘ a))) h

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable (G : TwoProverGame X Y A B) (α : I)

/-- Sum a score over independently redrawn selected trials and the remaining transcript. -/
noncomputable def priorTrialScore (Q : PMF Transcript) (read : PairQ → U) (e : Fin m ≃ Free)
    (score : Fin m → Label → U → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ z, ((priorTrialAndRest G α C Q (e i)) z).toReal *
    (let ((msg, q), r) := z
     score i (restoreCheckedTranscript C (e i) r msg) (read q))

private theorem priorTrialScore_le [Fintype U]
    (Q : PMF Transcript) (read : PairQ → U) (e : Fin m ≃ Free)
    (score : Fin m → Label → U → ℝ) {bound : ℝ}
    (hzero : ∀ i t u, 0 ≤ score i t u) (hbound : ∀ i t u, score i t u ≤ bound) :
    let P := Q.map (questionTranscriptProjection C read e)
    priorTrialScore C G α Q read e score ≤
      (∑ i : Fin m, ∑ z, (P z).toReal * score i z.1 (z.2 i)) +
      bound * ∑ j : Free, dist (Q.map fun z => (freeTrials C z j, restTranscript C j z))
        (priorTrialAndRest G α C Q j) := by
  classical
  intro P
  let J (j : Free) := Q.map fun z => (freeTrials C z j, restTranscript C j z)
  let R := priorTrialAndRest G α C Q
  let d (j : Free) := dist (J j) (R j)
  unfold priorTrialScore
  rw [← e.sum_comp d, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  let f (z : (Message × PairQ) × Rest (e i)) :=
    score i (restoreCheckedTranscript C (e i) z.2 z.1.1) (read z.1.2)
  have h := abs_sum_mul_sub_le_of_nonneg (R (e i)) (J (e i)) f
    (fun z => hzero _ _ _) (fun z => hbound _ _ _)
  rw [dist_comm] at h
  have heval : (∑ z, (J (e i) z).toReal * f z) =
      ∑ z, (P z).toReal * score i z.1 (z.2 i) := by
    simp only [J, P, sum_map_mul]
    refine sum_congr rfl fun z _ => ?_
    simp only [f, restoreCheckedTranscript_restTranscript]
    rfl
  rw [heval] at h
  exact sub_le_iff_le_add'.mp ((le_abs_self _).trans h)

/-- The squared change on an independently redrawn trial uses the same conditional
states as the winning law. The read function selects the relevant player's question. -/
noncomputable def priorConditionalTraceNormSq [Fintype U] [DecidableEq U]
    (Q : PMF Transcript) (read : PairQ → U)
    (e : Fin m ≃ Free) (ρ : Label × (Fin m → U) → Matrix D D ℂ) : ℝ :=
  let P := Q.map (questionTranscriptProjection C read e)
  priorTrialScore C G α Q read e (fun i t u => conditionalTraceNormSq P ρ t i u)

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Transfer the trace deviation to an independent prior draw of the selected trial.
The extra cost is four times the statistical-distance bound. The density family
specifies conditional states also at null labels, where the comparison only uses
that they are density matrices. -/
theorem priorConditionalTraceNormSq_le [Fintype U] [DecidableEq U] (S : RepeatedStrategy)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support)
    (read : PairQ → U) (e : Fin m ≃ Free) {ρ : Label × (Fin m → U) → Matrix D D ℂ}
    (hρ : ∀ z, IsDensityMatrix (ρ z)) :
    let T := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let Q := T.filter W hs
    let P := Q.map (questionTranscriptProjection C read e)
    let p := (T.toOuterMeasure W).toReal
    let w := (α : ℝ) ^ 2 / 2
    let ε₁ := Real.sqrt (m * Real.log (1 / p) / 2)
    let ε₂ := Real.sqrt (m * Real.log (Fintype.card (C → A × B) / p) / 2)
    w * priorConditionalTraceNormSq C G α Q read e ρ ≤
      w * sumConditionalTraceNormSq P ρ + 8 * (w * ε₁ + (1 + w) * (2 * ε₁ + ε₂)) := by
  classical
  intro T W Q P p w ε₁ ε₂
  have h := priorTrialScore_le C G α Q read e (fun i t u => conditionalTraceNormSq P ρ t i u)
    (fun _ _ _ => sq_nonneg _) (fun i t u => conditionalTraceNormSq_le_four P hρ t i u)
  dsimp only at h
  rw [← sumConditionalTraceNormSq_eq_sum_joint P ρ] at h
  have hdist := sum_dist_trial_rest_independent_given_wins G α C S hs
  have hcard : Fintype.card Free = m := (Fintype.card_congr e.symm).trans (Fintype.card_fin m)
  dsimp only at hdist
  rw [hcard] at hdist
  change w * _ ≤ 2 * (w * ε₁ + (1 + w) * (2 * ε₁ + ε₂)) at hdist
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  unfold priorConditionalTraceNormSq
  refine (mul_le_mul_of_nonneg_left h hw).trans ?_
  rw [mul_add, mul_left_comm w 4]
  apply add_le_add_right
  rw [show (8 * (w * ε₁ + (1 + w) * (2 * ε₁ + ε₂))) =
    4 * (2 * (w * ε₁ + (1 + w) * (2 * ε₁ + ε₂))) by ring]
  exact mul_le_mul_of_nonneg_left hdist (by norm_num)

/-- Evaluate a score at one coordinate under the tagged independent anchored redraw. -/
@[expose] noncomputable def taggedPairCoordinateScore (Q : PMF Transcript) (read : PairQ → U)
    (tag : PairQ → Message) (e : Fin m ≃ Free) (score : Fin m → Label → U → ℝ) (i : Fin m) : ℝ :=
  ∑ q, ((G.anchored α).questions q).toReal * ∑ r,
    ((Q.map (restTranscript C (e i))) r).toReal *
      score i (restoreCheckedTranscript C (e i) r (tag q)) (read q)

/-- Sum the coordinate scores of the independent anchored redraw. -/
@[expose] noncomputable def taggedPairScore (Q : PMF Transcript) (read : PairQ → U)
    (tag : PairQ → Message) (e : Fin m ≃ Free) (score : Fin m → Label → U → ℝ) : ℝ :=
  ∑ i, taggedPairCoordinateScore C G α Q read tag e score i

/-- A nonnegative score has nonnegative expectation at each redrawn coordinate. -/
theorem taggedPairCoordinateScore_nonneg (Q : PMF Transcript) (read : PairQ → U)
    (tag : PairQ → Message) (e : Fin m ≃ Free) (f : Fin m → Label → U → ℝ) (i : Fin m)
    (hf : ∀ t u, 0 ≤ f i t u) : 0 ≤ taggedPairCoordinateScore C G α Q read tag e f i := by
  unfold taggedPairCoordinateScore
  exact sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg
    (sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (hf _ _))

/-- The squared mean is at most the second moment at a redrawn coordinate. -/
theorem taggedPairCoordinateScore_sq_le (Q : PMF Transcript) (read : PairQ → U)
    (tag : PairQ → Message) (e : Fin m ≃ Free) (f : Fin m → Label → U → ℝ) (i : Fin m) :
    (taggedPairCoordinateScore C G α Q read tag e f i) ^ 2 ≤
      taggedPairCoordinateScore C G α Q read tag e (fun j t u => (f j t u) ^ 2) i := by
  classical
  let Samples := PairQ × Rest (e i)
  let p (z : Samples) : ℝ :=
    ((G.anchored α).questions z.1).toReal * ((Q.map (restTranscript C (e i))) z.2).toReal
  let F (z : Samples) := f i (restoreCheckedTranscript C (e i) z.2 (tag z.1)) (read z.1)
  have hp (z : Samples) : 0 ≤ p z := mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hmass : ∑ z, p z = (1 : ℝ) := by
    simp only [Samples, Fintype.sum_prod_type, p, ← mul_sum, sum_toReal, mul_one]
  have he (g : Fin m → Label → U → ℝ) :
      (∑ z : Samples, p z * g i (restoreCheckedTranscript C (e i) z.2 (tag z.1)) (read z.1)) =
      taggedPairCoordinateScore C G α Q read tag e g i := by
    simp only [Samples, Fintype.sum_prod_type, p, taggedPairCoordinateScore, mul_sum, mul_assoc]
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset Samples)
    (r := fun z => p z * F z) (f := p) (g := fun z => p z * (F z) ^ 2)
    (fun z _ => hp z) (fun z _ => mul_nonneg (hp z) (sq_nonneg _))
    (fun z _ => by ring_nf; rfl)
  rw [hmass, one_mul] at h
  simpa only [F, he f, he (fun i t u => (f i t u) ^ 2)] using h

private theorem taggedPairScore_sq_le (Q : PMF Transcript) (read : PairQ → U)
    (tag : PairQ → Message) (e : Fin m ≃ Free) (f : Fin m → Label → U → ℝ) :
    (taggedPairScore C G α Q read tag e f) ^ 2 ≤
      m * taggedPairScore C G α Q read tag e (fun i t u => (f i t u) ^ 2) := by
  classical
  let g := taggedPairCoordinateScore C G α Q read tag e f
  have h := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin m)) (fun _ => (1 : ℝ)) g
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  unfold taggedPairScore
  exact h.trans (mul_le_mul_of_nonneg_left
    (sum_le_sum fun i _ => taggedPairCoordinateScore_sq_le C G α Q read tag e f i)
    (Nat.cast_nonneg _))

/-- Average a score bounded by a main term plus a penalty. A second-moment bound on the
main term and a first-moment bound on the penalty suffice, including at zero weight. -/
theorem taggedPairScore_le_sqrt_add (Q : PMF Transcript) (read : PairQ → U)
    (tag : PairQ → Message) (e : Fin m ≃ Free) (score main penalty : Fin m → Label → U → ℝ)
    {w B M : ℝ} (hw : 0 ≤ w)
    (hpoint : ∀ i t u, score i t u ≤ main i t u + penalty i t u)
    (hB : w * taggedPairScore C G α Q read tag e (fun i t u => (main i t u) ^ 2) ≤ B)
    (hM : w * taggedPairScore C G α Q read tag e penalty ≤ M) :
    w * taggedPairScore C G α Q read tag e score ≤ Real.sqrt (m * w * B) + M := by
  classical
  have hsum : taggedPairScore C G α Q read tag e score ≤
      taggedPairScore C G α Q read tag e main + taggedPairScore C G α Q read tag e penalty := by
    unfold taggedPairScore taggedPairCoordinateScore
    simp only [mul_sum, ← sum_add_distrib, ← mul_add]
    exact sum_le_sum fun i _ => sum_le_sum fun q _ => sum_le_sum fun r _ =>
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpoint i _ _)
        ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
  have hsq := mul_le_mul_of_nonneg_left
    (taggedPairScore_sq_le C G α Q read tag e main) (sq_nonneg w)
  rw [← mul_pow] at hsq
  have hmain : w * taggedPairScore C G α Q read tag e main ≤ Real.sqrt (m * w * B) := by
    apply Real.le_sqrt_of_sq_le
    refine hsq.trans ?_
    rw [show w ^ 2 * ((m : ℝ) *
      taggedPairScore C G α Q read tag e (fun i t u => (main i t u) ^ 2)) =
      (m * w) * (w * taggedPairScore C G α Q read tag e (fun i t u => (main i t u) ^ 2)) by ring]
    exact mul_le_mul_of_nonneg_left hB (mul_nonneg (Nat.cast_nonneg _) hw)
  exact (mul_le_mul_of_nonneg_left hsum hw).trans
    ((mul_add _ _ _).le.trans (add_le_add hmain hM))

/-- Pull a constant out of the averaged tagged score. -/
theorem taggedPairScore_mul (Q : PMF Transcript) (read : PairQ → U)
    (tag : PairQ → Message) (e : Fin m ≃ Free) (f : Fin m → Label → U → ℝ) (a : ℝ) :
    taggedPairScore C G α Q read tag e (fun i t u => a * f i t u) =
      a * taggedPairScore C G α Q read tag e f := by
  simp only [taggedPairScore, taggedPairCoordinateScore, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun q _ => sum_congr rfl fun r _ => ?_
  ring


private theorem taggedPairScore_fixedTag_le_of_erase
    (Q : PMF Transcript) (read : PairQ → U) (tag : PairQ → Message) (msg : Message)
    (e : Fin m ≃ Free) (f : Fin m → Label → U → ℝ) (hf : ∀ i t u, 0 ≤ f i t u)
    (erase : PairQ → PairQ) (htag : ∀ q, tag (erase q) = msg)
    (hread : ∀ q, read (erase q) = read q)
    (hslice : ∀ g : PairQ → ℝ, (∀ q, 0 ≤ g q) →
      (α : ℝ) * (∑ q, ((G.anchored α).questions q).toReal * g (erase q)) ≤
        ∑ q, ((G.anchored α).questions q).toReal * g q) :
    (α : ℝ) * taggedPairScore C G α Q read (fun _ => msg) e f ≤
      taggedPairScore C G α Q read tag e f := by
  classical
  unfold taggedPairScore taggedPairCoordinateScore
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  let g (q : PairQ) : ℝ := ∑ r, ((Q.map (restTranscript C (e i))) r).toReal *
    f i (restoreCheckedTranscript C (e i) r (tag q)) (read q)
  have h := hslice g (fun q => sum_nonneg fun r _ =>
    mul_nonneg ENNReal.toReal_nonneg (hf _ _ _))
  simpa only [g, htag, hread] using h

/-- Holding the left message at its anchor costs one factor of the anchor rate. -/
theorem leftAnchorTagScore_le (Q : PMF Transcript) (e : Fin m ≃ Free)
    (f : Fin m → Label → Option Y → ℝ) (hf : ∀ i t u, 0 ≤ f i t u) :
    (α : ℝ) * taggedPairScore C G α Q Prod.snd (fun _ => Sum.inl none) e f ≤
      taggedPairScore C G α Q Prod.snd (Sum.inl ∘ Prod.fst) e f := by
  apply taggedPairScore_fixedTag_le_of_erase C G α Q _ _ _ e f hf
    (fun q => (none, q.2)) (fun _ => rfl) (fun _ => rfl)
  intro g hg
  rw [TwoProverGame.anchored_questions]
  exact rate_mul_sum_anchorPair_erase_left_le G.questions α α g hg

/-- Holding the right message at its anchor costs one factor of the anchor rate. -/
theorem rightAnchorTagScore_le (Q : PMF Transcript) (e : Fin m ≃ Free)
    (f : Fin m → Label → Option X → ℝ) (hf : ∀ i t u, 0 ≤ f i t u) :
    (α : ℝ) * taggedPairScore C G α Q Prod.fst (fun _ => Sum.inr none) e f ≤
      taggedPairScore C G α Q Prod.fst (Sum.inr ∘ Prod.snd) e f := by
  apply taggedPairScore_fixedTag_le_of_erase C G α Q _ _ _ e f hf
    (fun q => (q.1, none)) (fun _ => rfl) (fun _ => rfl)
  intro g hg
  rw [TwoProverGame.anchored_questions]
  exact rate_mul_sum_anchorPair_erase_right_le G.questions α α g hg

/-- Average the conditional trace deviation using an independent anchored pair, with the
noisy message set to the indicated player's question. -/
noncomputable def taggedPairConditionalTraceNormSq [Fintype U] [DecidableEq U]
    (Q : PMF Transcript) (read : PairQ → U)
    (tag : PairQ → Message) (e : Fin m ≃ Free) (ρ : Label × (Fin m → U) → Matrix D D ℂ) : ℝ :=
  let P := Q.map (questionTranscriptProjection C read e)
  taggedPairScore C G α Q read tag e (fun i t u => conditionalTraceNormSq P ρ t i u)

private theorem weighted_sum_comm {L R : Type*} [Fintype L] [Fintype R]
    (l : L → ℝ) (r : R → ℝ) (f : L → R → ℝ) :
    (∑ a, l a * ∑ b, r b * f a b) = ∑ b, r b * ∑ a, l a * f a b := by
  simp only [mul_sum]
  rw [sum_comm]
  simp only [mul_left_comm]

private theorem taggedPairScore_le_of_compare
    (Q : PMF Transcript) (read : PairQ → U) (tag : PairQ → Message)
    (e : Fin m ≃ Free) (score : Fin m → Label → U → ℝ)
    (hscore : ∀ i t u, 0 ≤ score i t u)
    (compare : ∀ (score : Message → U → ℝ), (∀ msg u, 0 ≤ score msg u) →
      ((α : ℝ) / 4) * (∑ q, ((G.anchored α).questions q).toReal * score (tag q) (read q)) ≤
        ∑ z, (law G.questions α z).toReal * score z.1 (read z.2)) :
    ((α : ℝ) / 4) * taggedPairScore C G α Q read tag e score ≤
      priorTrialScore C G α Q read e score := by
  classical
  unfold taggedPairScore taggedPairCoordinateScore priorTrialScore
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  let R := Q.map (restTranscript C (e i))
  let F (r : Rest (e i)) (msg : Message) (x : U) :=
    score i (restoreCheckedTranscript C (e i) r msg) x
  change (α : ℝ) / 4 * (∑ q, ((G.anchored α).questions q).toReal *
      ∑ r, (R r).toReal * F r (tag q) (read q)) ≤
    ∑ z, ((priorTrialAndRest G α C Q (e i)) z).toReal *
        (let ((msg, q), r) := z; F r msg (read q))
  rw [priorTrialAndRest, sum_bind_mul]
  simp only [sum_map_mul (Q.map (restTranscript C (e i)))]
  change _ ≤ ∑ z, (law G.questions α z).toReal *
    ∑ r, (R r).toReal * F r z.1 (read z.2)
  rw [weighted_sum_comm (fun q => ((G.anchored α).questions q).toReal) (fun r => (R r).toReal)
        (fun q r => F r (tag q) (read q)),
    weighted_sum_comm (fun z => (law G.questions α z).toReal) (fun r => (R r).toReal)
      (fun z r => F r z.1 (read z.2)), mul_sum]
  refine sum_le_sum fun r _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (compare (F r) (fun _ _ => hscore _ _ _)) ENNReal.toReal_nonneg

/-- Select the left tag and set its value to the corresponding question. -/
theorem leftTaggedPairScore_le (Q : PMF Transcript) (e : Fin m ≃ Free)
    (score : Fin m → Label → Option Y → ℝ)
    (hscore : ∀ i t u, 0 ≤ score i t u) :
    ((α : ℝ) / 4) * taggedPairScore C G α Q Prod.snd (Sum.inl ∘ Prod.fst) e score ≤
      priorTrialScore C G α Q Prod.snd e score := by
  apply taggedPairScore_le_of_compare C G α Q _ _ e score hscore
  intro score hs
  rw [TwoProverGame.anchored_questions]
  refine (sum_anchoredPair_le_sum_leftReveal G.questions α
    (fun q => score (.inl q.1) q.2) (fun q => hs _ _)).trans ?_
  refine sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  rcases z with ⟨m, x, y⟩
  cases m with
  | inl m => exact le_rfl
  | inr m => exact hs _ _

/-- Setting Alice's tag to her original question costs a factor at most `4 / α` relative
to the independently redrawn trial. Use Alice's density family to compare her reduced states. -/
theorem leftTaggedPairConditionalTraceNormSq_le (Q : PMF Transcript) (e : Fin m ≃ Free)
    [DecidableEq Y] (ρ : Label × (Fin m → Option Y) → Matrix D D ℂ) :
    ((α : ℝ) / 4) *
        taggedPairConditionalTraceNormSq C G α Q Prod.snd (Sum.inl ∘ Prod.fst) e ρ ≤
      priorConditionalTraceNormSq C G α Q Prod.snd e ρ := by
  unfold taggedPairConditionalTraceNormSq priorConditionalTraceNormSq
  exact leftTaggedPairScore_le C G α Q e _ (fun _ _ _ => sq_nonneg _)

/-- Select the right tag and set its value to the corresponding question. -/
theorem rightTaggedPairScore_le (Q : PMF Transcript) (e : Fin m ≃ Free)
    (score : Fin m → Label → Option X → ℝ)
    (hscore : ∀ i t u, 0 ≤ score i t u) :
    ((α : ℝ) / 4) * taggedPairScore C G α Q Prod.fst (Sum.inr ∘ Prod.snd) e score ≤
      priorTrialScore C G α Q Prod.fst e score := by
  apply taggedPairScore_le_of_compare C G α Q _ _ e score hscore
  intro score hs
  rw [TwoProverGame.anchored_questions]
  refine (sum_anchoredPair_le_sum_rightReveal G.questions α
    (fun q => score (.inr q.2) q.1) (fun q => hs _ _)).trans ?_
  refine sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  rcases z with ⟨m, x, y⟩
  cases m with
  | inl m => exact hs _ _
  | inr m => exact le_rfl

/-- Setting Bob's tag to his original question has the same cost. Use Bob's density family to
compare his reduced states. -/
theorem rightTaggedPairConditionalTraceNormSq_le (Q : PMF Transcript) (e : Fin m ≃ Free)
    [DecidableEq X] (ρ : Label × (Fin m → Option X) → Matrix D D ℂ) :
    ((α : ℝ) / 4) *
        taggedPairConditionalTraceNormSq C G α Q Prod.fst (Sum.inr ∘ Prod.snd) e ρ ≤
      priorConditionalTraceNormSq C G α Q Prod.fst e ρ := by
  unfold taggedPairConditionalTraceNormSq priorConditionalTraceNormSq
  exact rightTaggedPairScore_le C G α Q e _ (fun _ _ _ => sq_nonneg _)

/-- Average the squared trace norm between the winning-law states at the selected prior
question and at its anchor value. Both states use the same restored transcript. -/
@[expose] noncomputable def taggedPairAnchorTraceNormSq [Fintype U] [DecidableEq U]
    (Q : PMF Transcript) (read : PairQ → U)
    (tag : PairQ → Message) (anchor : U) (e : Fin m ≃ Free)
    (ρ : Label × (Fin m → U) → Matrix D D ℂ) : ℝ :=
  let P := Q.map (questionTranscriptProjection C read e)
  taggedPairScore C G α Q read tag e fun i t u =>
    let state := quantumMarginalGivenMap (conditionalSnd P t) (fun y => ρ (t, y)) (fun y => y i)
    (state u - state anchor).traceNorm ^ 2

private theorem traceNorm_sub_sq_le (M N R : Matrix D D ℂ) :
    (M - N).traceNorm ^ 2 ≤ 2 * ((M - R).traceNorm ^ 2 + (N - R).traceNorm ^ 2) := by
  have h := traceNorm_add_le (M - R) (-(N - R))
  rw [show M - R + -(N - R) = M - N by abel, traceNorm_neg] at h
  have h₀ := traceNorm_nonneg (M - N)
  have h₁ := traceNorm_nonneg (M - R)
  have h₂ := traceNorm_nonneg (N - R)
  have hsq := (sq_le_sq₀ h₀ (add_nonneg h₁ h₂)).mpr h
  nlinarith [sq_nonneg ((M - R).traceNorm - (N - R).traceNorm)]

private theorem taggedPairComparisonScore_le_of_erase
    (Q : PMF Transcript) (read : PairQ → U) (tag : PairQ → Message) (anchor : U)
    (e : Fin m ≃ Free) (score comparison : Fin m → Label → U → ℝ)
    {k : ℝ} (hk : 0 ≤ k) (hscore : ∀ i t u, 0 ≤ score i t u)
    (hcompare : ∀ i t u, comparison i t u ≤ k * (score i t u + score i t anchor))
    (erase : PairQ → PairQ) (htag : ∀ q, tag (erase q) = tag q)
    (hread : ∀ q, read (erase q) = anchor)
    (hslice : ∀ f : PairQ → ℝ, (∀ q, 0 ≤ f q) →
      (α : ℝ) * (∑ q, ((G.anchored α).questions q).toReal * f (erase q)) ≤
        ∑ q, ((G.anchored α).questions q).toReal * f q) :
    (α : ℝ) * taggedPairScore C G α Q read tag e comparison ≤
      (k * (α : ℝ) + k) * taggedPairScore C G α Q read tag e score := by
  classical
  let p := (G.anchored α).questions
  unfold taggedPairScore
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun i _ => ?_
  let R := Q.map (restTranscript C (e i))
  let f (r : Rest (e i)) (q : PairQ) :=
    score i (restoreCheckedTranscript C (e i) r (tag q)) (read q)
  let g (r : Rest (e i)) (q : PairQ) :=
    comparison i (restoreCheckedTranscript C (e i) r (tag q)) (read q)
  change (α : ℝ) * (∑ q, (p q).toReal * ∑ r, (R r).toReal * g r q) ≤
    (k * (α : ℝ) + k) * (∑ q, (p q).toReal * ∑ r, (R r).toReal * f r q)
  rw [weighted_sum_comm _ _ (fun q r => g r q),
    weighted_sum_comm _ _ (fun q r => f r q), mul_sum, mul_sum]
  refine sum_le_sum fun r _ => ?_
  rw [mul_left_comm (α : ℝ), mul_left_comm (k * (α : ℝ) + k)]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have htri (q : PairQ) : g r q ≤ k * (f r q + f r (erase q)) := by
    simpa only [f, g, htag, hread] using
      hcompare i (restoreCheckedTranscript C (e i) r (tag q)) (read q)
  have hsum : (∑ q, (p q).toReal * g r q) ≤
      k * ((∑ q, (p q).toReal * f r q) + ∑ q, (p q).toReal * f r (erase q)) := by
    simp only [mul_add, mul_sum]
    rw [← sum_add_distrib]
    refine sum_le_sum fun q _ => ?_
    exact (mul_le_mul_of_nonneg_left (htri q) ENNReal.toReal_nonneg).trans_eq (by ring)
  have hsum' := mul_le_mul_of_nonneg_left hsum α.2.1
  have herase := hslice (f r) (fun q => hscore _ _ _)
  change (α : ℝ) * (∑ q, (p q).toReal * f r (erase q)) ≤
    ∑ q, (p q).toReal * f r q at herase
  nlinarith only [hsum', mul_le_mul_of_nonneg_left herase hk]

/-- Bound a comparison against the anchored question by the separate scores at the
sampled and anchored observations, with the left tag fixed. -/
theorem leftTaggedPairComparisonScore_le
    (Q : PMF Transcript) (e : Fin m ≃ Free) (score comparison : Fin m → Label → Option Y → ℝ)
    {k : ℝ} (hk : 0 ≤ k) (hscore : ∀ i t u, 0 ≤ score i t u)
    (hcompare : ∀ i t u, comparison i t u ≤ k * (score i t u + score i t none)) :
    (α : ℝ) * taggedPairScore C G α Q Prod.snd (Sum.inl ∘ Prod.fst) e comparison ≤
      (k * (α : ℝ) + k) * taggedPairScore C G α Q Prod.snd (Sum.inl ∘ Prod.fst) e score := by
  apply taggedPairComparisonScore_le_of_erase C G α Q _ _ none e score comparison
    hk hscore hcompare (fun q => (q.1, none)) (fun _ => rfl) (fun _ => rfl)
  intro f hf
  rw [TwoProverGame.anchored_questions]
  exact rate_mul_sum_anchorPair_erase_right_le G.questions α α f hf

/-- Bound a comparison against the anchored question by the separate scores at the
sampled and anchored observations, with the right tag fixed. -/
theorem rightTaggedPairComparisonScore_le
    (Q : PMF Transcript) (e : Fin m ≃ Free) (score comparison : Fin m → Label → Option X → ℝ)
    {k : ℝ} (hk : 0 ≤ k) (hscore : ∀ i t u, 0 ≤ score i t u)
    (hcompare : ∀ i t u, comparison i t u ≤ k * (score i t u + score i t none)) :
    (α : ℝ) * taggedPairScore C G α Q Prod.fst (Sum.inr ∘ Prod.snd) e comparison ≤
      (k * (α : ℝ) + k) * taggedPairScore C G α Q Prod.fst (Sum.inr ∘ Prod.snd) e score := by
  apply taggedPairComparisonScore_le_of_erase C G α Q _ _ none e score comparison
    hk hscore hcompare (fun q => (none, q.2)) (fun _ => rfl) (fun _ => rfl)
  intro f hf
  rw [TwoProverGame.anchored_questions]
  exact rate_mul_sum_anchorPair_erase_left_le G.questions α α f hf

/-- Compare Alice's reduced states at Bob's actual/anchor questions under the prior pair
and the winning remaining transcript. The message stays set to Alice's question. -/
theorem leftTaggedPairAnchorTraceNormSq_le (Q : PMF Transcript) (e : Fin m ≃ Free)
    [DecidableEq Y] (ρ : Label × (Fin m → Option Y) → Matrix D D ℂ) :
    (α : ℝ) * taggedPairAnchorTraceNormSq C G α Q Prod.snd (Sum.inl ∘ Prod.fst) none e ρ ≤
      (2 * (α : ℝ) + 2) *
        taggedPairConditionalTraceNormSq C G α Q Prod.snd (Sum.inl ∘ Prod.fst) e ρ := by
  unfold taggedPairAnchorTraceNormSq taggedPairConditionalTraceNormSq
  exact leftTaggedPairComparisonScore_le C G α Q e _ _ (by norm_num : (0 : ℝ) ≤ 2)
    (fun _ _ _ => sq_nonneg _) (fun _ _ _ => traceNorm_sub_sq_le _ _ _)

/-- Compare Bob's reduced states at Alice's actual/anchor questions under the prior pair
and the winning remaining transcript. The message stays set to Bob's question. -/
theorem rightTaggedPairAnchorTraceNormSq_le (Q : PMF Transcript) (e : Fin m ≃ Free)
    [DecidableEq X] (ρ : Label × (Fin m → Option X) → Matrix D D ℂ) :
    (α : ℝ) * taggedPairAnchorTraceNormSq C G α Q Prod.fst (Sum.inr ∘ Prod.snd) none e ρ ≤
      (2 * (α : ℝ) + 2) *
        taggedPairConditionalTraceNormSq C G α Q Prod.fst (Sum.inr ∘ Prod.snd) e ρ := by
  unfold taggedPairAnchorTraceNormSq taggedPairConditionalTraceNormSq
  exact rightTaggedPairComparisonScore_le C G α Q e _ _ (by norm_num : (0 : ℝ) ≤ 2)
    (fun _ _ _ => sq_nonneg _) (fun _ _ _ => traceNorm_sub_sq_le _ _ _)


/-- The selected question and restored label occur together under the winning law. -/
@[expose] def WinningQuestionSupported {L : Type*} (P : PMF (L × (Fin m → U)))
    (i : Fin m) (t : L) (u : U) : Prop :=
  (t, u) ∈ (P.map fun z => (z.1, z.2 i)).support

/-- Joint support provides both support hypotheses for a winning conditional state. -/
theorem winningQuestionSupported_iff {L : Type*} (P : PMF (L × (Fin m → U)))
    (i : Fin m) (t : L) (u : U) :
    WinningQuestionSupported P i t u ↔
      t ∈ (P.map Prod.fst).support ∧ u ∈ ((conditionalSnd P t).map fun z => z i).support := by
  classical
  rw [WinningQuestionSupported, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨⟨t', z⟩, hz, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have ht : t' ∈ (P.map Prod.fst).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨(t', z), hz, rfl⟩
    exact ⟨ht, (PMF.mem_support_map_iff _ _ _).mpr
      ⟨z, (mem_support_conditionalSnd_iff P t' ht z).mpr hz, rfl⟩⟩
  · rintro ⟨ht, hu⟩
    obtain ⟨z, hz, hzi⟩ := (PMF.mem_support_map_iff _ _ _).mp hu
    exact ⟨(t, z), (mem_support_conditionalSnd_iff P t ht z).mp hz, Prod.ext rfl hzi⟩

open Classical in
/-- The indicator that a selected question or its anchor is outside joint winning support. -/
@[expose] noncomputable def winningAnchorMiss {L : Type*} (P : PMF (L × (Fin m → U)))
    (anchor : U) (i : Fin m) (t : L) (u : U) : ℝ :=
  if WinningQuestionSupported P i t u ∧ WinningQuestionSupported P i t anchor then 0 else 1

open Classical in
private noncomputable def winningQuestionMiss (P : PMF (Label × (Fin m → U)))
    (i : Fin m) (t : Label) (u : U) : ℝ :=
  if WinningQuestionSupported P i t u then 0 else 1

omit [Fintype X] [Fintype Y] [Fintype A] [Fintype B] in
private theorem winningQuestionMiss_nonneg (P : PMF (Label × (Fin m → U))) (i t u) :
    0 ≤ winningQuestionMiss C P i t u := by
  unfold winningQuestionMiss
  split <;> norm_num

omit [Fintype X] [Fintype Y] [Fintype A] [Fintype B] in
private theorem winningAnchorMiss_le (P : PMF (Label × (Fin m → U))) (anchor : U) (i t u) :
    winningAnchorMiss P anchor i t u ≤
      1 * (winningQuestionMiss C P i t u + winningQuestionMiss C P i t anchor) := by
  classical
  by_cases hu : WinningQuestionSupported P i t u <;>
    by_cases ha : WinningQuestionSupported P i t anchor <;>
    norm_num [winningAnchorMiss, winningQuestionMiss, hu, ha]

/-- Sum the probabilities of missing joint support at the sampled or anchored question
under the independent tagged redraw. The same restored transcript is used for both. -/
@[expose] noncomputable def taggedPairAnchorMissMass (Q : PMF Transcript) (read : PairQ → U)
    (tag : PairQ → Message) (anchor : U) (e : Fin m ≃ Free) : ℝ :=
  taggedPairScore C G α Q read tag e
    (winningAnchorMiss (Q.map (questionTranscriptProjection C read e)) anchor)

private theorem priorTrialScore_winningQuestionMiss_le [Finite U] (Q : PMF Transcript)
    (read : PairQ → U) (e : Fin m ≃ Free) :
    let P := Q.map (questionTranscriptProjection C read e)
    priorTrialScore C G α Q read e (winningQuestionMiss C P) ≤
      ∑ j : Free, dist (Q.map fun z => (freeTrials C z j, restTranscript C j z))
        (priorTrialAndRest G α C Q j) := by
  classical
  intro P
  let := Fintype.ofFinite U
  have h := priorTrialScore_le C G α Q read e (winningQuestionMiss C P)
    (winningQuestionMiss_nonneg C P) (bound := 1) (fun i t u => by
      unfold winningQuestionMiss
      split <;> norm_num)
  change _ ≤ (∑ i : Fin m, ∑ z, (P z).toReal * winningQuestionMiss C P i z.1 (z.2 i)) +
    1 * _ at h
  have hzero (i : Fin m) : (∑ z, (P z).toReal * winningQuestionMiss C P i z.1 (z.2 i)) = 0 := by
    refine sum_eq_zero fun z _ => ?_
    by_cases hz : z ∈ P.support
    · have ho : WinningQuestionSupported P i z.1 (z.2 i) :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨z, hz, rfl⟩
      simp [winningQuestionMiss, ho]
    · simp [(PMF.apply_eq_zero_iff _ _).mpr hz]
  simpa only [hzero, sum_const_zero, zero_add, one_mul] using h

private theorem taggedPairAnchorMissMass_le_of_scores [Finite U] (Q : PMF Transcript)
    (read : PairQ → U) (tag : PairQ → Message) (anchor : U) (e : Fin m ≃ Free)
    (hTag : let P := Q.map (questionTranscriptProjection C read e)
      ((α : ℝ) / 4) * taggedPairScore C G α Q read tag e (winningQuestionMiss C P) ≤
        priorTrialScore C G α Q read e (winningQuestionMiss C P))
    (hErase : let P := Q.map (questionTranscriptProjection C read e)
      (α : ℝ) * taggedPairAnchorMissMass C G α Q read tag anchor e ≤
        ((α : ℝ) + 1) * taggedPairScore C G α Q read tag e (winningQuestionMiss C P)) :
    ((α : ℝ) / 4) * (α : ℝ) * taggedPairAnchorMissMass C G α Q read tag anchor e ≤
      ((α : ℝ) + 1) * ∑ j : Free,
        dist (Q.map fun z => (freeTrials C z j, restTranscript C j z))
          (priorTrialAndRest G α C Q j) := by
  dsimp only at hTag hErase
  have hα : 0 ≤ (α : ℝ) := α.2.1
  have h := hTag.trans (priorTrialScore_winningQuestionMiss_le C G α Q read e)
  calc
    _ ≤ ((α : ℝ) / 4) * (((α : ℝ) + 1) *
        taggedPairScore C G α Q read tag e
          (winningQuestionMiss C (Q.map (questionTranscriptProjection C read e)))) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hErase (by positivity)
    _ ≤ _ := by
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left h (by positivity)

/-- For Alice's marginal, the mass of missing support under the tagged redraw and its
Bob-anchor comparison is bounded by the summed prior-trial statistical-distance cost. -/
theorem leftTaggedPairAnchorMissMass_le (Q : PMF Transcript) (e : Fin m ≃ Free) :
    ((α : ℝ) / 4) * (α : ℝ) *
        taggedPairAnchorMissMass C G α Q Prod.snd (Sum.inl ∘ Prod.fst) none e ≤
      ((α : ℝ) + 1) * ∑ j : Free,
        dist (Q.map fun z => (freeTrials C z j, restTranscript C j z))
          (priorTrialAndRest G α C Q j) := by
  let P := Q.map (questionTranscriptProjection C Prod.snd e)
  have hTag := leftTaggedPairScore_le C G α Q e _ (winningQuestionMiss_nonneg C P)
  have hErase := leftTaggedPairComparisonScore_le C G α Q e _ (winningAnchorMiss P none)
    (by norm_num : (0 : ℝ) ≤ 1) (winningQuestionMiss_nonneg C P) (winningAnchorMiss_le C P none)
  exact taggedPairAnchorMissMass_le_of_scores C G α Q _ _ none e hTag
    (by simpa only [one_mul, taggedPairAnchorMissMass, P] using hErase)

/-- For Bob's marginal, the same bound holds after exchanging the tags and players. -/
theorem rightTaggedPairAnchorMissMass_le (Q : PMF Transcript) (e : Fin m ≃ Free) :
    ((α : ℝ) / 4) * (α : ℝ) *
        taggedPairAnchorMissMass C G α Q Prod.fst (Sum.inr ∘ Prod.snd) none e ≤
      ((α : ℝ) + 1) * ∑ j : Free,
        dist (Q.map fun z => (freeTrials C z j, restTranscript C j z))
          (priorTrialAndRest G α C Q j) := by
  let P := Q.map (questionTranscriptProjection C Prod.fst e)
  have hTag := rightTaggedPairScore_le C G α Q e _ (winningQuestionMiss_nonneg C P)
  have hErase := rightTaggedPairComparisonScore_le C G α Q e _ (winningAnchorMiss P none)
    (by norm_num : (0 : ℝ) ≤ 1) (winningQuestionMiss_nonneg C P) (winningAnchorMiss_le C P none)
  exact taggedPairAnchorMissMass_le_of_scores C G α Q _ _ none e hTag
    (by simpa only [one_mul, taggedPairAnchorMissMass, P] using hErase)

end Cslib.PCP.AnchoredDependency
