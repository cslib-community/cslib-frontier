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
import CslibFrontier.Probability.StatisticalDistance

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
-/

public section

namespace Cslib.PCP.AnchoredDependency

open Cslib.Probability.PMF
open Quantum Matrix Finset
open ParallelRepetition (Revealed Shared)
open scoped unitInterval Cslib.Probability.PMF

variable {X Y A B ι κ D U : Type*} {n m : ℕ}
variable [Fintype D] [DecidableEq D] [Fintype U] [DecidableEq U]
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

/-- The squared change on an independently redrawn trial uses the same conditional
states as the winning law. The read function selects the relevant player's question. -/
noncomputable def priorConditionalTraceNormSq (Q : PMF Transcript) (read : PairQ → U)
    (e : Fin m ≃ Free) (ρ : Label × (Fin m → U) → Matrix D D ℂ) : ℝ :=
  let P := Q.map (questionTranscriptProjection C read e)
  ∑ i : Fin m, ∑ z, ((priorTrialAndRest G α C Q (e i)) z).toReal *
    (let ((msg, q), r) := z
     conditionalTraceNormSq P ρ (restoreCheckedTranscript C (e i) r msg) i (read q))

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Transfer the trace deviation to an independent prior draw of the selected trial.
The extra cost is four times the statistical-distance bound. The density family
specifies conditional states also at null labels, where the comparison only uses
that they are density matrices. -/
theorem priorConditionalTraceNormSq_le (S : RepeatedStrategy)
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
  let J (j : Free) := Q.map fun z => (freeTrials C z j, restTranscript C j z)
  let R := priorTrialAndRest G α C Q
  let d (j : Free) := dist (J j) (R j)
  let score (i : Fin m) (z : (Message × PairQ) × Rest (e i)) : ℝ :=
    let ((msg, q), r) := z
    conditionalTraceNormSq P ρ (restoreCheckedTranscript C (e i) r msg) i (read q)
  have hscore (i : Fin m) (z : (Message × PairQ) × Rest (e i)) : |score i z - 2| ≤ 2 := by
    rcases z with ⟨⟨msg, q⟩, r⟩
    have hfour := conditionalTraceNormSq_le_four P hρ
      (restoreCheckedTranscript C (e i) r msg) i (read q)
    have hzero : 0 ≤ score i ((msg, q), r) := sq_nonneg _
    change score i ((msg, q), r) ≤ 4 at hfour
    rw [abs_le]
    constructor <;> linarith
  have htransport (i : Fin m) :
      (∑ z, (R (e i) z).toReal * score i z) ≤
        (∑ z, (J (e i) z).toReal * score i z) + 4 * d (e i) := by
    have h := abs_sum_mul_sub_le (R (e i)) (J (e i)) (fun z => score i z - 2) (hscore i)
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, sum_toReal, one_mul,
      sub_sub_sub_cancel_right] at h
    rw [dist_comm] at h
    linarith [(le_abs_self _).trans h]
  have heval (i : Fin m) :
      (∑ z, (J (e i) z).toReal * score i z) =
        ∑ z, (P z).toReal * conditionalTraceNormSq P ρ z.1 i (z.2 i) := by
    simp only [J, P, sum_map_mul]
    refine sum_congr rfl fun z _ => ?_
    simp only [score, restoreCheckedTranscript_restTranscript]
    rfl
  have hcard : Fintype.card Free = m := by simpa using Fintype.card_congr e.symm
  have hdist : w * (∑ i : Fin m, d (e i)) ≤
      2 * (w * ε₁ + (1 + w) * (2 * ε₁ + ε₂)) := by
    rw [e.sum_comp d]
    have h := sum_dist_trial_rest_independent_given_wins G α C S hs
    simp only at h
    rw [hcard] at h
    exact h
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hsum := mul_le_mul_of_nonneg_left (sum_le_sum fun i (_ : i ∈ univ) => htransport i) hw
  simp only [heval, sum_add_distrib, ← mul_sum,
    ← sumConditionalTraceNormSq_eq_sum_joint P ρ] at hsum
  change w * (∑ i : Fin m, ∑ z, (R (e i) z).toReal * score i z) ≤ _
  linarith

/-- Average over the anchored question pair and the remaining winning transcript, setting
the noisy message to the indicated player's question. -/
noncomputable def taggedPairConditionalTraceNormSq (Q : PMF Transcript) (read : PairQ → U)
    (tag : PairQ → Message) (e : Fin m ≃ Free) (ρ : Label × (Fin m → U) → Matrix D D ℂ) : ℝ :=
  let P := Q.map (questionTranscriptProjection C read e)
  ∑ i : Fin m, ∑ q, ((G.anchored α).questions q).toReal * ∑ r,
    ((Q.map (restTranscript C (e i))) r).toReal *
      conditionalTraceNormSq P ρ (restoreCheckedTranscript C (e i) r (tag q)) i (read q)

private theorem weighted_sum_comm {L R : Type*} [Fintype L] [Fintype R]
    (l : L → ℝ) (r : R → ℝ) (f : L → R → ℝ) :
    (∑ a, l a * ∑ b, r b * f a b) = ∑ b, r b * ∑ a, l a * f a b := by
  simp only [mul_sum]
  rw [sum_comm]
  simp only [mul_left_comm]

private theorem taggedPairConditionalTraceNormSq_le_of_scores
    (Q : PMF Transcript) (read : PairQ → U) (tag : PairQ → Message)
    (e : Fin m ≃ Free) (ρ : Label × (Fin m → U) → Matrix D D ℂ)
    (compare : ∀ (score : Message → U → ℝ), (∀ msg u, 0 ≤ score msg u) →
      ((α : ℝ) / 4) * (∑ q, ((G.anchored α).questions q).toReal * score (tag q) (read q)) ≤
        ∑ z, (law G.questions α z).toReal * score z.1 (read z.2)) :
    ((α : ℝ) / 4) * taggedPairConditionalTraceNormSq C G α Q read tag e ρ ≤
      priorConditionalTraceNormSq C G α Q read e ρ := by
  classical
  let P := Q.map (questionTranscriptProjection C read e)
  unfold taggedPairConditionalTraceNormSq priorConditionalTraceNormSq
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  let R := Q.map (restTranscript C (e i))
  let F (r : Rest (e i)) (msg : Message) (x : U) :=
    conditionalTraceNormSq P ρ (restoreCheckedTranscript C (e i) r msg) i x
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
  exact mul_le_mul_of_nonneg_left (compare (F r) (fun _ _ => sq_nonneg _)) ENNReal.toReal_nonneg

/-- Setting Alice's tag to her original question costs a factor at most `4 / α` relative
to the independently redrawn trial. Use Alice's density family to compare her reduced states. -/
theorem leftTaggedPairConditionalTraceNormSq_le (Q : PMF Transcript) (e : Fin m ≃ Free)
    [DecidableEq Y] (ρ : Label × (Fin m → Option Y) → Matrix D D ℂ) :
    ((α : ℝ) / 4) *
        taggedPairConditionalTraceNormSq C G α Q Prod.snd (Sum.inl ∘ Prod.fst) e ρ ≤
      priorConditionalTraceNormSq C G α Q Prod.snd e ρ := by
  apply taggedPairConditionalTraceNormSq_le_of_scores
  intro score hs
  rw [TwoProverGame.anchored_questions]
  refine (sum_anchoredPair_le_sum_leftReveal G.questions α
    (fun q => score (.inl q.1) q.2) (fun q => hs _ _)).trans ?_
  refine sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  rcases z with ⟨m, x, y⟩
  cases m with
  | inl m => exact le_rfl
  | inr m => exact hs _ _

/-- Setting Bob's tag to his original question has the same cost. Use Bob's density family to
compare his reduced states. -/
theorem rightTaggedPairConditionalTraceNormSq_le (Q : PMF Transcript) (e : Fin m ≃ Free)
    [DecidableEq X] (ρ : Label × (Fin m → Option X) → Matrix D D ℂ) :
    ((α : ℝ) / 4) *
        taggedPairConditionalTraceNormSq C G α Q Prod.fst (Sum.inr ∘ Prod.snd) e ρ ≤
      priorConditionalTraceNormSq C G α Q Prod.fst e ρ := by
  apply taggedPairConditionalTraceNormSq_le_of_scores
  intro score hs
  rw [TwoProverGame.anchored_questions]
  refine (sum_anchoredPair_le_sum_rightReveal G.questions α
    (fun q => score (.inr q.2) q.1) (fun q => hs _ _)).trans ?_
  refine sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  rcases z with ⟨m, x, y⟩
  cases m with
  | inl m => exact hs _ _
  | inr m => exact le_rfl

/-- Average the squared trace norm between the winning-law states at the selected prior
question and at its anchor value. Both states use the same restored transcript. -/
noncomputable def taggedPairAnchorTraceNormSq (Q : PMF Transcript) (read : PairQ → U)
    (tag : PairQ → Message) (anchor : U) (e : Fin m ≃ Free)
    (ρ : Label × (Fin m → U) → Matrix D D ℂ) : ℝ :=
  let P := Q.map (questionTranscriptProjection C read e)
  ∑ i : Fin m, ∑ q, ((G.anchored α).questions q).toReal * ∑ r,
    let t := restoreCheckedTranscript C (e i) r (tag q)
    let state := quantumMarginalGivenMap (conditionalSnd P t) (fun y => ρ (t, y)) (fun y => y i)
    ((Q.map (restTranscript C (e i))) r).toReal * (state (read q) - state anchor).traceNorm ^ 2

private theorem traceNorm_sub_sq_le (M N R : Matrix D D ℂ) :
    (M - N).traceNorm ^ 2 ≤ 2 * ((M - R).traceNorm ^ 2 + (N - R).traceNorm ^ 2) := by
  have h := traceNorm_add_le (M - R) (-(N - R))
  rw [show M - R + -(N - R) = M - N by abel, traceNorm_neg] at h
  have h₀ := traceNorm_nonneg (M - N)
  have h₁ := traceNorm_nonneg (M - R)
  have h₂ := traceNorm_nonneg (N - R)
  have hsq := (sq_le_sq₀ h₀ (add_nonneg h₁ h₂)).mpr h
  nlinarith [sq_nonneg ((M - R).traceNorm - (N - R).traceNorm)]

private theorem taggedPairAnchorTraceNormSq_le_of_erase
    (Q : PMF Transcript) (read : PairQ → U) (tag : PairQ → Message) (anchor : U)
    (e : Fin m ≃ Free) (ρ : Label × (Fin m → U) → Matrix D D ℂ)
    (erase : PairQ → PairQ) (htag : ∀ q, tag (erase q) = tag q)
    (hread : ∀ q, read (erase q) = anchor)
    (hslice : ∀ f : PairQ → ℝ, (∀ q, 0 ≤ f q) →
      (α : ℝ) * (∑ q, ((G.anchored α).questions q).toReal * f (erase q)) ≤
        ∑ q, ((G.anchored α).questions q).toReal * f q) :
    (α : ℝ) * taggedPairAnchorTraceNormSq C G α Q read tag anchor e ρ ≤
      (2 * (α : ℝ) + 2) * taggedPairConditionalTraceNormSq C G α Q read tag e ρ := by
  classical
  let P := Q.map (questionTranscriptProjection C read e)
  let p := (G.anchored α).questions
  unfold taggedPairAnchorTraceNormSq taggedPairConditionalTraceNormSq
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun i _ => ?_
  let R := Q.map (restTranscript C (e i))
  let f (r : Rest (e i)) (q : PairQ) :=
    conditionalTraceNormSq P ρ (restoreCheckedTranscript C (e i) r (tag q)) i (read q)
  let g (r : Rest (e i)) (q : PairQ) :=
    let t := restoreCheckedTranscript C (e i) r (tag q)
    let state := quantumMarginalGivenMap (conditionalSnd P t) (fun y => ρ (t, y)) (fun y => y i)
    (state (read q) - state anchor).traceNorm ^ 2
  change (α : ℝ) * (∑ q, (p q).toReal * ∑ r, (R r).toReal * g r q) ≤
    (2 * (α : ℝ) + 2) * (∑ q, (p q).toReal * ∑ r, (R r).toReal * f r q)
  rw [weighted_sum_comm _ _ (fun q r => g r q),
    weighted_sum_comm _ _ (fun q r => f r q), mul_sum, mul_sum]
  refine sum_le_sum fun r _ => ?_
  rw [mul_left_comm (α : ℝ), mul_left_comm (2 * (α : ℝ) + 2)]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have htri (q : PairQ) : g r q ≤ 2 * (f r q + f r (erase q)) := by
    simp only [f, htag, hread, g, conditionalTraceNormSq]
    exact traceNorm_sub_sq_le _ _ _
  have hsum : (∑ q, (p q).toReal * g r q) ≤
      2 * ((∑ q, (p q).toReal * f r q) + ∑ q, (p q).toReal * f r (erase q)) := by
    simp only [mul_add, mul_sum]
    rw [← sum_add_distrib]
    refine sum_le_sum fun q _ => ?_
    exact (mul_le_mul_of_nonneg_left (htri q) ENNReal.toReal_nonneg).trans_eq (by ring)
  have hsum' := mul_le_mul_of_nonneg_left hsum α.2.1
  have herase := hslice (f r) (fun q => sq_nonneg _)
  change (α : ℝ) * (∑ q, (p q).toReal * f r (erase q)) ≤
    ∑ q, (p q).toReal * f r q at herase
  linarith

/-- Compare Alice's reduced states at Bob's actual/anchor questions under the prior pair
and the winning remaining transcript. The message stays set to Alice's question. -/
theorem leftTaggedPairAnchorTraceNormSq_le (Q : PMF Transcript) (e : Fin m ≃ Free)
    [DecidableEq Y] (ρ : Label × (Fin m → Option Y) → Matrix D D ℂ) :
    (α : ℝ) * taggedPairAnchorTraceNormSq C G α Q Prod.snd (Sum.inl ∘ Prod.fst) none e ρ ≤
      (2 * (α : ℝ) + 2) *
        taggedPairConditionalTraceNormSq C G α Q Prod.snd (Sum.inl ∘ Prod.fst) e ρ := by
  apply taggedPairAnchorTraceNormSq_le_of_erase C G α Q Prod.snd (Sum.inl ∘ Prod.fst) none e ρ
    (fun q => (q.1, none)) (fun _ => rfl) (fun _ => rfl)
  intro f hf
  rw [TwoProverGame.anchored_questions]
  exact rate_mul_sum_anchorPair_erase_right_le G.questions α α f hf

/-- Compare Bob's reduced states at Alice's actual/anchor questions under the prior pair
and the winning remaining transcript. The message stays set to Bob's question. -/
theorem rightTaggedPairAnchorTraceNormSq_le (Q : PMF Transcript) (e : Fin m ≃ Free)
    [DecidableEq X] (ρ : Label × (Fin m → Option X) → Matrix D D ℂ) :
    (α : ℝ) * taggedPairAnchorTraceNormSq C G α Q Prod.fst (Sum.inr ∘ Prod.snd) none e ρ ≤
      (2 * (α : ℝ) + 2) *
        taggedPairConditionalTraceNormSq C G α Q Prod.fst (Sum.inr ∘ Prod.snd) e ρ := by
  apply taggedPairAnchorTraceNormSq_le_of_erase C G α Q Prod.fst (Sum.inr ∘ Prod.snd) none e ρ
    (fun q => (none, q.2)) (fun _ => rfl) (fun _ => rfl)
  intro f hf
  rw [TwoProverGame.anchored_questions]
  exact rate_mul_sum_anchorPair_erase_left_le G.questions α α f hf

end Cslib.PCP.AnchoredDependency
