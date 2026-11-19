/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredNoisyStates
public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredTranscriptDistance
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.AnchorPair
import CslibFrontier.Probability.PMF.Map

/-!
# Normalization weights of the checked branches

For a selected question pair and a retained transcript, the remaining transcript kernel
has mass equal to the prior retained-question mass times the squared checked-branch norm.
The anchor-weighted squared error in the ratio of branch norms is bounded by the absolute
difference of these kernel masses.

This is the unnormalized comparison used in
[Bavarian, Vidick and Yuen, Lemma 5.17][BavarianVidickYuen2022]
(arXiv:1509.07466v2, §5.3, printed pp. 28–30).

## Main results

* `restKernel_apply_toReal_eq_norm_sq`: exact joint weight of a checked branch.
* `weightedAnchorRestScore_eq_winMass_mul`: convert the weighted score to the conditional mean.
* `anchorBranchNorm_pos_of_mem_support`: validity of the denominator on winning anchor draws.
* `sum_restNormalizationRatioLoss_le`: summed two-anchor-weighted comparison for the
  ordinary branch.
* `sum_leftNoisyNormalizationRatioLoss_le`: the corresponding noisy-branch bound.
-/

public section

namespace Cslib.PCP.AnchoredDependency

open Cslib.Probability.PMF
open ParallelRepetition (Revealed Shared)
open Finset
open scoped unitInterval

variable {X Y A B ι κ : Type*} {n : ℕ}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (G : TwoProverGame X Y A B) (α : I) (C : Finset (Fin n))

local notation "Free" => {i : Fin n // i ∉ C}
local notation "PairQ" => (Option X × Option Y)
local notation "Rest" => Shared (Option X) (Option Y) A B C
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ

private theorem restKernel_apply_eq (S : RepeatedStrategy) (j : Free) (q : PairQ)
    (r : Rest j) :
    restKernel G α C S j q r = restQuestionsLaw G α C j (restQuestions C j r) *
      answersGivenRest G α C S j (restQuestions C j r) q r.answers := by
  let f (r : Rest j) := (restQuestions C j r, r.answers)
  have h := map_apply_of_injective (restKernel G α C S j q)
    (restQuestions_answers_injective C j) r
  change ((restKernel G α C S j q).map f) (f r) = _ at h
  rw [show (restKernel G α C S j q).map f =
      (restQuestionsLaw G α C j).bind (fun t =>
        (answersGivenRest G α C S j t q).map (t, ·)) from map_restKernel_eq_bind G α C S j q,
    bind_map_prodMk_apply] at h
  exact h.symm

/-- The remaining transcript has its prior question weight times the squared branch norm.
At a null retained-question label both sides vanish. -/
theorem restKernel_apply_toReal_eq_norm_sq (S : RepeatedStrategy) (j : Free) (q : PairQ)
    (r : Rest j) :
    (restKernel G α C S j q r).toReal =
      (restQuestionsLaw G α C j (restQuestions C j r)).toReal *
        ‖checkedVectorGivenRest G α C S j (restQuestions C j r) q
          (Prod.fst ∘ r.answers) (Prod.snd ∘ r.answers)‖ ^ 2 := by
  rw [restKernel_apply_eq, ENNReal.toReal_mul]
  by_cases ht : restQuestions C j r ∈ (restQuestionsLaw G α C j).support
  · rw [norm_checkedVectorGivenRest_sq_answers G α C S j _ q _ _ ht]
    rfl
  · rw [(PMF.apply_eq_zero_iff _ _).mpr ht, ENNReal.toReal_zero, zero_mul, zero_mul]

private theorem sq_ratio_le_abs_sq_sub (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y ^ 2 * (1 - x / y) ^ 2 ≤ |x ^ 2 - y ^ 2| := by
  by_cases hzero : y = 0
  · simp [hzero, sq_nonneg]
  rw [show y ^ 2 * (1 - x / y) ^ 2 = (y - x) ^ 2 by field_simp]
  by_cases hxy : x ≤ y
  · rw [abs_of_nonpos (sub_nonpos.mpr ((sq_le_sq₀ hx hy).mpr hxy))]
    nlinarith only [mul_nonneg hx (sub_nonneg.mpr hxy)]
  · have hyx := (lt_of_not_ge hxy).le
    rw [abs_of_nonneg (sub_nonneg.mpr ((sq_le_sq₀ hy hx).mpr hyx))]
    nlinarith only [mul_nonneg hy (sub_nonneg.mpr hyx)]

/-- Score the prior question pair against the unnormalized two-anchor winning transcript. -/
@[expose] noncomputable def weightedAnchorRestScore (S : RepeatedStrategy) (j : Free)
    (score : PairQ → Rest j → ℝ) : ℝ :=
  open Classical in
  ∑ q, (((law G.questions α).map Prod.snd) q).toReal *
    ∑ r ∈ univ.filter (· ∈ winsOnRest G α C j),
      (restKernel G α C S j (none, none) r).toReal * score q r

/-- A nonnegative score has nonnegative two-anchor winning weight. -/
theorem weightedAnchorRestScore_nonneg (S : RepeatedStrategy) (j : Free)
    (score : PairQ → Rest j → ℝ) (h : ∀ q r, 0 ≤ score q r) :
    0 ≤ weightedAnchorRestScore G α C S j score := by
  unfold weightedAnchorRestScore
  exact sum_nonneg fun q _ => mul_nonneg ENNReal.toReal_nonneg
    (sum_nonneg fun r _ => mul_nonneg ENNReal.toReal_nonneg (h q r))

/-- Recover the conditional expectation by dividing by the two-anchor win probability,
when this conditioning is supported. -/
theorem weightedAnchorRestScore_eq_winMass_mul (S : RepeatedStrategy) (j : Free)
    (hwin : ∃ r ∈ winsOnRest G α C j, r ∈ (restKernel G α C S j (none, none)).support)
    (score : PairQ → Rest j → ℝ) :
    let K := restKernel G α C S j (none, none)
    let W := winsOnRest G α C j
    weightedAnchorRestScore G α C S j score =
      (K.toOuterMeasure W).toReal *
        ∑ q, (((law G.questions α).map Prod.snd) q).toReal *
          ∑ r, ((K.filter W hwin) r).toReal * score q r := by
  classical
  intro K W
  let p := (K.toOuterMeasure W).toReal
  have hp : 0 < p := (toOuterMeasure_toReal_pos_iff K W).mpr hwin
  unfold weightedAnchorRestScore
  rw [mul_sum]
  refine sum_congr rfl fun q _ => ?_
  rw [mul_left_comm p]
  apply congrArg ((((law G.questions α).map Prod.snd) q).toReal * ·)
  rw [mul_sum, sum_filter]
  refine sum_congr rfl fun r _ => ?_
  change (if r ∈ W then (K r).toReal * score q r else 0) =
    p * (((K.filter W hwin) r).toReal * score q r)
  rw [filter_apply_toReal]
  change _ = p * ((if r ∈ W then (K r).toReal / p else 0) * score q r)
  by_cases hr : r ∈ W
  · rw [ite_eq_left hr, ite_eq_left hr, ← mul_assoc, mul_comm p, div_mul_cancel₀ _ hp.ne']
  · simp only [hr, ite_false, zero_mul, mul_zero]

/-- Dividing by positive two-anchor win mass gives the ordinary conditional mean. -/
theorem weightedAnchorRestScore_div_winMass (S : RepeatedStrategy) (j : Free)
    (hwin : ∃ r ∈ winsOnRest G α C j, r ∈ (restKernel G α C S j (none, none)).support)
    (score : PairQ → Rest j → ℝ) :
    let K := restKernel G α C S j (none, none)
    let W := winsOnRest G α C j
    weightedAnchorRestScore G α C S j score / anchorWinProbability G α C S j =
      ∑ q, (((law G.questions α).map Prod.snd) q).toReal *
        ∑ r, ((K.filter W hwin) r).toReal * score q r := by
  intro K W
  have hp : 0 < anchorWinProbability G α C S j := (toOuterMeasure_toReal_pos_iff K W).mpr hwin
  apply (div_eq_iff hp.ne').mpr
  rw [mul_comm]
  exact weightedAnchorRestScore_eq_winMass_mul G α C S j hwin score

/-- A sampled two-anchor winning transcript has a nonzero anchor branch norm. -/
theorem anchorBranchNorm_pos_of_mem_support (S : RepeatedStrategy) (j : Free)
    (hwin : ∃ r ∈ winsOnRest G α C j, r ∈ (restKernel G α C S j (none, none)).support)
    (r : Rest j)
    (hr : r ∈ ((restKernel G α C S j (none, none)).filter (winsOnRest G α C j) hwin).support) :
    0 < ‖checkedVectorGivenRest G α C S j (restQuestions C j r) (none, none)
      (Prod.fst ∘ r.answers) (Prod.snd ∘ r.answers)‖ := by
  rw [PMF.support_filter] at hr
  have hm := ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hr.2) (PMF.apply_ne_top _ _)
  rw [restKernel_apply_toReal_eq_norm_sq] at hm
  refine lt_of_le_of_ne (norm_nonneg _) fun hzero => ?_
  rw [← hzero, zero_pow (by decide), mul_zero] at hm
  exact (lt_irrefl _ hm)

/-- The two-anchor-weighted squared error in the ratio of ordinary branch norms, summed
over winning remaining transcripts and averaged over the selected prior questions. -/
@[expose] noncomputable def restNormalizationRatioLoss (S : RepeatedStrategy) (j : Free) : ℝ :=
  weightedAnchorRestScore G α C S j fun q r =>
    let normAt (q' : PairQ) := ‖checkedVectorGivenRest G α C S j (restQuestions C j r)
      q' (Prod.fst ∘ r.answers) (Prod.snd ∘ r.answers)‖
    (1 - normAt q / normAt (none, none)) ^ 2

private theorem restNormalizationRatioLoss_le (S : RepeatedStrategy) (j : Free) :
    restNormalizationRatioLoss G α C S j ≤ restKernelWinL1 G α C S j := by
  classical
  unfold restNormalizationRatioLoss weightedAnchorRestScore restKernelWinL1
  refine sum_le_sum fun q _ => mul_le_mul_of_nonneg_left
    (sum_le_sum fun r _ => ?_) ENNReal.toReal_nonneg
  let normAt (q' : PairQ) := ‖checkedVectorGivenRest G α C S j (restQuestions C j r)
    q' (Prod.fst ∘ r.answers) (Prod.snd ∘ r.answers)‖
  let mass := (restQuestionsLaw G α C j (restQuestions C j r)).toReal
  have h (q' : PairQ) : (restKernel G α C S j q' r).toReal = mass * normAt q' ^ 2 :=
    restKernel_apply_toReal_eq_norm_sq G α C S j q' r
  dsimp only
  rw [h q, h (none, none), mul_assoc, ← mul_sub, abs_mul,
    abs_of_nonneg (show 0 ≤ mass from ENNReal.toReal_nonneg)]
  exact mul_le_mul_of_nonneg_left (sq_ratio_le_abs_sq_sub _ _ (norm_nonneg _) (norm_nonneg _))
    ENNReal.toReal_nonneg

/-- Summed squared comparison of the ordinary branch normalization weights. Multiplying by
the two-anchor win probability gives the unnormalized expectation used here. -/
theorem sum_restNormalizationRatioLoss_le (S : RepeatedStrategy)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support) :
    let T := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let p := (T.toOuterMeasure W).toReal
    let w := (α : ℝ) ^ 2 / 2
    let ε₁ := Real.sqrt (Fintype.card Free * Real.log (1 / p) / 2)
    let ε₂ := Real.sqrt (Fintype.card Free * Real.log (Fintype.card (C → A × B) / p) / 2)
    w * (∑ j : Free, restNormalizationRatioLoss G α C S j) ≤
      p * ((2 * w + 1 / 2) * ε₁ + 2 * ((1 + w) * (2 * ε₁ + ε₂))) := by
  intro T W p w ε₁ ε₂
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  exact (mul_le_mul_of_nonneg_left
    (sum_le_sum fun j _ => restNormalizationRatioLoss_le G α C S j) hw).trans
    (sum_restKernelWinL1_le G α C S hs)


/-- The two-anchor-weighted squared ratio error for the noisy left-tagged branch. -/
@[expose] noncomputable def leftNoisyNormalizationRatioLoss (S : RepeatedStrategy) (j : Free) : ℝ :=
  weightedAnchorRestScore G α C S j fun q r =>
    let (x, y) := q
    let t := restQuestions C j r
    let a := Prod.fst ∘ r.answers
    let b := Prod.snd ∘ r.answers
    let v := checkedVectorGivenBob G α C S j t (.inl x) y a b
    let v₀ := checkedVectorGivenRest G α C S j t (none, none) a b
    (1 - ‖v‖ / ‖v₀‖) ^ 2

private theorem noisyRatioPoint_le (S : RepeatedStrategy) (j : Free) (q : PairQ)
    (r : Rest j) :
    let (x, y) := q
    let t := restQuestions C j r
    let a := Prod.fst ∘ r.answers
    let b := Prod.snd ∘ r.answers
    let v := checkedVectorGivenBob G α C S j t (.inl x) y a b
    let v₀ := checkedVectorGivenRest G α C S j t (none, none) a b
    let K := restKernel G α C S j
    (K (none, none) r).toReal * (1 - ‖v‖ / ‖v₀‖) ^ 2 ≤
      |(K q r).toReal - (K (none, none) r).toReal| +
        |(K (none, y) r).toReal - (K (none, none) r).toReal| := by
  rcases q with ⟨x, y⟩
  dsimp (config := { zeta := false }) only
  intro t a b v v₀ K
  let mass := (restQuestionsLaw G α C j t).toReal
  let β := (noise α : ℝ)
  have hβ : 0 ≤ β := (noise α).2.1
  have hβ₁ : β ≤ 1 := (noise α).2.2
  have hm : 0 ≤ mass := ENNReal.toReal_nonneg
  have h₀ : (K (none, none) r).toReal = mass * ‖v₀‖ ^ 2 :=
    restKernel_apply_toReal_eq_norm_sq G α C S j (none, none) r
  have hmix : mass * ‖v‖ ^ 2 =
      β * (K (none, y) r).toReal + (1 - β) * (K (x, y) r).toReal := by
    change mass * ‖checkedVectorGivenBob G α C S j t (.inl x) y a b‖ ^ 2 = _
    rw [norm_checkedVectorGivenBob_sq_inl]
    rw [show (K (none, y) r).toReal = mass *
        ‖checkedVectorGivenRest G α C S j t (none, y) a b‖ ^ 2 from
        restKernel_apply_toReal_eq_norm_sq G α C S j (none, y) r,
      show (K (x, y) r).toReal = mass *
        ‖checkedVectorGivenRest G α C S j t (x, y) a b‖ ^ 2 from
        restKernel_apply_toReal_eq_norm_sq G α C S j (x, y) r]
    change mass * (β * _ + (1 - β) * _) = _
    ring
  calc
    _ ≤ |mass * ‖v‖ ^ 2 - (K (none, none) r).toReal| := by
      rw [h₀, mul_assoc, ← mul_sub, abs_mul, abs_of_nonneg hm]
      exact mul_le_mul_of_nonneg_left
        (sq_ratio_le_abs_sq_sub _ _ (norm_nonneg _) (norm_nonneg _)) hm
    _ = |(1 - β) * ((K (x, y) r).toReal - (K (none, none) r).toReal) +
        β * ((K (none, y) r).toReal - (K (none, none) r).toReal)| := by
      rw [hmix]
      congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hβ₁), abs_of_nonneg hβ]
      exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) (by linarith only [hβ]))
        (mul_le_of_le_one_left (abs_nonneg _) hβ₁))

private theorem leftNoisyNormalizationRatioLoss_le (S : RepeatedStrategy) (j : Free) :
    (α : ℝ) * leftNoisyNormalizationRatioLoss G α C S j ≤
      ((α : ℝ) + 1) * restKernelWinL1 G α C S j := by
  classical
  let μ := (law G.questions α).map Prod.snd
  let E := univ.filter (· ∈ winsOnRest G α C j)
  let K := restKernel G α C S j
  let d (q : PairQ) := ∑ r ∈ E, |(K q r).toReal - (K (none, none) r).toReal|
  have hd (q : PairQ) : 0 ≤ d q := sum_nonneg fun _ _ => abs_nonneg _
  have hsum : leftNoisyNormalizationRatioLoss G α C S j ≤
      (∑ q, (μ q).toReal * d q) + ∑ q, (μ q).toReal * d (none, q.2) := by
    unfold leftNoisyNormalizationRatioLoss weightedAnchorRestScore
    simp only [← sum_add_distrib, ← mul_add]
    refine sum_le_sum fun q _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    simp only [d, ← sum_add_distrib]
    exact sum_le_sum fun r _ => noisyRatioPoint_le G α C S j q r
  have he : (α : ℝ) * (∑ q, (μ q).toReal * d (none, q.2)) ≤ ∑ q, (μ q).toReal * d q := by
    dsimp only [μ]
    rw [map_snd_law]
    exact rate_mul_sum_anchorPair_erase_left_le G.questions α α d hd
  have h := mul_le_mul_of_nonneg_left hsum α.2.1
  change _ ≤ ((α : ℝ) + 1) * (∑ q, (μ q).toReal * d q)
  rw [add_mul, one_mul]
  rw [mul_add] at h
  exact h.trans (add_le_add_right he _)

/-- Summed two-anchor-weighted comparison for the noisy left-tagged branch. An extra
anchor-rate factor pays for erasing Alice's question under the prior draw. -/
theorem sum_leftNoisyNormalizationRatioLoss_le (S : RepeatedStrategy)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support) :
    let T := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let p := (T.toOuterMeasure W).toReal
    let w := (α : ℝ) ^ 2 / 2
    let ε₁ := Real.sqrt (Fintype.card Free * Real.log (1 / p) / 2)
    let ε₂ := Real.sqrt (Fintype.card Free * Real.log (Fintype.card (C → A × B) / p) / 2)
    w * ((α : ℝ) * ∑ j : Free, leftNoisyNormalizationRatioLoss G α C S j) ≤
      ((α : ℝ) + 1) * (p * ((2 * w + 1 / 2) * ε₁ + 2 * ((1 + w) * (2 * ε₁ + ε₂)))) := by
  intro T W p w ε₁ ε₂
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hα : 0 ≤ (α : ℝ) := α.2.1
  have h : (α : ℝ) * (∑ j : Free, leftNoisyNormalizationRatioLoss G α C S j) ≤
      ((α : ℝ) + 1) * (∑ j : Free, restKernelWinL1 G α C S j) := by
    rw [mul_sum, mul_sum]
    exact sum_le_sum fun j _ => leftNoisyNormalizationRatioLoss_le G α C S j
  refine (mul_le_mul_of_nonneg_left h hw).trans ?_
  rw [mul_left_comm w]
  exact mul_le_mul_of_nonneg_left (sum_restKernelWinL1_le G α C S hs) (by positivity)

end Cslib.PCP.AnchoredDependency
