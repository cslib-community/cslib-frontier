/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredCommonState
public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredGoodNormalization
import CslibFrontier.Foundations.LinearAlgebra.Matrix.UnitaryGroup
import CslibFrontier.Probability.PMF.AnchorPair

/-!
# Mean error of the prepared state for anchored repetition

The provers share the normalized doubly anchored checked branch for a sampled
winning remaining transcript. Each prover acts on their own part, using their own
question and the shared transcript. The pointwise comparison to the actual branch
is averaged on the winning two-anchor law. A squared norm-ratio bound gives a
first-moment bound by Cauchy–Schwarz. Replacing one question by its anchor costs an
extra factor of the inverse anchor rate in the second moment.

## Main results

* `mean_preparedCheckedVector_error_le`: the conditional mean preparation bound.
* `exists_good_prepared_state_coordinates`: choose the same good coordinates and
  local unitaries for the preparation bound.

## References

* [Bavarian, Vidick and Yuen, Claim 5.19][BavarianVidickYuen2022]
  (arXiv:1509.07466v2, §5.4, printed pp. 31–34).
-/

public section

namespace Cslib.PCP.AnchoredDependency

open Matrix Finset Cslib.Probability.PMF
open ParallelRepetition (Revealed Shared)
open scoped unitInterval Kronecker

variable {X Y A B ι κ : Type*} {n m : ℕ}
  [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (G : TwoProverGame X Y A B) (α : I) (C : Finset (Fin n))

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Rest" => Shared (Option X) (Option Y) A B C
local notation "PairQ" => (Option X × Option Y)
local notation "Label" => (Revealed (Option X) (Option Y) C × ((C → A) × (C → B)))
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ
local notation "act" => toEuclideanCLM (𝕜 := ℂ)

private theorem anchoredPairRestScore_erase_le (j : Free) (R : PMF (Rest j))
    (f : PairQ → Rest j → ℝ) (hf : ∀ q r, 0 ≤ f q r) (erase : PairQ → PairQ)
    (herase : ∀ g : PairQ → ℝ, (∀ q, 0 ≤ g q) →
      (α : ℝ) * (∑ q, ((G.anchored α).questions q).toReal * g (erase q)) ≤
        ∑ q, ((G.anchored α).questions q).toReal * g q) :
    (α : ℝ) * anchoredPairRestScore C G α j R (fun q r => f (erase q) r) ≤
      anchoredPairRestScore C G α j R f :=
  herase (fun q => ∑ r, (R r).toReal * f q r)
    (fun q => sum_nonneg fun r _ => mul_nonneg ENNReal.toReal_nonneg (hf q r))

private theorem anchoredPairRestScore_erase_left_le (j : Free) (R : PMF (Rest j))
    (f : PairQ → Rest j → ℝ) (hf : ∀ q r, 0 ≤ f q r) :
    (α : ℝ) * anchoredPairRestScore C G α j R (fun q r => f (none, q.2) r) ≤
      anchoredPairRestScore C G α j R f := by
  apply anchoredPairRestScore_erase_le G α C j R f hf (fun q => (none, q.2))
  intro g hg
  rw [TwoProverGame.anchored_questions]
  exact rate_mul_sum_anchorPair_erase_left_le G.questions α α g hg

private theorem anchoredPairRestScore_erase_right_le (j : Free) (R : PMF (Rest j))
    (f : PairQ → Rest j → ℝ) (hf : ∀ q r, 0 ≤ f q r) :
    (α : ℝ) * anchoredPairRestScore C G α j R (fun q r => f (q.1, none) r) ≤
      anchoredPairRestScore C G α j R f := by
  apply anchoredPairRestScore_erase_le G α C j R f hf (fun q => (q.1, none))
  intro g hg
  rw [TwoProverGame.anchored_questions]
  exact rate_mul_sum_anchorPair_erase_right_le G.questions α α g hg

/-- The vector prepared by the separate local actions on the shared two-anchor branch. -/
@[expose] noncomputable def preparedCheckedVector (S : RepeatedStrategy) (j : Free) (r : Rest j)
    (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ) : EuclideanSpace ℂ (ι × κ) :=
  act (U ⊗ₖ V) (NormedSpace.normalize (checkedVectorGivenRest G α C S j
    (restQuestions C j r) (none, none) (Prod.fst ∘ r.answers) (Prod.snd ∘ r.answers)))

/-- The prepared vector has norm one on the support of the winning two-anchor law. -/
theorem norm_preparedCheckedVector (S : RepeatedStrategy) (j : Free)
    (hwin : ∃ r ∈ winsOnRest G α C j, r ∈ (restKernel G α C S j (none, none)).support)
    (r : Rest j)
    (hr : r ∈ ((restKernel G α C S j (none, none)).filter (winsOnRest G α C j) hwin).support)
    {U : Matrix ι ι ℂ} {V : Matrix κ κ ℂ} (hU : U ∈ unitaryGroup ι ℂ)
    (hV : V ∈ unitaryGroup κ ℂ) : ‖preparedCheckedVector G α C S j r U V‖ = 1 := by
  unfold preparedCheckedVector
  rw [(mem_unitaryGroup_iff_forall_norm_toEuclideanCLM _).mp (kronecker_mem_unitary hU hV)]
  exact NormedSpace.norm_normalize (norm_pos_iff.mp
    (anchorBranchNorm_pos_of_mem_support G α C S j hwin r hr))

/-- Bound on the conditional mean preparation error at a good coordinate. -/
@[expose] noncomputable def anchorPreparationErrorBound (α : I) (τ η : ℝ) : ℝ :=
  let β := (noise α : ℝ)
  (τ + Real.sqrt (η / (α : ℝ))) + (τ + Real.sqrt (η / (α : ℝ))) +
    (Real.sqrt β⁻¹ + Real.sqrt (1 - β)⁻¹) * (τ + Real.sqrt η + Real.sqrt (η / (α : ℝ))) +
    Real.sqrt η

/-- The mean distance between the prepared and actual normalized states over independent
prior questions and the winning two-anchor remaining transcript. The first two unitaries
depend only on the question of the player that applies them and on the shared transcript. -/
theorem mean_preparedCheckedVector_error_le (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (VA : Fin m → Label → Option X → Matrix ι ι ℂ)
    (VB VAB : Fin m → Label → Option Y → Matrix κ κ ℂ) (i : Fin m)
    (hVA : ∀ t x, VA i t x ∈ unitaryGroup ι ℂ)
    (hVB : ∀ t y, VB i t y ∈ unitaryGroup κ ℂ)
    (hVAB : ∀ t y, VAB i t y ∈ unitaryGroup κ ℂ)
    (hα : 0 < (α : ℝ)) {p τ η : ℝ}
    (hwin : ∃ r ∈ winsOnRest G α C (e i), r ∈ (restKernel G α C S (e i) (none, none)).support) :
    let j := e i
    let R := (restKernel G α C S j (none, none)).filter (winsOnRest G α C j) hwin
    AnchorNormalizationAt C G α S j p η →
    AnchorAlignmentOnRestAt C G α S e VA VB VAB i R τ →
    anchoredPairRestScore C G α j R (fun q r =>
      ‖preparedCheckedVector G α C S j r
        (VA i (restoreCheckedTranscript C j r (.inr none)) q.1)
        (VB i (restoreCheckedTranscript C j r (.inl none)) q.2) -
        NormedSpace.normalize (checkedVectorGivenRest G α C S j (restQuestions C j r)
          q (Prod.fst ∘ r.answers) (Prod.snd ∘ r.answers))‖) ≤
      anchorPreparationErrorBound α τ η := by
  intro j R hNorm hAlign
  let score := anchoredPairRestScore C G α j R
  let φ (q : PairQ) (r : Rest j) := checkedVectorGivenRest G α C S j (restQuestions C j r)
    q (Prod.fst ∘ r.answers) (Prod.snd ∘ r.answers)
  let φN (q : PairQ) (r : Rest j) := checkedVectorGivenBob G α C S j (restQuestions C j r)
    (.inl q.1) q.2 (Prod.fst ∘ r.answers) (Prod.snd ∘ r.answers)
  let tA (r : Rest j) := restoreCheckedTranscript C j r (.inr none)
  let φA (x : Option X) (r : Rest j) :=
    checkedVectorGivenAlice G α C S j (tA r).1 x (Prod.fst ∘ r.answers) (Prod.snd ∘ r.answers)
  let d (q : PairQ) (r : Rest j) := |1 - ‖φ q r‖ / ‖φ (none, none) r‖|
  let dN (q : PairQ) (r : Rest j) := |1 - ‖φN q r‖ / ‖φ (none, none) r‖|
  let U (q : PairQ) (r : Rest j) := VA i (tA r) q.1
  let V (q : PairQ) (r : Rest j) := VB i (restoreCheckedTranscript C j r (.inl none)) q.2
  let W (q : PairQ) (r : Rest j) := VAB i (restoreCheckedTranscript C j r (.inl q.1)) q.2
  let errA q r := localUnitaryError (U q r) (φA none r) (φA q.1 r)
  let errB q r := localUnitaryError (V q r) (φ (none, none) r) (φ (none, q.2) r)
  let errN q r := localUnitaryError (W q r) (φN q r) (φN (q.1, none) r)
  let β := (noise α : ℝ)
  let b := Real.sqrt β⁻¹ + Real.sqrt (1 - β)⁻¹
  let ε := Real.sqrt (η / (α : ℝ))
  have hβnonneg : 0 ≤ b := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have heA : score errA ≤ τ := hAlign.1
  let bob (r : Rest j) (msg : Option X ⊕ Option Y) (y : Option Y) :=
    let label := restoreCheckedTranscript C j r msg
    checkedVectorGivenBob G α C S j (omitMessage C j label.1) (label.1.halves j) y
      label.2.1 label.2.2
  have hbob (r : Rest j) (msg : Option X ⊕ Option Y) (y : Option Y) :
      bob r msg y = checkedVectorGivenBob G α C S j (restQuestions C j r) msg y
        (Prod.fst ∘ r.answers) (Prod.snd ∘ r.answers) := by
    dsimp only [bob]
    rw [omitMessage_restoreCheckedTranscript, halves_restoreCheckedTranscript]
    rfl
  have heB : score errB ≤ τ := by
    have hb := hAlign.2.1
    change score (fun q r => localUnitaryError (V q r)
      (bob r (.inl none) none) (bob r (.inl none) q.2)) ≤ τ at hb
    simp only [hbob, checkedVectorGivenBob_inl_none] at hb
    exact hb
  have heN : score errN ≤ τ := by
    have hn := hAlign.2.2
    change score (fun q r => localUnitaryError (W q r)
      (bob r (.inl q.1) q.2) (bob r (.inl q.1) none)) ≤ τ at hn
    simp only [hbob] at hn
    exact hn
  have hscore (f : PairQ → Rest j → ℝ) :
      score f = weightedAnchorRestScore G α C S j f / anchorWinProbability G α C S j := by
    have h := weightedAnchorRestScore_div_winMass G α C S j hwin f
    dsimp only [score, anchoredPairRestScore]
    dsimp only at h
    rw [TwoProverGame.anchored_questions, ← map_snd_law G.questions α, ← h]
  have hd : score (fun q r => (d q r) ^ 2) ≤ η := by
    rw [hscore]
    simpa only [d, φ, sq_abs, restNormalizationRatioLoss] using hNorm.2.2.1
  have hdN : score (fun q r => (dN q r) ^ 2) ≤ η := by
    rw [hscore]
    simpa only [dN, φN, φ, sq_abs, leftNoisyNormalizationRatioLoss] using hNorm.2.2.2
  have hmean {f : PairQ → Rest j → ℝ} {a : ℝ}
      (h : score (fun q r => (f q r) ^ 2) ≤ a) : score f ≤ Real.sqrt a :=
    Real.le_sqrt_of_sq_le ((anchoredPairRestScore_sq_le C G α j R f).trans h)
  have hdA' : score (fun q r => d (q.1, none) r) ≤ ε := hmean <|
    (le_div_iff₀ hα).2 ((mul_comm _ _).le.trans
      ((anchoredPairRestScore_erase_right_le G α C j R _ (fun q r => sq_nonneg (d q r))).trans hd))
  have hdB' : score (fun q r => d (none, q.2) r) ≤ ε := hmean <|
    (le_div_iff₀ hα).2 ((mul_comm _ _).le.trans
      ((anchoredPairRestScore_erase_left_le G α C j R _ (fun q r => sq_nonneg (d q r))).trans hd))
  have hdN' : score (fun q r => dN (q.1, none) r) ≤ ε := hmean <|
    (le_div_iff₀ hα).2 ((mul_comm _ _).le.trans
      ((anchoredPairRestScore_erase_right_le G α C j R _
        (fun q r => sq_nonneg (dN q r))).trans hdN))
  change score (fun q r => ‖preparedCheckedVector G α C S j r (U q r) (V q r) -
      NormedSpace.normalize (φ q r)‖) ≤ _
  calc
    _ ≤ score (fun q r => (errB q r + d (none, q.2) r) + (errA q r + d (q.1, none) r) +
        b * (errN q r + dN q r + dN (q.1, none) r) + d q r) := by
      apply anchoredPairRestScore_mono
      intro q r hr
      let γ := ‖φ (none, none) r‖
      have hγ : 0 < γ := anchorBranchNorm_pos_of_mem_support G α C S j hwin r hr
      have hBob := norm_right_sub_div_le (hVB (restoreCheckedTranscript C j r (.inl none)) q.2)
        (φ (none, none) r) (φ (none, q.2) r) hγ.le
      have hNoisy := norm_right_sub_div_le (hVAB (restoreCheckedTranscript C j r (.inl q.1)) q.2)
        (φN q r) (φN (q.1, none) r) hγ.le
      have hAlice := norm_right_sub_div_le (hVA (tA r) q.1) (φA none r) (φA q.1 r) hγ.le
      have hswap (U' : Matrix ι ι ℂ) (x : Option X) :
          ‖act (U' ⊗ₖ (1 : Matrix κ κ ℂ)) (φ (none, none) r) - φ (x, none) r‖ =
            ‖act ((1 : Matrix κ κ ℂ) ⊗ₖ U') (φA none r) - φA x r‖ := by
        have h := norm_sub_checkedAlice_inr_none G α C S j (tA r).1 x
          (Prod.fst ∘ r.answers) (Prod.snd ∘ r.answers) U'
          (halves_restoreCheckedTranscript C j r (.inr none))
        simpa only [tA, φA, φ, omitMessage_restoreCheckedTranscript] using h
      have hnorm (x : Option X) : ‖φ (x, none) r‖ = ‖φA x r‖ := by
        simpa only [zero_kronecker, kronecker_zero, map_zero, zero_apply, zero_sub,
          norm_neg] using hswap 0 x
      simp only [← hswap, ← hnorm] at hAlice
      have hz : |1 - ‖φ (none, none) r‖ / γ| = 0 := by
        change |1 - γ / γ| = 0
        rw [div_self hγ.ne', sub_self, abs_zero]
      rw [hz, add_zero] at hBob hAlice
      have h := norm_sub_normalized_checked_common_le G α C S j (restQuestions C j r)
        q.1 q.2 (Prod.fst ∘ r.answers) (Prod.snd ∘ r.answers)
        (U q r) (V q r) (W q r) (hVA _ _) (hVAB _ _) hα
      change ‖preparedCheckedVector G α C S j r (U q r) (V q r) -
        NormedSpace.normalize (φ q r)‖ ≤ _ at h
      dsimp only at h
      rw [add_div, add_div, mul_div_assoc, abs_sub_comm] at h
      exact h.trans (add_le_add (add_le_add (add_le_add hBob hAlice)
        (mul_le_mul_of_nonneg_left hNoisy hβnonneg)) le_rfl)
    _ ≤ _ := by
      simp only [score, anchoredPairRestScore_add, anchoredPairRestScore_mul]
      exact add_le_add
        (add_le_add (add_le_add (add_le_add heB hdB') (add_le_add heA hdA'))
          (mul_le_mul_of_nonneg_left (add_le_add (add_le_add heN (hmean hdN)) hdN') hβnonneg))
        (hmean hd)

/-- On a common set of coordinates the two local actions give the mean preparation
bound. Bob's auxiliary unitary is used to derive the bound and is absent from the
prepared vector. -/
theorem exists_good_prepared_state_coordinates [NeZero m] [Nonempty A] [Nonempty B]
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support)
    (hα : 0 < (α : ℝ)) {τ η ξ : ℝ} (hτ : 0 < τ) (hη : 0 < η) (hξ : 0 < ξ) :
    let p := ((transcriptLaw G α C S).toOuterMeasure (winsOnChecked G α C)).toReal
    let answers := Fintype.card (C → A × B)
    ∃ (U : (i : Fin m) → Rest (e i) → Option X → Matrix ι ι ℂ)
      (V : (i : Fin m) → Rest (e i) → Option Y → Matrix κ κ ℂ) (good : Finset (Fin m)),
      (∀ i r x, U i r x ∈ unitaryGroup ι ℂ) ∧
      (∀ i r y, V i r y ∈ unitaryGroup κ ℂ) ∧
      ((uniformOfFintype (Fin m)).toOuterMeasure {i | i ∉ good}).toReal ≤
        (anchorAlignmentFailureBound α m answers p τ +
          anchorNormalizationFailureBound α m answers p η) +
          anchorRestFailureBound α m answers p ξ ∧
      ∀ i ∈ good,
        ∃ hwin : ∃ r ∈ winsOnRest G α C (e i),
            r ∈ (restKernel G α C S (e i) (none, none)).support,
          let j := e i
          let R := (restKernel G α C S j (none, none)).filter (winsOnRest G α C j) hwin
          anchoredPairRestScore C G α j R (fun q r =>
            ‖preparedCheckedVector G α C S j r (U i r q.1) (V i r q.2) -
              NormedSpace.normalize (checkedVectorGivenRest G α C S j (restQuestions C j r)
                q (Prod.fst ∘ r.answers) (Prod.snd ∘ r.answers))‖) ≤
            anchorPreparationErrorBound α (τ + 2 * ξ) η := by
  intro p answers
  obtain ⟨VA, VB, VAB, good, hVA, hVB, hVAB, hprob, hgood⟩ :=
    exists_good_conditioned_alignment_coordinates C G α S e hs hα hτ hη hξ
  let U (i : Fin m) (r : Rest (e i)) := VA i (restoreCheckedTranscript C (e i) r (.inr none))
  let V (i : Fin m) (r : Rest (e i)) := VB i (restoreCheckedTranscript C (e i) r (.inl none))
  refine ⟨U, V, good, fun i r x => hVA i _ x, fun i r y => hVB i _ y, hprob, ?_⟩
  intro i hi
  obtain ⟨hn, hwin, ha⟩ := hgood i hi
  exact ⟨hwin, mean_preparedCheckedVector_error_le G α C S e VA VB VAB i
    (hVA i) (hVB i) (hVAB i) hα hwin hn ha⟩

end Cslib.PCP.AnchoredDependency
