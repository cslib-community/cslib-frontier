/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredGoodCoordinates
public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredNormalizationWeights
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.FiniteMarkov

/-!
# Common alignment and normalization coordinates

The weighted normalization losses become conditional means on a coordinate where the
two-anchor win probability remains at least half the overall win probability. A single
finite Markov bound controls both ratio losses and the possible drop in win probability.
Intersecting with the alignment set produces common coordinates for the two analyses.
These are the good-coordinate steps of
[Bavarian, Vidick and Yuen, Lemmas 5.12 and 5.17][BavarianVidickYuen2022]
(arXiv:1509.07466v2, §§5.2–5.4, printed pp. 22 and 28–31).

## Main results

* `exists_good_normalization_coordinates`: positive two-anchor win mass and both
  conditional squared ratio bounds.
* `exists_good_alignment_normalization_coordinates`: three unitary families and one
  set on which the alignment and normalization estimates hold together.
-/

public section

namespace Cslib.PCP.AnchoredDependency

open Cslib.Probability.PMF
open Matrix Finset
open ParallelRepetition (Revealed)
open scoped unitInterval

variable {X Y A B ι κ : Type*} {n m : ℕ}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (C : Finset (Fin n)) (G : TwoProverGame X Y A B) (α : I)

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Info" => Revealed (Option X) (Option Y) C
local notation "Label" => (Info × ((C → A) × (C → B)))
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ

/-- Estimate for the probability of missing a good normalization coordinate. -/
@[expose] noncomputable def anchorNormalizationFailureBound
    (α : I) (m answers : ℕ) (p η : ℝ) : ℝ :=
  let w := (α : ℝ) ^ 2 / 2
  let ε₁ := Real.sqrt (m * Real.log (1 / p) / 2)
  let ε₂ := Real.sqrt (m * Real.log (answers / p) / 2)
  let B := p * ((2 * w + 1 / 2) * ε₁ + 2 * ((1 + w) * (2 * ε₁ + ε₂)))
  ((α : ℝ) * η * (p * ε₁ / 2) + (2 * (α : ℝ) + 1) * B) /
    ((m : ℝ) * (w * (α : ℝ) * η * (p / 2)))

/-- At a good coordinate the two-anchor win probability is positive, and the
ordinary and noisy conditional squared norm-ratio losses meet the same threshold. -/
@[expose] def AnchorNormalizationAt (S : RepeatedStrategy) (j : Free) (p η : ℝ) : Prop :=
  let p₀ := anchorWinProbability G α C S j
  p / 2 ≤ p₀ ∧ 0 < p₀ ∧
    restNormalizationRatioLoss G α C S j / p₀ ≤ η ∧
    leftNoisyNormalizationRatioLoss G α C S j / p₀ ≤ η

/-- The ordinary and noisy ratios admit a common conditional error bound, at
coordinates where two-anchor conditioning retains at least half the overall win mass.
The threshold `η` bounds the expected squared errors. -/
theorem exists_good_normalization_coordinates [NeZero m]
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support)
    (hα : 0 < (α : ℝ)) {η : ℝ} (hη : 0 < η) :
    let p := ((transcriptLaw G α C S).toOuterMeasure (winsOnChecked G α C)).toReal
    ∃ good : Finset (Fin m),
      ((uniformOfFintype (Fin m)).toOuterMeasure {i | i ∉ good}).toReal ≤
        anchorNormalizationFailureBound α m (Fintype.card (C → A × B)) p η ∧
      ∀ i ∈ good, AnchorNormalizationAt C G α S (e i) p η := by
  classical
  intro p
  let w := (α : ℝ) ^ 2 / 2
  let ε₁ := Real.sqrt (m * Real.log (1 / p) / 2)
  let ε₂ := Real.sqrt (m * Real.log (Fintype.card (C → A × B) / p) / 2)
  let budget := p * ((2 * w + 1 / 2) * ε₁ + 2 * ((1 + w) * (2 * ε₁ + ε₂)))
  let deviation (i : Fin m) := |p - anchorWinProbability G α C S (e i)|
  let ordinary (i : Fin m) := restNormalizationRatioLoss G α C S (e i)
  let noisy (i : Fin m) := leftNoisyNormalizationRatioLoss G α C S (e i)
  let f (i : Fin m) := w * (α : ℝ) * (η * deviation i + ordinary i + noisy i)
  let threshold := w * (α : ℝ) * η * (p / 2)
  let good := univ.filter fun i => f i ≤ threshold
  have hcard : Fintype.card Free = m := (Fintype.card_congr e.symm).trans (Fintype.card_fin m)
  have hp : 0 < p := (toOuterMeasure_toReal_pos_iff _ _).mpr hs
  have hw : 0 < w := by dsimp only [w]; positivity
  have hwa := mul_pos hw hα
  have hor (i : Fin m) : 0 ≤ ordinary i :=
    weightedAnchorRestScore_nonneg G α C S (e i) _ (fun _ _ => sq_nonneg _)
  have hno (i : Fin m) : 0 ≤ noisy i := by
    unfold noisy leftNoisyNormalizationRatioLoss
    apply weightedAnchorRestScore_nonneg
    rintro ⟨x, y⟩ r
    exact sq_nonneg _
  have hdev : (α : ℝ) ^ 2 * ∑ i, deviation i ≤ p * ε₁ := by
    have h := sum_abs_anchorWinProbability_sub_le G α C S hs
    dsimp only at h
    rw [hcard, ← e.sum_comp (fun j => |p - anchorWinProbability G α C S j|)] at h
    exact h
  have hOrd : w * ∑ i, ordinary i ≤ budget := by
    have h := sum_restNormalizationRatioLoss_le G α C S hs
    dsimp only at h
    rw [hcard, ← e.sum_comp (restNormalizationRatioLoss G α C S)] at h
    exact h
  have hNoisy : w * ((α : ℝ) * ∑ i, noisy i) ≤ ((α : ℝ) + 1) * budget := by
    have h := sum_leftNoisyNormalizationRatioLoss_le G α C S hs
    dsimp only at h
    rw [hcard, ← e.sum_comp (leftNoisyNormalizationRatioLoss G α C S)] at h
    exact h
  have htotal : ∑ i, f i ≤
      (α : ℝ) * η * (p * ε₁ / 2) + (2 * (α : ℝ) + 1) * budget := by
    unfold f
    simp only [← mul_sum, sum_add_distrib]
    have h₁ := mul_le_mul_of_nonneg_left hdev
      (show 0 ≤ (α : ℝ) * η / 2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hOrd hα.le
    dsimp only [w] at h₁ h₂ hNoisy ⊢
    linarith only [h₁, h₂, hNoisy]
  refine ⟨good, ?_, ?_⟩
  · have ht : 0 < threshold := by dsimp only [threshold]; positivity
    have h := uniform_compl_finset_le_of_sum good f ht
      (fun i => mul_nonneg hwa.le
        (add_nonneg (add_nonneg (mul_nonneg hη.le (abs_nonneg _)) (hor i)) (hno i)))
      (fun i hi => by
        have h : threshold < f i := by
          simpa only [good, mem_filter, mem_univ, true_and, not_le] using hi
        exact h.le)
      htotal
    simpa only [anchorNormalizationFailureBound, Fintype.card_fin] using h
  · intro i hi
    have h := (mem_filter.mp hi).2
    have hh : η * deviation i + ordinary i + noisy i ≤ η * (p / 2) := by
      apply le_of_mul_le_mul_left _ hwa
      simpa only [f, threshold, mul_assoc] using h
    have hdev' : deviation i ≤ p / 2 := by
      apply le_of_mul_le_mul_left _ hη
      linarith only [hh, hor i, hno i]
    have hlower : p / 2 ≤ anchorWinProbability G α C S (e i) := by
      have h := (le_abs_self (p - anchorWinProbability G α C S (e i))).trans hdev'
      linarith only [h]
    have hpos := (half_pos hp).trans_le hlower
    have hprod := mul_le_mul_of_nonneg_left hlower hη.le
    refine ⟨hlower, hpos, (div_le_iff₀ hpos).mpr ?_, (div_le_iff₀ hpos).mpr ?_⟩
    · change ordinary i ≤ η * anchorWinProbability G α C S (e i)
      linarith only [hh, hprod, hno i, mul_nonneg hη.le (abs_nonneg
        (p - anchorWinProbability G α C S (e i)))]
    · change noisy i ≤ η * anchorWinProbability G α C S (e i)
      linarith only [hh, hprod, hor i, mul_nonneg hη.le (abs_nonneg
        (p - anchorWinProbability G α C S (e i)))]

/-- All three alignments and both conditional normalization ratios hold on the
same set of unchecked coordinates. The failure bound adds the two estimates. -/
theorem exists_good_alignment_normalization_coordinates [NeZero m] [Nonempty A] [Nonempty B]
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support)
    (hα : 0 < (α : ℝ)) {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) :
    let T := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let Q := T.filter W hs
    let p := (T.toOuterMeasure W).toReal
    let answers := Fintype.card (C → A × B)
    ∃ (VA : Fin m → Label → Option X → Matrix ι ι ℂ)
      (VB VAB : Fin m → Label → Option Y → Matrix κ κ ℂ) (good : Finset (Fin m)),
      (∀ i t x, VA i t x ∈ unitaryGroup ι ℂ) ∧
      (∀ i t y, VB i t y ∈ unitaryGroup κ ℂ) ∧
      (∀ i t y, VAB i t y ∈ unitaryGroup κ ℂ) ∧
      ((uniformOfFintype (Fin m)).toOuterMeasure {i | i ∉ good}).toReal ≤
        anchorAlignmentFailureBound α m answers p τ +
          anchorNormalizationFailureBound α m answers p η ∧
      ∀ i ∈ good, AnchorAlignmentAt C G α S Q e VA VB VAB i τ ∧
        AnchorNormalizationAt C G α S (e i) p η := by
  classical
  intro T W Q p answers
  obtain ⟨VA, VB, VAB, a, hVA, hVB, hVAB, ha, hA⟩ :=
    exists_good_alignment_coordinates C G α S e hs hα hτ
  obtain ⟨b, hb, hB⟩ := exists_good_normalization_coordinates C G α S e hs hα hη
  refine ⟨VA, VB, VAB, a ∩ b, hVA, hVB, hVAB, ?_, ?_⟩
  · let U := uniformOfFintype (Fin m)
    let A₀ : Set (Fin m) := {i | i ∉ a}
    let B₀ : Set (Fin m) := {i | i ∉ b}
    have he : {i | i ∉ a ∩ b} = A₀ ∪ B₀ := by
      ext i
      simp only [mem_inter, Set.mem_ofPred_eq, Set.mem_union, A₀, B₀, not_and_or]
    have hu := MeasureTheory.measure_union_le (μ := U.toOuterMeasure) A₀ B₀
    have htA := toOuterMeasure_ne_top U A₀
    have htB := toOuterMeasure_ne_top U B₀
    rw [he]
    exact ((ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨htA, htB⟩) hu).trans_eq
      (ENNReal.toReal_add htA htB)).trans (add_le_add ha hb)
  · intro i hi
    obtain ⟨hia, hib⟩ := mem_inter.mp hi
    exact ⟨hA i hia, hB i hib⟩

end Cslib.PCP.AnchoredDependency
