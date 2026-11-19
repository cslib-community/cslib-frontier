/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredLocalUnitary
import CslibFrontier.Foundations.Data.Finset.Markov
public import CslibFrontier.Probability.PMF.Uniform

/-!
# Good coordinates for anchored local alignment

Under the independent question redraw, each of the three alignments in equations (29)–(31)
has a bounded sum of squared errors. A single Markov estimate bounds the probability that a
uniform unchecked coordinate fails any of the three first-moment bounds. The two fixed-tag
unitaries depend only on their own question and the remaining transcript.
This is the good-coordinate step of
[Bavarian, Vidick and Yuen, Lemma 5.12][BavarianVidickYuen2022]
(arXiv:1509.07466v2, §5.2, printed pp. 22 and 27–28), with an explicit threshold.

## Main results

* `exists_good_alignment_coordinates`: choose the three families of unitaries and one
  set of coordinates on which all three mean vector errors are below the same threshold.
-/

public section

namespace Cslib.PCP.AnchoredDependency

open Cslib.Probability.PMF
open Matrix Finset
open ParallelRepetition (Revealed)
open scoped unitInterval

variable {X Y A B ι κ U : Type*} {n m : ℕ}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (C : Finset (Fin n)) (G : TwoProverGame X Y A B) (α : I)

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Info" => Revealed (Option X) (Option Y) C
local notation "Label" => (Info × ((C → A) × (C → B)))
local notation "PairQ" => (Option X × Option Y)
local notation "Message" => (Option X ⊕ Option Y)
local notation "Transcript" => ((Info × (C → A × B)) × (Free → PairQ))
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ

private theorem taggedPairCoordinateScore_le_of_sq (Q : PMF Transcript)
    (read : PairQ → U) (tag : PairQ → Message) (e : Fin m ≃ Free)
    (f : Fin m → Label → U → ℝ) (i : Fin m) {τ : ℝ} (hτ : 0 ≤ τ)
    (hf : ∀ t u, 0 ≤ f i t u)
    (hs : taggedPairCoordinateScore C G α Q read tag e (fun j t u => (f j t u) ^ 2) i ≤ τ ^ 2) :
    taggedPairCoordinateScore C G α Q read tag e f i ≤ τ :=
  (sq_le_sq₀ (taggedPairCoordinateScore_nonneg C G α Q read tag e f i hf) hτ).mp
    ((taggedPairCoordinateScore_sq_le C G α Q read tag e f i).trans hs)

private theorem uniform_bad_coordinates_le [NeZero m] (good : Finset (Fin m))
    (f : Fin m → ℝ) {threshold bound : ℝ} (ht : 0 < threshold)
    (hf : ∀ i, 0 ≤ f i) (hbad : ∀ i ∉ good, threshold ≤ f i)
    (hbound : ∑ i, f i ≤ bound) :
    ((uniformOfFintype (Fin m)).toOuterMeasure {i | i ∉ good}).toReal ≤
      bound / ((m : ℝ) * threshold) := by
  classical
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne _))
  rw [toOuterMeasure_uniformOfFintype_toReal, Fintype.card_fin, le_div_iff₀ (mul_pos hm ht)]
  rw [← mul_assoc, div_mul_cancel₀ _ hm.ne']
  exact (card_filter_mul_le_sum univ (fun i => i ∉ good) f (fun i _ => hf i)
    (fun i _ => hbad i)).trans hbound

/-- A single set of unchecked coordinates satisfies the three mean-error bounds with
threshold `τ`. The failure probability is explicit in the summed alignment bound.
Positive anchor rate, threshold and number of unchecked coordinates allow division. -/
theorem exists_good_alignment_coordinates [NeZero m] [Nonempty A] [Nonempty B]
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support)
    (hα : 0 < (α : ℝ)) {τ : ℝ} (hτ : 0 < τ) :
    let T := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let Q := T.filter W hs
    let p := (T.toOuterMeasure W).toReal
    let vA (i : Fin m) (label : Label) (x : Option X) :=
      let (t, a, b) := label
      checkedVectorGivenAlice G α C S (e i) t x a b
    let vB (i : Fin m) (label : Label) (y : Option Y) :=
      let (t, a, b) := label
      checkedVectorGivenBob G α C S (e i) (omitMessage C (e i) t) (t.halves (e i)) y a b
    ∃ (VA : Fin m → Label → Option X → Matrix ι ι ℂ)
      (VB VAB : Fin m → Label → Option Y → Matrix κ κ ℂ) (good : Finset (Fin m)),
      (∀ i t x, VA i t x ∈ unitaryGroup ι ℂ) ∧
      (∀ i t y, VB i t y ∈ unitaryGroup κ ℂ) ∧
      (∀ i t y, VAB i t y ∈ unitaryGroup κ ℂ) ∧
      ((uniformOfFintype (Fin m)).toOuterMeasure {i | i ∉ good}).toReal ≤
        (2 + (α : ℝ)) * anchoredAlignmentBound α m (Fintype.card (C → A × B)) p /
          ((m : ℝ) * ((α : ℝ) * anchoredAlignmentScale α * τ ^ 2)) ∧
      ∀ i ∈ good,
        taggedPairCoordinateScore C G α Q Prod.fst (fun _ => Sum.inr none) e
          (fun j t x => localUnitaryError (VA j t x) (vA j t none) (vA j t x)) i ≤ τ ∧
        taggedPairCoordinateScore C G α Q Prod.snd (fun _ => Sum.inl none) e
          (fun j t y => localUnitaryError (VB j t y) (vB j t none) (vB j t y)) i ≤ τ ∧
        taggedPairCoordinateScore C G α Q Prod.snd (Sum.inl ∘ Prod.fst) e
          (fun j t y => localUnitaryError (VAB j t y) (vB j t y) (vB j t none)) i ≤ τ := by
  classical
  intro T W Q p vA vB
  obtain ⟨VA, hVA, hA⟩ := exists_alice_anchorLocalUnitary_le C G α S e hs
  obtain ⟨VB, hVB, hB⟩ := exists_bob_anchorLocalUnitary_le C G α S e hs
  obtain ⟨VAB, hVAB, hAB⟩ := exists_bob_taggedLocalUnitary_le C G α S e hs
  let fA i t x := localUnitaryError (VA i t x) (vA i t none) (vA i t x)
  let fB i t y := localUnitaryError (VB i t y) (vB i t none) (vB i t y)
  let fAB i t y := localUnitaryError (VAB i t y) (vB i t y) (vB i t none)
  let a i := taggedPairCoordinateScore C G α Q Prod.fst (fun _ => Sum.inr none) e
    (fun j t x => (fA j t x) ^ 2) i
  let b i := taggedPairCoordinateScore C G α Q Prod.snd (fun _ => Sum.inl none) e
    (fun j t y => (fB j t y) ^ 2) i
  let ab i := taggedPairCoordinateScore C G α Q Prod.snd (Sum.inl ∘ Prod.fst) e
    (fun j t y => (fAB j t y) ^ 2) i
  let good := univ.filter (fun i => a i + b i + ab i ≤ τ ^ 2)
  let scale := (α : ℝ) * anchoredAlignmentScale α
  let bound := anchoredAlignmentBound α m (Fintype.card (C → A × B)) p
  have ha (i : Fin m) : 0 ≤ a i := taggedPairCoordinateScore_nonneg C G α Q _ _ e _ i
    (fun _ _ => sq_nonneg _)
  have hb (i : Fin m) : 0 ≤ b i := taggedPairCoordinateScore_nonneg C G α Q _ _ e _ i
    (fun _ _ => sq_nonneg _)
  have hab (i : Fin m) : 0 ≤ ab i := taggedPairCoordinateScore_nonneg C G α Q _ _ e _ i
    (fun _ _ => sq_nonneg _)
  have hscale : 0 < scale := by dsimp [scale, anchoredAlignmentScale]; positivity
  change scale * (∑ i, a i) ≤ bound at hA
  change scale * (∑ i, b i) ≤ bound at hB
  change anchoredAlignmentScale α * (∑ i, ab i) ≤ bound at hAB
  have htotal : ∑ i, scale * (a i + b i + ab i) ≤ (2 + (α : ℝ)) * bound := by
    rw [← mul_sum, sum_add_distrib, sum_add_distrib, mul_add, mul_add]
    have h := mul_le_mul_of_nonneg_left hAB hα.le
    rw [← mul_assoc] at h
    change scale * (∑ i, ab i) ≤ (α : ℝ) * bound at h
    linarith only [hA, hB, h]
  refine ⟨VA, VB, VAB, good, hVA, hVB, hVAB, ?_, ?_⟩
  · apply uniform_bad_coordinates_le good (fun i => scale * (a i + b i + ab i))
      (mul_pos hscale (sq_pos_of_pos hτ))
    · exact fun i => mul_nonneg hscale.le (add_nonneg (add_nonneg (ha i) (hb i)) (hab i))
    · intro i hi
      have hh : τ ^ 2 < a i + b i + ab i := by
        simpa only [good, mem_filter, mem_univ, true_and, not_le] using hi
      exact mul_le_mul_of_nonneg_left hh.le hscale.le
    · exact htotal
  · intro i hi
    have hh := (mem_filter.mp hi).2
    refine ⟨taggedPairCoordinateScore_le_of_sq C G α Q _ _ e fA i hτ.le
      (fun _ _ => localUnitaryError_nonneg _ _ _) ?_,
      taggedPairCoordinateScore_le_of_sq C G α Q _ _ e fB i hτ.le
        (fun _ _ => localUnitaryError_nonneg _ _ _) ?_,
      taggedPairCoordinateScore_le_of_sq C G α Q _ _ e fAB i hτ.le
        (fun _ _ => localUnitaryError_nonneg _ _ _) ?_⟩
    · change a i ≤ τ ^ 2
      linarith only [hh, hb i, hab i]
    · change b i ≤ τ ^ 2
      linarith only [hh, ha i, hab i]
    · change ab i ≤ τ ^ 2
      linarith only [hh, ha i, hb i]

end Cslib.PCP.AnchoredDependency
