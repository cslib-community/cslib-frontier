/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredLocalUnitary
import CslibFrontier.Probability.PMF.FiniteMarkov
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
open ParallelRepetition (Revealed Shared)
open scoped unitInterval Cslib.Probability.PMF

variable {X Y A B ι κ U : Type*} {n m : ℕ}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (C : Finset (Fin n)) (G : TwoProverGame X Y A B) (α : I)

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Info" => Revealed (Option X) (Option Y) C
local notation "Label" => (Info × ((C → A) × (C → B)))
local notation "PairQ" => (Option X × Option Y)
local notation "Message" => (Option X ⊕ Option Y)
local notation "Rest" => Shared (Option X) (Option Y) A B C
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

/-- Uniform failure bound from the summed alignment estimate and the mean-error threshold. -/
@[expose] noncomputable def anchorAlignmentFailureBound (α : I) (m answers : ℕ) (p τ : ℝ) : ℝ :=
  (2 + (α : ℝ)) * anchoredAlignmentBound α m answers p /
    ((m : ℝ) * ((α : ℝ) * anchoredAlignmentScale α * τ ^ 2))

local notation "aliceVector" => fun (S : RepeatedStrategy) (j : Free)
    (label : Label) (x : Option X) =>
  checkedVectorGivenAlice G α C S j (Prod.fst label) x
    (Prod.fst (Prod.snd label)) (Prod.snd (Prod.snd label))

local notation "bobVector" => fun (S : RepeatedStrategy) (j : Free)
    (label : Label) (y : Option Y) =>
  checkedVectorGivenBob G α C S j (omitMessage C j (Prod.fst label))
    (Revealed.halves (Prod.fst label) j) y (Prod.fst (Prod.snd label)) (Prod.snd (Prod.snd label))

/-- The three mean alignment comparisons under a given remaining-transcript law. -/
@[expose] def AnchorAlignmentOnRestAt (S : RepeatedStrategy)
    (e : Fin m ≃ Free) (VA : Fin m → Label → Option X → Matrix ι ι ℂ)
    (VB VAB : Fin m → Label → Option Y → Matrix κ κ ℂ) (i : Fin m)
    (R : PMF (Rest (e i))) (τ : ℝ) : Prop :=
  let vA := aliceVector S (e i)
  let vB := bobVector S (e i)
  taggedPairRestScore C G α (e i) R Prod.fst (fun _ => Sum.inr none)
    (fun t x => localUnitaryError (VA i t x) (vA t none) (vA t x)) ≤ τ ∧
  taggedPairRestScore C G α (e i) R Prod.snd (fun _ => Sum.inl none)
    (fun t y => localUnitaryError (VB i t y) (vB t none) (vB t y)) ≤ τ ∧
  taggedPairRestScore C G α (e i) R Prod.snd (Sum.inl ∘ Prod.fst)
    (fun t y => localUnitaryError (VAB i t y) (vB t y) (vB t none)) ≤ τ

/-- The three mean alignment comparisons under the winning remaining-transcript law. -/
@[expose] def AnchorAlignmentAt (S : RepeatedStrategy) (Q : PMF Transcript)
    (e : Fin m ≃ Free) (VA : Fin m → Label → Option X → Matrix ι ι ℂ)
    (VB VAB : Fin m → Label → Option Y → Matrix κ κ ℂ) (i : Fin m) (τ : ℝ) : Prop :=
  AnchorAlignmentOnRestAt C G α S e VA VB VAB i (Q.map (restTranscript C (e i))) τ

private theorem taggedPairUnitaryError_le_of_dist {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (j : Free) {R R' : PMF (Rest j)} (read : PairQ → U) (tag : PairQ → Message)
    (V : Label → U → Matrix E E ℂ) (v u : Label → U → EuclideanSpace ℂ (D × E))
    (hV : ∀ t x, V t x ∈ unitaryGroup E ℂ)
    {τ ξ : ℝ} (hd : dist R R' ≤ ξ)
    (h : taggedPairRestScore C G α j R read tag
      (fun t x => localUnitaryError (V t x) (v t x) (u t x)) ≤ τ) :
    taggedPairRestScore C G α j R' read tag
      (fun t x => localUnitaryError (V t x) (v t x) (u t x)) ≤ τ + 2 * ξ :=
  (taggedPairRestScore_le_add_dist C G α j R R' read tag _
    (fun _ _ => localUnitaryError_nonneg _ _ _)
    (fun t x => localUnitaryError_le_two (hV t x) _ _)).trans
    (add_le_add h (mul_le_mul_of_nonneg_left hd (by norm_num)))

/-- Changing the remaining-transcript law increases each mean alignment error by at
most twice the statistical distance. The local unitary families are the same. -/
theorem AnchorAlignmentOnRestAt.transfer (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (VA : Fin m → Label → Option X → Matrix ι ι ℂ)
    (VB VAB : Fin m → Label → Option Y → Matrix κ κ ℂ) (i : Fin m)
    (hVA : ∀ t x, VA i t x ∈ unitaryGroup ι ℂ)
    (hVB : ∀ t y, VB i t y ∈ unitaryGroup κ ℂ)
    (hVAB : ∀ t y, VAB i t y ∈ unitaryGroup κ ℂ)
    {R R' : PMF (Rest (e i))} {τ ξ : ℝ} (hd : dist R R' ≤ ξ)
    (h : AnchorAlignmentOnRestAt C G α S e VA VB VAB i R τ) :
    AnchorAlignmentOnRestAt C G α S e VA VB VAB i R' (τ + 2 * ξ) := by
  unfold AnchorAlignmentOnRestAt at h ⊢
  let vA := aliceVector S (e i)
  let vB := bobVector S (e i)
  exact ⟨
    taggedPairUnitaryError_le_of_dist C G α (e i) Prod.fst (fun _ => Sum.inr none)
      (VA i) (fun t _ => vA t none) vA hVA hd h.1,
    taggedPairUnitaryError_le_of_dist C G α (e i) Prod.snd (fun _ => Sum.inl none)
      (VB i) (fun t _ => vB t none) vB hVB hd h.2.1,
    taggedPairUnitaryError_le_of_dist C G α (e i) Prod.snd (Sum.inl ∘ Prod.fst)
      (VAB i) vB (fun t _ => vB t none) hVAB hd h.2.2⟩

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
    ∃ (VA : Fin m → Label → Option X → Matrix ι ι ℂ)
      (VB VAB : Fin m → Label → Option Y → Matrix κ κ ℂ) (good : Finset (Fin m)),
      (∀ i t x, VA i t x ∈ unitaryGroup ι ℂ) ∧
      (∀ i t y, VB i t y ∈ unitaryGroup κ ℂ) ∧
      (∀ i t y, VAB i t y ∈ unitaryGroup κ ℂ) ∧
      ((uniformOfFintype (Fin m)).toOuterMeasure {i | i ∉ good}).toReal ≤
        anchorAlignmentFailureBound α m (Fintype.card (C → A × B)) p τ ∧
      ∀ i ∈ good, AnchorAlignmentAt C G α S Q e VA VB VAB i τ := by
  classical
  intro T W Q p
  let vA (i : Fin m) := aliceVector S (e i)
  let vB (i : Fin m) := bobVector S (e i)
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
  · have h := uniform_compl_finset_le_of_sum good (fun i => scale * (a i + b i + ab i))
      (mul_pos hscale (sq_pos_of_pos hτ))
      (fun i => mul_nonneg hscale.le (add_nonneg (add_nonneg (ha i) (hb i)) (hab i)))
      (fun i hi => by
        have hh : τ ^ 2 < a i + b i + ab i := by
          simpa only [good, mem_filter, mem_univ, true_and, not_le] using hi
        exact mul_le_mul_of_nonneg_left hh.le hscale.le)
      htotal
    simpa only [anchorAlignmentFailureBound, Fintype.card_fin] using h
  · intro i hi
    unfold AnchorAlignmentAt AnchorAlignmentOnRestAt
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
