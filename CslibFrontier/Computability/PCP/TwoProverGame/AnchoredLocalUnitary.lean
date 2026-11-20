/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredPriorTraceDeviation
import CslibFrontier.Foundations.Quantum.DensityMatrix.FidelityTraceDistance
public import CslibFrontier.Foundations.Analysis.Normed.Normalize

/-!
# Local-unitary alignment under the tagged redraw

A supported observation supplies a noisy checked-answer purification of the corresponding
winning conditional state. Uhlmann's theorem aligns the two purifications for the sampled
question and its anchor. When either endpoint is outside winning support, the identity has
squared error at most four, including when a normalized vector is zero. Averaging uses the
trace-norm comparison and the probability of missing support.

This proves the tagged, coordinate-summed alignment step of
[Bavarian, Vidick and Yuen, Lemma 5.12][BavarianVidickYuen2022]
(arXiv:1509.07466v2, §5.2, printed pp. 22 and 27–28).

## Using the alignment bounds

Use `exists_bob_taggedLocalUnitary_le` for a left message set by the sampled Alice
question. The comparison takes Bob's sampled-question branch to his anchored branch and
allows the unitary to depend on both questions. The exchanged result uses the right tag.
For a message fixed at its anchor, use `exists_bob_anchorLocalUnitary_le` or
`exists_alice_anchorLocalUnitary_le`. These start from the doubly anchored branch
and use only the moving player's question and the remaining transcript. The Alice
construction uses the Bob-first ordering, so her local action is on the second factor.

The error uses `NormedSpace.normalize`: a nonzero vector becomes a unit vector and zero
stays zero. The support term accounts for using the identity when either endpoint is
missing. At strictly positive anchor rate `α`, divide by `anchoredAlignmentScale α`
in the sampled-tag bound and by `(α : ℝ) * anchoredAlignmentScale α` in the fixed-tag
bound. The unequal-dimension anchoring test checks
the latter division at `α = 1/2`.

The bounds sum squared errors over coordinates. Good-coordinate probabilities and
asymptotic rates require further steps, as do the normalization-weight comparison and
the strategy for the repetition theorem.

## Main definitions

* `localUnitaryError` and `localUnitaryErrorSq`: alignment errors of two normalized noisy branches.
* `anchoredAlignmentScale` and `anchoredAlignmentBound`: the coefficient and error in
  the coordinate-summed bounds.

## Main results

* `exists_bob_taggedLocalUnitary_le` and `exists_alice_taggedLocalUnitary_le`:
  the averaged alignment bounds for the two message tags.
* `exists_bob_anchorLocalUnitary_le` and `exists_alice_anchorLocalUnitary_le`:
  the averaged alignment from the doubly anchored branch with the other message fixed.
-/

public section

namespace Cslib.PCP.AnchoredDependency

open Cslib.Probability.PMF
open Quantum Matrix
open ParallelRepetition (Revealed)
open scoped unitInterval Kronecker

variable {X Y A B ι κ U L R : Type*} {n m : ℕ}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (C : Finset (Fin n))

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Info" => Revealed (Option X) (Option Y) C
local notation "Answer" => ((C → A) × (C → B))
local notation "Label" => (Info × Answer)
local notation "PairQ" => (Option X × Option Y)
local notation "Message" => (Option X ⊕ Option Y)
local notation "Transcript" => ((Info × (C → A × B)) × (Free → PairQ))
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ

/-- Distance after normalizing the branches and acting on the second tensor factor. -/
noncomputable def localUnitaryError (V : Matrix κ κ ℂ)
    (v u : EuclideanSpace ℂ (ι × κ)) : ℝ :=
  ‖WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ V) *ᵥ (NormedSpace.normalize v).ofLp) -
    NormedSpace.normalize u‖

/-- Squared alignment error of two normalized noisy branches. -/
@[expose] noncomputable def localUnitaryErrorSq (V : Matrix κ κ ℂ)
    (v u : EuclideanSpace ℂ (ι × κ)) : ℝ :=
  localUnitaryError V v u ^ 2

omit [DecidableEq κ] in
/-- A unitary alignment error is a norm. -/
theorem localUnitaryError_nonneg (V : Matrix κ κ ℂ) (v u : EuclideanSpace ℂ (ι × κ)) :
    0 ≤ localUnitaryError V v u := by
  unfold localUnitaryError
  exact norm_nonneg _

/-- A unitary maps the normalized first branch into the closed unit ball. -/
theorem localUnitaryError_le_two {V : Matrix κ κ ℂ} (hV : V ∈ unitaryGroup κ ℂ)
    (v u : EuclideanSpace ℂ (ι × κ)) : localUnitaryError V v u ≤ 2 := by
  let M := (1 : Matrix ι ι ℂ) ⊗ₖ V
  let f := toEuclideanCLM (n := ι × κ) (𝕜 := ℂ) M
  have hM : M ∈ unitaryGroup (ι × κ) ℂ := kronecker_mem_unitary (one_mem _) hV
  change ‖f (NormedSpace.normalize v) - NormedSpace.normalize u‖ ≤ 2
  refine (norm_sub_le _ _).trans ?_
  rw [(mem_unitaryGroup_iff_forall_norm_toEuclideanCLM M).mp hM (NormedSpace.normalize v)]
  exact (add_le_add (NormedSpace.norm_normalize_le_one v)
    (NormedSpace.norm_normalize_le_one u)).trans_eq (by norm_num)

/-- Before normalizing, the scaled unitary error is bounded by its normalized counterpart
and the two relative norm deviations. -/
theorem norm_right_sub_div_le {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {U : Matrix E E ℂ} (hU : U ∈ unitaryGroup E ℂ) (v u : EuclideanSpace ℂ (D × E))
    {γ : ℝ} (hγ : 0 ≤ γ) :
    ‖toEuclideanCLM (𝕜 := ℂ) ((1 : Matrix D D ℂ) ⊗ₖ U) v - u‖ / γ ≤
      localUnitaryError U v u + |1 - ‖v‖ / γ| + |1 - ‖u‖ / γ| := by
  let f := toEuclideanCLM (𝕜 := ℂ) ((1 : Matrix D D ℂ) ⊗ₖ U)
  have hf := (mem_unitaryGroup_iff_forall_norm_toEuclideanCLM _).mp
    (kronecker_mem_unitary (one_mem (unitaryGroup D ℂ)) hU)
  exact NormedSpace.norm_sub_div_le_normalized_add (f.restrictScalars ℝ) hf v u hγ

private theorem localUnitaryErrorSq_one_le (v u : EuclideanSpace ℂ (ι × κ)) :
    localUnitaryErrorSq 1 v u ≤ 4 := by
  rw [localUnitaryErrorSq, show (4 : ℝ) = 2 ^ 2 by norm_num]
  exact pow_le_pow_left₀ (localUnitaryError_nonneg _ _ _)
    (localUnitaryError_le_two (one_mem _) v u) 2

variable (G : TwoProverGame X Y A B) (α : I)

/-- Pointwise purification alignment extends to both endpoints of the tagged redraw,
with a penalty on the event that either endpoint is outside the winning support. -/
private theorem exists_taggedPairLocalUnitary_le [Fintype U] [DecidableEq U]
    (Q : PMF Transcript) (read : PairQ → U) (tag : PairQ → Message) (anchor : U) (e : Fin m ≃ Free)
    (ρ : Label × (Fin m → U) → Matrix ι ι ℂ)
    (v : Fin m → Label → U → EuclideanSpace ℂ (ι × κ))
    (hpur : let P := Q.map (questionTranscriptProjection C read e)
      ∀ i t u, WinningQuestionSupported P i t u →
        ‖NormedSpace.normalize (v i t u)‖ = 1 ∧
        quantumMarginalGivenMap (conditionalSnd P t) (fun z => ρ (t, z)) (fun z => z i) u =
          partialTraceRight (pureState (NormedSpace.normalize (v i t u))))
    {w B M : ℝ} (hw : 0 ≤ w)
    (hB : w * taggedPairAnchorTraceNormSq C G α Q read tag anchor e ρ ≤ B)
    (hM : w * taggedPairAnchorMissMass C G α Q read tag anchor e ≤ M) :
    ∃ V : Fin m → Label → U → Matrix κ κ ℂ,
      (∀ i t u, V i t u ∈ unitaryGroup κ ℂ) ∧
      w * taggedPairScore C G α Q read tag e
        (fun i t u => localUnitaryErrorSq (V i t u) (v i t u) (v i t anchor)) ≤
        Real.sqrt (m * w * B) + 4 * M := by
  classical
  let P := Q.map (questionTranscriptProjection C read e)
  let stateAt (i : Fin m) (t : Label) (u : U) :=
    quantumMarginalGivenMap (conditionalSnd P t) (fun z => ρ (t, z)) (fun z => z i) u
  let d (i : Fin m) (t : Label) (u : U) := (stateAt i t u - stateAt i t anchor).traceNorm
  have hlocal (i : Fin m) (t : Label) (u : U) :
      ∃ V ∈ unitaryGroup κ ℂ, localUnitaryErrorSq V (v i t u) (v i t anchor) ≤
        d i t u + 4 * winningAnchorMiss P anchor i t u := by
    by_cases h : WinningQuestionSupported P i t u ∧ WinningQuestionSupported P i t anchor
    · obtain ⟨h₁, he₁⟩ := hpur i t u h.1
      obtain ⟨h₂, he₂⟩ := hpur i t anchor h.2
      obtain ⟨V, hV, herr⟩ := exists_localUnitary_norm_sub_sq_le_traceNorm _ _ h₁ h₂
      refine ⟨V, hV, ?_⟩
      change stateAt i t u = _ at he₁
      change stateAt i t anchor = _ at he₂
      rw [winningAnchorMiss, ite_eq_left h, mul_zero, add_zero]
      change _ ≤ (stateAt i t u - stateAt i t anchor).traceNorm
      rw [he₁, he₂]
      exact herr
    · refine ⟨1, by simp, (localUnitaryErrorSq_one_le _ _).trans ?_⟩
      simp only [winningAnchorMiss, ite_eq_right h, mul_one]
      exact le_add_of_nonneg_left (traceNorm_nonneg _)
  choose V hV hscore using hlocal
  refine ⟨V, hV, taggedPairScore_le_sqrt_add C G α Q read tag e _ d
    (fun i t u => 4 * winningAnchorMiss P anchor i t u) hw hscore hB ?_⟩
  rw [taggedPairScore_mul, mul_left_comm w]
  exact mul_le_mul_of_nonneg_left hM (by norm_num)


/-- Scale used to state the summed alignment bounds without dividing by the anchor rate. -/
@[expose] noncomputable def anchoredAlignmentScale (α : I) : ℝ :=
  ((α : ℝ) ^ 2 / 2) * ((α : ℝ) / 4 * (α : ℝ))

/-- Bound on the scaled, summed squared alignment error from the checked-win probability,
the number of unchecked coordinates and the cardinality of the checked-answer alphabet. -/
@[expose] noncomputable def anchoredAlignmentBound (α : I) (m answers : ℕ) (p : ℝ) : ℝ :=
  let w := (α : ℝ) ^ 2 / 2
  let ε₁ := Real.sqrt (m * Real.log (1 / p) / 2)
  let ε₂ := Real.sqrt (m * Real.log (answers / p) / 2)
  let D := 2 * (w * ε₁ + (1 + w) * (2 * ε₁ + ε₂))
  let B := (2 * (α : ℝ) + 2) * (w * (2 * (Real.log answers - Real.log p)) + 4 * D)
  Real.sqrt (m * anchoredAlignmentScale α * B) + 4 * (((α : ℝ) + 1) * D)

private theorem exists_quantitativeTaggedPairLocalUnitary_le [Fintype U] [DecidableEq U]
    [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    (S : RepeatedStrategy)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support)
    (read : PairQ → U) (tag : PairQ → Message) (anchor : U) (e : Fin m ≃ Free)
    (ρ : Label × (Fin m → U) → Matrix L L ℂ)
    (v : Fin m → Label → U → EuclideanSpace ℂ (L × R))
    (hρ : ∀ z, IsDensityMatrix (ρ z)) :
    let T := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let Q := T.filter W hs
    let p := (T.toOuterMeasure W).toReal
    let P := Q.map (questionTranscriptProjection C read e)
    (∀ i t u, WinningQuestionSupported P i t u →
        ‖NormedSpace.normalize (v i t u)‖ = 1 ∧
        quantumMarginalGivenMap (conditionalSnd P t) (fun z => ρ (t, z)) (fun z => z i) u =
          partialTraceRight (pureState (NormedSpace.normalize (v i t u)))) →
    (sumConditionalTraceNormSq P ρ ≤ 2 * (Real.log (Fintype.card Answer) - Real.log p)) →
    ((α : ℝ) / 4 * taggedPairConditionalTraceNormSq C G α Q read tag e ρ ≤
      priorConditionalTraceNormSq C G α Q read e ρ) →
    ((α : ℝ) * taggedPairAnchorTraceNormSq C G α Q read tag anchor e ρ ≤
      (2 * (α : ℝ) + 2) * taggedPairConditionalTraceNormSq C G α Q read tag e ρ) →
    ((α : ℝ) / 4 * (α : ℝ) * taggedPairAnchorMissMass C G α Q read tag anchor e ≤
      ((α : ℝ) + 1) * ∑ j : Free, dist (Q.map fun z =>
        (freeTrials C z j, restTranscript C j z)) (priorTrialAndRest G α C Q j)) →
    ∃ V : Fin m → Label → U → Matrix R R ℂ,
      (∀ i t u, V i t u ∈ unitaryGroup R ℂ) ∧
      anchoredAlignmentScale α * taggedPairScore C G α Q read tag e
        (fun i t u => localUnitaryErrorSq (V i t u) (v i t u) (v i t anchor)) ≤
        anchoredAlignmentBound α m (Fintype.card (C → A × B)) p := by
  classical
  intro T W Q p P hpur hwin htag hanchor hmiss
  let w := (α : ℝ) ^ 2 / 2
  let ε₁ := Real.sqrt (m * Real.log (1 / p) / 2)
  let ε₂ := Real.sqrt (m * Real.log (Fintype.card (C → A × B) / p) / 2)
  let D := 2 * (w * ε₁ + (1 + w) * (2 * ε₁ + ε₂))
  let bound := (2 * (α : ℝ) + 2) *
    (w * (2 * (Real.log (Fintype.card Answer) - Real.log p)) + 4 * D)
  have hα : 0 ≤ (α : ℝ) := α.2.1
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hscale : 0 ≤ anchoredAlignmentScale α := by unfold anchoredAlignmentScale; positivity
  have hraw := priorConditionalTraceNormSq_le C G α S hs read e hρ
  dsimp only at hraw
  have htrace : w * priorConditionalTraceNormSq C G α Q read e ρ ≤
      w * (2 * (Real.log (Fintype.card Answer) - Real.log p)) + 4 * D := by
    refine hraw.trans ?_
    have h := add_le_add (mul_le_mul_of_nonneg_left hwin hw) (le_refl (4 * D))
    convert h using 1
    dsimp only [D, ε₁, ε₂, w]
    ring
  have hB : anchoredAlignmentScale α * taggedPairAnchorTraceNormSq C G α Q read tag anchor e ρ ≤
      bound := by
    have h₁ := mul_le_mul_of_nonneg_left hanchor (show 0 ≤ w * ((α : ℝ) / 4) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htag hw)
      (show 0 ≤ 2 * (α : ℝ) + 2 by positivity)
    have h₃ := mul_le_mul_of_nonneg_left htrace (show 0 ≤ 2 * (α : ℝ) + 2 by positivity)
    calc
      _ = (w * ((α : ℝ) / 4)) *
          ((α : ℝ) * taggedPairAnchorTraceNormSq C G α Q read tag anchor e ρ) := by
        unfold anchoredAlignmentScale
        dsimp only [w]
        ring
      _ ≤ _ := h₁
      _ = (2 * (α : ℝ) + 2) *
          (w * ((α : ℝ) / 4 * taggedPairConditionalTraceNormSq C G α Q read tag e ρ)) := by ring
      _ ≤ _ := h₂.trans h₃
  have hcard : Fintype.card Free = m := (Fintype.card_congr e.symm).trans (Fintype.card_fin m)
  have hdist := sum_dist_trial_rest_independent_given_wins G α C S hs
  dsimp only at hdist
  rw [hcard] at hdist
  have hM : anchoredAlignmentScale α * taggedPairAnchorMissMass C G α Q read tag anchor e ≤
      ((α : ℝ) + 1) * D := by
    have h₂ := mul_le_mul_of_nonneg_left hdist (show 0 ≤ (α : ℝ) + 1 by positivity)
    change w * ((α : ℝ) / 4 * (α : ℝ)) * _ ≤ _
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left hmiss hw).trans (by
      rw [mul_left_comm w]
      exact h₂)
  have h := exists_taggedPairLocalUnitary_le C G α Q read tag anchor e ρ v hpur hscale hB hM
  have hAnswer : Fintype.card Answer = Fintype.card (C → A × B) :=
    Fintype.card_congr (Equiv.arrowProdEquivProdArrow C (fun _ => A) (fun _ => B)).symm
  simpa only [anchoredAlignmentBound, bound, D, ε₁, ε₂, w, hAnswer] using h

/-- Averaged local unitaries on Bob's system align the sampled and anchored noisy branches
when the selected message is Alice's tagged question. -/
theorem exists_bob_taggedLocalUnitary_le [Nonempty A] [Nonempty B]
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support) :
    let T := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let Q := T.filter W hs
    let v (i : Fin m) (label : Label) (y : Option Y) :=
      let (t, a, b) := label
      checkedVectorGivenBob G α C S (e i) (omitMessage C (e i) t) (t.halves (e i)) y a b
    ∃ V : Fin m → Label → Option Y → Matrix κ κ ℂ,
      (∀ i t y, V i t y ∈ unitaryGroup κ ℂ) ∧
      anchoredAlignmentScale α * taggedPairScore C G α Q Prod.snd (Sum.inl ∘ Prod.fst) e
        (fun i t y => localUnitaryErrorSq (V i t y) (v i t y) (v i t none)) ≤
        anchoredAlignmentBound α m (Fintype.card (C → A × B)) (T.toOuterMeasure W).toReal := by
  classical
  intro T W Q v
  obtain ⟨ρ, hρ, hbranch, htrace⟩ :=
    exists_alice_sum_conditionalTraceNormSq_le_after_wins G α C S e hs
  refine exists_quantitativeTaggedPairLocalUnitary_le C G α S hs
    Prod.snd (Sum.inl ∘ Prod.fst) none e ρ v hρ ?_ htrace
    (leftTaggedPairConditionalTraceNormSq_le C G α Q e ρ)
    (leftTaggedPairAnchorTraceNormSq_le C G α Q e ρ)
    (leftTaggedPairAnchorMissMass_le C G α Q e)
  intro i label y hy
  rcases label with ⟨t, a, b⟩
  obtain ⟨ht, hy⟩ := (winningQuestionSupported_iff _ _ _ _).mp hy
  exact checkedVectorGivenBob_purifies_winningMarginal G α C S e hs hρ hbranch t a b i y ht hy

/-- Averaged local unitaries on Alice's system align the sampled and anchored noisy branches
when the selected message is Bob's tagged question. Alice is the second tensor factor. -/
theorem exists_alice_taggedLocalUnitary_le [Nonempty A] [Nonempty B]
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support) :
    let T := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let Q := T.filter W hs
    let v (i : Fin m) (label : Label) (x : Option X) :=
      let (t, a, b) := label
      checkedVectorGivenAlice G α C S (e i) t x a b
    ∃ V : Fin m → Label → Option X → Matrix ι ι ℂ,
      (∀ i t x, V i t x ∈ unitaryGroup ι ℂ) ∧
      anchoredAlignmentScale α * taggedPairScore C G α Q Prod.fst (Sum.inr ∘ Prod.snd) e
        (fun i t x => localUnitaryErrorSq (V i t x) (v i t x) (v i t none)) ≤
        anchoredAlignmentBound α m (Fintype.card (C → A × B)) (T.toOuterMeasure W).toReal := by
  classical
  intro T W Q v
  obtain ⟨ρ, hρ, hbranch, htrace⟩ :=
    exists_bob_sum_conditionalTraceNormSq_le_after_wins G α C S e hs
  refine exists_quantitativeTaggedPairLocalUnitary_le C G α S hs
    Prod.fst (Sum.inr ∘ Prod.snd) none e ρ v hρ ?_ htrace
    (rightTaggedPairConditionalTraceNormSq_le C G α Q e ρ)
    (rightTaggedPairAnchorTraceNormSq_le C G α Q e ρ)
    (rightTaggedPairAnchorMissMass_le C G α Q e)
  intro i label x hx
  rcases label with ⟨t, a, b⟩
  obtain ⟨ht, hx⟩ := (winningQuestionSupported_iff _ _ _ _).mp hx
  exact checkedVectorGivenAlice_purifies_winningMarginal G α C S e hs hρ hbranch t a b i x ht hx


/-- Reversing alignment exchanges the branches and takes the adjoint of the unitary. -/
theorem localUnitaryErrorSq_conjTranspose {V : Matrix κ κ ℂ} (hV : V ∈ unitaryGroup κ ℂ)
    (v u : EuclideanSpace ℂ (ι × κ)) :
    localUnitaryErrorSq Vᴴ u v = localUnitaryErrorSq V v u := by
  let M := (1 : Matrix ι ι ℂ) ⊗ₖ V
  let N := (1 : Matrix ι ι ℂ) ⊗ₖ Vᴴ
  let f := toEuclideanCLM (n := ι × κ) (𝕜 := ℂ) M
  have hM : M ∈ unitaryGroup (ι × κ) ℂ := kronecker_mem_unitary (one_mem _) hV
  have hMN : M * N = 1 := by
    dsimp only [M, N]
    rw [← mul_kronecker_mul, Matrix.one_mul, ← star_eq_conjTranspose,
      (mem_unitaryGroup_iff.mp hV), one_kronecker_one]
  let ψ := NormedSpace.normalize v
  let φ := NormedSpace.normalize u
  let φ' := WithLp.toLp 2 (N *ᵥ φ.ofLp)
  have he : f φ' = φ := by
    change WithLp.toLp 2 (M *ᵥ (N *ᵥ φ.ofLp)) = φ
    rw [mulVec_mulVec, hMN, one_mulVec, WithLp.toLp_ofLp]
  unfold localUnitaryErrorSq localUnitaryError
  change ‖φ' - ψ‖ ^ 2 = ‖f ψ - φ‖ ^ 2
  rw [← (mem_unitaryGroup_iff_forall_norm_toEuclideanCLM M).mp hM (φ' - ψ),
    map_sub, he, norm_sub_rev]

private theorem exists_fixedAnchorLocalUnitary_le
    (Q : PMF Transcript) (read : PairQ → U) (tag : PairQ → Message) (anchor : U) (e : Fin m ≃ Free)
    (msg : Message) (v : Fin m → Label → U → EuclideanSpace ℂ (ι × κ))
    (hsel : ∀ f : Fin m → Label → U → ℝ, (∀ i t u, 0 ≤ f i t u) →
      (α : ℝ) * taggedPairScore C G α Q read (fun _ => msg) e f ≤
        taggedPairScore C G α Q read tag e f)
    {B : ℝ}
    (h : ∃ V : Fin m → Label → U → Matrix κ κ ℂ,
      (∀ i t u, V i t u ∈ unitaryGroup κ ℂ) ∧
      anchoredAlignmentScale α * taggedPairScore C G α Q read tag e
        (fun i t u => localUnitaryErrorSq (V i t u) (v i t u) (v i t anchor)) ≤ B) :
    ∃ V : Fin m → Label → U → Matrix κ κ ℂ,
      (∀ i t u, V i t u ∈ unitaryGroup κ ℂ) ∧
      ((α : ℝ) * anchoredAlignmentScale α) *
        taggedPairScore C G α Q read (fun _ => msg) e
          (fun i t u => localUnitaryErrorSq (V i t u) (v i t anchor) (v i t u)) ≤ B := by
  obtain ⟨V, hV, hbound⟩ := h
  refine ⟨fun i t u => (V i t u)ᴴ, ?_, ?_⟩
  · intro i t u
    change (V i t u)ᴴ ∈ unitaryGroup κ ℂ
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_conjTranspose,
      ← star_eq_conjTranspose]
    exact mem_unitaryGroup_iff'.mp (hV i t u)
  · simp only [localUnitaryErrorSq_conjTranspose (hV _ _ _)]
    rw [mul_comm (α : ℝ), mul_assoc]
    have hscale : 0 ≤ anchoredAlignmentScale α := by
      have hα := α.2.1
      unfold anchoredAlignmentScale
      positivity
    have hfixed := hsel (fun i t u => localUnitaryErrorSq (V i t u) (v i t u) (v i t anchor))
      (fun _ _ _ => sq_nonneg _)
    exact (mul_le_mul_of_nonneg_left hfixed hscale).trans hbound

/-- With Alice's message anchored, Bob's unitary depends on the remaining transcript and
Bob's question. It takes the doubly anchored branch to the branch with Bob's actual question.
This is the summed squared form of the alignment in equation (30). -/
theorem exists_bob_anchorLocalUnitary_le [Nonempty A] [Nonempty B]
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support) :
    let T := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let Q := T.filter W hs
    let v (i : Fin m) (label : Label) (y : Option Y) :=
      let (t, a, b) := label
      checkedVectorGivenBob G α C S (e i) (omitMessage C (e i) t) (t.halves (e i)) y a b
    ∃ V : Fin m → Label → Option Y → Matrix κ κ ℂ,
      (∀ i t y, V i t y ∈ unitaryGroup κ ℂ) ∧
      ((α : ℝ) * anchoredAlignmentScale α) *
        taggedPairScore C G α Q Prod.snd (fun _ => Sum.inl none) e
          (fun i t y => localUnitaryErrorSq (V i t y) (v i t none) (v i t y)) ≤
          anchoredAlignmentBound α m (Fintype.card (C → A × B)) (T.toOuterMeasure W).toReal := by
  intro T W Q v
  exact exists_fixedAnchorLocalUnitary_le C G α Q Prod.snd (Sum.inl ∘ Prod.fst) none e
    (Sum.inl none) v (leftAnchorTagScore_le C G α Q e)
    (exists_bob_taggedLocalUnitary_le C G α S e hs)

/-- With Bob's message anchored, Alice's unitary depends on the remaining transcript and
Alice's question. It takes the doubly anchored branch to the branch with Alice's actual
question, with Alice's system second. This is the summed squared alignment for equation (29). -/
theorem exists_alice_anchorLocalUnitary_le [Nonempty A] [Nonempty B]
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support) :
    let T := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let Q := T.filter W hs
    let v (i : Fin m) (label : Label) (x : Option X) :=
      let (t, a, b) := label
      checkedVectorGivenAlice G α C S (e i) t x a b
    ∃ V : Fin m → Label → Option X → Matrix ι ι ℂ,
      (∀ i t x, V i t x ∈ unitaryGroup ι ℂ) ∧
      ((α : ℝ) * anchoredAlignmentScale α) *
        taggedPairScore C G α Q Prod.fst (fun _ => Sum.inr none) e
          (fun i t x => localUnitaryErrorSq (V i t x) (v i t none) (v i t x)) ≤
          anchoredAlignmentBound α m (Fintype.card (C → A × B)) (T.toOuterMeasure W).toReal := by
  intro T W Q v
  exact exists_fixedAnchorLocalUnitary_le C G α Q Prod.fst (Sum.inr ∘ Prod.snd) none e
    (Sum.inr none) v (rightAnchorTagScore_le C G α Q e)
    (exists_alice_taggedLocalUnitary_le C G α S e hs)

end Cslib.PCP.AnchoredDependency
