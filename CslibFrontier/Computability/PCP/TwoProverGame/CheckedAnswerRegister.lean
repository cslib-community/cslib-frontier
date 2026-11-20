/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AveragedAnswerMarginals
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Normalize
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BlockDiagonalOrder
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyDomination
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map

/-!
# Checked-answer states with a retained question register

Sample a classical label carrying the transcript and Bob's question, then sample the
full local questions independently given that label. Retain the label and both checked
answers while discarding Bob's quantum register. The state restricted to a label-dependent
answer event has trace equal to the actual probability of the event.

Its normalized state has relative entropy at most the logarithm of the number of
answer labels minus the logarithm of the event probability, relative to the product
reference with uniform answers. This combines the operator comparison and postselection
cost used in [Bavarian, Vidick and Yuen, Claim 5.13][BavarianVidickYuen2022].

## Main definitions

* `checkedAnswerRegister`: the subnormalized Alice state with both classical registers.
* `checkedAnswerProductReference`: the product of Alice's marginal, Bob's label law and
  the uniform checked-answer state, conditional on the retained label.

## Main results

* `trace_checkedAnswerRegister`: the restricted operator has the actual event probability.
* `relativeEntropy_normalize_checkedAnswerRegister_le`: the logarithmic event and answer budget.
-/

public section

namespace Cslib.PCP.QuantumStrategy

open Quantum Matrix Finset Cslib.Probability.PMF
open scoped ComplexOrder MatrixOrder

variable {τ X Y L A B ι κ : Type*} [Fintype τ] [DecidableEq τ] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype X] [Fintype Y]

variable (S : QuantumStrategy X Y (τ → A) (τ → B) ι κ) (C : Finset τ)

local notation "Answer" => ((C → A) × (C → B))
local notation "Space" => (ι × (L × Answer))

/-- The joint law obtained by sampling a label and then running the independently
averaged checked-answer experiment at that label. -/
@[expose] noncomputable def checkedAnswersWithLabel (p : L → PMF X) (r : PMF L) (q : L → PMF Y) :
    PMF (L × Answer) :=
  r.bind fun y => ((p y).bind fun x => (q y).bind fun t => S.checkedAnswers C x t).map (y, ·)

omit [Fintype X] [Fintype Y] in
/-- The joint mass is the label mass times the conditional checked-answer mass. -/
theorem checkedAnswersWithLabel_apply (p : L → PMF X) (r : PMF L) (q : L → PMF Y)
    (z : L × Answer) :
    S.checkedAnswersWithLabel C p r q z =
      r z.1 * ((p z.1).bind fun x => (q z.1).bind fun t => S.checkedAnswers C x t) z.2 :=
  bind_map_prodMk_apply r (fun y => (p y).bind fun x => (q y).bind fun t =>
    S.checkedAnswers C x t) z

open Classical in
/-- The checked-answer operator retains Bob's label and both checked answers as classical
registers. The event is applied before normalization, so excluded branches are zero blocks. -/
noncomputable def checkedAnswerRegister (p : L → PMF X) (r : PMF L) (q : L → PMF Y)
    (W : L → Set Answer) : Matrix Space Space ℂ :=
  blockDiagonal fun (y, a, b) => if (a, b) ∈ W y then
    (r y).toReal • partialTraceRight (pureState (S.averagedCheckedVector C (p y) (q y) a b)) else 0

open Classical in
/-- At each label the reference uses the nonselective Alice marginal and an independent
uniform answer register. It is normalized when the answer alphabet is nonempty. -/
noncomputable def checkedAnswerProductReference (p : L → PMF X) (r : PMF L) :
    Matrix Space Space ℂ :=
  blockDiagonal fun (y, _) =>
    ((r y).toReal / Fintype.card Answer) • S.averagedCheckedMarginalAlice C (p y)

open Classical in
/-- Only equal classical labels in the retained event contribute a matrix entry. -/
theorem checkedAnswerRegister_apply (p : L → PMF X) (r : PMF L) (q : L → PMF Y)
    (W : L → Set Answer) (i j : ι) (y : L) (a : C → A) (b : C → B) (z' : L × Answer) :
    S.checkedAnswerRegister C p r q W (i, (y, a, b)) (j, z') =
      if (y, a, b) = z' ∧ (a, b) ∈ W y then
        (r y).toReal • partialTraceRight
          (pureState (S.averagedCheckedVector C (p y) (q y) a b)) i j else 0 := by
  by_cases he : (y, a, b) = z'
  · subst z'
    by_cases hw : (a, b) ∈ W y <;> simp [checkedAnswerRegister, blockDiagonal_apply, hw]
  · simp [checkedAnswerRegister, blockDiagonal_apply, he]

omit [Fintype Y] in
open Classical in
/-- In each classical block the reference uses the Alice state at that label
and assigns equal weight to every checked answer. -/
theorem checkedAnswerProductReference_apply (p : L → PMF X) (r : PMF L)
    (i j : ι) (z z' : L × Answer) :
    S.checkedAnswerProductReference C p r (i, z) (j, z') =
      if z = z' then
        ((r z.1).toReal / Fintype.card Answer) •
          S.averagedCheckedMarginalAlice C (p z.1) i j else 0 := by
  rcases z with ⟨y, a, b⟩
  by_cases he : (y, a, b) = z'
  · subst z'
    simp [checkedAnswerProductReference, blockDiagonal_apply]
  · simp [checkedAnswerProductReference, blockDiagonal_apply, he]

/-- The retained state is positive before and after restricting the accepted answers. -/
theorem posSemidef_checkedAnswerRegister [Finite L] (p : L → PMF X) (r : PMF L) (q : L → PMF Y)
    (W : L → Set Answer) : (S.checkedAnswerRegister C p r q W).PosSemidef := by
  classical
  rw [checkedAnswerRegister]
  apply posSemidef_blockDiagonal
  rintro ⟨y, a, b⟩
  dsimp only
  split_ifs
  · exact (posSemidef_partialTraceRight (posSemidef_pureState _)).smul ENNReal.toReal_nonneg
  · exact PosSemidef.zero

omit [Fintype Y] in
/-- The product reference has trace one when there is a possible checked answer. -/
theorem isDensityMatrix_checkedAnswerProductReference [Fintype L]
    [Nonempty (C → A)] [Nonempty (C → B)] (p : L → PMF X) (r : PMF L) :
    IsDensityMatrix (S.checkedAnswerProductReference C p r) := by
  classical
  have hm (y : L) := S.isDensityMatrix_averagedCheckedMarginalAlice C (p y)
  rw [checkedAnswerProductReference]
  refine ⟨posSemidef_blockDiagonal fun z => (hm z.1).posSemidef.smul
    (div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)), ?_⟩
  rw [trace_blockDiagonal, Fintype.sum_prod_type]
  simp only [trace_smul, (hm _).trace_eq_one, Complex.real_smul, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
  have hc : (Fintype.card Answer : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [mul_div_cancel₀ _ hc]
  exact_mod_cast sum_toReal r

/-- The trace of the restricted register is the probability of the retained answers under
the original question draws and the strategy's checked-answer law. -/
theorem trace_checkedAnswerRegister [Fintype L] (p : L → PMF X) (r : PMF L) (q : L → PMF Y)
    (W : L → Set Answer) :
    (S.checkedAnswerRegister C p r q W).trace.re =
      ((S.checkedAnswersWithLabel C p r q).toOuterMeasure {z | z.2 ∈ W z.1}).toReal := by
  classical
  rw [checkedAnswerRegister, trace_blockDiagonal, Complex.re_sum, toOuterMeasure_toReal_eq_sum_ite]
  apply sum_congr rfl
  rintro ⟨y, a, b⟩ _
  by_cases h : (a, b) ∈ W y
  · simp only [h, ite_true, Set.mem_ofPred_eq, trace_smul, trace_partialTraceRight, trace_pureState,
      S.norm_averagedCheckedVector_sq, Complex.real_smul, ← Complex.ofReal_mul, Complex.ofReal_re,
      S.checkedAnswersWithLabel_apply, ENNReal.toReal_mul, mul_one]
  · simp [h]

/-- Each retained branch is bounded by the Alice marginal at that label times its weight.
Making the checked answers uniform in the product reference costs exactly their cardinality. -/
theorem checkedAnswerRegister_le_card_smul [Finite L] (p : L → PMF X) (r : PMF L) (q : L → PMF Y)
    (W : L → Set Answer) :
    S.checkedAnswerRegister C p r q W ≤
      (Fintype.card Answer : ℝ) • S.checkedAnswerProductReference C p r := by
  classical
  by_cases hc : Fintype.card Answer = 0
  · have : IsEmpty Answer := Fintype.card_eq_zero_iff.mp hc
    have : IsEmpty Space := inferInstanceAs (IsEmpty (ι × (L × Answer)))
    exact le_of_eq (Subsingleton.elim _ _)
  have hcard : (Fintype.card Answer : ℝ) ≠ 0 := by exact_mod_cast hc
  rw [checkedAnswerRegister, checkedAnswerProductReference, ← blockDiagonal_smul]
  apply blockDiagonal_mono
  rintro ⟨y, a, b⟩
  simp only [Pi.smul_apply, smul_smul, mul_div_cancel₀ _ hcard]
  split_ifs
  · exact smul_le_smul_of_nonneg_left
      (S.partialTraceRight_averagedCheckedVector_le C (p y) (q y) a b) ENNReal.toReal_nonneg
  · exact ((S.isDensityMatrix_averagedCheckedMarginalAlice C (p y)).posSemidef.smul
      ENNReal.toReal_nonneg).nonneg

/-- Conditioning on a positive-probability event in the checked answers costs its negative
log probability. Keeping the checked answers in the state costs at most the logarithm of
their alphabet size. Bob's classical question label remains present in both states. -/
theorem relativeEntropy_normalize_checkedAnswerRegister_le
    [Fintype L] [DecidableEq L] [DecidableEq A] [DecidableEq B]
    [Nonempty (C → A)] [Nonempty (C → B)]
    (p : L → PMF X) (r : PMF L) (q : L → PMF Y) (W : L → Set Answer)
    (hW : 0 < ((S.checkedAnswersWithLabel C p r q).toOuterMeasure {z | z.2 ∈ W z.1}).toReal) :
    relativeEntropy (normalizeDensity (S.checkedAnswerRegister C p r q W))
      (S.checkedAnswerProductReference C p r) ≤
        ((Real.log (Fintype.card Answer) -
          Real.log ((S.checkedAnswersWithLabel C p r q).toOuterMeasure {z | z.2 ∈ W z.1}).toReal :
            ℝ) : WithTop ℝ) := by
  let R := S.checkedAnswerRegister C p r q W
  let T := S.checkedAnswerProductReference C p r
  let ρ := normalizeDensity R
  have hR : R.PosSemidef := S.posSemidef_checkedAnswerRegister C p r q W
  have hT : T.PosSemidef := (S.isDensityMatrix_checkedAnswerProductReference C p r).posSemidef
  have hm := S.trace_checkedAnswerRegister C p r q W
  rw [← hm] at hW ⊢
  change 0 < R.trace.re at hW
  have hρ : IsDensityMatrix ρ := isDensityMatrix_normalizeDensity hR hW
  have hcard : (0 : ℝ) < Fintype.card Answer := by exact_mod_cast Fintype.card_pos
  have hbound := relativeEntropy_le_add_log_of_le_smul hρ hR hT hcard
    (S.checkedAnswerRegister_le_card_smul C p r q W)
  have he : relativeEntropy ρ R = ((-Real.log R.trace.re : ℝ) : WithTop ℝ) := by
    conv_lhs => rw [← trace_smul_normalizeDensity hR]
    rw [relativeEntropy_smul_right hρ.posSemidef.isHermitian hρ.posSemidef.isHermitian hW,
      relativeEntropy_self, hρ.trace_eq_one, Complex.one_re, mul_one, zero_add]
  rw [he, ← WithTop.coe_add] at hbound
  simpa only [sub_eq_add_neg, add_comm] using hbound

end Cslib.PCP.QuantumStrategy
