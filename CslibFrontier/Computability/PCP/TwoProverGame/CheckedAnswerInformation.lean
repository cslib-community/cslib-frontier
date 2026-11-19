/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.CheckedAnswerRegister
public import CslibFrontier.Foundations.Quantum.DensityMatrix.QuantumRaz
import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumConditioning
import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumPostselection
import CslibFrontier.Probability.PMF.Event
import Mathlib.Probability.Distributions.Uniform

/-!
# Coordinate information after a checked win

Condition on a shared label, draw the second player's question tuple from a product law,
and run the checked-answer experiment. The win filter sees the shared label and the checked
answers. Regroup those observations into a transcript and keep the question tuple in a
separate classical register. Each conditional quantum block is the normalized Alice
marginal of the original checked branch.

The sum of the coordinate mutual informations, averaged over the winning transcripts,
is bounded by the logarithm of the checked-answer alphabet size minus the logarithm of
the win probability. This is the information comparison used on the Alice side of
[Bavarian, Vidick and Yuen, Claim 5.13][BavarianVidickYuen2022].

## Main definitions

* `checkedWinTranscriptLaw`: the filtered law grouped by the shared label and checked answers.

## Main results

* `exists_checkedWin_coordinateInformation_le`: the coordinate bound with an explicit
  characterization of the conditional quantum states at every supported branch.
-/

public section

namespace Cslib.PCP.QuantumStrategy

open Quantum Matrix Finset Cslib.Probability.PMF
open scoped ComplexOrder

universe u

variable {τ X Y Ω A B ι κ : Type*} [Fintype τ] [DecidableEq τ]
  [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype X] [Fintype Y]
  [Fintype Ω]

variable (S : QuantumStrategy X Y (τ → A) (τ → B) ι κ) (C : Finset τ)
variable {m : ℕ} (V : Fin m → Type u) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

local notation "Answer" => ((C → A) × (C → B))
local notation "Transcript" => (Ω × Answer)

private def checkedTranscriptEquiv :
    ((Ω × (∀ i, V i)) × Answer) ≃ (Transcript × (∀ i, V i)) where
  toFun | ((ω, y), a) => ((ω, a), y)
  invFun | ((ω, a), y) => ((ω, y), a)
  left_inv _ := rfl
  right_inv _ := rfl

variable (p : Ω → PMF X) (r : PMF Ω) (s : Ω → ∀ i, PMF (V i))
  (q : Ω → (∀ i, V i) → PMF Y) (W : Ω → Set ((C → A) × (C → B)))

local notation "Prior" => (PMF.bind r fun ω => PMF.map (fun y => (ω, y)) (pi (s ω)))
local notation "QuestionA" => (fun z => p (Prod.fst z))
local notation "QuestionB" => (fun (ω, y) => q ω y)
local notation "Win" => (Set.ofPred fun z => Prod.snd z ∈ W (Prod.fst (Prod.fst z)))
local notation "Law" => (S.checkedAnswersWithLabel C QuestionA Prior QuestionB)

/-- The winning law, with the shared label and checked answers grouped into the transcript. -/
noncomputable def checkedWinTranscriptLaw (h : (0 : ℝ) < ((Law).toOuterMeasure Win).toReal) :
    PMF (Transcript × (∀ i, V i)) :=
  ((Law).filter Win ((toOuterMeasure_toReal_pos_iff _ _).mp h)).map
    (checkedTranscriptEquiv (C := C) (A := A) (B := B) (Ω := Ω) V)

omit [Fintype X] [Fintype Y] [Fintype Ω] [∀ i, DecidableEq (V i)] in
/-- Conditioning precedes the regrouping of the visible transcript and question tuple. -/
theorem checkedWinTranscriptLaw_eq_filter_map (h : (0 : ℝ) < ((Law).toOuterMeasure Win).toReal)
    (hs : ∃ z ∈ Win, z ∈ (Law).support) :
    S.checkedWinTranscriptLaw C V p r s q W h =
      ((Law).filter Win hs).map
        (fun ((ω, y), a) => ((ω, a), y)) := by
  unfold checkedWinTranscriptLaw
  rfl

omit [Fintype X] [Fintype Y] [Fintype Ω] [∀ i, DecidableEq (V i)] in
open Classical in
/-- The filtered transcript mass is the original checked-answer mass divided by the
win probability on the retained event, and zero off that event. -/
theorem checkedWinTranscriptLaw_apply_toReal (h : (0 : ℝ) < ((Law).toOuterMeasure Win).toReal)
    (ω : Ω) (a : C → A) (b : C → B) (y : ∀ i, V i) :
    (S.checkedWinTranscriptLaw C V p r s q W h ((ω, a, b), y)).toReal =
      if (a, b) ∈ W ω then ((Law) ((ω, y), a, b)).toReal / ((Law).toOuterMeasure Win).toReal
      else 0 := by
  let e := checkedTranscriptEquiv (C := C) (A := A) (B := B) (Ω := Ω) V
  change ((((Law).filter Win _).map e) (e ((ω, y), a, b))).toReal = _
  rw [map_equiv_apply, Equiv.symm_apply_apply, filter_apply_toReal]
  rfl

omit [Fintype Ω] in
/-- After observing a function of the free question tuple, the conditional Alice marginal
is obtained by averaging Bob's question law in that prior fiber and then normalizing the
checked-answer branch. Both the winning transcript and the fiber must have positive mass. -/
theorem quantumMarginalGivenMap_checkedWinTranscriptLaw {U : Type*}
    (h : (0 : ℝ) < ((Law).toOuterMeasure Win).toReal)
    {ρ : Transcript × (∀ i, V i) → Matrix ι ι ℂ}
    (hρ : ∀ z, IsDensityMatrix (ρ z))
    (hbranch : ∀ (ω : Ω) (a : C → A) (b : C → B) (y : ∀ i, V i),
      ((ω, a, b), y) ∈ (S.checkedWinTranscriptLaw C V p r s q W h).support →
      ρ ((ω, a, b), y) = normalizeDensity (partialTraceRight (pureState
        (S.averagedCheckedVector C (p ω) (q ω y) a b))))
    (ω : Ω) (a : C → A) (b : C → B) (f : (∀ i, V i) → U) (u : U)
    (ht : (ω, a, b) ∈ ((S.checkedWinTranscriptLaw C V p r s q W h).map Prod.fst).support)
    (hu : u ∈ ((conditionalSnd (S.checkedWinTranscriptLaw C V p r s q W h)
      (ω, a, b)).map f).support) :
    let base := conditionalSnd ((pi (s ω)).map fun y => (f y, y)) u
    quantumMarginalGivenMap
        (conditionalSnd (S.checkedWinTranscriptLaw C V p r s q W h) (ω, a, b))
        (fun y => ρ ((ω, a, b), y)) f u =
      normalizeDensity (partialTraceRight (pureState
        (S.averagedCheckedVector C (p ω) (base.bind (q ω)) a b))) := by
  classical
  let P := S.checkedWinTranscriptLaw C V p r s q W h
  let t : Transcript := (ω, a, b)
  let Q := conditionalSnd P t
  let M (y : ∀ i, V i) :=
    partialTraceRight (pureState (S.averagedCheckedVector C (p ω) (q ω y) a b))
  let c := (r ω).toReal / ((Law).toOuterMeasure Win).toReal / ((P.map Prod.fst) t).toReal
  have hW : (a, b) ∈ W ω := by
    by_contra hn
    obtain ⟨⟨t', y⟩, hy, ht'⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
    change t' = t at ht'
    subst t'
    have hpos := ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hy) (P.apply_ne_top (t, y))
    change ((S.checkedWinTranscriptLaw C V p r s q W h) ((ω, a, b), y)).toReal > 0 at hpos
    rw [S.checkedWinTranscriptLaw_apply_toReal C V p r s q W h, ite_eq_right hn] at hpos
    exact (lt_irrefl 0) hpos
  have hweight (y : ∀ i, V i) : (Q y).toReal = c * (pi (s ω) y).toReal * (M y).trace.re := by
    rw [show Q = conditionalSnd P t from rfl, conditionalSnd_apply _ _ ht, ENNReal.toReal_div]
    change ((S.checkedWinTranscriptLaw C V p r s q W h) ((ω, a, b), y)).toReal / _ = _
    rw [S.checkedWinTranscriptLaw_apply_toReal C V p r s q W h, ite_eq_left hW,
      checkedAnswersWithLabel_apply, bind_map_prodMk_apply, ENNReal.toReal_mul, ENNReal.toReal_mul]
    change ((r ω).toReal * (pi (s ω) y).toReal *
      (((p ω).bind fun x => (q ω y).bind fun z => S.checkedAnswers C x z) (a, b)).toReal) /
        ((Law).toOuterMeasure Win).toReal / ((P.map Prod.fst) t).toReal = _
    rw [← norm_averagedCheckedVector_sq, show M y = _ from rfl,
      trace_partialTraceRight, trace_pureState, Complex.ofReal_re]
    dsimp only [c]
    ring
  have hstate (y : ∀ i, V i) (hy : y ∈ Q.support) : ρ (t, y) = normalizeDensity (M y) :=
    hbranch ω a b y ((mem_support_conditionalSnd_iff P t ht y).mp hy)
  have he := quantumMarginalGivenMap_eq_normalize_of_weighted (pi (s ω)) Q
    (fun _ => posSemidef_partialTraceRight (posSemidef_pureState _))
    (fun y => hρ (t, y)) hstate hweight f hu
  rw [quantumMarginalGivenMap_eq_sum (pi (s ω))] at he
  change _ = normalizeDensity (∑ y,
    (conditionalSnd ((pi (s ω)).map fun y => (f y, y)) u y).toReal • M y) at he
  rw [← S.partialTraceRight_averagedCheckedVector_bind C (p ω) _ (q ω) a b] at he
  exact he

/-- The coordinate-information sum of the actual filtered checked-answer experiment.
On supported outcomes the conditional blocks are the normalized marginals of the
strategy's square-root checked-answer vectors. -/
theorem exists_checkedWin_coordinateInformation_le
    [Nonempty (C → A)] [Nonempty (C → B)]
    (h : (0 : ℝ) < ((Law).toOuterMeasure Win).toReal) :
    let P := S.checkedWinTranscriptLaw C V p r s q W h
    ∃ ρ : Transcript × (∀ i, V i) → Matrix ι ι ℂ,
      (∀ z, IsDensityMatrix (ρ z)) ∧
      (∀ (ω : Ω) (a : C → A) (b : C → B) (y : (∀ i, V i)),
        ((ω, a, b), y) ∈ P.support →
        ρ ((ω, a, b), y) =
          normalizeDensity (partialTraceRight (pureState
            (S.averagedCheckedVector C (p ω) (q ω y) a b)))) ∧
      (∑ t, (((P.map Prod.fst) t).toReal : WithTop ℝ) *
        ∑ i, mutualInformation
          (classicalQuantumMarginal (conditionalSnd P t) (fun y => ρ (t, y)) (fun y => y i))) ≤
        ((Real.log (Fintype.card Answer) - Real.log ((Law).toOuterMeasure Win).toReal : ℝ) :
          WithTop ℝ) := by
  classical
  let e := checkedTranscriptEquiv (C := C) (A := A) (B := B) (Ω := Ω) V
  let E := Equiv.prodCongr (Equiv.refl ι) e
  let P := S.checkedWinTranscriptLaw C V p r s q W h
  let R := S.checkedAnswerRegister C QuestionA Prior QuestionB (fun z => W z.1)
  let D := S.checkedAnswerProductReference C QuestionA Prior
  let mass := ((Law).toOuterMeasure Win).toReal
  let marginal (ω : Ω) (a : C → A) (b : C → B) (y : (∀ i, V i)) :=
    partialTraceRight (pureState (S.averagedCheckedVector C (p ω) (q ω y) a b))
  let blocks : Transcript × (∀ i, V i) → Matrix ι ι ℂ := fun ((ω, a, b), y) =>
    if (a, b) ∈ W ω then (mass⁻¹ * (Prior (ω, y)).toReal) • marginal ω a b y else 0
  have hR : R.PosSemidef := S.posSemidef_checkedAnswerRegister C _ _ _ _
  have hD : IsDensityMatrix D := S.isDensityMatrix_checkedAnswerProductReference C _ _
  have hmass : R.trace.re = mass := S.trace_checkedAnswerRegister C _ _ _ _
  have hpos (z : Transcript × (∀ i, V i)) : (blocks z).PosSemidef := by
    rcases z with ⟨⟨ω, a, b⟩, y⟩
    dsimp only [blocks]
    split_ifs
    · exact (posSemidef_partialTraceRight (posSemidef_pureState _)).smul
        (mul_nonneg (inv_nonneg.mpr h.le) ENNReal.toReal_nonneg)
    · exact PosSemidef.zero
  have hp := S.checkedWinTranscriptLaw_apply_toReal C V p r s q W h
  have hb (ω : Ω) (a : C → A) (b : C → B) (y : (∀ i, V i)) :
      (marginal ω a b y).trace.re =
        ((((p ω).bind fun x => (q ω y).bind fun t => S.checkedAnswers C x t) (a, b))).toReal := by
    dsimp only [marginal]
    rw [trace_partialTraceRight, trace_pureState, Complex.ofReal_re,
      S.norm_averagedCheckedVector_sq]
  have ht (z : Transcript × (∀ i, V i)) : (blocks z).trace.re = (P z).toReal := by
    rcases z with ⟨⟨ω, a, b⟩, y⟩
    rw [hp]
    dsimp only [blocks]
    split_ifs
    · rw [trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, hb, S.checkedAnswersWithLabel_apply, ENNReal.toReal_mul]
      ring
    · simp
  have heR : Matrix.reindex E E (normalizeDensity R) = blockDiagonal blocks := by
    ext ⟨i, ⟨ω, a, b⟩, y⟩ ⟨j, ⟨ω', a', b'⟩, y'⟩
    rw [normalizeDensity_apply, hmass]
    simp only [E, e, Matrix.reindex_apply, submatrix_apply, Equiv.prodCongr_symm,
      Equiv.prodCongr_apply, Equiv.refl_symm, checkedTranscriptEquiv, Equiv.coe_fn_symm_mk,
      Matrix.smul_apply]
    change mass⁻¹ • S.checkedAnswerRegister C QuestionA Prior QuestionB
      (fun z => W z.1) (i, ((ω, y), a, b)) (j, ((ω', y'), a', b')) = _
    rw [S.checkedAnswerRegister_apply, blockDiagonal_apply]
    by_cases he : ((ω, a, b), y) = ((ω', a', b'), y')
    · simp only [Prod.mk.injEq] at he
      rcases he with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
      by_cases hw : (a, b) ∈ W ω <;>
        simp [hw, blocks, marginal, Complex.ofReal_mul, mul_assoc]
    · have hn : ((ω, y), a, b) ≠ ((ω', y'), a', b') := fun h' => he (congrArg e h')
      simp [he, hn]
  let T : PMF Transcript := r.bind fun ω => (Probability.PMF.uniformOfFintype Answer).map (ω, ·)
  let U : PMF (Transcript × (∀ i, V i)) := T.bind fun t => (pi (s t.1)).map (t, ·)
  let σ (t : Transcript) := S.averagedCheckedMarginalAlice C (p t.1)
  have hσ (t : Transcript) : IsDensityMatrix (σ t) :=
    S.isDensityMatrix_averagedCheckedMarginalAlice C _
  have heD : Matrix.reindex E E D = classicalQuantumState U (σ ∘ Prod.fst) := by
    ext ⟨i, ⟨ω, a, b⟩, y⟩ ⟨j, ⟨ω', a', b'⟩, y'⟩
    simp only [E, e, Matrix.reindex_apply, submatrix_apply, Equiv.prodCongr_symm,
      Equiv.prodCongr_apply, Equiv.refl_symm, checkedTranscriptEquiv, Equiv.coe_fn_symm_mk]
    change S.checkedAnswerProductReference C QuestionA Prior
      (i, ((ω, y), a, b)) (j, ((ω', y'), a', b')) = _
    rw [S.checkedAnswerProductReference_apply, classicalQuantumState, blockDiagonal_apply]
    by_cases he : ((ω, a, b), y) = ((ω', a', b'), y')
    · simp only [Prod.mk.injEq] at he
      rcases he with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
      simp only [ite_true]
      simp only [T, U, bind_map_prodMk_apply, ENNReal.toReal_mul,
        Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        σ, Function.comp_apply, Matrix.smul_apply]
      rw [div_eq_mul_inv, mul_right_comm]
    · have hn : ((ω, y), a, b) ≠ ((ω', y'), a', b') := fun h' => he (congrArg e h')
      simp [he, hn]
  obtain ⟨ρ, hρ, hnorm, hblocks⟩ := exists_classicalQuantumState_eq_blockDiagonal
    P blocks hpos ht (isDensityMatrix_pureState S.norm_state).partialTraceRight
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro ω a b y hz
    have hp' := ENNReal.toReal_pos hz (P.apply_ne_top _)
    rw [hp] at hp'
    split_ifs at hp' with hw
    · have hPrior : 0 < (Prior (ω, y)).toReal := by
        by_contra! h0
        have hz' := le_antisymm h0 ENNReal.toReal_nonneg
        rw [S.checkedAnswersWithLabel_apply, ENNReal.toReal_mul, hz', zero_mul, zero_div] at hp'
        exact lt_irrefl _ hp'
      rw [hnorm _ hz]
      simp only [blocks, hw, ite_true]
      rw [normalizeDensity_apply, normalizeDensity_apply, trace_smul, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, smul_smul,
        _root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ (mul_pos (inv_pos.mpr h) hPrior).ne',
        mul_one]
    · exact (lt_irrefl _ hp').elim
  · have hbound := sum_weighted_coordinate_mutualInformation_le_relativeEntropy V P hρ T
      (fun t => s t.1) hσ
    rw [show (T.bind fun t => (pi (s t.1)).map (t, ·)) = U from rfl] at hbound
    rw [hblocks, ← heR, ← heD] at hbound
    have hR' := (isDensityMatrix_normalizeDensity hR (hmass.symm ▸ h)).posSemidef.isHermitian
    have hre := relativeEntropy_reindex E hR' hD.posSemidef
    have hbudget := S.relativeEntropy_normalize_checkedAnswerRegister_le C
      QuestionA Prior QuestionB (fun z => W z.1) h
    refine hbound.trans (le_trans ?_ hbudget)
    convert hre.le using 2

end Cslib.PCP.QuantumStrategy
