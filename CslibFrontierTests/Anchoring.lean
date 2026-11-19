/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredGoodNormalization
import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredNoisyStates
import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredNormalizationWeights
import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredTranscriptDistance
import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson

/-! # Anchoring the CHSH game -/

set_option linter.privateModule false

open Cslib.PCP.TwoProverGame
open scoped unitInterval Real ENNReal Cslib.Probability.PMF

private noncomputable def half : I := ⟨1 / 2, by constructor <;> norm_num⟩

example : (chsh.anchored half).questions (none, none) = 1 / 4 := by
  rw [anchored_questions_apply]
  norm_num [half, ENNReal.ofReal_div_of_pos]
  rw [← ENNReal.inv_pow]
  norm_num

example : (chsh.anchored half).value = 15 / 16 := by
  rw [value_anchored, value_chsh]
  norm_num [half]

example : (chsh.anchored half).quantumValue = 1 - (1 - Real.cos (π / 8) ^ 2) / 4 := by
  rw [quantumValue_anchored, quantumValue_chsh]
  norm_num [half]
  ring

/-- Drawing the noisy reveal independently at each coordinate recovers repeated anchored CHSH. -/
example (n : ℕ) :
    (Cslib.Probability.PMF.pi fun _ : Fin n =>
      Cslib.PCP.AnchoredDependency.law chsh.questions half).map
        (fun samples => (Prod.fst ∘ Prod.snd ∘ samples, Prod.snd ∘ Prod.snd ∘ samples)) =
          ((chsh.anchored half).pow n).questions :=
  Cslib.PCP.AnchoredDependency.map_questions_pi_law chsh half n

/-- Checking one coordinate of two-copy CHSH leaves the verifier's question law intact. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 2)) :
    (Cslib.PCP.AnchoredDependency.transcriptLaw chsh half {0} S).map
      (fun r => let ((t, _), u) := r; t.combine u) =
        Cslib.Probability.PMF.pi (fun _ : Fin 2 => (chsh.anchored half).questions) :=
  Cslib.PCP.AnchoredDependency.map_questionPairs_transcriptLaw chsh half {0} S


open Cslib.PCP.AnchoredDependency
open Cslib.Probability.PMF (conditionalSnd)

/-- The other retained data have the same probabilities with or without the noisy message
when both questions at the left-out coordinate are anchors. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 2))
    (hW : ∃ r ∈ winsOnChecked chsh half ({0} : Finset (Fin 2)),
      r ∈ (transcriptLaw chsh half {0} S).support)
    (j : {i : Fin 2 // i ∉ ({0} : Finset (Fin 2))}) (m : Option Bool ⊕ Option Bool) :
    let Q := (transcriptLaw chsh half {0} S).filter (winsOnChecked chsh half {0}) hW
    let J := Q.map fun r => (freeTrials {0} r j, restTranscript {0} j r)
    let J' := Q.map fun r => ((freeTrials {0} r j).2, restTranscript {0} j r)
    (m, (none, none)) ∈ (J.map Prod.fst).support →
      ∀ r, conditionalSnd J (m, (none, none)) r = conditionalSnd J' (none, none) r := by
  dsimp only
  intro hs r
  exact congrArg (fun p => p r)
    (conditionalSnd_restTranscript_given_wins chsh half {0} S j hW (m, (none, none)) hs)

/-- With anchor rate one half, the two-anchor probability used in the transcript bound
is at least one eighth. This gives an unscaled comparison after a win in copy zero. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 2))
    (hW : ∃ r ∈ winsOnChecked chsh half ({0} : Finset (Fin 2)),
      r ∈ (transcriptLaw chsh half {0} S).support) :
    let C : Finset (Fin 2) := {0}
    let P := transcriptLaw chsh half C S
    let W := winsOnChecked chsh half C
    let Q := P.filter W hW
    let p := (P.toOuterMeasure W).toReal
    let m := Fintype.card {i : Fin 2 // i ∉ C}
    let ε₁ := Real.sqrt (m * Real.log (1 / p) / 2)
    let ε₂ := Real.sqrt (m * Real.log (Fintype.card (C → Bool × Bool) / p) / 2)
    (∑ j : {i : Fin 2 // i ∉ C},
      dist (questionsAndAnchoredRest chsh half C Q j) (questionsAndRest chsh half C Q j)) ≤
        9 * (2 * ε₁ + ε₂) := by
  dsimp only
  have h := (sum_dist_anchoredRest_given_wins chsh half {0} S hW).2
  have hw : (half : ℝ) ^ 2 / 2 = 1 / 8 := by norm_num [half]
  rw [hw] at h
  linarith


/-- A checked-answer branch of the two-copy experiment has a nonzero vector whenever
the conditional law of the actual transcript gives those answers positive mass. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 2))
    (j : {i : Fin 2 // i ∉ ({0} : Finset (Fin 2))})
    (t : RestQuestions (Option Bool) (Option Bool) {0} j)
    (ht : t ∈ (restQuestionsLaw chsh half {0} j).support)
    (hq : (none, none) ∈ ((law chsh.questions half).map Prod.snd).support)
    (hans : (fun _ => (true, true)) ∈
      (conditionalSnd (observedCheckedAnswers chsh half {0} S j) ((none, none), t)).support) :
    checkedVectorGivenRest chsh half {0} S j t (none, none)
      (fun _ => true) (fun _ => true) ≠ 0 := by
  have h := norm_checkedVectorGivenRest_sq_observed chsh half {0} S j t (none, none)
    (fun _ => true) (fun _ => true) ht hq
  have hmass := ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hans) (PMF.apply_ne_top _ _)
  intro hz
  rw [hz, norm_zero, zero_pow (by decide)] at h
  linarith


/-- With final anchoring probability one half, the extra erasure behind a left
message weighs the anchor branch by one quarter. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 2))
    (j : {i : Fin 2 // i ∉ ({0} : Finset (Fin 2))})
    (t : RestQuestions (Option Bool) (Option Bool) {0} j)
    (ht : t ∈ (restQuestionsLaw chsh half {0} j).support)
    (hm : Sum.inl (some true) ∈ ((law chsh.questions half).map Prod.fst).support)
    (hy : none ∈ (bobGivenMessage chsh.questions half (Sum.inl (some true))).support)
    (a b : ({0} : Finset (Fin 2)) → Bool) :
    (conditionalSnd (observedCheckedAnswersByBob chsh half {0} S j)
      ((Sum.inl (some true), none), t) (fun i => (a i, b i))).toReal =
      1 / 4 * ‖checkedVectorGivenRest chsh half {0} S j t (none, none) a b‖ ^ 2 +
        3 / 4 * ‖checkedVectorGivenRest chsh half {0} S j t (some true, none) a b‖ ^ 2 := by
  rw [← norm_checkedVectorGivenBob_sq chsh half {0} S j t _ _ a b ht hm hy,
    norm_checkedVectorGivenBob_sq_inl, coe_noise]
  norm_num [half]

open Cslib.Quantum (classicalQuantumMarginal mutualInformation)

private noncomputable def acceptingGame : Cslib.PCP.TwoProverGame Bool Bool Bool Bool :=
  ⟨chsh.questions, fun _ _ _ _ => True⟩

private noncomputable def anchoredEcho :
    Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
      (Fin 2 → Bool) (Fin 2 → Bool) (Fin 1) (Fin 1) :=
  Cslib.PCP.QuantumStrategy.ofDeterministic
    (fun x i => (x i).getD false) (fun y i => (y i).getD false)

private theorem acceptingGame_winsOnChecked :
    winsOnChecked acceptingGame half ({0} : Finset (Fin 2)) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  rintro ⟨⟨t, a⟩, u⟩
  change ∀ i : ({0} : Finset (Fin 2)),
    (acceptingGame.anchored half).accepts (t.questions i).1 (t.questions i).2 (a i).1 (a i).2
  intro i
  rw [anchored_accepts]
  cases (t.questions i).1 <;> cases (t.questions i).2 <;> trivial

private theorem acceptingGame_win_supported {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
      (Fin 2 → Bool) (Fin 2 → Bool) ι κ) :
    ∃ z ∈ winsOnChecked acceptingGame half ({0} : Finset (Fin 2)),
      z ∈ (transcriptLaw acceptingGame half {0} S).support := by
  rw [acceptingGame_winsOnChecked]
  obtain ⟨z, hz⟩ := (transcriptLaw acceptingGame half {0} S).support_nonempty
  exact ⟨z, Set.mem_univ _, hz⟩

private theorem acceptingGame_win_mass {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
      (Fin 2 → Bool) (Fin 2 → Bool) ι κ) :
    (transcriptLaw acceptingGame half {0} S).toOuterMeasure (winsOnChecked acceptingGame half {0}) =
      1 := by
  rw [acceptingGame_winsOnChecked, PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe]

private theorem singletonCheckedAnswer_card :
    Fintype.card ((({0} : Finset (Fin 2)) → Bool) ×
      (({0} : Finset (Fin 2)) → Bool)) = 4 := by decide

/-- A two-copy echo strategy with one checked and one unchecked coordinate has the
information budget `log 4` when every checked answer is accepted. -/
example :
    let C : Finset (Fin 2) := {0}
    let e : Fin 1 ≃ {i : Fin 2 // i ∉ C} := (Fintype.equivFinOfCardEq (by decide)).symm
    let T := transcriptLaw acceptingGame half C anchoredEcho
    let W := winsOnChecked acceptingGame half C
    ∃ hW : ∃ z ∈ W, z ∈ T.support,
      let P := (T.filter W hW).map (bobTranscriptProjection C e)
      ∃ ρ : _ → Matrix (Fin 1) (Fin 1) ℂ,
        (∑ t, (((P.map Prod.fst) t).toReal : WithTop ℝ) *
          mutualInformation (classicalQuantumMarginal (conditionalSnd P t)
            (fun y => ρ (t, y)) (fun y => y 0))) ≤ (Real.log 4 : ℝ) := by
  dsimp only
  have hW := acceptingGame_win_supported anchoredEcho
  obtain ⟨ρ, _, _, h⟩ := exists_anchored_coordinateInformation_le_after_wins acceptingGame half
    {0} anchoredEcho (Fintype.equivFinOfCardEq (by decide : _ = 1)).symm hW
  refine ⟨hW, ρ, ?_⟩
  simpa only [Fintype.sum_unique, Fin.default_eq_zero, singletonCheckedAnswer_card, Nat.cast_ofNat,
    acceptingGame_win_mass, ENNReal.toReal_one, Real.log_one, sub_zero] using h

/-- With unequal local dimensions the winning information bound on Alice's question
uses Bob's three-dimensional density matrices. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 3)) :
    let C : Finset (Fin 2) := {0}
    let e : Fin 1 ≃ {i : Fin 2 // i ∉ C} := (Fintype.equivFinOfCardEq (by decide)).symm
    let T := transcriptLaw acceptingGame half C S
    let W := winsOnChecked acceptingGame half C
    let P := (T.filter W (acceptingGame_win_supported S)).map (aliceTranscriptProjection C e)
    ∃ ρ : _ → Matrix (Fin 3) (Fin 3) ℂ,
      (∀ z, Cslib.Quantum.IsDensityMatrix (ρ z)) ∧
      (∑ t, (((P.map Prod.fst) t).toReal : WithTop ℝ) *
        mutualInformation (classicalQuantumMarginal (conditionalSnd P t)
          (fun x => ρ (t, x)) (fun x => x 0))) ≤ (Real.log 4 : ℝ) := by
  dsimp only
  obtain ⟨ρ, hρ, _, h⟩ := exists_bob_anchored_coordinateInformation_le_after_wins acceptingGame half
    {0} S (Fintype.equivFinOfCardEq (by decide : _ = 1)).symm (acceptingGame_win_supported S)
  refine ⟨ρ, hρ, ?_⟩
  simpa only [Fintype.sum_unique, Fin.default_eq_zero, singletonCheckedAnswer_card, Nat.cast_ofNat,
    acceptingGame_win_mass, ENNReal.toReal_one, Real.log_one, sub_zero] using h

/-- The squared trace-norm budget after revealing Alice's unchecked question in the
two-copy accepting game also applies when Bob's system has the larger dimension. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 3)) :
    let C : Finset (Fin 2) := {0}
    let e : Fin 1 ≃ {i : Fin 2 // i ∉ C} := (Fintype.equivFinOfCardEq (by decide)).symm
    let T := transcriptLaw acceptingGame half C S
    let W := winsOnChecked acceptingGame half C
    let P := (T.filter W (acceptingGame_win_supported S)).map (aliceTranscriptProjection C e)
    ∃ ρ : _ → Matrix (Fin 3) (Fin 3) ℂ,
      (∀ z, Cslib.Quantum.IsDensityMatrix (ρ z)) ∧
      Cslib.Quantum.sumConditionalTraceNormSq P ρ ≤ 2 * Real.log 4 := by
  dsimp only
  obtain ⟨ρ, hρ, _, h⟩ := exists_bob_sum_conditionalTraceNormSq_le_after_wins
    acceptingGame half {0} S (Fintype.equivFinOfCardEq (by decide : _ = 1)).symm
    (acceptingGame_win_supported S)
  refine ⟨ρ, hρ, ?_⟩
  simpa only [singletonCheckedAnswer_card, Nat.cast_ofNat, acceptingGame_win_mass,
    ENNReal.toReal_one, Real.log_one, sub_zero] using h

/-- With Bob's noisy-message tag fixed to his question, the prior-question trace
and anchor comparisons use the same three-dimensional states as the winning law. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 3)) :
    let C : Finset (Fin 2) := {0}
    let e : Fin 1 ≃ {i : Fin 2 // i ∉ C} := (Fintype.equivFinOfCardEq (by decide)).symm
    let T := transcriptLaw acceptingGame half C S
    let W := winsOnChecked acceptingGame half C
    let Q := T.filter W (acceptingGame_win_supported S)
    let P := Q.map (aliceTranscriptProjection C e)
    let w := (half : ℝ) ^ 2 / 2
    let K := w * (2 * Real.log 4) + 8 * ((1 + w) * Real.sqrt (Real.log 4 / 2))
    ∃ ρ : _ → Matrix (Fin 3) (Fin 3) ℂ,
      Cslib.Quantum.sumConditionalTraceNormSq P ρ ≤ 2 * Real.log 4 ∧
      w * ((half : ℝ) / 4 *
        taggedPairConditionalTraceNormSq C acceptingGame half Q Prod.fst (Sum.inr ∘ Prod.snd) e ρ) ≤
          K ∧
      w * ((half : ℝ) / 4) * ((half : ℝ) *
        taggedPairAnchorTraceNormSq C acceptingGame half Q Prod.fst (Sum.inr ∘ Prod.snd) none e ρ) ≤
          (2 * (half : ℝ) + 2) * K := by
  intro C e T W Q P w K
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  obtain ⟨ρ, hρ, _, hwin⟩ := exists_bob_sum_conditionalTraceNormSq_le_after_wins
    acceptingGame half C S e (acceptingGame_win_supported S)
  have hwin' : Cslib.Quantum.sumConditionalTraceNormSq P ρ ≤ 2 * Real.log 4 := by
    simpa only [C, singletonCheckedAnswer_card, Nat.cast_ofNat, acceptingGame_win_mass,
      ENNReal.toReal_one, Real.log_one, sub_zero] using hwin
  have hcard : Fintype.card (({0} : Finset (Fin 2)) → Bool × Bool) = 4 := by decide
  have hprior := priorConditionalTraceNormSq_le C acceptingGame half S
    (acceptingGame_win_supported S) Prod.fst e hρ
  dsimp only at hprior
  simp only [C, hcard, Nat.cast_ofNat, acceptingGame_win_mass, ENNReal.toReal_one, div_one,
    Real.log_one, Nat.cast_one, one_mul, zero_div, Real.sqrt_zero, mul_zero, zero_add] at hprior
  have htag := rightTaggedPairConditionalTraceNormSq_le C acceptingGame half Q e ρ
  let d := taggedPairConditionalTraceNormSq C acceptingGame half Q Prod.fst
    (Sum.inr ∘ Prod.snd) e ρ
  have hd : w * ((half : ℝ) / 4 * d) ≤ K :=
    (mul_le_mul_of_nonneg_left htag hw).trans
      (hprior.trans (add_le_add_left (mul_le_mul_of_nonneg_left hwin' hw) _))
  refine ⟨ρ, hwin', hd, ?_⟩
  have hanchor := rightTaggedPairAnchorTraceNormSq_le C acceptingGame half Q e ρ
  have hα : 0 ≤ (half : ℝ) := half.2.1
  calc
    _ ≤ (w * ((half : ℝ) / 4)) * ((2 * (half : ℝ) + 2) * d) :=
      mul_le_mul_of_nonneg_left hanchor (mul_nonneg hw (by positivity))
    _ = (2 * (half : ℝ) + 2) * (w * ((half : ℝ) / 4 * d)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

/-- A supported observation of Alice's unchecked question gives an actual unit
checked-answer vector purifying Bob's state on the original three-dimensional system. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 3)) :
    let C : Finset (Fin 2) := {0}
    let e : Fin 1 ≃ {i : Fin 2 // i ∉ C} := (Fintype.equivFinOfCardEq (by decide)).symm
    let Q := (transcriptLaw acceptingGame half C S).filter (winsOnChecked acceptingGame half C)
      (acceptingGame_win_supported S)
    let P := Q.map (aliceTranscriptProjection C e)
    ∃ ρ : _ → Matrix (Fin 3) (Fin 3) ℂ,
      ∀ label (_ : label ∈ (P.map Prod.fst).support) (u : Option Bool),
        u ∈ ((conditionalSnd P label).map (fun x => x 0)).support →
        let (t, a, b) := label
        let p := Cslib.Probability.PMF.pi fun j : Fin 1 =>
          aliceGivenMessage acceptingGame.questions half (t.halves (e j))
        let q := (conditionalSnd (p.map fun x => (x 0, x)) u).map (completeAliceQuestions C e t)
        let v := S.normalizedCheckedVector C q (bobQuestionsGivenInfo acceptingGame half C t) a b
        ‖v‖ = 1 ∧
          Cslib.Quantum.quantumMarginalGivenMap (conditionalSnd P label)
            (fun x => ρ (label, x)) (fun x => x 0) u =
            Cslib.Quantum.partialTraceLeft (Cslib.Quantum.pureState v) := by
  intro C e Q P
  obtain ⟨ρ, hρ, hbranch, _⟩ := exists_bob_anchored_coordinateInformation_le_after_wins
    acceptingGame half C S e (acceptingGame_win_supported S)
  refine ⟨ρ, ?_⟩
  rintro ⟨t, a, b⟩ ht u hu
  have he := quantumMarginalGivenMap_aliceTranscriptProjection acceptingGame half C S e
    (acceptingGame_win_supported S) hρ hbranch t a b (fun x => x 0) u ht hu
  change Cslib.Quantum.quantumMarginalGivenMap (conditionalSnd P (t, a, b))
    (fun x => ρ ((t, a, b), x)) (fun x => x 0) u = _ at he
  rw [← S.partialTraceLeft_pureState_normalizedCheckedVector] at he
  refine ⟨?_, he⟩
  have htrace := (Cslib.Quantum.isDensityMatrix_quantumMarginalGivenMap
    (conditionalSnd P (t, a, b)) (fun x => hρ ((t, a, b), x)) (fun x => x 0) u).trace_eq_one
  rw [he, Cslib.Quantum.trace_partialTraceLeft, Cslib.Quantum.trace_pureState] at htrace
  have hn := congrArg Complex.re htrace
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    (by simpa only [Complex.ofReal_re, Complex.one_re, one_pow] using hn)

/-- The noisy vector at a supported Alice question purifies Bob's state with Bob's
three-dimensional system first and Alice's two-dimensional system second. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 3)) :
    let C : Finset (Fin 2) := {0}
    let e : Fin 1 ≃ {i : Fin 2 // i ∉ C} := (Fintype.equivFinOfCardEq (by decide)).symm
    let P := ((transcriptLaw acceptingGame half C S).filter (winsOnChecked acceptingGame half C)
      (acceptingGame_win_supported S)).map (aliceTranscriptProjection C e)
    ∃ ρ : _ → Matrix (Fin 3) (Fin 3) ℂ,
      ∀ label (_ : label ∈ (P.map Prod.fst).support) (u : Option Bool),
        u ∈ ((conditionalSnd P label).map (fun x => x 0)).support →
        let (t, a, b) := label
        let v : EuclideanSpace ℂ (Fin 3 × Fin 2) :=
          checkedVectorGivenAlice acceptingGame half C S (e 0) t u a b
        let ψ := ‖v‖⁻¹ • v
        ‖ψ‖ = 1 ∧
          Cslib.Quantum.quantumMarginalGivenMap (conditionalSnd P label) (fun x => ρ (label, x))
            (fun x => x 0) u = Cslib.Quantum.partialTraceRight (Cslib.Quantum.pureState ψ) := by
  intro C e P
  obtain ⟨ρ, hρ, hbranch, _⟩ := exists_bob_anchored_coordinateInformation_le_after_wins
    acceptingGame half C S e (acceptingGame_win_supported S)
  refine ⟨ρ, ?_⟩
  rintro ⟨t, a, b⟩ ht u hu
  exact checkedVectorGivenAlice_purifies_winningMarginal acceptingGame half C S e
    (acceptingGame_win_supported S) hρ hbranch t a b 0 u ht hu

/-- The support penalty is one if either endpoint is missing, including when only the
anchor has zero winning mass. It is zero when both endpoints occur. -/
example :
    let P : PMF (Unit × (Fin 1 → Bool)) := PMF.pure ((), fun _ => false)
    winningAnchorMiss P false 0 () false = 0 ∧
      winningAnchorMiss P false 0 () true = 1 ∧ winningAnchorMiss P true 0 () false = 1 := by
  simp [winningAnchorMiss, WinningQuestionSupported, PMF.pure_map]

open Finset in
/-- A one-coordinate transcript supported on a left nonanchor message gives positive
missing mass when both questions are erased, in either tagged redraw. -/
example :
    let C : Finset (Fin 1) := ∅
    let e : Fin 1 ≃ {i : Fin 1 // i ∉ C} := (Fintype.equivFinOfCardEq (by decide)).symm
    let t : Cslib.PCP.ParallelRepetition.Revealed (Option Bool) (Option Bool) C :=
      ⟨fun _ => (none, none), fun _ => Sum.inl (some false)⟩
    let z := ((t, fun _ : C => (false, false)),
      fun _ : {i : Fin 1 // i ∉ C} => (some false, none))
    let Q := PMF.pure z
    let d := ∑ j : {i : Fin 1 // i ∉ C}, dist (Q.map fun v =>
      (freeTrials C v j, restTranscript C j v)) (priorTrialAndRest acceptingGame half C Q j)
    let left :=
      taggedPairAnchorMissMass C acceptingGame half Q Prod.snd (Sum.inl ∘ Prod.fst) none e
    let right :=
      taggedPairAnchorMissMass C acceptingGame half Q Prod.fst (Sum.inr ∘ Prod.snd) none e
    0 < left ∧ 0 < right ∧
      ((half : ℝ) / 4) * (half : ℝ) * left ≤ ((half : ℝ) + 1) * d ∧
      ((half : ℝ) / 4) * (half : ℝ) * right ≤ ((half : ℝ) + 1) * d := by
  classical
  intro C e t z Q d left right
  have hpos (read : Option Bool × Option Bool → Option Bool)
      (tag : Option Bool × Option Bool → Option Bool ⊕ Option Bool)
      (htag : tag (none, none) ≠ Sum.inl (some false)) :
      0 < taggedPairAnchorMissMass C acceptingGame half Q read tag none e := by
    let r := restTranscript C (e 0) z
    let label := restoreCheckedTranscript C (e 0) r (tag (none, none))
    let P := Q.map (questionTranscriptProjection C read e)
    have hm : ¬ WinningQuestionSupported P 0 label (read (none, none)) := by
      intro h
      change (_, _) ∈ (P.map fun v => (v.1, v.2 0)).support at h
      simp only [P, Q, PMF.pure_map, PMF.mem_support_pure_iff] at h
      have hmsg := congrArg (fun v => v.1.1.halves (e 0)) h
      exact htag (by simpa [label, restoreCheckedTranscript, questionTranscriptProjection, z, t]
        using hmsg)
    have hmiss (i : Fin 1) (t' : _) (u : Option Bool) : 0 ≤ winningAnchorMiss P none i t' u := by
      unfold winningAnchorMiss
      split <;> norm_num
    unfold taggedPairAnchorMissMass taggedPairScore taggedPairCoordinateScore taggedPairRestScore
    apply sum_pos' (fun i _ => sum_nonneg fun q _ => mul_nonneg ENNReal.toReal_nonneg
      (sum_nonneg fun r' _ => mul_nonneg ENNReal.toReal_nonneg (hmiss _ _ _)))
    refine ⟨0, mem_univ _, ?_⟩
    apply sum_pos' (fun q _ => mul_nonneg ENNReal.toReal_nonneg
      (sum_nonneg fun r' _ => mul_nonneg ENNReal.toReal_nonneg (hmiss _ _ _)))
    refine ⟨(none, none), mem_univ _, mul_pos ?_ ?_⟩
    · rw [anchored_questions_apply]
      norm_num [half, ENNReal.toReal_pow]
    · apply sum_pos' (fun r' _ => mul_nonneg ENNReal.toReal_nonneg (hmiss _ _ _))
      refine ⟨r, mem_univ _, ?_⟩
      change 0 < ((Q.map (restTranscript C (e 0))) r).toReal *
        winningAnchorMiss P none 0 label (read (none, none))
      simp [Q, r, PMF.pure_map, winningAnchorMiss, hm]
  exact ⟨hpos Prod.snd (Sum.inl ∘ Prod.fst) (by decide),
    hpos Prod.fst (Sum.inr ∘ Prod.snd) (by decide),
    leftTaggedPairAnchorMissMass_le C acceptingGame half Q e,
    rightTaggedPairAnchorMissMass_le C acceptingGame half Q e⟩


/-- The fixed-right-tag estimate acts on Alice's original two-dimensional local system
and allows division by the alignment scale at anchor rate one half. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 3)) :
    let C : Finset (Fin 2) := {0}
    let e : Fin 1 ≃ {i : Fin 2 // i ∉ C} := (Fintype.equivFinOfCardEq (by decide)).symm
    let Q := (transcriptLaw acceptingGame half C S).filter (winsOnChecked acceptingGame half C)
      (acceptingGame_win_supported S)
    let Label := Cslib.PCP.ParallelRepetition.Revealed (Option Bool) (Option Bool) C ×
      ((C → Bool) × (C → Bool))
    ∃ V : Fin 1 → Label → Option Bool → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ i t x, V i t x ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      taggedPairScore C acceptingGame half Q Prod.fst (fun _ => Sum.inr none) e
        (fun i label x =>
          let (t, a, b) := label
          let v u := checkedVectorGivenAlice acceptingGame half C S (e i) t u a b
          localUnitaryErrorSq (V i label x) (v none) (v x)) ≤
        anchoredAlignmentBound half 1 4 1 / ((half : ℝ) * anchoredAlignmentScale half) := by
  intro C e Q Label
  obtain ⟨V, hV, hbound⟩ :=
    exists_alice_anchorLocalUnitary_le C acceptingGame half S e (acceptingGame_win_supported S)
  refine ⟨V, hV, ?_⟩
  have hp : 0 < (half : ℝ) * anchoredAlignmentScale half := by
    norm_num [anchoredAlignmentScale, half]
  rw [le_div_iff₀ hp, mul_comm]
  have hc : Fintype.card (({0} : Finset (Fin 2)) → Bool × Bool) = 4 := by decide
  simpa only [C, hc, acceptingGame_win_mass, ENNReal.toReal_one] using hbound

private theorem zero_mem_of_uniform_failure_lt_one (good : Finset (Fin 1))
    (h : ((Cslib.Probability.PMF.uniformOfFintype (Fin 1)).toOuterMeasure
      {i | i ∉ good}).toReal < 1) :
    (0 : Fin 1) ∈ good := by
  by_contra hn
  have he : {i : Fin 1 | i ∉ good} = Set.univ := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi, hn]
  rw [he] at h
  have hm : ((Cslib.Probability.PMF.uniformOfFintype (Fin 1)).toOuterMeasure Set.univ) = 1 :=
    ((Cslib.Probability.PMF.uniformOfFintype (Fin 1)).toOuterMeasure_apply_eq_one_iff
      Set.univ).mpr (Set.subset_univ _)
  rw [hm, ENNReal.toReal_one] at h
  exact (lt_irrefl _ h)

/-- With a failure bound below one, the sole unchecked coordinate admits all three
unitary choices on the original, unequal-dimensional local systems. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 3)) {τ : ℝ} (hτ : 0 < τ)
    (hsmall : (2 + (half : ℝ)) * anchoredAlignmentBound half 1 4 1 <
      (half : ℝ) * anchoredAlignmentScale half * τ ^ 2) :
    let C : Finset (Fin 2) := {0}
    let e : Fin 1 ≃ {i : Fin 2 // i ∉ C} := (Fintype.equivFinOfCardEq (by decide)).symm
    let Q := (transcriptLaw acceptingGame half C S).filter (winsOnChecked acceptingGame half C)
      (acceptingGame_win_supported S)
    let Label := Cslib.PCP.ParallelRepetition.Revealed (Option Bool) (Option Bool) C ×
      ((C → Bool) × (C → Bool))
    let vA (i : Fin 1) (label : Label) (x : Option Bool) :=
      let (t, a, b) := label
      checkedVectorGivenAlice acceptingGame half C S (e i) t x a b
    let vB (i : Fin 1) (label : Label) (y : Option Bool) :=
      let (t, a, b) := label
      checkedVectorGivenBob acceptingGame half C S (e i) (omitMessage C (e i) t)
        (t.halves (e i)) y a b
    ∃ (VA : Fin 1 → Label → Option Bool → Matrix (Fin 2) (Fin 2) ℂ)
      (VB VAB : Fin 1 → Label → Option Bool → Matrix (Fin 3) (Fin 3) ℂ),
      taggedPairCoordinateScore C acceptingGame half Q Prod.fst (fun _ => Sum.inr none) e
        (fun j t x => localUnitaryError (VA j t x) (vA j t none) (vA j t x)) 0 ≤ τ ∧
      taggedPairCoordinateScore C acceptingGame half Q Prod.snd (fun _ => Sum.inl none) e
        (fun j t y => localUnitaryError (VB j t y) (vB j t none) (vB j t y)) 0 ≤ τ ∧
      taggedPairCoordinateScore C acceptingGame half Q Prod.snd (Sum.inl ∘ Prod.fst) e
        (fun j t y => localUnitaryError (VAB j t y) (vB j t y) (vB j t none)) 0 ≤ τ := by
  classical
  intro C e Q Label vA vB
  have hα : 0 < (half : ℝ) := by norm_num [half]
  obtain ⟨VA, VB, VAB, good, _, _, _, hprob, hmean⟩ :=
    exists_good_alignment_coordinates C acceptingGame half S e
      (acceptingGame_win_supported S) hα hτ
  refine ⟨VA, VB, VAB, hmean 0 ?_⟩
  apply zero_mem_of_uniform_failure_lt_one good
  have hc : Fintype.card (({0} : Finset (Fin 2)) → Bool × Bool) = 4 := by decide
  have hdenom : 0 < (half : ℝ) * anchoredAlignmentScale half * τ ^ 2 := by
    unfold anchoredAlignmentScale
    positivity
  have hle := hprob
  simp only [anchorAlignmentFailureBound, C, hc, acceptingGame_win_mass, ENNReal.toReal_one,
    Nat.cast_one, one_mul] at hle
  exact hle.trans_lt ((div_lt_one hdenom).mpr hsmall)

open Finset in
/-- The ordinary and noisy ratio estimates use the actual winning law of a two-copy
accepting game with one checked coordinate and unequal local dimensions. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 3)) :
    let C : Finset (Fin 2) := {0}
    let w := (half : ℝ) ^ 2 / 2
    let ε₁ := Real.sqrt ((1 : ℝ) * Real.log (1 / 1) / 2)
    let ε₂ := Real.sqrt ((1 : ℝ) * Real.log (4 / 1) / 2)
    let B := (2 * w + 1 / 2) * ε₁ + 2 * ((1 + w) * (2 * ε₁ + ε₂))
    w * (∑ j : {i : Fin 2 // i ∉ C}, restNormalizationRatioLoss acceptingGame half C S j) ≤ B ∧
      w * ((half : ℝ) * ∑ j : {i : Fin 2 // i ∉ C},
        leftNoisyNormalizationRatioLoss acceptingGame half C S j) ≤ ((half : ℝ) + 1) * B := by
  intro C w ε₁ ε₂ B
  have hcard : Fintype.card {i : Fin 2 // i ∉ ({0} : Finset (Fin 2))} = 1 := by decide
  have hanswers : Fintype.card (({0} : Finset (Fin 2)) → Bool × Bool) = 4 := by decide
  constructor
  · have h := sum_restNormalizationRatioLoss_le acceptingGame half C S
      (acceptingGame_win_supported S)
    simpa only [C, B, w, ε₁, ε₂, hcard, hanswers, acceptingGame_win_mass,
      ENNReal.toReal_one, Nat.cast_one,
      Nat.cast_ofNat, one_mul] using h
  · have h := sum_leftNoisyNormalizationRatioLoss_le acceptingGame half C S
      (acceptingGame_win_supported S)
    simpa only [C, B, w, ε₁, ε₂, hcard, hanswers, acceptingGame_win_mass,
      ENNReal.toReal_one, Nat.cast_one,
      Nat.cast_ofNat, one_mul] using h

/-- The sole unchecked coordinate satisfies the alignment and conditional normalization
estimates together when their combined failure bound is below one. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 3)) {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η)
    (hsmall : anchorAlignmentFailureBound half 1 4 1 τ +
      anchorNormalizationFailureBound half 1 4 1 η < 1) :
    let C : Finset (Fin 2) := {0}
    let e : Fin 1 ≃ {i : Fin 2 // i ∉ C} := (Fintype.equivFinOfCardEq (by decide)).symm
    let Q := (transcriptLaw acceptingGame half C S).filter (winsOnChecked acceptingGame half C)
      (acceptingGame_win_supported S)
    let Label := Cslib.PCP.ParallelRepetition.Revealed (Option Bool) (Option Bool) C ×
      ((C → Bool) × (C → Bool))
    ∃ (VA : Fin 1 → Label → Option Bool → Matrix (Fin 2) (Fin 2) ℂ)
      (VB VAB : Fin 1 → Label → Option Bool → Matrix (Fin 3) (Fin 3) ℂ),
      AnchorAlignmentAt C acceptingGame half S Q e VA VB VAB 0 τ ∧
        AnchorNormalizationAt C acceptingGame half S (e 0) 1 η := by
  intro C e Q Label
  have hα : 0 < (half : ℝ) := by norm_num [half]
  obtain ⟨VA, VB, VAB, good, _, _, _, hprob, hgood⟩ :=
    exists_good_alignment_normalization_coordinates C acceptingGame half S e
      (acceptingGame_win_supported S) hα hτ hη
  have hc : Fintype.card (({0} : Finset (Fin 2)) → Bool × Bool) = 4 := by decide
  simp only [C, hc, acceptingGame_win_mass, ENNReal.toReal_one] at hprob
  have h0 := zero_mem_of_uniform_failure_lt_one good (hprob.trans_lt hsmall)
  refine ⟨VA, VB, VAB, (hgood 0 h0).1, ?_⟩
  simpa only [C, acceptingGame_win_mass, ENNReal.toReal_one] using (hgood 0 h0).2

/-- The common good coordinate supplies a supported two-anchor draw for the alignment scores. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 3))
    {τ η ξ : ℝ} (hτ : 0 < τ) (hη : 0 < η) (hξ : 0 < ξ)
    (hsmall : anchorAlignmentFailureBound half 1 4 1 τ +
      anchorNormalizationFailureBound half 1 4 1 η + anchorRestFailureBound half 1 4 1 ξ < 1) :
    let C : Finset (Fin 2) := {0}
    let e : Fin 1 ≃ {i : Fin 2 // i ∉ C} := (Fintype.equivFinOfCardEq (by decide)).symm
    let Label := Cslib.PCP.ParallelRepetition.Revealed (Option Bool) (Option Bool) C ×
      ((C → Bool) × (C → Bool))
    let K := restKernel acceptingGame half C S (e 0) (none, none)
    let W := winsOnRest acceptingGame half C (e 0)
    ∃ (VA : Fin 1 → Label → Option Bool → Matrix (Fin 2) (Fin 2) ℂ)
      (VB VAB : Fin 1 → Label → Option Bool → Matrix (Fin 3) (Fin 3) ℂ),
      AnchorNormalizationAt C acceptingGame half S (e 0) 1 η ∧
        ∃ hwin : ∃ r ∈ W, r ∈ K.support,
          AnchorAlignmentOnRestAt C acceptingGame half S e VA VB VAB 0
            (K.filter W hwin) (τ + 2 * ξ) := by
  intro C e Label K W
  have hα : 0 < (half : ℝ) := by norm_num [half]
  obtain ⟨VA, VB, VAB, good, _, _, _, hprob, hgood⟩ :=
    exists_good_conditioned_alignment_coordinates C acceptingGame half S e
      (acceptingGame_win_supported S) hα hτ hη hξ
  have hc : Fintype.card (({0} : Finset (Fin 2)) → Bool × Bool) = 4 := by decide
  simp only [C, hc, acceptingGame_win_mass, ENNReal.toReal_one] at hprob
  have h0 := zero_mem_of_uniform_failure_lt_one good (hprob.trans_lt hsmall)
  refine ⟨VA, VB, VAB, ?_, (hgood 0 h0).2⟩
  simpa only [C, acceptingGame_win_mass, ENNReal.toReal_one] using (hgood 0 h0).1
