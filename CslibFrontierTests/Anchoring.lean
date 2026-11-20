/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredCoordinateInformation
import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredNoisyStates
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
  have hW : ∃ z ∈ winsOnChecked acceptingGame half ({0} : Finset (Fin 2)),
      z ∈ (transcriptLaw acceptingGame half {0} anchoredEcho).support := by
    rw [acceptingGame_winsOnChecked]
    obtain ⟨z, hz⟩ := (transcriptLaw acceptingGame half {0} anchoredEcho).support_nonempty
    exact ⟨z, Set.mem_univ _, hz⟩
  obtain ⟨ρ, _, _, h⟩ := exists_anchored_coordinateInformation_le_after_wins acceptingGame half
    {0} anchoredEcho (Fintype.equivFinOfCardEq (by decide : _ = 1)).symm hW
  refine ⟨hW, ρ, ?_⟩
  have hcard : Fintype.card ((({0} : Finset (Fin 2)) → Bool) ×
      (({0} : Finset (Fin 2)) → Bool)) = 4 := by decide
  have hmass : (transcriptLaw acceptingGame half {0} anchoredEcho).toOuterMeasure
      (winsOnChecked acceptingGame half {0}) = 1 := by
    rw [acceptingGame_winsOnChecked, PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe]
  simpa only [Fintype.sum_unique, Fin.default_eq_zero, hcard, Nat.cast_ofNat, hmass,
    ENNReal.toReal_one, Real.log_one, sub_zero] using h
