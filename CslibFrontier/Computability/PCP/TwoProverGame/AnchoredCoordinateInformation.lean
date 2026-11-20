/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredNoisyStates
public import CslibFrontier.Computability.PCP.TwoProverGame.CheckedAnswerInformation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Filter
import CslibFrontier.Probability.Product.Split

/-!
# Checked-answer information for the anchored transcript

The noisy reveal makes the two free-question tuples independent conditional on the
revealed information. Thus one can sample Bob's free tuple from the corresponding
product law, average Alice's full questions, and retain the checked answers.
The resulting law is the same projection of the original anchored transcript used
in [Bavarian, Vidick and Yuen, Claim 5.13][BavarianVidickYuen2022].
Grouping the winning law by an observation of the free tuple gives the normalized
checked branch with the prior question law restricted to that observation. This is
the reduction to an averaged branch used in the purification step of Claims 5.15–5.16
(arXiv:1509.07466v2, §5.2, printed pp. 27–28).

## Main results

* `map_transcriptLaw_eq_checkedAnswersWithLabel`: the sampler identity before filtering.
* `exists_anchored_coordinateInformation_le_after_wins`: the Alice marginal bound
  weighted by the verifier's winning transcript.
* `exists_bob_anchored_coordinateInformation_le_after_wins`: the Bob marginal bound
  obtained by exchanging the players in the same experiment.
* `quantumMarginalGivenMap_bobTranscriptProjection` and
  `quantumMarginalGivenMap_aliceTranscriptProjection`: the supported conditional state
  is the normalized marginal of the branch computed with the prior question fiber.
* `checkedVectorGivenBob_purifies_winningMarginal` and
  `checkedVectorGivenAlice_purifies_winningMarginal`: the noisy vectors, normalized
  on supported selected-question observations, purify the corresponding reduced states.
-/

public section

namespace Cslib.PCP.AnchoredDependency

open Cslib.Probability.PMF
open Quantum Matrix
open ParallelRepetition (Revealed)
open scoped unitInterval

variable {X Y A B ι κ : Type*} {n m : ℕ}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (G : TwoProverGame X Y A B) (α : I) (C : Finset (Fin n))

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Info" => Revealed (Option X) (Option Y) C
local notation "PairQ" => (Option X × Option Y)
local notation "Answer" => ((C → A) × (C → B))
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ

/-- Alice's full-question law, conditional on the shared questions and noisy messages. -/
noncomputable def aliceQuestionsGivenInfo (t : Info) : PMF (Fin n → Option X) :=
  (pi fun j : Free => aliceGivenMessage G.questions α (t.halves j)).map
    (appendQuestions C (Prod.fst ∘ t.questions))

/-- The independent Bob question law at a free coordinate of the retained information. -/
noncomputable def bobQuestionGivenInfo (t : Info) (j : Free) : PMF (Option Y) :=
  bobGivenMessage G.questions α (t.halves j)

/-- Insert the checked Bob questions into the renumbered free tuple. -/
def completeBobQuestions (e : Fin m ≃ Free) (t : Info) (y : Fin m → Option Y) :
    Fin n → Option Y :=
  appendQuestions C (Prod.snd ∘ t.questions) (y ∘ e.symm)

omit [Fintype A] [Fintype B] in
private theorem pairGiven_eq_independent_of_support (t : Info)
    (ht : t ∈ (infoLaw G α C).support) (j : Free) :
    pairGiven G α C j t = (aliceGivenMessage G.questions α (t.halves j)).bind
      (fun x => (bobQuestionGivenInfo G α C t j).map (x, ·)) := by
  have hm : t.halves j ∈ ((law G.questions α).map Prod.fst).support := by
    simp only [infoLaw, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at ht
    obtain ⟨_, -, halves, hhalves, rfl⟩ := ht
    exact (mem_support_pi_iff _ _).mp hhalves j
  unfold pairGiven bobQuestionGivenInfo
  conv_lhs => rw [law_eq_bind_messages]
  exact conditionalSnd_bind_pair _ _ _ hm

omit [Fintype A] [Fintype B] in
private theorem splitFree_givenInfo (t : Info) (ht : t ∈ (infoLaw G α C).support) :
    (pi fun j : Free => pairGiven G α C j t).map
      (fun (u : Free → PairQ) => (Prod.fst ∘ u, Prod.snd ∘ u)) =
        (pi fun j : Free => aliceGivenMessage G.questions α (t.halves j)).bind fun x =>
          (pi fun j : Free => bobQuestionGivenInfo G α C t j).map (x, ·) := by
  simp_rw [pairGiven_eq_independent_of_support G α C t ht]
  exact pi_bind_pair _ _

omit [Fintype A] [Fintype B] in
private theorem map_questionsGivenRest_omit {U : Type*} [Finite U] (f : PairQ → U)
    (j : Free) (t : Info) (z : PairQ) :
    (questionsGivenRest G α C j (omitMessage C j t) z).map (fun q => f ∘ q) =
      (pi (Function.update (fun i => (pairGiven G α C i t).map f) j (PMF.pure (f z)))).map
        (appendQuestions C (f ∘ t.questions)) := by
  rw [questionsGivenRest_omit, map_pi_update_combine]

omit [Fintype A] [Fintype B] in
private theorem aliceQuestionsGivenInfo_eq_bind_rest (t : Info)
    (ht : t ∈ (infoLaw G α C).support) (j : Free) (y : Option Y) :
    aliceQuestionsGivenInfo G α C t =
      (aliceGivenMessage G.questions α (t.halves j)).bind fun x =>
        aliceQuestionsGivenRest G α C j (omitMessage C j t) (x, y) := by
  have hleft (i : Free) : (pairGiven G α C i t).map Prod.fst =
      aliceGivenMessage G.questions α (t.halves i) := by
    rw [pairGiven_eq_independent_of_support G α C t ht, map_fst_bind_pair]
  simp only [aliceQuestionsGivenRest, map_questionsGivenRest_omit, hleft]
  unfold aliceQuestionsGivenInfo
  rw [← PMF.map_bind, pi_bind_update
    (α := fun _ : Free => Option X) (fun i => aliceGivenMessage G.questions α (t.halves i)) j]

omit [Fintype A] [Fintype B] in
private theorem bobQuestionsGivenRest_eq_priorFiber (t : Info) (ht : t ∈ (infoLaw G α C).support)
    (e : Fin m ≃ Free) (i : Fin m) (y : Option Y)
    (hy : y ∈ (bobQuestionGivenInfo G α C t (e i)).support) :
    bobQuestionsGivenRest G α C (e i) (omitMessage C (e i) t) (none, y) =
      (conditionalSnd ((pi fun j : Fin m => bobQuestionGivenInfo G α C t (e j)).map
        (fun z => (z i, z))) y).map (completeBobQuestions C e t) := by
  have hright (j : Free) : (pairGiven G α C j t).map Prod.snd =
      bobQuestionGivenInfo G α C t j := by
    rw [pairGiven_eq_independent_of_support G α C t ht]
    simp only [PMF.map_bind, PMF.map_comp]
    change ((aliceGivenMessage G.questions α (t.halves j)).bind fun _ =>
      (bobQuestionGivenInfo G α C t j).map id) = _
    rw [PMF.map_id, PMF.bind_const]
  let p := bobQuestionGivenInfo G α C t
  let u := Function.update (fun j => p (e j)) i (PMF.pure y)
  let v := Function.update p (e i) (PMF.pure y)
  rw [conditionalSnd_pi_eval (fun j : Fin m => p (e j)) i y hy]
  simp only [bobQuestionsGivenRest, map_questionsGivenRest_omit, hright]
  change (pi v).map (appendQuestions C (Prod.snd ∘ t.questions)) =
    (pi u).map (appendQuestions C (Prod.snd ∘ t.questions) ∘ (fun z => z ∘ e.symm))
  rw [← PMF.map_comp]
  change _ = ((pi u).map (fun z j => z (e.symm j))).map
    (appendQuestions C (Prod.snd ∘ t.questions))
  rw [pi_map_comp_injective (α := fun _ : Fin m => Option Y) u e.symm.injective]
  apply congrArg (fun r : PMF (Free → Option Y) => r.map
    (appendQuestions C (Prod.snd ∘ t.questions)))
  apply congrArg pi
  funext j
  by_cases hj : j = e i
  · subst j
    simp [u, v]
  · have hj' : e.symm j ≠ i := fun h => hj ((e.apply_symm_apply j).symm.trans (congrArg e h))
    simp [u, v, hj, hj']

/-- Forget Alice's free questions and split the checked answers by player. The original
transcript, projected to this data, is the checked-answer sampler with Bob's independent
free tuple retained as the question register. -/
theorem map_transcriptLaw_eq_checkedAnswersWithLabel (S : RepeatedStrategy) (e : Fin m ≃ Free) :
    (transcriptLaw G α C S).map (fun ((t, a), u) =>
      ((t, fun j => (u (e j)).2), (Prod.fst ∘ a, Prod.snd ∘ a))) =
      S.checkedAnswersWithLabel C
        (fun (t, _) => aliceQuestionsGivenInfo G α C t)
        ((infoLaw G α C).bind fun t => (pi fun j => bobQuestionGivenInfo G α C t (e j))
          |>.map (t, ·))
        (fun (t, y) => PMF.pure (completeBobQuestions C e t y)) := by
  rw [transcriptLaw, sideJoint, PMF.map_bind, QuantumStrategy.checkedAnswersWithLabel]
  simp only [PMF.bind_bind, PMF.bind_map, PMF.pure_bind, Function.comp_def]
  apply bind_congr_on_support
  intro t ht
  let read (x : Free → Option X) (y : Free → Option Y) :=
    (S.checkedAnswers C (appendQuestions C (Prod.fst ∘ t.questions) x)
      (appendQuestions C (Prod.snd ∘ t.questions) y)).map ((t, y ∘ e), ·)
  have hread (u : Free → PairQ) :
      (S.answers (Prod.fst ∘ t.combine u) (Prod.snd ∘ t.combine u)).map
        (fun (a, b) => ((t, fun j => (u (e j)).2), (fun i : C => a i, fun i : C => b i))) =
      read (Prod.fst ∘ u) (Prod.snd ∘ u) := by
    rw [project_combine C Prod.fst t u, project_combine C Prod.snd t u]
    simp only [read, QuantumStrategy.checkedAnswers, PMF.map_comp, Function.comp_def]
    congr 1
  simp only [sideKernel, checkedAnswerLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
  simp only [Function.comp_def] at hread
  simp_rw [hread]
  have hsplit :
      (pi fun j : Free => pairGiven G α C j t).bind
          (fun u => read (Prod.fst ∘ u) (Prod.snd ∘ u)) =
        ((pi fun j : Free => pairGiven G α C j t).map
          (fun (u : Free → PairQ) => (Prod.fst ∘ u, Prod.snd ∘ u))).bind
            (fun (x, y) => read x y) := by
    rw [PMF.bind_map]
    rfl
  change ((pi fun j : Free => pairGiven G α C j t).bind
    fun u => read (Prod.fst ∘ u) (Prod.snd ∘ u)) = _
  rw [hsplit, splitFree_givenInfo G α C t ht]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  simp only [aliceQuestionsGivenInfo, PMF.bind_map, Function.comp_def]
  have hmap : (pi fun j : Free => bobQuestionGivenInfo G α C t j).map (fun y => y ∘ e) =
      pi (fun j : Fin m => bobQuestionGivenInfo G α C t (e j)) :=
    pi_map_comp_injective (bobQuestionGivenInfo G α C t) e.injective
  rw [← hmap, PMF.bind_map]
  congr 1 with y
  simp only [read, completeBobQuestions, Function.comp_def, Equiv.apply_symm_apply]

/-- Retain the shared transcript and a function of the question pair at each unchecked
coordinate. -/
@[expose] def questionTranscriptProjection {U : Type*} (read : PairQ → U) (e : Fin m ≃ Free)
    (z : (Info × (C → A × B)) × (Free → PairQ)) :
    (Info × Answer) × (Fin m → U) :=
  let ((t, a), u) := z
  ((t, (Prod.fst ∘ a, Prod.snd ∘ a)), fun i => read (u (e i)))

/-- The projection of the original transcript to its checked answers and Bob's
renumbered free questions. -/
@[expose] def bobTranscriptProjection (e : Fin m ≃ Free)
    (z : (Info × (C → A × B)) × (Free → PairQ)) :
    (Info × Answer) × (Fin m → Option Y) :=
  questionTranscriptProjection C Prod.snd e z

private def anchoredInfoWins (t : Info) : Set Answer :=
  {a | ∀ i : C, (G.anchored α).accepts (t.questions i).1 (t.questions i).2 (a.1 i) (a.2 i)}

private theorem checkedWinTranscriptLaw_eq_anchored_filter
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support) :
    let T := transcriptLaw G α C S
    let p := aliceQuestionsGivenInfo G α C
    let r := infoLaw G α C
    let s (t : Info) (i : Fin m) := bobQuestionGivenInfo G α C t (e i)
    let q (t : Info) (y : Fin m → Option Y) := PMF.pure (completeBobQuestions C e t y)
    let W := anchoredInfoWins G α C
    let L := S.checkedAnswersWithLabel C (fun (t, _) => p t)
      (r.bind fun t => (pi (s t)).map (t, ·)) (fun (t, y) => q t y)
    let event : Set ((Info × (Fin m → Option Y)) × Answer) := {z | z.2 ∈ W (Prod.fst z.1)}
    ∃ hwin : (0 : ℝ) < (L.toOuterMeasure event).toReal,
      S.checkedWinTranscriptLaw C (fun _ : Fin m => Option Y) p r s q W hwin =
        (T.filter (winsOnChecked G α C) hs).map (bobTranscriptProjection C e) ∧
      L.toOuterMeasure event = T.toOuterMeasure (winsOnChecked G α C) := by
  classical
  let T := transcriptLaw G α C S
  let p := aliceQuestionsGivenInfo G α C
  let r := infoLaw G α C
  let s (t : Info) (i : Fin m) := bobQuestionGivenInfo G α C t (e i)
  let q (t : Info) (y : Fin m → Option Y) := PMF.pure (completeBobQuestions C e t y)
  let W := anchoredInfoWins G α C
  let L := S.checkedAnswersWithLabel C (fun (t, _) => p t)
    (r.bind fun t => (pi (s t)).map (t, ·)) (fun (t, y) => q t y)
  let f : (Info × (C → A × B)) × (Free → PairQ) → (Info × (Fin m → Option Y)) × Answer :=
    fun ((t, a), u) => ((t, fun j => (u (e j)).2), (Prod.fst ∘ a, Prod.snd ∘ a))
  let event : Set ((Info × (Fin m → Option Y)) × Answer) := {z | z.2 ∈ W (Prod.fst z.1)}
  have hf : T.map f = L := map_transcriptLaw_eq_checkedAnswersWithLabel G α C S e
  have hpre : f ⁻¹' event = winsOnChecked G α C := rfl
  have hmass : L.toOuterMeasure event = T.toOuterMeasure (winsOnChecked G α C) := by
    rw [← hf, PMF.toOuterMeasure_map_apply, hpre]
  have hwin : (0 : ℝ) < (L.toOuterMeasure event).toReal := by
    rw [hmass]
    exact (toOuterMeasure_toReal_pos_iff T _).mpr hs
  have hevent := (toOuterMeasure_toReal_pos_iff L event).mp hwin
  have hevent' : ∃ z ∈ event, z ∈ (T.map f).support := hf.symm ▸ hevent
  have hs' : ∃ z ∈ f ⁻¹' event, z ∈ T.support := hpre.symm ▸ hs
  have hfilter : L.filter event hevent = (T.map f).filter event hevent' := by
    congr 1
    exact hf.symm
  have hP : S.checkedWinTranscriptLaw C (fun _ : Fin m => Option Y) p r s q W hwin =
      (T.filter (winsOnChecked G α C) hs).map (bobTranscriptProjection C e) := by
    rw [S.checkedWinTranscriptLaw_eq_filter_map C (fun _ : Fin m => Option Y) p r s q W hwin
        hevent, hfilter, filter_map T f event hevent' hs', PMF.map_comp]
    congr 1
  exact ⟨hwin, hP, hmass⟩

/-- The Alice side of the coordinate-information estimate after the anchored verifier's
actual checked wins. The left side is the sum over the free coordinates, weighted by the
winning transcript law. All divergences use natural logarithms. -/
theorem exists_anchored_coordinateInformation_le_after_wins
    [DecidableEq Y] [Nonempty A] [Nonempty B]
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support) :
    let P := ((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
      (bobTranscriptProjection C e)
    ∃ ρ : (Info × Answer) × (Fin m → Option Y) → Matrix ι ι ℂ,
      (∀ z, IsDensityMatrix (ρ z)) ∧
      (∀ (t : Info) (a : C → A) (b : C → B) (y : Fin m → Option Y),
        ((t, a, b), y) ∈ P.support →
        ρ ((t, a, b), y) = normalizeDensity (partialTraceRight (pureState
          (S.averagedCheckedVector C (aliceQuestionsGivenInfo G α C t)
            (PMF.pure (completeBobQuestions C e t y)) a b)))) ∧
      (∑ t, (((P.map Prod.fst) t).toReal : WithTop ℝ) *
        ∑ i, mutualInformation
          (classicalQuantumMarginal (conditionalSnd P t) (fun y => ρ (t, y)) (fun y => y i))) ≤
        ((Real.log (Fintype.card Answer) -
          Real.log ((transcriptLaw G α C S).toOuterMeasure (winsOnChecked G α C)).toReal : ℝ) :
          WithTop ℝ) := by
  classical
  obtain ⟨hwin, hP, hmass⟩ := checkedWinTranscriptLaw_eq_anchored_filter G α C S e hs
  obtain ⟨ρ, hρ, hbranches, hbound⟩ := S.exists_checkedWin_coordinateInformation_le C
    (fun _ : Fin m => Option Y) (aliceQuestionsGivenInfo G α C) (infoLaw G α C)
    (fun t i => bobQuestionGivenInfo G α C t (e i))
    (fun t y => PMF.pure (completeBobQuestions C e t y)) (anchoredInfoWins G α C) hwin
  refine ⟨ρ, hρ, ?_, ?_⟩
  · simpa only [hP] using hbranches
  · rw [hP, hmass] at hbound
    exact hbound

/-- The Alice state conditioned under the winning law on an observation of Bob's free
tuple is the normalized marginal of the averaged checked branch in the prior fiber. -/
theorem quantumMarginalGivenMap_bobTranscriptProjection [DecidableEq Y] {U : Type*}
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support)
    {ρ : (Info × Answer) × (Fin m → Option Y) → Matrix ι ι ℂ}
    (hρ : ∀ z, IsDensityMatrix (ρ z))
    (hbranch : ∀ (t : Info) (a : C → A) (b : C → B) (y : Fin m → Option Y),
      ((t, a, b), y) ∈ (((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
        (bobTranscriptProjection C e)).support →
      ρ ((t, a, b), y) = normalizeDensity (partialTraceRight (pureState
        (S.averagedCheckedVector C (aliceQuestionsGivenInfo G α C t)
          (PMF.pure (completeBobQuestions C e t y)) a b))))
    (t : Info) (a : C → A) (b : C → B) (f : (Fin m → Option Y) → U) (u : U)
    (ht : (t, a, b) ∈ ((((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
      (bobTranscriptProjection C e)).map Prod.fst).support)
    (hu : u ∈ ((conditionalSnd
      (((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
        (bobTranscriptProjection C e)) (t, a, b)).map f).support) :
    let P := ((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
      (bobTranscriptProjection C e)
    let p := pi fun j : Fin m => bobQuestionGivenInfo G α C t (e j)
    let q := (conditionalSnd (p.map fun y => (f y, y)) u).map (completeBobQuestions C e t)
    quantumMarginalGivenMap (conditionalSnd P (t, a, b)) (fun y => ρ ((t, a, b), y)) f u =
      normalizeDensity (partialTraceRight (pureState
        (S.averagedCheckedVector C (aliceQuestionsGivenInfo G α C t) q a b))) := by
  classical
  obtain ⟨hwin, hP, _⟩ := checkedWinTranscriptLaw_eq_anchored_filter G α C S e hs
  have hbranch' := hbranch
  rw [← hP] at hbranch' ht hu
  have h := S.quantumMarginalGivenMap_checkedWinTranscriptLaw C (fun _ : Fin m => Option Y)
    (aliceQuestionsGivenInfo G α C) (infoLaw G α C)
    (fun t i => bobQuestionGivenInfo G α C t (e i))
    (fun t y => PMF.pure (completeBobQuestions C e t y)) (anchoredInfoWins G α C)
    hwin hρ hbranch' t a b f u ht hu
  rw [hP] at h
  exact h

/-- On a supported winning observation of Bob's selected question, the normalized noisy
checked-answer vector purifies Alice's conditional reduced state. -/
theorem checkedVectorGivenBob_purifies_winningMarginal [DecidableEq Y]
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support)
    {ρ : (Info × Answer) × (Fin m → Option Y) → Matrix ι ι ℂ}
    (hρ : ∀ z, IsDensityMatrix (ρ z)) :
    let P := ((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
      (bobTranscriptProjection C e)
    (∀ (t : Info) (a : C → A) (b : C → B) (y : Fin m → Option Y),
      ((t, a, b), y) ∈ P.support →
      ρ ((t, a, b), y) = normalizeDensity (partialTraceRight (pureState
        (S.averagedCheckedVector C (aliceQuestionsGivenInfo G α C t)
          (PMF.pure (completeBobQuestions C e t y)) a b)))) →
    ∀ (t : Info) (a : C → A) (b : C → B) (i : Fin m) (y : Option Y),
      (t, a, b) ∈ (P.map Prod.fst).support →
      y ∈ ((conditionalSnd P (t, a, b)).map fun z => z i).support →
      let j := e i
      let v := checkedVectorGivenBob G α C S j (omitMessage C j t) (t.halves j) y a b
      let ψ := ‖v‖⁻¹ • v
      ‖ψ‖ = 1 ∧
        quantumMarginalGivenMap (conditionalSnd P (t, a, b)) (fun z => ρ ((t, a, b), z))
          (fun z => z i) y = partialTraceRight (pureState ψ) := by
  classical
  intro P hbranch t a b i y ht hy
  obtain ⟨z, hz, hzi⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
  have hzP := (mem_support_conditionalSnd_iff P (t, a, b) ht z).mp hz
  obtain ⟨hwin, hP, _⟩ := checkedWinTranscriptLaw_eq_anchored_filter G α C S e hs
  dsimp only [P] at hzP
  rw [← hP] at hzP
  obtain ⟨htInfo, hprior⟩ := S.prior_mem_support_of_checkedWinTranscriptLaw C
    (fun _ : Fin m => Option Y) (aliceQuestionsGivenInfo G α C) (infoLaw G α C)
    (fun t k => bobQuestionGivenInfo G α C t (e k))
    (fun t z => PMF.pure (completeBobQuestions C e t z)) (anchoredInfoWins G α C)
    hwin t a b z hzP
  have hyPrior := (mem_support_pi_iff _ _).mp hprior i
  rw [hzi] at hyPrior
  have he := quantumMarginalGivenMap_bobTranscriptProjection G α C S e hs hρ hbranch t a b
    (fun z => z i) y ht hy
  dsimp only at he
  rw [← bobQuestionsGivenRest_eq_priorFiber G α C t htInfo e i y hyPrior,
    aliceQuestionsGivenInfo_eq_bind_rest G α C t htInfo (e i) y, ← checkedVectorGivenBob_eq,
    normalizeDensity_partialTraceRight_pureState] at he
  refine ⟨?_, he⟩
  have htrace := (isDensityMatrix_quantumMarginalGivenMap (conditionalSnd P (t, a, b))
    (fun z => hρ ((t, a, b), z)) (fun z => z i) y).trace_eq_one
  rw [he, trace_partialTraceRight, trace_pureState] at htrace
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    (by simpa only [Complex.ofReal_re, Complex.one_re, one_pow] using congrArg Complex.re htrace)

local notation "SwappedInfo" => Revealed (Option Y) (Option X) C
local notation "Raw" => ((Info × (C → A × B)) × (Free → PairQ))
local notation "SwappedRaw" => ((SwappedInfo × (C → B × A)) ×
  (Free → Option Y × Option X))

private def swapTranscript (z : Raw) : SwappedRaw :=
  let ((t, a), u) := z
  ((swapInfo C t, Prod.swap ∘ a), Prod.swap ∘ u)

omit [Fintype X] [Fintype Y] in
private theorem completeTranscript_swap (S : RepeatedStrategy) (qs : C → PairQ)
    (trials : Free → (Option X ⊕ Option Y) × PairQ) :
    completeTranscript C S.swap (Prod.swap ∘ qs) (fun j =>
        Prod.map Sum.swap Prod.swap (trials j)) =
      (completeTranscript C S qs trials).map (swapTranscript C) := by
  let t : Info := ⟨qs, Prod.fst ∘ trials⟩
  let u := Prod.snd ∘ trials
  have hcombine : (swapInfo C t).combine (Prod.swap ∘ u) = Prod.swap ∘ t.combine u := by
    funext i
    by_cases hi : i ∈ C <;>
      simp [swapInfo, Revealed.combine, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  change (checkedAnswerLaw C S.swap ((swapInfo C t).combine (Prod.swap ∘ u))).map
      (fun v => ((swapInfo C t, v), Prod.swap ∘ u)) =
    ((checkedAnswerLaw C S (t.combine u)).map (fun v => ((t, v), u))).map (swapTranscript C)
  rw [hcombine]
  simp only [checkedAnswerLaw, Function.comp_def, QuantumStrategy.answers_swap, PMF.map_comp]
  rfl

private theorem transcriptLaw_swap (S : RepeatedStrategy) :
    transcriptLaw G.swap α C S.swap = (transcriptLaw G α C S).map (swapTranscript C) := by
  rw [transcriptLaw_eq_complete, transcriptLaw_eq_complete, TwoProverGame.anchored_questions]
  change (pi fun _ : C => anchorPair (G.questions.map Prod.swap) α α).bind
      (fun qs => (pi fun _ : Free => law (G.questions.map Prod.swap) α).bind
        (completeTranscript C S.swap qs)) = _
  simp only [← map_swap_anchorPair, ← map_swap_law, pi_map, PMF.bind_map, Function.comp_def,
    PMF.map_bind, TwoProverGame.anchored_questions]
  apply congrArg ((pi fun _ : C => anchorPair G.questions α α).bind)
  funext qs
  apply congrArg ((pi fun _ : Free => law G.questions α).bind)
  funext tr
  exact completeTranscript_swap C S qs tr

omit [Fintype X] [Fintype Y] [Fintype A] [Fintype B] in
private theorem preimage_winsOnChecked_swap :
    swapTranscript C ⁻¹' winsOnChecked G.swap α C = winsOnChecked G α C := by
  ext ⟨⟨t, a⟩, u⟩
  change (∀ i : C, (G.swap.anchored α).accepts (t.questions i).2 (t.questions i).1
      (a i).2 (a i).1) ↔
    (∀ i : C, (G.anchored α).accepts (t.questions i).1 (t.questions i).2 (a i).1 (a i).2)
  apply forall_congr'
  intro i
  rw [TwoProverGame.anchored_accepts, TwoProverGame.anchored_accepts]
  cases (t.questions i).1 <;> cases (t.questions i).2 <;> rfl

/-- Bob's full-question law, conditional on the shared questions and noisy messages. -/
noncomputable def bobQuestionsGivenInfo (t : Info) : PMF (Fin n → Option Y) :=
  (pi fun j : Free => bobGivenMessage G.questions α (t.halves j)).map
    (appendQuestions C (Prod.snd ∘ t.questions))

/-- Insert the checked Alice questions into the renumbered free tuple. -/
def completeAliceQuestions (e : Fin m ≃ Free) (t : Info) (x : Fin m → Option X) :
    Fin n → Option X :=
  appendQuestions C (Prod.fst ∘ t.questions) (x ∘ e.symm)

omit [Fintype X] [Fintype A] [Fintype B] in
private theorem aliceQuestionsGivenInfo_swap (t : Info) :
    aliceQuestionsGivenInfo G.swap α C (swapInfo C t) = bobQuestionsGivenInfo G α C t := by
  have hk (j : Free) : aliceGivenMessage G.swap.questions α ((swapInfo C t).halves j) =
      bobGivenMessage G.questions α (t.halves j) := by
    have hμ : ((G.questions.map Prod.swap).map Prod.swap) = G.questions := by
      rw [PMF.map_comp, show Prod.swap ∘ (Prod.swap : X × Y → Y × X) = id from
        funext Prod.swap_swap, PMF.map_id]
    change aliceGivenMessage (G.questions.map Prod.swap) α (Sum.swap (t.halves j)) =
      bobGivenMessage G.questions α (t.halves j)
    cases t.halves j <;> simp [aliceGivenMessage, bobGivenMessage, hμ]
  simp only [aliceQuestionsGivenInfo, bobQuestionsGivenInfo, hk]
  rfl

/-- The projection of the original transcript to its checked answers and Alice's
renumbered free questions. -/
@[expose] def aliceTranscriptProjection (e : Fin m ≃ Free) (z : Raw) :
    (Info × Answer) × (Fin m → Option X) :=
  questionTranscriptProjection C Prod.fst e z

omit [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] in
private theorem mem_support_map_prodCongr_left {D E F : Type*} (P : PMF (D × F))
    (f : D ≃ E) {d : D} (hd : d ∈ (P.map Prod.fst).support) :
    f d ∈ ((P.map (f.prodCongr (Equiv.refl F))).map Prod.fst).support := by
  rw [PMF.map_comp, show Prod.fst ∘ f.prodCongr (Equiv.refl F) = f ∘ Prod.fst from rfl,
    ← PMF.map_comp]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨d, hd, rfl⟩

private def swapLabel :
    (Info × Answer) ≃ (SwappedInfo × ((C → B) × (C → A))) :=
  (swapInfo C).prodCongr (Equiv.prodComm _ _)

private theorem winning_questionProjections_swap
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support) :
    let T := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let Ts := transcriptLaw G.swap α C S.swap
    let Ws := winsOnChecked G.swap α C
    let P := (T.filter W hs).map (aliceTranscriptProjection C e)
    let g := (swapLabel (A := A) (B := B) (X := X) (Y := Y) C).prodCongr
      (Equiv.refl (Fin m → Option X))
    ∃ hss : ∃ z ∈ Ws, z ∈ Ts.support,
      (Ts.filter Ws hss).map (bobTranscriptProjection C e) = P.map g ∧
      Ts.toOuterMeasure Ws = T.toOuterMeasure W := by
  classical
  let T := transcriptLaw G α C S
  let W := winsOnChecked G α C
  let Ts := transcriptLaw G.swap α C S.swap
  let Ws := winsOnChecked G.swap α C
  let f := swapLabel (X := X) (Y := Y) (A := A) (B := B) C
  let g := f.prodCongr (Equiv.refl (Fin m → Option X))
  have hmap : Ts = T.map (swapTranscript C) := transcriptLaw_swap G α C S
  have hpre : swapTranscript C ⁻¹' Ws = W := preimage_winsOnChecked_swap G α C
  have hmass : Ts.toOuterMeasure Ws = T.toOuterMeasure W := by
    rw [hmap, PMF.toOuterMeasure_map_apply, hpre]
  have hss : ∃ z ∈ Ws, z ∈ Ts.support := by
    rw [← toOuterMeasure_toReal_pos_iff, hmass, toOuterMeasure_toReal_pos_iff]
    exact hs
  let P := (T.filter W hs).map (aliceTranscriptProjection C e)
  let Ps := (Ts.filter Ws hss).map (bobTranscriptProjection C e)
  have hPs : Ps = P.map g := by
    have hss' : ∃ z ∈ Ws, z ∈ (T.map (swapTranscript C)).support := hmap ▸ hss
    have hs' : ∃ z ∈ swapTranscript C ⁻¹' Ws, z ∈ T.support := hpre.symm ▸ hs
    have hfilter : Ts.filter Ws hss = (T.map (swapTranscript C)).filter Ws hss' := by
      congr 1
    dsimp only [Ps, P]
    rw [hfilter, filter_map T _ _ hss' hs', PMF.map_comp, PMF.map_comp]
    congr 1
    congr 1
  exact ⟨hss, hPs, hmass⟩

/-- Bob's coordinate-information bound in the summed form of equation (36) of
[Bavarian, Vidick and Yuen, Claim 5.13][BavarianVidickYuen2022]
(arXiv:1509.07466v2, §5, printed pp. 23–24). The state at each supported transcript
is the normalized Bob marginal of the original strategy's checked-answer branch. -/
theorem exists_bob_anchored_coordinateInformation_le_after_wins
    [DecidableEq X] [Nonempty A] [Nonempty B]
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support) :
    let P := ((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
      (aliceTranscriptProjection C e)
    ∃ ρ : (Info × Answer) × (Fin m → Option X) → Matrix κ κ ℂ,
      (∀ z, IsDensityMatrix (ρ z)) ∧
      (∀ (t : Info) (a : C → A) (b : C → B) (x : Fin m → Option X),
        ((t, a, b), x) ∈ P.support →
        ρ ((t, a, b), x) = normalizeDensity (partialTraceLeft (pureState
          (S.averagedCheckedVector C (PMF.pure (completeAliceQuestions C e t x))
            (bobQuestionsGivenInfo G α C t) a b)))) ∧
      (∑ t, (((P.map Prod.fst) t).toReal : WithTop ℝ) *
        ∑ i, mutualInformation
          (classicalQuantumMarginal (conditionalSnd P t) (fun x => ρ (t, x)) (fun x => x i))) ≤
        ((Real.log (Fintype.card Answer) -
          Real.log ((transcriptLaw G α C S).toOuterMeasure (winsOnChecked G α C)).toReal : ℝ) :
          WithTop ℝ) := by
  classical
  let T := transcriptLaw G α C S
  let W := winsOnChecked G α C
  let Ts := transcriptLaw G.swap α C S.swap
  let Ws := winsOnChecked G.swap α C
  let f := swapLabel (X := X) (Y := Y) (A := A) (B := B) C
  let g := f.prodCongr (Equiv.refl (Fin m → Option X))
  obtain ⟨hss, hPs, hmass⟩ := winning_questionProjections_swap G α C S e hs
  let P := (T.filter W hs).map (aliceTranscriptProjection C e)
  let Ps := (Ts.filter Ws hss).map (bobTranscriptProjection C e)
  change Ps = P.map g at hPs
  obtain ⟨ρ, hρ, hbranch, hbound⟩ :=
    exists_anchored_coordinateInformation_le_after_wins G.swap α C S.swap e hss
  change _ ≤ ((Real.log (Fintype.card ((C → B) × (C → A))) -
    Real.log (Ts.toOuterMeasure Ws).toReal : ℝ) : WithTop ℝ) at hbound
  have hcard : Fintype.card ((C → B) × (C → A)) = Fintype.card Answer :=
    Fintype.card_congr (Equiv.prodComm _ _)
  rw [hmass, hcard] at hbound
  refine ⟨ρ ∘ g, fun z => hρ (g z), ?_, ?_⟩
  · intro t a b x hx
    have hxs : ((swapInfo C t, b, a), x) ∈ Ps.support := by
      rw [hPs, PMF.mem_support_map_iff]
      exact ⟨((t, a, b), x), hx, rfl⟩
    change ρ ((swapInfo C t, b, a), x) = _
    have hq : completeBobQuestions C e (swapInfo C t) x = completeAliceQuestions C e t x := rfl
    rw [hbranch _ _ _ _ hxs, aliceQuestionsGivenInfo_swap, hq,
      QuantumStrategy.partialTraceRight_averagedCheckedVector_swap]
  · change _ ≤ ((Real.log (Fintype.card Answer) -
      Real.log (T.toOuterMeasure W).toReal : ℝ) : WithTop ℝ)
    refine le_trans ?_ hbound
    rw [← Equiv.sum_comp f]
    have hmarg : Ps.map Prod.fst = (P.map Prod.fst).map f := by
      simp only [hPs, PMF.map_comp]
      rfl
    apply le_of_eq
    refine Finset.sum_congr rfl fun t _ => ?_
    have hmass' : (Ps.map Prod.fst) (f t) = (P.map Prod.fst) t := by
      rw [hmarg, map_equiv_apply, Equiv.symm_apply_apply]
    rw [hmass']
    by_cases ht : t ∈ (P.map Prod.fst).support
    · have hc := conditionalSnd_map_prodCongr P f (Equiv.refl _) t
      simp only [Equiv.coe_refl, PMF.map_id] at hc
      rw [← hPs] at hc
      rw [hc]
      rfl
    · have hz := (PMF.apply_eq_zero_iff _ _).mpr ht
      change (↑((P.map Prod.fst) t).toReal : WithTop ℝ) * _ =
        (↑((P.map Prod.fst) t).toReal : WithTop ℝ) * _
      rw [hz, ENNReal.toReal_zero, WithTop.coe_zero, zero_mul, zero_mul]

private theorem bobTranscriptBranch_swap (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (P : PMF ((Info × Answer) × (Fin m → Option X)))
    {ρ : (Info × Answer) × (Fin m → Option X) → Matrix κ κ ℂ}
    (hbranch : ∀ (t : Info) (a : C → A) (b : C → B) (x : Fin m → Option X),
      ((t, a, b), x) ∈ P.support →
      ρ ((t, a, b), x) = normalizeDensity (partialTraceLeft (pureState
        (S.averagedCheckedVector C (PMF.pure (completeAliceQuestions C e t x))
          (bobQuestionsGivenInfo G α C t) a b)))) :
    let g := (swapLabel (X := X) (Y := Y) (A := A) (B := B) C).prodCongr
      (Equiv.refl (Fin m → Option X))
    ∀ (ts : SwappedInfo) (bs : C → B) (as : C → A) (x : Fin m → Option X),
      ((ts, bs, as), x) ∈ (P.map g).support →
      ρ (g.symm ((ts, bs, as), x)) = normalizeDensity (partialTraceRight (pureState
        (S.swap.averagedCheckedVector C (aliceQuestionsGivenInfo G.swap α C ts)
          (PMF.pure (completeBobQuestions C e ts x)) bs as))) := by
  classical
  intro g ts bs as x hx
  let t' := (swapInfo (X := Option X) (Y := Option Y) C).symm ts
  have ht' : swapInfo C t' = ts := (swapInfo C).apply_symm_apply ts
  have hx' : ((t', as, bs), x) ∈ P.support := by
    rw [PMF.mem_support_iff, map_equiv_apply] at hx
    exact (PMF.mem_support_iff _ _).mpr hx
  change ρ ((t', as, bs), x) = _
  rw [hbranch t' as bs x hx', ← ht', aliceQuestionsGivenInfo_swap]
  change _ = normalizeDensity (partialTraceRight (pureState
    (S.swap.averagedCheckedVector C (bobQuestionsGivenInfo G α C t')
      (PMF.pure (completeAliceQuestions C e t' x)) bs as)))
  rw [QuantumStrategy.partialTraceRight_averagedCheckedVector_swap]

/-- The Bob state conditioned under the winning law on an observation of Alice's free
tuple is the normalized marginal of the averaged checked branch in the prior fiber. -/
theorem quantumMarginalGivenMap_aliceTranscriptProjection [DecidableEq X] {U : Type*}
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support)
    {ρ : (Info × Answer) × (Fin m → Option X) → Matrix κ κ ℂ}
    (hρ : ∀ z, IsDensityMatrix (ρ z))
    (hbranch : ∀ (t : Info) (a : C → A) (b : C → B) (x : Fin m → Option X),
      ((t, a, b), x) ∈ (((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
        (aliceTranscriptProjection C e)).support →
      ρ ((t, a, b), x) = normalizeDensity (partialTraceLeft (pureState
        (S.averagedCheckedVector C (PMF.pure (completeAliceQuestions C e t x))
          (bobQuestionsGivenInfo G α C t) a b))))
    (t : Info) (a : C → A) (b : C → B) (f : (Fin m → Option X) → U) (u : U)
    (ht : (t, a, b) ∈ ((((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
      (aliceTranscriptProjection C e)).map Prod.fst).support)
    (hu : u ∈ ((conditionalSnd
      (((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
        (aliceTranscriptProjection C e)) (t, a, b)).map f).support) :
    let P := ((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
      (aliceTranscriptProjection C e)
    let p := pi fun j : Fin m => aliceGivenMessage G.questions α (t.halves (e j))
    let q := (conditionalSnd (p.map fun x => (f x, x)) u).map (completeAliceQuestions C e t)
    quantumMarginalGivenMap (conditionalSnd P (t, a, b)) (fun x => ρ ((t, a, b), x)) f u =
      normalizeDensity (partialTraceLeft (pureState
        (S.averagedCheckedVector C q (bobQuestionsGivenInfo G α C t) a b))) := by
  classical
  intro P p q
  let labelSwap := swapLabel (X := X) (Y := Y) (A := A) (B := B) C
  let g := labelSwap.prodCongr (Equiv.refl (Fin m → Option X))
  obtain ⟨hss, hPs, _⟩ := winning_questionProjections_swap G α C S e hs
  let Ps := ((transcriptLaw G.swap α C S.swap).filter (winsOnChecked G.swap α C) hss).map
    (bobTranscriptProjection C e)
  change Ps = P.map g at hPs
  let ρs := ρ ∘ g.symm
  have hρs : ∀ z, IsDensityMatrix (ρs z) := fun z => hρ (g.symm z)
  have hbranch_s := bobTranscriptBranch_swap G α C S e P hbranch
  dsimp only at hbranch_s
  rw [← hPs] at hbranch_s
  have hts := mem_support_map_prodCongr_left P labelSwap ht
  rw [← hPs] at hts
  have hcond := conditionalSnd_map_prodCongr P labelSwap (Equiv.refl _) (t, a, b)
  simp only [Equiv.coe_refl, PMF.map_id] at hcond
  rw [← hPs] at hcond
  change conditionalSnd Ps (swapInfo C t, b, a) = conditionalSnd P (t, a, b) at hcond
  have hus : u ∈ ((conditionalSnd Ps (swapInfo C t, b, a)).map f).support := hcond.symm ▸ hu
  have he := quantumMarginalGivenMap_bobTranscriptProjection G.swap α C S.swap e hss hρs
    hbranch_s (swapInfo C t) b a f u hts hus
  change quantumMarginalGivenMap (conditionalSnd Ps (swapInfo C t, b, a))
    (fun x => ρs ((swapInfo C t, b, a), x)) f u = _ at he
  rw [hcond, aliceQuestionsGivenInfo_swap] at he
  have hk (i : Fin m) : bobQuestionGivenInfo G.swap α C (swapInfo C t) (e i) =
      aliceGivenMessage G.questions α (t.halves (e i)) := by
    change bobGivenMessage (G.questions.map Prod.swap) α (Sum.swap (t.halves (e i))) =
      aliceGivenMessage G.questions α (t.halves (e i))
    cases t.halves (e i) <;> rfl
  simp only [hk] at he
  change _ = normalizeDensity (partialTraceRight (pureState
    (S.swap.averagedCheckedVector C (bobQuestionsGivenInfo G α C t) q b a))) at he
  rw [QuantumStrategy.partialTraceRight_averagedCheckedVector_swap] at he
  have hr : (fun x => ρs ((swapInfo C t, b, a), x)) = fun x => ρ ((t, a, b), x) := by
    funext x
    exact congrArg ρ (g.symm_apply_apply ((t, a, b), x))
  rw [hr] at he
  exact he

/-- On a supported winning observation of Alice's selected question, the normalized
noisy checked-answer vector purifies Bob's conditional reduced state. -/
theorem checkedVectorGivenAlice_purifies_winningMarginal [DecidableEq X]
    (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support)
    {ρ : (Info × Answer) × (Fin m → Option X) → Matrix κ κ ℂ}
    (hρ : ∀ z, IsDensityMatrix (ρ z)) :
    let P := ((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
      (aliceTranscriptProjection C e)
    (∀ (t : Info) (a : C → A) (b : C → B) (x : Fin m → Option X),
      ((t, a, b), x) ∈ P.support →
      ρ ((t, a, b), x) = normalizeDensity (partialTraceLeft (pureState
        (S.averagedCheckedVector C (PMF.pure (completeAliceQuestions C e t x))
          (bobQuestionsGivenInfo G α C t) a b)))) →
    ∀ (t : Info) (a : C → A) (b : C → B) (i : Fin m) (x : Option X),
      (t, a, b) ∈ (P.map Prod.fst).support →
      x ∈ ((conditionalSnd P (t, a, b)).map fun z => z i).support →
      let v := checkedVectorGivenAlice G α C S (e i) t x a b
      let ψ := ‖v‖⁻¹ • v
      ‖ψ‖ = 1 ∧
        quantumMarginalGivenMap (conditionalSnd P (t, a, b)) (fun z => ρ ((t, a, b), z))
          (fun z => z i) x = partialTraceRight (pureState ψ) := by
  classical
  intro P hbranch t a b i x ht hx
  let f := swapLabel (X := X) (Y := Y) (A := A) (B := B) C
  let g := f.prodCongr (Equiv.refl (Fin m → Option X))
  obtain ⟨hss, hPs, _⟩ := winning_questionProjections_swap G α C S e hs
  let Ps := ((transcriptLaw G.swap α C S.swap).filter (winsOnChecked G.swap α C) hss).map
    (bobTranscriptProjection C e)
  change Ps = P.map g at hPs
  have hbranch_s := bobTranscriptBranch_swap G α C S e P hbranch
  dsimp only at hbranch_s
  rw [← hPs] at hbranch_s
  have hts := mem_support_map_prodCongr_left P f ht
  have hcond := conditionalSnd_map_prodCongr P f (Equiv.refl _) (t, a, b)
  simp only [Equiv.coe_refl, PMF.map_id] at hcond
  rw [← hPs] at hts hcond
  have hxs : x ∈ ((conditionalSnd Ps (f (t, a, b))).map (fun z => z i)).support :=
    hcond.symm ▸ hx
  have h := checkedVectorGivenBob_purifies_winningMarginal G.swap α C S.swap e hss
    (ρ := ρ ∘ g.symm) (fun z => hρ (g.symm z)) hbranch_s (swapInfo C t) b a i x hts hxs
  change conditionalSnd Ps (swapInfo C t, b, a) = conditionalSnd P (t, a, b) at hcond
  have hr : (fun z => (ρ ∘ g.symm) ((swapInfo C t, b, a), z)) = fun z => ρ ((t, a, b), z) := by
    funext z
    exact congrArg ρ (g.symm_apply_apply ((t, a, b), z))
  dsimp only at h
  rw [hcond, hr, ← checkedVectorGivenAlice_eq] at h
  exact h

end Cslib.PCP.AnchoredDependency
