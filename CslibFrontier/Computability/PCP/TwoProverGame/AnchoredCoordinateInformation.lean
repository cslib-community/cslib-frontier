/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredConditionalStates
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

## Main results

* `map_transcriptLaw_eq_checkedAnswersWithLabel`: the sampler identity before filtering.
* `exists_anchored_coordinateInformation_le_after_wins`: the Alice marginal bound
  weighted by the verifier's winning transcript.
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

private def appendQuestions {Q : Type*} (checked : C → Q) (free : Free → Q) : Fin n → Q :=
  (Equiv.piEquivPiSubtypeProd (· ∈ C) fun _ => Q).symm (checked, free)

omit [Fintype X] [Fintype Y] in
private theorem project_combine {Q : Type*} (f : PairQ → Q) (t : Info) (u : Free → PairQ) :
    f ∘ t.combine u = appendQuestions C (f ∘ t.questions) (f ∘ u) := by
  funext i
  by_cases hi : i ∈ C <;>
    simp [appendQuestions, Revealed.combine, Equiv.piEquivPiSubtypeProd_symm_apply, hi]

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
private theorem splitFree_givenInfo (t : Info) (ht : t ∈ (infoLaw G α C).support) :
    (pi fun j : Free => pairGiven G α C j t).map
      (fun (u : Free → PairQ) => (Prod.fst ∘ u, Prod.snd ∘ u)) =
        (pi fun j : Free => aliceGivenMessage G.questions α (t.halves j)).bind fun x =>
          (pi fun j : Free => bobQuestionGivenInfo G α C t j).map (x, ·) := by
  have hm (j : Free) : t.halves j ∈ ((law G.questions α).map Prod.fst).support := by
    simp only [infoLaw, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at ht
    obtain ⟨_, -, halves, hhalves, rfl⟩ := ht
    exact (mem_support_pi_iff _ _).mp hhalves j
  have hp (j : Free) :
      pairGiven G α C j t = (aliceGivenMessage G.questions α (t.halves j)).bind
        (fun x => (bobQuestionGivenInfo G α C t j).map (x, ·)) := by
    unfold pairGiven bobQuestionGivenInfo
    conv_lhs => rw [law_eq_bind_messages]
    exact conditionalSnd_bind_pair _ _ _ (hm j)
  simp_rw [hp]
  exact pi_bind_pair _ _

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

/-- The projection of the original transcript to its checked answers and Bob's
renumbered free questions. -/
@[expose] def bobTranscriptProjection (e : Fin m ≃ Free)
    (z : (Info × (C → A × B)) × (Free → PairQ)) :
    (Info × Answer) × (Fin m → Option Y) :=
  let ((t, a), u) := z
  ((t, (Prod.fst ∘ a, Prod.snd ∘ a)), fun i => (u (e i)).2)

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
  let T := transcriptLaw G α C S
  let p := aliceQuestionsGivenInfo G α C
  let r := infoLaw G α C
  let s (t : Info) (i : Fin m) := bobQuestionGivenInfo G α C t (e i)
  let q (t : Info) (y : Fin m → Option Y) := PMF.pure (completeBobQuestions C e t y)
  let W (t : Info) : Set Answer :=
    {a | ∀ i : C, (G.anchored α).accepts (t.questions i).1 (t.questions i).2 (a.1 i) (a.2 i)}
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
  obtain ⟨ρ, hρ, hbranches, hbound⟩ := S.exists_checkedWin_coordinateInformation_le C
    (fun _ : Fin m => Option Y) p r s q W hwin
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
  refine ⟨ρ, hρ, ?_, ?_⟩
  · simpa only [hP] using hbranches
  · rw [hP, show (L.toOuterMeasure event).toReal =
        (T.toOuterMeasure (winsOnChecked G α C)).toReal from congrArg ENNReal.toReal hmass]
      at hbound
    exact hbound

end Cslib.PCP.AnchoredDependency
