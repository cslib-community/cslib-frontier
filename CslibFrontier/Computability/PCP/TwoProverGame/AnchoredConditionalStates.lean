/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredTranscript
public import CslibFrontier.Computability.PCP.TwoProverGame.AveragedAnswerStates
import CslibFrontier.Probability.PMF.Map

/-!
# Conditional checked-answer states of the anchored experiment

Once the selected pair and the remaining question information are fixed, the hidden local
questions are independent. The norm of the averaged checked-answer branch therefore measures
the probability of the checked answers in the actual anchored experiment.

This identifies the fixed-question normalization in
[Bavarian, Vidick and Yuen, Proposition 4.9][BavarianVidickYuen2022], equation (20).

## Main results

* `questionsGivenRest_eq_bind`: the local question laws are independent at a supported observation.
* `norm_checkedVectorGivenRest_sq_observed`: the branch weight equals the conditional probability
  of the checked answers in the original anchored sampler.
-/

public section

open scoped unitInterval

namespace Cslib.PCP.AnchoredDependency

open Cslib.Probability.PMF
open ParallelRepetition (Revealed Shared)

private theorem map_snd_bind_pair {U V : Type*} (p : PMF U) (q : PMF V) :
    (p.bind fun x => q.map (x, ·)).map Prod.snd = q := by
  simp only [PMF.map_bind, PMF.map_comp]
  change (p.bind fun _ => q.map id) = q
  simp only [PMF.map_id, PMF.bind_const]

private theorem bind_marginals_eq {U V : Type*} (p : PMF U) (q : PMF V) :
    let joint := p.bind fun x => q.map (x, ·)
    (joint.map Prod.fst).bind (fun x => (joint.map Prod.snd).map (x, ·)) = joint := by
  simp only [map_snd_bind_pair, map_fst_bind_pair]

variable {X Y A B ι κ : Type*} {n : ℕ}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "PairQ" => (Option X × Option Y)
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ

variable (G : TwoProverGame X Y A B) (α : I) (C : Finset (Fin n))

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Saved" => RestQuestions (Option X) (Option Y) C

/-- The Alice question tuple law at fixed remaining information and selected question pair. -/
@[expose] noncomputable def aliceQuestionsGivenRest (j : Free) (t : Saved j) (q : PairQ) :
    PMF (Fin n → Option X) :=
  (questionsGivenRest G α C j t q).map (fun u => Prod.fst ∘ u)

/-- The Bob question tuple law at fixed remaining information and selected question pair. -/
@[expose] noncomputable def bobQuestionsGivenRest (j : Free) (t : Saved j) (q : PairQ) :
    PMF (Fin n → Option Y) :=
  (questionsGivenRest G α C j t q).map (fun u => Prod.snd ∘ u)

omit [Fintype A] [Fintype B] in
/-- The two parties' entire question tuples are independent given the retained information
and the selected pair. -/
theorem questionsGivenRest_eq_bind (j : Free) (t : Saved j) (q : PairQ)
    (ht : t ∈ (restQuestionsLaw G α C j).support) :
    questionsGivenRest G α C j t q =
      (aliceQuestionsGivenRest G α C j t q).bind fun x =>
        (bobQuestionsGivenRest G α C j t q).map fun y i => (x i, y i) := by
  let full := restoreMessage C j t
  let p := Function.update (fun i => pairGiven G α C i full) j (PMF.pure q)
  have hp (i : Free) :
      ((p i).map Prod.fst).bind (fun x => ((p i).map Prod.snd).map (x, ·)) = p i := by
    by_cases hi : i = j
    · subst i
      simp only [p, Function.update_self, PMF.pure_map, PMF.pure_bind, Prod.mk.eta]
    · have hm := mem_support_halves_of_mem_support_restQuestionsLaw G α C j t ht ⟨i, hi⟩
      dsimp only [p]
      rw [Function.update_of_ne hi]
      change ((conditionalSnd (law G.questions α) (full.halves i)).map Prod.fst).bind
        (fun x => ((conditionalSnd (law G.questions α) (full.halves i)).map Prod.snd).map (x, ·))
          = conditionalSnd (law G.questions α) (full.halves i)
      have htag : full.halves i = t.halves ⟨i, hi⟩ := by
        simp only [full, restoreMessage, dite_eq_right hi]
      rw [htag]
      revert hm
      cases t.halves ⟨i, hi⟩ with
      | inl m =>
        intro hm
        rw [conditionalSnd_law_inl _ _ _ hm]
        exact bind_marginals_eq _ _
      | inr m =>
        intro hm
        rw [conditionalSnd_law_inr _ _ _ hm]
        exact bind_marginals_eq _ _
  let priorX := pi (fun i => (p i).map Prod.fst)
  let priorY := pi (fun i => (p i).map Prod.snd)
  let split (u : Free → PairQ) := (Prod.fst ∘ u, Prod.snd ∘ u)
  have hsplit : (pi p).map split = priorX.bind (fun x => priorY.map (x, ·)) := by
    simpa only [hp, split, priorX, priorY, Function.comp_def] using
      (pi_bind_pair (fun i => (p i).map Prod.fst) (fun i _ => (p i).map Prod.snd))
  let appendX (u : Free → Option X) :=
    (Equiv.piEquivPiSubtypeProd (· ∈ C) fun _ => Option X).symm (Prod.fst ∘ t.questions, u)
  let appendY (u : Free → Option Y) :=
    (Equiv.piEquivPiSubtypeProd (· ∈ C) fun _ => Option Y).symm (Prod.snd ∘ t.questions, u)
  have hcombine (u : Free → PairQ) :
      full.combine u = fun i => (appendX (Prod.fst ∘ u) i, appendY (Prod.snd ∘ u) i) := by
    unfold Revealed.combine
    funext i
    by_cases hi : i ∈ C <;>
      simp [Equiv.piEquivPiSubtypeProd_symm_apply, hi, appendX, appendY, full, restoreMessage]
  have hx : aliceQuestionsGivenRest G α C j t q = priorX.map appendX := by
    unfold aliceQuestionsGivenRest questionsGivenRest
    rw [PMF.map_comp, show priorX = _ from pi_map p (fun _ => Prod.fst), PMF.map_comp]
    congr 1
    funext u
    rw [Function.comp_apply, hcombine]
    rfl
  have hy : bobQuestionsGivenRest G α C j t q = priorY.map appendY := by
    unfold bobQuestionsGivenRest questionsGivenRest
    rw [PMF.map_comp, show priorY = _ from pi_map p (fun _ => Prod.snd), PMF.map_comp]
    congr 1
    funext u
    rw [Function.comp_apply, hcombine]
    rfl
  rw [hx, hy]
  change (pi p).map full.combine = _
  have h := congrArg (PMF.map fun (x, y) i => (appendX x i, appendY y i)) hsplit
  rw [PMF.map_comp] at h
  have he : (fun (x, y) i => (appendX x i, appendY y i)) ∘ split = full.combine :=
    funext fun u => (hcombine u).symm
  rw [he] at h
  simpa only [PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def] using h

/-- The branch vector selected by the checked answers, with the retained information and
the selected question pair held fixed. -/
@[expose] noncomputable def checkedVectorGivenRest (S : RepeatedStrategy) (j : Free) (t : Saved j)
    (q : PairQ) (a : C → A) (b : C → B) : EuclideanSpace ℂ (ι × κ) :=
  S.averagedCheckedVector C (aliceQuestionsGivenRest G α C j t q)
    (bobQuestionsGivenRest G α C j t q) a b

/-- The branch weight is the point mass of the reconstructed answer kernel. -/
theorem norm_checkedVectorGivenRest_sq_answers (S : RepeatedStrategy) (j : Free) (t : Saved j)
    (q : PairQ) (a : C → A) (b : C → B) (ht : t ∈ (restQuestionsLaw G α C j).support) :
    ‖checkedVectorGivenRest G α C S j t q a b‖ ^ 2 =
      (answersGivenRest G α C S j t q (fun i => (a i, b i))).toReal := by
  let pack := (Equiv.arrowProdEquivProdArrow C (fun _ => A) (fun _ => B)).symm
  have hpack (x : Fin n → Option X) (y : Fin n → Option Y) :
      checkedAnswerLaw C S (fun i => (x i, y i)) = (S.checkedAnswers C x y).map pack := by
    simp only [checkedAnswerLaw, QuantumStrategy.checkedAnswers, PMF.map_comp,
      Function.comp_def, pack]
    rfl
  rw [checkedVectorGivenRest, QuantumStrategy.norm_averagedCheckedVector_sq]
  rw [answersGivenRest, questionsGivenRest_eq_bind G α C j t q ht, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def, hpack, ← PMF.map_bind]
  rw [show (fun i => (a i, b i)) = pack (a, b) from rfl,
    map_apply_of_injective _ pack.injective (a, b)]

/-- The squared norm of the branch is the probability of the checked answers conditional on
the retained questions and messages in the experiment with the selected pair fixed. -/
theorem norm_checkedVectorGivenRest_sq (S : RepeatedStrategy) (j : Free) (t : Saved j)
    (q : PairQ) (a : C → A) (b : C → B) (ht : t ∈ (restQuestionsLaw G α C j).support) :
    ‖checkedVectorGivenRest G α C S j t q a b‖ ^ 2 =
      (conditionalSnd ((restKernel G α C S j q).map (fun r => (restQuestions C j r, r.answers)))
        t (fun i => (a i, b i))).toReal := by
  rw [map_restKernel_eq_bind, conditionalSnd_bind_pair _ _ _ ht,
    norm_checkedVectorGivenRest_sq_answers G α C S j t q a b ht]

local notation "Trial" => ((Option X ⊕ Option Y) × PairQ)

/-- Keep a chosen observation of the selected trial, together with the retained question
information and the checked answers from the original transcript. -/
noncomputable def observedCheckedAnswersBy {O : Type*} (S : RepeatedStrategy) (j : Free)
    (observe : Trial → O) : PMF ((O × Saved j) × (C → A × B)) :=
  (transcriptLaw G α C S).map fun r =>
    let rest := restTranscript C j r
    ((observe (freeTrials C r j), restQuestions C j rest), rest.answers)

/-- Disintegrate the original checked answers by the selected trial and retained information,
then apply the requested observation to the selected trial. -/
theorem observedCheckedAnswersBy_eq_bind {O : Type*} (S : RepeatedStrategy) (j : Free)
    (observe : Trial → O) :
    observedCheckedAnswersBy G α C S j observe =
      (law G.questions α).bind fun trial =>
        (restQuestionsLaw G α C j).bind fun t =>
          (answersGivenRest G α C S j t trial.2).map ((observe trial, t), ·) := by
  let read := fun p : Trial × Shared (Option X) (Option Y) A B C j =>
    let (trial, rest) := p
    ((observe trial, restQuestions C j rest), rest.answers)
  have h := congrArg (PMF.map read) (map_trial_restTranscriptLaw G α C S j)
  have hk (trial : Trial) :
      (restKernel G α C S j trial.2).map
        (fun r => ((observe trial, restQuestions C j r), r.answers)) =
      (restQuestionsLaw G α C j).bind fun t =>
        (answersGivenRest G α C S j t trial.2).map ((observe trial, t), ·) := by
    have h' := congrArg (PMF.map fun z : Saved j × (C → A × B) => ((observe trial, z.1), z.2))
      (map_restKernel_eq_bind G α C S j trial.2)
    simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def] using h'
  simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, read, observedCheckedAnswersBy, hk]
    using h

/-- Keep the selected question pair as the observation of the selected trial. -/
noncomputable def observedCheckedAnswers (S : RepeatedStrategy) (j : Free) :
    PMF ((PairQ × Saved j) × (C → A × B)) :=
  observedCheckedAnswersBy G α C S j Prod.snd

/-- The effect-based branch weight agrees with the conditional answer probability in
the original sampler, given the selected question pair and retained question information. -/
theorem norm_checkedVectorGivenRest_sq_observed (S : RepeatedStrategy) (j : Free) (t : Saved j)
    (q : PairQ) (a : C → A) (b : C → B) (ht : t ∈ (restQuestionsLaw G α C j).support)
    (hq : q ∈ ((law G.questions α).map Prod.snd).support) :
    ‖checkedVectorGivenRest G α C S j t q a b‖ ^ 2 =
      (conditionalSnd (observedCheckedAnswers G α C S j) (q, t) (fun i => (a i, b i))).toReal := by
  let P := (law G.questions α).map Prod.snd
  let Q := restQuestionsLaw G α C j
  let H := fun z : PairQ × Saved j => answersGivenRest G α C S j z.2 z.1
  let prior := P.bind fun q' => Q.map (q', ·)
  have hLaw : observedCheckedAnswers G α C S j =
      prior.bind fun z => (H z).map (z, ·) := by
    rw [observedCheckedAnswers, observedCheckedAnswersBy_eq_bind]
    simp only [prior, P, Q, H, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  have hsupport : (q, t) ∈ prior.support := by
    refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨q, hq, ?_⟩
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩
  rw [hLaw, conditionalSnd_bind_pair _ _ _ hsupport]
  exact norm_checkedVectorGivenRest_sq_answers G α C S j t q a b ht

end Cslib.PCP.AnchoredDependency
