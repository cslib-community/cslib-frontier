/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredConditionalStates

/-!
# Checked-answer states with a selected noisy message

At a fixed message and selected Bob question, Alice's selected question still has its prior
law given the message. Averaging her checked effects over that last draw yields the branch
weight in the original transcript with just those observations. For a left message this is
the noisy-anchor case of [Bavarian, Vidick and Yuen, Proposition 4.9][BavarianVidickYuen2022],
equation (22).

## Main definitions

* `checkedVectorGivenBob`: average the hidden Alice question and keep Alice's system first.
* `checkedVectorGivenAlice`: average the hidden Bob question and keep Bob's system first.

## Main results

* `norm_checkedVectorGivenBob_sq`: the noisy branch weight agrees with the original conditional
  answer probability.
* `norm_checkedVectorGivenBob_sq_inl`: the weight splits into the anchor and ordinary branches.
-/

public section

open scoped unitInterval

namespace Cslib.PCP.AnchoredDependency

open Cslib.Probability.PMF
open ParallelRepetition (Revealed)

variable {X Y A B ι κ : Type*} {n : ℕ}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "Message" => (Option X ⊕ Option Y)
local notation "PairQ" => (Option X × Option Y)
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ

variable (G : TwoProverGame X Y A B) (α : I) (C : Finset (Fin n))

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Saved" => RestQuestions (Option X) (Option Y) C

omit [Fintype A] [Fintype B] in
private theorem map_questionsGivenRest_congr {T : Type*} [Finite T] (f : PairQ → T)
    (j : Free) (t : Saved j) (q q' : PairQ) (h : f q = f q') :
    (questionsGivenRest G α C j t q).map (fun u => f ∘ u) =
      (questionsGivenRest G α C j t q').map (fun u => f ∘ u) := by
  simp only [questionsGivenRest, map_pi_update_combine, h]

omit [Fintype A] [Fintype B] in
/-- Keeping Alice's selected question fixed keeps her entire conditional question law fixed. -/
theorem aliceQuestionsGivenRest_congr (j : Free) (t : Saved j) (q q' : PairQ)
    (h : q.1 = q'.1) :
    aliceQuestionsGivenRest G α C j t q = aliceQuestionsGivenRest G α C j t q' :=
  map_questionsGivenRest_congr G α C Prod.fst j t q q' h

omit [Fintype A] [Fintype B] in
/-- Keeping Bob's selected question fixed keeps his entire conditional question law fixed. -/
theorem bobQuestionsGivenRest_congr (j : Free) (t : Saved j) (q q' : PairQ)
    (h : q.2 = q'.2) :
    bobQuestionsGivenRest G α C j t q = bobQuestionsGivenRest G α C j t q' :=
  map_questionsGivenRest_congr G α C Prod.snd j t q q' h

/-- The observation consists of the selected message and Bob's selected question. -/
noncomputable def observedCheckedAnswersByBob (S : RepeatedStrategy) (j : Free) :
    PMF (((Message × Option Y) × Saved j) × (C → A × B)) :=
  observedCheckedAnswersBy G α C S j (fun (m, _, y) => (m, y))

/-- Conditional answer law with the selected message and Bob's question fixed. -/
theorem conditionalSnd_observedCheckedAnswersByBob (S : RepeatedStrategy) (j : Free) (t : Saved j)
    (m : Message) (y : Option Y) (ht : t ∈ (restQuestionsLaw G α C j).support)
    (hm : m ∈ ((law G.questions α).map Prod.fst).support)
    (hy : y ∈ (bobGivenMessage G.questions α m).support) :
    conditionalSnd (observedCheckedAnswersByBob G α C S j) ((m, y), t) =
      (aliceGivenMessage G.questions α m).bind fun x => answersGivenRest G α C S j t (x, y) := by
  let μ := (law G.questions α).map Prod.fst
  let L := aliceGivenMessage G.questions α
  let R := bobGivenMessage G.questions α
  let Q := restQuestionsLaw G α C j
  let prior := μ.bind fun m' => (R m').bind fun y' => Q.map ((m', y'), ·)
  let kernel := fun ((m', y'), t') => (L m').bind fun x => answersGivenRest G α C S j t' (x, y')
  have hlaw := congrArg (fun P => P.bind fun (m', x, y') => Q.bind fun t' =>
    (answersGivenRest G α C S j t' (x, y')).map (((m', y'), t'), ·))
    (law_eq_bind_messages G.questions α)
  have hobs : observedCheckedAnswersByBob G α C S j =
      prior.bind fun z => (kernel z).map (z, ·) := by
    rw [observedCheckedAnswersByBob, observedCheckedAnswersBy_eq_bind]
    refine hlaw.trans ?_
    simp only [prior, kernel, μ, L, R, PMF.bind_bind, PMF.bind_map, PMF.map_bind, Function.comp_def]
    congr 1 with trial : 1
    rw [PMF.bind_comm (aliceGivenMessage G.questions α trial.1)
      (bobGivenMessage G.questions α trial.1)]
    congr 1 with y' : 1
    exact PMF.bind_comm _ _ _
  have hs : ((m, y), t) ∈ prior.support := by
    refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨m, hm, ?_⟩
    refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨y, hy, ?_⟩
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩
  rw [hobs, conditionalSnd_bind_pair _ _ _ hs]

omit [Fintype A] [Fintype B] in
/-- A left-tagged message gives a coin mixture of the anchor and selected Alice question laws. -/
theorem bind_aliceQuestionsGivenRest_inl (j : Free) (t : Saved j) (x : Option X) (y : Option Y) :
    ((aliceGivenMessage G.questions α (.inl x)).bind fun x' =>
      aliceQuestionsGivenRest G α C j t (x', y)) =
      (coin (noise α)).bind fun erase =>
        if erase then aliceQuestionsGivenRest G α C j t (none, none)
        else aliceQuestionsGivenRest G α C j t (x, none) := by
  simp only [aliceGivenMessage, noisyQuestion, PMF.bind_map, Function.comp_def]
  congr 1 with erase : 1
  cases erase
  · exact aliceQuestionsGivenRest_congr G α C j t (x, y) (x, none) rfl
  · exact aliceQuestionsGivenRest_congr G α C j t (none, y) (none, none) rfl

/-- The checked-answer branch formed by averaging the hidden selected Alice question. -/
noncomputable def checkedVectorGivenBob (S : RepeatedStrategy) (j : Free) (t : Saved j)
    (m : Message) (y : Option Y) (a : C → A) (b : C → B) : EuclideanSpace ℂ (ι × κ) :=
  S.averagedCheckedVector C
    ((aliceGivenMessage G.questions α m).bind fun x => aliceQuestionsGivenRest G α C j t (x, y))
    (bobQuestionsGivenRest G α C j t (none, y)) a b

/-- The noisy checked branch uses the selected-message mixture for Alice and fixes
Bob's selected question. -/
theorem checkedVectorGivenBob_eq (S : RepeatedStrategy) (j : Free) (t : Saved j)
    (m : Message) (y : Option Y) (a : C → A) (b : C → B) :
    checkedVectorGivenBob G α C S j t m y a b =
      S.averagedCheckedVector C
        ((aliceGivenMessage G.questions α m).bind fun x => aliceQuestionsGivenRest G α C j t (x, y))
        (bobQuestionsGivenRest G α C j t (none, y)) a b := by
  unfold checkedVectorGivenBob
  rfl

/-- A fixed left anchor message makes the noisy Alice draw the anchor with probability one. -/
theorem checkedVectorGivenBob_inl_none (S : RepeatedStrategy) (j : Free) (t : Saved j)
    (y : Option Y) (a : C → A) (b : C → B) :
    checkedVectorGivenBob G α C S j t (.inl none) y a b =
      checkedVectorGivenRest G α C S j t (none, y) a b := by
  rw [checkedVectorGivenBob_eq, bind_aliceQuestionsGivenRest_inl, checkedVectorGivenRest]
  simp only [ite_self, PMF.bind_const,
    aliceQuestionsGivenRest_congr G α C j t (none, y) (none, none) rfl]

/-- The noisy branch at a selected Alice question, with Bob's system in the first
tensor factor so that the retained state is its right partial trace. -/
noncomputable def checkedVectorGivenAlice (S : RepeatedStrategy) (j : Free)
    (t : Revealed (Option X) (Option Y) C) (x : Option X) (a : C → A) (b : C → B) :
    EuclideanSpace ℂ (κ × ι) :=
  let ts := swapInfo C t
  checkedVectorGivenBob G.swap α C S.swap j (omitMessage C j ts) (ts.halves j) x b a

/-- The noisy branch for Alice is the Bob-question construction after exchanging players. -/
theorem checkedVectorGivenAlice_eq (S : RepeatedStrategy) (j : Free)
    (t : Revealed (Option X) (Option Y) C) (x : Option X) (a : C → A) (b : C → B) :
    let ts := swapInfo C t
    checkedVectorGivenAlice G α C S j t x a b =
      checkedVectorGivenBob G.swap α C S.swap j (omitMessage C j ts) (ts.halves j) x b a := by
  unfold checkedVectorGivenAlice
  rfl

/-- At the fixed right anchor message, Alice's noisy branch is the ordinary branch
with Bob anchored, expressed in the exchanged tensor order. -/
theorem checkedVectorGivenAlice_inr_none (S : RepeatedStrategy) (j : Free)
    (t : Revealed (Option X) (Option Y) C) (x : Option X) (a : C → A) (b : C → B)
    (hm : t.halves j = .inr none) :
    (checkedVectorGivenAlice G α C S j t x a b).ofLp =
      (checkedVectorGivenRest G α C S j (omitMessage C j t) (x, none) a b).ofLp ∘
        Equiv.prodComm κ ι := by
  have hm' : (swapInfo C t).halves j = .inl none := by
    change Sum.swap (t.halves j) = _
    rw [hm]
    rfl
  rw [checkedVectorGivenAlice_eq]
  dsimp only
  rw [hm', checkedVectorGivenBob_inl_none]
  unfold checkedVectorGivenRest aliceQuestionsGivenRest bobQuestionsGivenRest
  rw [show (none, x) = Prod.swap (x, (none : Option Y)) from rfl, questionsGivenRest_swap]
  simp only [PMF.map_comp, Function.comp_def]
  exact QuantumStrategy.averagedCheckedVector_swap S C _ _ a b

/-- The branch has the correct checked-answer probability in the original transcript
when Alice's question is hidden and the selected message and Bob's question are fixed. -/
theorem norm_checkedVectorGivenBob_sq (S : RepeatedStrategy) (j : Free) (t : Saved j)
    (m : Message) (y : Option Y) (a : C → A) (b : C → B)
    (ht : t ∈ (restQuestionsLaw G α C j).support)
    (hm : m ∈ ((law G.questions α).map Prod.fst).support)
    (hy : y ∈ (bobGivenMessage G.questions α m).support) :
    ‖checkedVectorGivenBob G α C S j t m y a b‖ ^ 2 =
      (conditionalSnd (observedCheckedAnswersByBob G α C S j) ((m, y), t)
        (fun i => (a i, b i))).toReal := by
  rw [conditionalSnd_observedCheckedAnswersByBob G α C S j t m y ht hm hy,
    checkedVectorGivenBob, QuantumStrategy.norm_averagedCheckedVector_sq, PMF.bind_bind,
    bind_apply_toReal, bind_apply_toReal]
  apply Finset.sum_congr rfl
  intro x _
  rw [← bobQuestionsGivenRest_congr G α C j t (x, y) (none, y) rfl,
    ← QuantumStrategy.norm_averagedCheckedVector_sq]
  exact congrArg ((aliceGivenMessage G.questions α m x).toReal * ·)
    (norm_checkedVectorGivenRest_sq_answers G α C S j t (x, y) a b ht)


/-- For a selected left message, the noisy branch weight interpolates between the
anchor and the original question at the sampler's exact erase rate. -/
theorem norm_checkedVectorGivenBob_sq_inl (S : RepeatedStrategy) (j : Free) (t : Saved j)
    (x : Option X) (y : Option Y) (a : C → A) (b : C → B) :
    ‖checkedVectorGivenBob G α C S j t (.inl x) y a b‖ ^ 2 =
      (noise α : ℝ) * ‖checkedVectorGivenRest G α C S j t (none, y) a b‖ ^ 2 +
        (1 - (noise α : ℝ)) * ‖checkedVectorGivenRest G α C S j t (x, y) a b‖ ^ 2 := by
  rw [checkedVectorGivenBob_eq, bind_aliceQuestionsGivenRest_inl,
    QuantumStrategy.norm_averagedCheckedVector_sq_coin, checkedVectorGivenRest,
    checkedVectorGivenRest, aliceQuestionsGivenRest_congr G α C j t (none, y) (none, none) rfl,
    aliceQuestionsGivenRest_congr G α C j t (x, y) (x, none) rfl,
    bobQuestionsGivenRest_congr G α C j t (x, y) (none, y) rfl]

end Cslib.PCP.AnchoredDependency
