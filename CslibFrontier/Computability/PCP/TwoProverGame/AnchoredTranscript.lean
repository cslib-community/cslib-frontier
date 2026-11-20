/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredConditioning
import CslibFrontier.Probability.PMF.Filter
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.Product.Resample

/-!
# The transcript with one noisy message omitted

For an unchecked coordinate, the rest of the transcript is sampled by first fixing that
coordinate's question pair and then sampling every other trial and the checked answers.
This is the conditional independence used in the proof of
[Bavarian, Vidick and Yuen, Lemma 4.6(3)][BavarianVidickYuen2022], arXiv:1509.07466v2,
pp. 14–15. The winning event depends only on the rest of the transcript, so the
independence survives conditioning on the checked wins.

## Main results

* `map_trial_restTranscriptLaw`: the remaining transcript uses only the selected question pair.
* `conditionalSnd_restTranscript_given_wins`: the same conditional law after checked wins.
-/

public section

open scoped unitInterval

namespace Cslib.PCP.AnchoredDependency

open Cslib.Probability.PMF
open ParallelRepetition (Revealed Shared)

variable {X Y A B ι κ : Type*} {n : ℕ}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "PairQ" => (Option X × Option Y)
local notation "Trial" => ((Option X ⊕ Option Y) × PairQ)
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ

variable (G : TwoProverGame X Y A B) (α : I) (C : Finset (Fin n))

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Info" => Revealed (Option X) (Option Y) C
local notation "Rest" => Shared (Option X) (Option Y) A B C
local notation "Transcript" => ((Info × (C → A × B)) × (Free → PairQ))

/-- Keep the checked questions and answers and the messages at all other unchecked trials. -/
def restTranscript (j : Free) (r : Transcript) : Rest j :=
  let ((t, v), _) := r
  Shared.ofRevealed j t v

/-- The checked wins are determined by the remaining transcript. -/
def winsOnRest (j : Free) : Set (Rest j) :=
  {r | ∀ i : C, (G.anchored α).accepts (r.questions i).1 (r.questions i).2
    (r.answers i).1 (r.answers i).2}

omit [Fintype X] [Fintype Y] [Fintype A] [Fintype B] in
theorem preimage_winsOnRest (j : Free) :
    restTranscript C j ⁻¹' winsOnRest G α C j = winsOnChecked (A := A) (B := B) G α C := by
  ext ⟨⟨t, v⟩, u⟩
  simp only [Set.mem_preimage, restTranscript, winsOnRest, winsOnChecked,
    Set.mem_ofPred_eq, Shared.ofRevealed.eq_1]

/-- Given the selected question pair, draw every other trial and form the remaining
transcript. The erased message slot can be filled with any value. -/
noncomputable def restKernel (S : RepeatedStrategy) (j : Free) (q : PairQ) : PMF (Rest j) :=
  (pi fun _ : C => (G.anchored α).questions).bind fun checked =>
    (pi fun _ : Free => law G.questions α).bind fun u =>
      (completeTranscript C S checked (Function.update u j (Sum.inl none, q))).map
        (restTranscript C j)

omit [Fintype X] [Fintype Y] in
private theorem map_rest_complete_update (S : RepeatedStrategy) (j : Free)
    (checked : C → PairQ) (u : Free → Trial) (m : Option X ⊕ Option Y) (q : PairQ) :
    (completeTranscript C S checked (Function.update u j (m, q))).map (restTranscript C j) =
      (completeTranscript C S checked (Function.update u j (Sum.inl none, q))).map
        (restTranscript C j) := by
  have hq : Prod.snd ∘ Function.update u j (m, q) =
      Prod.snd ∘ Function.update u j (Sum.inl none, q) := by
    funext i
    by_cases h : i = j <;> simp [h, Function.update_of_ne]
  simp only [completeTranscript, PMF.map_comp, Function.comp_def, restTranscript,
    Shared.ofRevealed.eq_1]
  have hcombine : (Revealed.mk checked (Prod.fst ∘ Function.update u j (m, q))).combine
      (Prod.snd ∘ Function.update u j (m, q)) =
      (Revealed.mk checked (Prod.fst ∘ Function.update u j (Sum.inl none, q))).combine
        (Prod.snd ∘ Function.update u j (Sum.inl none, q)) := by
    rw [hq]
    unfold Revealed.combine
    rfl
  simp only [Function.comp_def] at hcombine
  rw [hcombine]
  congr 1
  funext v
  congr 1
  funext i
  simp [Function.update_of_ne i.property]

/-- The joint law of the selected trial and remaining transcript samples the latter from
a kernel depending only on the selected question pair. -/
theorem map_trial_restTranscriptLaw (S : RepeatedStrategy) (j : Free) :
    (transcriptLaw G α C S).map (fun r => (freeTrials C r j, restTranscript C j r)) =
      (law G.questions α).bind fun trial =>
        (restKernel G α C S j trial.2).map (trial, ·) := by
  let p : Free → PMF Trial := fun _ => law G.questions α
  let checkedLaw := pi fun _ : C => (G.anchored α).questions
  let read (t : C → PairQ) (u : Free → Trial) := (completeTranscript C S t u).map
    (restTranscript C j)
  have hread (t : C → PairQ) (u : Free → Trial) :
      (completeTranscript C S t u).map
        (fun r => (freeTrials C r j, restTranscript C j r)) =
        (read t u).map (u j, ·) := by
    simp only [completeTranscript, read, PMF.map_comp, Function.comp_def, freeTrials]
  calc
    _ = checkedLaw.bind (fun t => (pi p).bind fun u => (read t u).map (u j, ·)) := by
      simp only [transcriptLaw_eq_complete, checkedLaw, PMF.map_bind, p, hread]
    _ = checkedLaw.bind (fun t => (p j).bind fun trial =>
        (pi (Function.update p j (PMF.pure trial))).bind fun u => (read t u).map (trial, ·)) := by
      congr 1 with t : 1
      exact (bind_pi_update p j fun trial u => (read t u).map (trial, ·)).symm
    _ = (p j).bind (fun trial => checkedLaw.bind fun t =>
        (pi (Function.update p j (PMF.pure trial))).bind fun u => (read t u).map (trial, ·)) :=
      PMF.bind_comm _ _ _
    _ = _ := by
      simp only [restKernel, PMF.map_bind]
      congr 1 with trial : 1
      congr 1 with t : 1
      rw [pi_update_pure, PMF.bind_map]
      congr 1 with u : 1
      rcases trial with ⟨m, q⟩
      simp only [Function.comp_def, read]
      rw [map_rest_complete_update C S j t u m q]

private theorem conditionalSnd_filter_forget {U V R : Type*} (prior : PMF U)
    (forget : U → V) (K : V → PMF R) (E : Set R)
    (hE : ∃ z ∈ Prod.snd ⁻¹' E, z ∈ (prior.bind fun x => (K (forget x)).map (x, ·)).support)
    (x : U) :
    let J := prior.bind fun y => (K (forget y)).map (y, ·)
    let F := J.filter (Prod.snd ⁻¹' E) hE
    x ∈ (F.map Prod.fst).support →
      conditionalSnd F x = conditionalSnd (F.map (Prod.map forget id)) (forget x) := by
  dsimp only
  let J := prior.bind fun y => (K (forget y)).map (y, ·)
  let drop : U × R → V × R := Prod.map forget id
  let J' := (prior.map forget).bind fun y => (K y).map (y, ·)
  let S₀ : Set (U × R) := Prod.snd ⁻¹' E
  let S₁ : Set (V × R) := Prod.snd ⁻¹' E
  have hJ : J.map drop = J' := by
    simp only [J, J', drop, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def,
      Prod.map_apply, id_eq]
  have hE' : ∃ z ∈ S₁, z ∈ J'.support := by
    obtain ⟨z, hz, hs⟩ := hE
    exact ⟨drop z, hz, hJ ▸ (PMF.mem_support_map_iff _ _ _).mpr ⟨z, hs, rfl⟩⟩
  let F := J.filter S₀ hE
  let F' := J'.filter S₁ hE'
  change x ∈ (F.map Prod.fst).support → conditionalSnd F x =
    conditionalSnd (F.map drop) (forget x)
  have hF : F.map drop = F' := by
    have hs : ∃ z ∈ S₁, z ∈ (J.map drop).support := hJ.symm ▸ hE'
    calc
      _ = (J.map drop).filter S₁ hs := (filter_map J drop S₁ hs hE).symm
      _ = _ := by unfold F'; congr
  intro hx
  rw [hF]
  have hp : (prior.map forget) (forget x) ≠ 0 := by
    obtain ⟨⟨y, r⟩, hyr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    have hJr : (y, r) ∈ J.support := by
      rw [PMF.support_filter] at hyr
      exact hyr.2
    have hmass := (PMF.mem_support_iff _ _).mp hJr
    dsimp only [J] at hmass
    rw [bind_map_prodMk_apply] at hmass
    exact ne_of_gt ((pos_iff_ne_zero.mpr (left_ne_zero_of_mul hmass)).trans_le
      (le_map_apply prior forget y))
  apply conditionalSnd_eq_of_scaled_slices F F' x (forget x)
    ((prior.map forget) (forget x)) (prior x) hx hp (PMF.apply_ne_top _ _)
  intro r
  have hmass : J'.toOuterMeasure S₁ = J.toOuterMeasure S₀ := by
    rw [← hJ, PMF.toOuterMeasure_map_apply]
    rfl
  dsimp only [F, F']
  rw [PMF.filter_apply, PMF.filter_apply, ← PMF.toOuterMeasure_apply,
    ← PMF.toOuterMeasure_apply, hmass]
  by_cases hr : r ∈ E
  · have hr₀ : (x, r) ∈ S₀ := hr
    have hr₁ : (forget x, r) ∈ S₁ := hr
    rw [Set.indicator_of_mem hr₀, Set.indicator_of_mem hr₁]
    dsimp only [J, J']
    rw [bind_map_prodMk_apply, bind_map_prodMk_apply]
    ac_rfl
  · have hr₀ : (x, r) ∉ S₀ := hr
    have hr₁ : (forget x, r) ∉ S₁ := hr
    rw [Set.indicator_of_notMem hr₀, Set.indicator_of_notMem hr₁, zero_mul, mul_zero, mul_zero]

/-- After conditioning on the checked wins, the remaining transcript given the selected pair
and its noisy message has the same law as when given the pair alone. -/
theorem conditionalSnd_restTranscript_given_wins (S : RepeatedStrategy) (j : Free)
    (hW : ∃ r ∈ winsOnChecked G α C, r ∈ (transcriptLaw G α C S).support) (trial : Trial) :
    let Q := (transcriptLaw G α C S).filter (winsOnChecked G α C) hW
    let J := Q.map fun r => (freeTrials C r j, restTranscript C j r)
    trial ∈ (J.map Prod.fst).support →
      conditionalSnd J trial =
        conditionalSnd (Q.map fun r => ((freeTrials C r j).2, restTranscript C j r)) trial.2 := by
  let P := transcriptLaw G α C S
  let E : Set (Trial × Rest j) := Prod.snd ⁻¹' winsOnRest G α C j
  let observe : Transcript → Trial × Rest j := fun r => (freeTrials C r j, restTranscript C j r)
  let K : PairQ → PMF (Rest j) := restKernel G α C S j
  have hpre : observe ⁻¹' E = winsOnChecked G α C := preimage_winsOnRest G α C j
  have hW' : ∃ r ∈ observe ⁻¹' E, r ∈ P.support := hpre.symm ▸ hW
  have hE : ∃ z ∈ E, z ∈ (P.map observe).support := by
    obtain ⟨r, hr, hs⟩ := hW'
    exact ⟨observe r, hr, (PMF.mem_support_map_iff _ _ _).mpr ⟨r, hs, rfl⟩⟩
  have hJ : P.map observe = (law G.questions α).bind (fun x => (K x.2).map (x, ·)) :=
    map_trial_restTranscriptLaw G α C S j
  have hE' : ∃ z ∈ E, z ∈ ((law G.questions α).bind
      (fun x => (K x.2).map (x, ·))).support := hJ ▸ hE
  have hF : (P.filter (winsOnChecked G α C) hW).map observe =
      ((law G.questions α).bind (fun x => (K x.2).map (x, ·))).filter E hE' := by
    calc
      _ = (P.filter (observe ⁻¹' E) hW').map observe := by congr
      _ = (P.map observe).filter E hE := (filter_map P observe E hE hW').symm
      _ = _ := by congr
  have hdrop : (P.filter (winsOnChecked G α C) hW).map
      (fun r => ((freeTrials C r j).2, restTranscript C j r)) =
        ((P.filter (winsOnChecked G α C) hW).map observe).map (Prod.map Prod.snd id) :=
    by simp only [PMF.map_comp, observe, Function.comp_def, Prod.map_apply, id_eq]
  dsimp only
  change trial ∈ (((P.filter (winsOnChecked G α C) hW).map observe).map Prod.fst).support → _
  rw [hdrop, hF]
  exact conditionalSnd_filter_forget (law G.questions α) Prod.snd K (winsOnRest G α C j) hE' trial

end Cslib.PCP.AnchoredDependency
