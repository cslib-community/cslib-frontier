/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredDependency
public import CslibFrontier.Computability.PCP.ParallelRepetition.CoordinateModel
import CslibFrontier.Probability.PMF.Filter
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.Product.Split

/-!
# Conditioning the repeated anchored experiment on wins

A transcript records the questions and answers in a checked set of coordinates and the noisy
messages on the other coordinates. The question pairs on the unchecked coordinates are
drawn independently given the messages, before sampling the strategy's answers. The shared
coordinate record from Holenstein's argument stores the noisy messages in its `halves` field.

The first two assertions of
[Bavarian, Vidick and Yuen, Lemma 4.6][BavarianVidickYuen2022] (arXiv:1509.07466v2, §4.3)
follow from the library's Raz and Holenstein bounds. We state the first in squared-sum form,
as in the source proof, and the second as a sum over unchecked coordinates. The bound uses
natural logarithms and the statistical distance of PMFs, so the Pinsker factor is `1 / 2`.
-/

public section

open scoped unitInterval Cslib.Probability.PMF

namespace Cslib.PCP.AnchoredDependency

open Cslib.Probability.PMF
open ParallelRepetition (Revealed)

variable {X Y A B ι κ : Type*} {n : ℕ}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "PairQ" => (Option X × Option Y)
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ

variable (G : TwoProverGame X Y A B) (α : I) (C : Finset (Fin n))

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Info" => Revealed (Option X) (Option Y) C
local notation "CheckedAnswers" => (C → A × B)
local notation "Transcript" => ((Info × CheckedAnswers) × (Free → PairQ))

/-- Draw the checked questions and the free-coordinate messages independently. -/
@[expose] noncomputable def infoLaw : PMF Info :=
  (pi fun _ : C => (G.anchored α).questions).bind fun checked =>
    (pi fun _ : Free => (law G.questions α).map Prod.fst).map fun messages =>
      ⟨checked, messages⟩

/-- The prior question-pair law at an unchecked coordinate given the revealed information. -/
@[expose] noncomputable def pairGiven (j : Free) (t : Info) : PMF PairQ :=
  conditionalSnd (law G.questions α) (t.halves j)

/-- The law of the checked answers at a full tuple of questions. -/
@[expose] noncomputable def checkedAnswerLaw (S : RepeatedStrategy) (q : Fin n → PairQ) :
    PMF CheckedAnswers :=
  (S.answers (Prod.fst ∘ q) (Prod.snd ∘ q)).map fun (a, b) i => (a i, b i)

/-- Sample the unchecked pairs given the revealed information and retain the strategy's
answers on the checked coordinates. -/
noncomputable def sideKernel (S : RepeatedStrategy) (t : Info) :
    PMF ((Free → PairQ) × CheckedAnswers) :=
  (pi fun j => pairGiven G α C j t).bind fun u =>
    (checkedAnswerLaw C S (t.combine u)).map (u, ·)

/-- Before looking at the answers, the unchecked pairs are independent given the messages. -/
theorem map_fst_sideKernel (S : RepeatedStrategy) (t : Info) :
    (sideKernel G α C S t).map Prod.fst = pi fun j => pairGiven G α C j t := by
  have h (u : Free → PairQ) :
      (checkedAnswerLaw C S (t.combine u)).map (fun _ => u) = PMF.pure u :=
    PMF.map_const _ _
  simp only [sideKernel, PMF.map_bind, PMF.map_comp, Function.comp_def, h, PMF.bind_pure]

/-- The joint law of the transcript and the unchecked questions. -/
noncomputable def transcriptLaw (S : RepeatedStrategy) : PMF Transcript :=
  sideJoint (infoLaw G α C) (sideKernel G α C S)

/-- The verifier accepts every coordinate in the checked set. -/
@[expose] def winsOnChecked : Set Transcript :=
  {r | let ((t, a), _) := r
       ∀ i : C, (G.anchored α).accepts (t.questions i).1 (t.questions i).2 (a i).1 (a i).2}

/-- Discard the checked data, keeping the message and pair at every unchecked coordinate. -/
@[expose] def freeTrials (r : Transcript) : Free → (Option X ⊕ Option Y) × PairQ :=
  let ((t, _), u) := r
  fun i => (t.halves i, u i)

/-- Attach the checked answers after sampling the checked questions and the unchecked trials. -/
@[expose] noncomputable def completeTranscript (S : RepeatedStrategy) (checked : C → PairQ)
    (u : Free → (Option X ⊕ Option Y) × PairQ) : PMF Transcript :=
  let t : Info := ⟨checked, Prod.fst ∘ u⟩
  (checkedAnswerLaw C S (t.combine (Prod.snd ∘ u))).map
    fun v => ((t, v), Prod.snd ∘ u)

/-- The transcript can equally be sampled by independent trials followed by the strategy's
checked answers. -/
theorem transcriptLaw_eq_complete (S : RepeatedStrategy) :
    transcriptLaw G α C S =
      (pi fun _ : C => (G.anchored α).questions).bind fun checked =>
        (pi fun _ : Free => law G.questions α).bind (completeTranscript C S checked) := by
  simp only [transcriptLaw, sideJoint, infoLaw, sideKernel, PMF.bind_bind, PMF.bind_map,
    PMF.map_bind, PMF.map_comp, Function.comp_def, pairGiven]
  congr 1 with checked : 1
  have h := congrArg (fun P : PMF ((Free → Option X ⊕ Option Y) × (Free → PairQ)) =>
    P.bind fun (m, u) =>
      (checkedAnswerLaw C S ((⟨checked, m⟩ : Info).combine u)).map
        fun v => (((⟨checked, m⟩ : Info), v), u))
    (pi_joint_eq_bind_conditionalSnd (fun _ : Free => law G.questions α))
  unfold completeTranscript
  simpa only [PMF.bind_map, PMF.bind_bind, Function.comp_def] using h.symm

/-- Before conditioning on wins, the checked questions and all unchecked trials are
independent, with their original laws. -/
theorem map_checked_freeTrials_transcriptLaw (S : RepeatedStrategy) :
    (transcriptLaw G α C S).map (fun r =>
      let ((t, _), _) := r
      (t.questions, freeTrials C r)) =
      (pi fun _ : C => (G.anchored α).questions).bind fun checked =>
        (pi fun _ : Free => law G.questions α).map (checked, ·) := by
  rw [transcriptLaw_eq_complete]
  simp only [PMF.map_bind, completeTranscript, PMF.map_comp, Function.comp_def, freeTrials]
  congr 1 with checked : 1
  rw [← PMF.bind_pure_comp]
  congr 1 with u : 1
  exact PMF.map_const _ _

/-- The unchecked message-and-question triples have the independent prior law. -/
theorem map_freeTrials_transcriptLaw (S : RepeatedStrategy) :
    (transcriptLaw G α C S).map (freeTrials C) = pi fun _ : Free => law G.questions α := by
  have h := congrArg (PMF.map Prod.snd) (map_checked_freeTrials_transcriptLaw G α C S)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const] at h
  change (transcriptLaw G α C S).map (freeTrials C) =
    (pi fun _ : Free => law G.questions α).map id at h
  simpa only [PMF.map_id] using h

/-- Recombining the two sets of question coordinates recovers the independent
question-pair sequence of the repeated verifier. -/
theorem map_questionPairs_transcriptLaw (S : RepeatedStrategy) :
    (transcriptLaw G α C S).map (fun r =>
      let ((t, _), u) := r
      t.combine u) = pi fun _ : Fin n => (G.anchored α).questions := by
  classical
  let split := Equiv.piEquivPiSubtypeProd (· ∈ C) fun _ => PairQ
  let hq (z : (C → PairQ) × (Free → (Option X ⊕ Option Y) × PairQ)) : Fin n → PairQ :=
    split.symm (z.1, Prod.snd ∘ z.2)
  have h := congrArg (PMF.map hq) (map_checked_freeTrials_transcriptLaw G α C S)
  have hfree : ((pi fun _ : Free => law G.questions α).map (fun u => Prod.snd ∘ u)) =
      (pi fun _ : Free => (G.anchored α).questions) := by
    calc
      _ = pi (fun _ : Free => (law G.questions α).map Prod.snd) :=
        (pi_map (fun _ : Free => law G.questions α) (fun _ => Prod.snd)).symm
      _ = _ := by simp only [map_snd_law, TwoProverGame.anchored_questions]
  have hs := pi_map_piEquivPiSubtypeProd (· ∈ C)
    (fun _ : Fin n => (G.anchored α).questions)
  calc
    _ = ((pi fun _ : C => (G.anchored α).questions).bind fun checked =>
        (pi fun _ : Free => law G.questions α).map (checked, ·)).map hq := by
      rw [PMF.map_comp] at h
      exact h
    _ = ((pi fun _ : C => (G.anchored α).questions).bind fun checked =>
        (pi fun _ : Free => (G.anchored α).questions).map (checked, ·)).map split.symm := by
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, hq]
      congr 1 with checked : 1
      rw [← hfree, PMF.map_comp]
      rfl
    _ = ((pi fun _ : Fin n => (G.anchored α).questions).map split).map split.symm := by
      convert congrArg (PMF.map split.symm) hs.symm using 4
    _ = _ := by rw [PMF.map_comp, Equiv.symm_comp_self, PMF.map_id]

/-- **BVY Lemma 4.6(2)** in summed form. Conditioned on winning the checked coordinates, the
questions at an unchecked coordinate are close, on average, to a draw from the prior
conditional law given its message, with the transcript held fixed. -/
theorem sum_dist_questions_given_wins_le (S : RepeatedStrategy)
    (hW : ∃ r ∈ winsOnChecked G α C, r ∈ (transcriptLaw G α C S).support) :
    let P := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let Q := P.filter W hW
    ∑ j : Free, dist (Q.map fun r => (r.1, r.2 j))
        ((Q.map Prod.fst).bind fun (t, v) => (pairGiven G α C j t).map ((t, v), ·)) ≤
      Real.sqrt (Fintype.card Free * Real.log (Fintype.card CheckedAnswers /
        (P.toOuterMeasure W).toReal) / 2) := by
  exact sum_dist_filter_sideJoint_le (infoLaw G α C) (pairGiven G α C)
    (sideKernel G α C S) (map_fst_sideKernel G α C S) _ hW

/-- **BVY Lemma 4.6(1)** in the squared-sum form used in its proof. -/
theorem sum_sq_dist_freeTrials_given_wins_le (S : RepeatedStrategy)
    (hW : ∃ r ∈ winsOnChecked G α C, r ∈ (transcriptLaw G α C S).support) :
    let P := transcriptLaw G α C S
    let W := winsOnChecked G α C
    ∑ j : Free, dist ((P.filter W hW).map fun r => freeTrials C r j) (law G.questions α) ^ 2 ≤
      Real.log (1 / (P.toOuterMeasure W).toReal) / 2 := by
  intro P W
  let F : Transcript → (Free → (Option X ⊕ Option Y) × PairQ) ×
      ((C → PairQ) × CheckedAnswers) := fun r =>
    let ((t, a), _) := r
    (freeTrials C r, t.questions, a)
  let event : Set ((Free → (Option X ⊕ Option Y) × PairQ) ×
      ((C → PairQ) × CheckedAnswers)) := {r |
    let (_, qs, answers) := r
    ∀ i : C, (G.anchored α).accepts (qs i).1 (qs i).2 (answers i).1 (answers i).2}
  have hpre : F ⁻¹' event = W := rfl
  have he : ∃ x ∈ event, x ∈ (P.map F).support := by
    obtain ⟨x, hx, hxp⟩ := hW
    refine ⟨F x, hx, ?_⟩
    rw [PMF.mem_support_map_iff]
    exact ⟨x, hxp, rfl⟩
  have hprior : (P.map F).map Prod.fst = pi fun _ : Free => law G.questions α := by
    rw [PMF.map_comp]
    exact map_freeTrials_transcriptLaw G α C S
  have h := sum_sq_dist_map_filter_le (fun _ : Free => law G.questions α)
    (P.map F) hprior event he
  have hfilter : (P.map F).filter event he = (P.filter W hW).map F := by
    subst W
    exact filter_map P F event he hW
  rw [hfilter, PMF.toOuterMeasure_map_apply, hpre] at h
  simpa only [PMF.map_comp, Function.comp_def, F] using h

end Cslib.PCP.AnchoredDependency
