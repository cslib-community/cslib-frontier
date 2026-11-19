/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredTranscript
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.StatisticalDistance
import Mathlib.Algebra.Order.Chebyshev

/-!
# Comparing anchored transcripts after conditioning on wins

The comparisons of [Bavarian, Vidick and Yuen, Lemma 4.6(3–4)][BavarianVidickYuen2022]
follow from the exact omitted-message identity and the probability of seeing two anchors
under every possible noisy message. Both comparisons first use the same prior trial distribution
and differ only in how they generate the remaining transcript. The lower bound on the two-anchor
slice then transfers the joint distance estimate to that conditional transcript.

## Main results

* `sum_dist_anchoredRest_given_wins`: summed distance bounds for replacing the remaining
  transcript by its law when both questions are anchors.
* `sum_dist_trial_rest_independent_given_wins`: replace the selected trial by its prior law
  independently of the winning remaining transcript.
-/

public section

open scoped unitInterval Cslib.Probability.PMF ENNReal

namespace Cslib.PCP.AnchoredDependency

open Cslib.Probability.PMF
open ParallelRepetition (Revealed Shared)

section Comparison

variable {M U R : Type*}

/-- Keep a message and the rest of the transcript and redraw the question pair given the message. -/
private noncomputable def redraw (p : PMF (M × R)) (k : M → PMF U) : PMF ((M × U) × R) :=
  p.bind fun (m, r) => (k m).map fun u => ((m, u), r)

private theorem redraw_eq (p : PMF (M × R)) (k : M → PMF U) :
    redraw p k = ((p.map Prod.fst).bind (fun m => (k m).map (m, ·))).bind
      fun z => (conditionalSnd p z.1).map (z, ·) := by
  conv_lhs => rw [← bind_conditionalSnd p]
  simp only [redraw, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  congr 1 with m : 1
  exact PMF.bind_comm _ _ _

variable [Fintype M] [Fintype U] [Fintype R]

/-- Use the same prior trial marginal on both sides of the comparison. -/
private theorem dist_prior_completions_le (prior : PMF (M × U)) (J : PMF ((M × U) × R))
    (K : U → PMF R)
    (hK : ∀ z ∈ (J.map Prod.fst).support, conditionalSnd J z = K z.2) :
    let P := J.map (Prod.map Prod.fst id)
    let L := conditionalSnd P
    dist (prior.bind fun z => (K z.2).map (z, ·))
      (prior.bind fun z => (L z.1).map (z, ·)) ≤
        2 * dist (J.map Prod.fst) prior + dist J (redraw P (conditionalSnd prior)) := by
  intro P L
  let left (z : M × U) := (K z.2).map (z, ·)
  let right (z : M × U) := (L z.1).map (z, ·)
  let priK := prior.bind left
  let priL := prior.bind right
  let mid := redraw P (conditionalSnd prior)
  have hJ : (J.map Prod.fst).bind left = J := by
    conv_rhs => rw [← bind_conditionalSnd J]
    apply bind_congr_on_support
    intro z hz
    simp only [left, hK z hz]
  have h₁ : dist priK J ≤ dist (J.map Prod.fst) prior := by
    have h := dist_bind_le prior (J.map Prod.fst) left
    rwa [hJ, dist_comm prior (J.map Prod.fst)] at h
  have hm : P.map Prod.fst = (J.map Prod.fst).map Prod.fst := by
    simp only [P, PMF.map_comp, Function.comp_def]
    rfl
  have h₂ : dist mid priL ≤ dist (J.map Prod.fst) prior := by
    dsimp only [mid, priL]
    rw [redraw_eq]
    apply (dist_bind_le _ _ right).trans
    nth_rewrite 2 [← bind_conditionalSnd prior]
    exact (dist_bind_le _ _ _).trans (by rw [hm]; exact dist_map_le _ _ Prod.fst)
  change dist priK priL ≤ _
  linarith [dist_triangle priK J priL, dist_triangle J mid priL]

/-- Retain one question-pair slice of the average conditional distance. -/
private theorem mass_mul_dist_slice_le (prior : PMF (M × U)) (K : U → PMF R) (L : M → PMF R)
    (u₀ : U) (w : ℝ) (h : ∀ m, w * ((prior.map Prod.fst) m).toReal ≤ (prior (m, u₀)).toReal) :
    w * dist (((prior.map Prod.fst).bind fun m => (K u₀).map (m, ·)))
        (((prior.map Prod.fst).bind fun m => (L m).map (m, ·))) ≤
      dist (prior.bind fun z => (K z.2).map (z, ·))
        (prior.bind fun z => (L z.1).map (z, ·)) := by
  classical
  rw [dist_bind_pair, dist_bind_pair, Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [← mul_assoc]
  exact (mul_le_mul_of_nonneg_right (h m) dist_nonneg).trans
    (Finset.single_le_sum (f := fun u => (prior (m, u)).toReal * dist (K u) (L m))
      (fun _ _ => mul_nonneg ENNReal.toReal_nonneg dist_nonneg) (Finset.mem_univ u₀))

end Comparison

variable {X Y A B ι κ : Type*} {n : ℕ}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "Message" => (Option X ⊕ Option Y)
local notation "PairQ" => (Option X × Option Y)
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ

variable (G : TwoProverGame X Y A B) (α : I) (C : Finset (Fin n))

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Rest" => Shared (Option X) (Option Y) A B C
local notation "Transcript" => ((Revealed (Option X) (Option Y) C × (C → A × B)) × (Free → PairQ))

/-- The law of the remaining transcript conditioned on the selected question pair. -/
noncomputable def restGivenPair (Q : PMF Transcript) (j : Free) (q : PairQ) : PMF (Rest j) :=
  conditionalSnd (Q.map fun r => ((freeTrials C r j).2, restTranscript C j r)) q

/-- The joint law of the selected message and the remaining transcript. -/
noncomputable def messageAndRest (Q : PMF Transcript) (j : Free) : PMF (Message × Rest j) :=
  Q.map fun r => ((freeTrials C r j).1, restTranscript C j r)

private theorem dist_prior_completions_given_wins (S : RepeatedStrategy) (j : Free)
    (hW : ∃ r ∈ winsOnChecked G α C, r ∈ (transcriptLaw G α C S).support) :
    let Q := (transcriptLaw G α C S).filter (winsOnChecked G α C) hW
    let P := law G.questions α
    let L := conditionalSnd (messageAndRest C Q j)
    let K := restGivenPair C Q j
    dist (P.bind fun z => (K z.2).map (z, ·)) (P.bind fun z => (L z.1).map (z, ·)) ≤
      2 * dist (Q.map fun r => freeTrials C r j) P +
        dist (Q.map fun r => (r.1, r.2 j))
          ((Q.map Prod.fst).bind fun (t, v) => (pairGiven G α C j t).map ((t, v), ·)) := by
  intro Q P L K
  let J := Q.map fun r => (freeTrials C r j, restTranscript C j r)
  have htrial : J.map Prod.fst = Q.map (fun r => freeTrials C r j) := PMF.map_comp _ _ _
  have hmessage : J.map (Prod.map Prod.fst id) = messageAndRest C Q j := by
    rw [PMF.map_comp]
    rfl
  have hk (z) (hz : z ∈ (J.map Prod.fst).support) : conditionalSnd J z = K z.2 :=
    conditionalSnd_restTranscript_given_wins G α C S j hW z hz
  have h := dist_prior_completions_le P J K hk
  dsimp only at h
  rw [hmessage, htrial] at h
  refine h.trans (add_le_add_right ?_ _)
  let read : (Revealed (Option X) (Option Y) C × (C → A × B)) × PairQ → _ :=
    fun ((t, v), q) => ((t.halves j, q), Shared.ofRevealed j t v)
  have hobs : J = (Q.map fun r => (r.1, r.2 j)).map read := by
    dsimp only [J]
    rw [PMF.map_comp]
    rfl
  have hredraw : redraw (messageAndRest C Q j) (conditionalSnd P) =
      ((Q.map Prod.fst).bind fun (t, v) => (pairGiven G α C j t).map ((t, v), ·)).map read := by
    simp only [redraw, messageAndRest, P, PMF.bind_map, PMF.map_bind, PMF.map_comp,
      Function.comp_def]
    congr 1
  rw [hobs, hredraw]
  exact dist_map_le _ _ read

omit [Fintype X] [Fintype Y] [Fintype A] [Fintype B] in
private theorem anchor_mass (m : Message) :
    ((α : ℝ) ^ 2 / 2) * (((law G.questions α).map Prod.fst) m).toReal ≤
      ((law G.questions α) (m, none, none)).toReal := by
  have h := ENNReal.toReal_mono (PMF.apply_ne_top _ _) (law_bothAnchors_le G.questions α m)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (noise α).2.1, ENNReal.toReal_ofReal α.2.1] at h
  rw [coe_noise] at h
  convert h using 1; ring

/-- The law of the selected message and the remaining transcript, keeping the message marginal
and generating the rest from the two-anchor conditional law. -/
noncomputable def messageAndAnchoredRest (Q : PMF Transcript) (j : Free) : PMF (Message × Rest j) :=
  ((messageAndRest C Q j).map Prod.fst).bind fun m =>
    (restGivenPair C Q j (none, none)).map (m, ·)

/-- The prior selected questions followed by the transcript law conditional on those questions. -/
noncomputable def questionsAndRest (Q : PMF Transcript) (j : Free) : PMF (PairQ × Rest j) :=
  ((law G.questions α).map Prod.snd).bind fun q => (restGivenPair C Q j q).map (q, ·)

/-- The prior selected questions independently of the two-anchor conditional transcript. -/
noncomputable def questionsAndAnchoredRest (Q : PMF Transcript) (j : Free) : PMF (PairQ × Rest j) :=
  ((law G.questions α).map Prod.snd).bind fun q =>
    (restGivenPair C Q j (none, none)).map (q, ·)

private theorem both_anchor_comparisons (S : RepeatedStrategy) (j : Free)
    (hW : ∃ r ∈ winsOnChecked G α C, r ∈ (transcriptLaw G α C S).support) :
    let Q := (transcriptLaw G α C S).filter (winsOnChecked G α C) hW
    let P := law G.questions α
    let w := (α : ℝ) ^ 2 / 2
    let d := dist (Q.map fun r => freeTrials C r j) P
    let e := 2 * d + dist (Q.map fun r => (r.1, r.2 j))
      ((Q.map Prod.fst).bind fun (t, v) => (pairGiven G α C j t).map ((t, v), ·))
    w * dist (messageAndAnchoredRest C Q j) (messageAndRest C Q j) ≤ 2 * w * d + e ∧
    w * dist (questionsAndAnchoredRest G α C Q j) (questionsAndRest G α C Q j) ≤ (1 + w) * e := by
  intro Q P w d e
  let M₀ := P.map Prod.fst
  let L := conditionalSnd (messageAndRest C Q j)
  let K := restGivenPair C Q j
  let K₀ := K (none, none)
  let paired (H : Message × PairQ → PMF (Rest j)) :=
    P.bind fun z => (H z).map (z, ·)
  let a := fun m : Message => K₀.map (m, ·)
  let b := fun m : Message => (L m).map (m, ·)
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have he : dist (paired (K ∘ Prod.snd)) (paired (L ∘ Prod.fst)) ≤ e :=
    dist_prior_completions_given_wins G α C S j hW
  have hslice : w * dist (M₀.bind a) (M₀.bind b) ≤ e :=
    (mass_mul_dist_slice_le P K L (none, none) w (anchor_mass G α)).trans he
  constructor
  · let M₁ := (messageAndRest C Q j).map Prod.fst
    have hm : dist M₁ M₀ ≤ d := by
      change dist ((messageAndRest C Q j).map Prod.fst) M₀ ≤ d
      rw [messageAndRest, PMF.map_comp]
      have h := dist_map_le (Q.map fun r => freeTrials C r j) P Prod.fst
      rwa [PMF.map_comp] at h
    have ha : dist (M₁.bind a) (M₀.bind a) ≤ d := (dist_bind_le _ _ _).trans hm
    have hb : dist (M₀.bind b) (M₁.bind b) ≤ d := by
      rw [dist_comm]
      exact (dist_bind_le _ _ _).trans hm
    change w * dist (M₁.bind a) (messageAndRest C Q j) ≤ _
    rw [← show M₁.bind b = messageAndRest C Q j from bind_conditionalSnd _]
    have htri := mul_le_mul_of_nonneg_left (dist_triangle (M₁.bind a) (M₀.bind a) (M₁.bind b)) hw
    have htri' := mul_le_mul_of_nonneg_left (dist_triangle (M₀.bind a) (M₀.bind b) (M₁.bind b)) hw
    nlinarith [mul_le_mul_of_nonneg_left ha hw, mul_le_mul_of_nonneg_left hb hw]
  · let k : Message × (Rest j) → PMF (PairQ × (Rest j)) :=
      fun (m, r) => (conditionalSnd P m).map (·, r)
    let forget : (Message × PairQ) × (Rest j) → PairQ × (Rest j) := Prod.map Prod.snd id
    have hmap (H : Message → PMF (Rest j)) :
        (M₀.bind fun m => (H m).map (m, ·)).bind k = (paired (H ∘ Prod.fst)).map forget := by
      change _ = (P.bind fun z => (H z.1).map (z, ·)).map forget
      conv_rhs => rw [← bind_conditionalSnd P]
      simp only [M₀, k, forget, PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
        Function.comp_def, Prod.map_apply, id_eq]
      congr 1 with m : 1
      exact PMF.bind_comm _ _ _
    have hr (H : PairQ → PMF (Rest j)) :
        (paired (H ∘ Prod.snd)).map forget =
          (P.map Prod.snd).bind fun q => (H q).map (q, ·) := by
      simp only [paired, forget, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def,
        Prod.map_apply, id_eq]
    have hanchor : (M₀.bind a).bind k = questionsAndAnchoredRest G α C Q j := by
      rw [show M₀.bind a = M₀.bind (fun m => (Function.const Message K₀ m).map (m, ·)) from rfl,
        hmap]
      exact hr (fun _ => K₀)
    have hother : (paired (K ∘ Prod.snd)).map forget = questionsAndRest G α C Q j := hr K
    have hleft : w * dist (questionsAndAnchoredRest G α C Q j) ((M₀.bind b).bind k) ≤ e := by
      rw [← hanchor]
      exact (mul_le_mul_of_nonneg_left (dist_bind_le _ _ _) hw).trans hslice
    have hright : dist ((M₀.bind b).bind k) (questionsAndRest G α C Q j) ≤ e := by
      change dist ((M₀.bind fun m => (L m).map (m, ·)).bind k) _ ≤ e
      rw [hmap, ← hother, dist_comm]
      exact (dist_map_le _ _ _).trans he
    have htri := mul_le_mul_of_nonneg_left
      (dist_triangle (questionsAndAnchoredRest G α C Q j) ((M₀.bind b).bind k)
        (questionsAndRest G α C Q j)) hw
    nlinarith [mul_le_mul_of_nonneg_left hright hw]

private theorem sum_dist_freeTrials_given_wins_le (S : RepeatedStrategy)
    (hW : ∃ r ∈ winsOnChecked G α C, r ∈ (transcriptLaw G α C S).support) :
    let P := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let Q := P.filter W hW
    let p := (P.toOuterMeasure W).toReal
    (∑ j : Free, dist (Q.map fun r => freeTrials C r j) (law G.questions α)) ≤
      Real.sqrt (Fintype.card Free * Real.log (1 / p) / 2) := by
  intro P W Q p
  let d (j : Free) := dist (Q.map fun r => freeTrials C r j) (law G.questions α)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := d)
  refine Real.le_sqrt_of_sq_le (hcs.trans ?_)
  rw [Finset.card_univ]
  have h := mul_le_mul_of_nonneg_left (sum_sq_dist_freeTrials_given_wins_le G α C S hW)
    (Nat.cast_nonneg (α := ℝ) (Fintype.card Free))
  exact h.trans_eq (by ring)

/-- **BVY Lemma 4.6(3–4)** in summed form. Replacing the remaining transcript by its
two-anchor conditional law has small statistical cost, both when keeping the selected
message and when keeping a prior draw of the selected questions. The factor `α² / 2` is
the lower bound on the prior probability of two anchors given each supported message.
The convention of `conditionalSnd` supplies a PMF even for a null observation. -/
theorem sum_dist_anchoredRest_given_wins (S : RepeatedStrategy)
    (hW : ∃ r ∈ winsOnChecked G α C, r ∈ (transcriptLaw G α C S).support) :
    let P := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let Q := P.filter W hW
    let p := (P.toOuterMeasure W).toReal
    let w := (α : ℝ) ^ 2 / 2
    let ε₁ := Real.sqrt (Fintype.card Free * Real.log (1 / p) / 2)
    let ε₂ := Real.sqrt (Fintype.card Free * Real.log (Fintype.card (C → A × B) / p) / 2)
    w * (∑ j : Free, dist (messageAndAnchoredRest C Q j) (messageAndRest C Q j)) ≤
      (2 + 2 * w) * ε₁ + ε₂ ∧
    w * (∑ j : Free, dist (questionsAndAnchoredRest G α C Q j) (questionsAndRest G α C Q j)) ≤
      (1 + w) * (2 * ε₁ + ε₂) := by
  classical
  intro P W Q p w ε₁ ε₂
  let d (j : Free) := dist (Q.map fun r => freeTrials C r j) (law G.questions α)
  let e (j : Free) := dist (Q.map fun r => (r.1, r.2 j))
    ((Q.map Prod.fst).bind fun (t, v) => (pairGiven G α C j t).map ((t, v), ·))
  have hd : (∑ j, d j) ≤ ε₁ := sum_dist_freeTrials_given_wins_le G α C S hW
  have he : (∑ j, e j) ≤ ε₂ := sum_dist_questions_given_wins_le G α C S hW
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  constructor
  · calc
      _ ≤ ∑ j, ((2 + 2 * w) * d j + e j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => by
          have h := (both_anchor_comparisons G α C S j hW).1
          change w * dist (messageAndAnchoredRest C Q j) (messageAndRest C Q j) ≤
            2 * w * d j + (2 * d j + e j) at h
          linarith
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        exact add_le_add (mul_le_mul_of_nonneg_left hd (by positivity)) he
  · calc
      _ ≤ ∑ j, ((1 + w) * (2 * d j + e j)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => (both_anchor_comparisons G α C S j hW).2
      _ ≤ _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hd (by norm_num)) he)
          (by positivity)

/-- Redraw the selected trial from the prior independently of the remaining transcript. -/
@[expose] noncomputable def priorTrialAndRest (Q : PMF Transcript) (j : Free) :
    PMF ((Message × PairQ) × Rest j) :=
  (law G.questions α).bind fun z => (Q.map (restTranscript C j)).map (z, ·)

/-- Replace the entire selected trial by an independent prior draw, while retaining
the original winning marginal of the remaining transcript. This controls the change of law
in the proof of [Bavarian, Vidick and Yuen, equation (48)][BavarianVidickYuen2022],
(arXiv:1509.07466v2, §5.2, printed pp. 25–26), before projecting to either question. -/
theorem sum_dist_trial_rest_independent_given_wins (S : RepeatedStrategy)
    (hW : ∃ r ∈ winsOnChecked G α C, r ∈ (transcriptLaw G α C S).support) :
    let P := transcriptLaw G α C S
    let W := winsOnChecked G α C
    let Q := P.filter W hW
    let p := (P.toOuterMeasure W).toReal
    let w := (α : ℝ) ^ 2 / 2
    let ε₁ := Real.sqrt (Fintype.card Free * Real.log (1 / p) / 2)
    let ε₂ := Real.sqrt (Fintype.card Free * Real.log (Fintype.card (C → A × B) / p) / 2)
    w * ∑ j : Free, dist (Q.map fun r => (freeTrials C r j, restTranscript C j r))
      (priorTrialAndRest G α C Q j) ≤
      2 * (w * ε₁ + (1 + w) * (2 * ε₁ + ε₂)) := by
  classical
  intro P W Q p w ε₁ ε₂
  let μ := law G.questions α
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hlocal (j : Free) :
      dist (Q.map fun r => (freeTrials C r j, restTranscript C j r))
        (priorTrialAndRest G α C Q j) ≤
        2 * (dist (Q.map fun r => freeTrials C r j) μ +
          dist (questionsAndAnchoredRest G α C Q j) (questionsAndRest G α C Q j)) := by
    let J := Q.map fun r => (freeTrials C r j, restTranscript C j r)
    let K := restGivenPair C Q j
    let K₀ := K (none, none)
    let R := Q.map (restTranscript C j)
    let T := μ.bind fun z => (K z.2).map (z, ·)
    let T₀ := μ.bind fun z => K₀.map (z, ·)
    let U := priorTrialAndRest G α C Q j
    have hJ : (J.map Prod.fst).bind (fun z => (K z.2).map (z, ·)) = J := by
      conv_rhs => rw [← bind_conditionalSnd J]
      apply bind_congr_on_support
      intro z hz
      rw [conditionalSnd_restTranscript_given_wins G α C S j hW z hz]
      rfl
    have hfirst : dist J T ≤ dist (Q.map fun r => freeTrials C r j) μ := by
      have h := dist_bind_le (J.map Prod.fst) μ (fun z => (K z.2).map (z, ·))
      rw [hJ, PMF.map_comp] at h
      exact h
    have hsecond : dist T T₀ =
        dist (questionsAndAnchoredRest G α C Q j) (questionsAndRest G α C Q j) := by
      change dist (μ.bind _) (μ.bind _) = dist ((μ.map Prod.snd).bind _) ((μ.map Prod.snd).bind _)
      rw [dist_bind_pair, dist_bind_pair, sum_map_mul]
      simp only [dist_comm _ K₀]
      rfl
    have hR : J.map Prod.snd = R := PMF.map_comp _ _ _
    have hT₀ : T₀.map Prod.snd = K₀ := by
      simp only [T₀, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
      exact PMF.map_id K₀
    have hlast : dist T₀ U ≤ dist J T₀ := by
      change dist (μ.bind _) (μ.bind _) ≤ _
      rw [dist_bind_pair, ← Finset.sum_mul, sum_toReal, one_mul]
      change dist K₀ R ≤ _
      rw [← hR, ← hT₀]
      rw [dist_comm]
      exact dist_map_le J T₀ Prod.snd
    have htriangle := dist_triangle J T T₀
    change dist J U ≤ _
    linarith [dist_triangle J T₀ U]
  calc
    _ ≤ w * ∑ j : Free, 2 * (dist (Q.map fun r => freeTrials C r j) μ +
          dist (questionsAndAnchoredRest G α C Q j) (questionsAndRest G α C Q j)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hlocal j) hw
    _ = 2 * (w * (∑ j : Free, dist (Q.map fun r => freeTrials C r j) μ) +
        w * ∑ j : Free, dist (questionsAndAnchoredRest G α C Q j)
          (questionsAndRest G α C Q j)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      ring
    _ ≤ _ := by
      have htrial := mul_le_mul_of_nonneg_left (sum_dist_freeTrials_given_wins_le G α C S hW) hw
      exact mul_le_mul_of_nonneg_left
        (add_le_add htrial (sum_dist_anchoredRest_given_wins G α C S hW).2) (by norm_num)

end Cslib.PCP.AnchoredDependency
