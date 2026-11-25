/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.PartialLabelScores
public import Mathlib.Data.FinEnum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Deterministic construction of balanced label schedules

The conditional-expectation construction in Lemma 4.5, printed p. 31 of [OpenAI2026ETH],
fixes one whole variable or factor label at a time. The generic pass `greedyLabelPassBy` does
this for any rational score whose average over the candidates for a fresh label does not exceed
its current value (`greedyLabelPassBy_spec`). Lemma 4.5 uses the normalized score
(`greedyLabelPass`, choosing by `bestVariableLabel` and `bestFactorLabel`); Lemma D.3 of the
same paper uses the incidence potential alone (`Cslib.PacketPacking`). A slot that is already
assigned is retained, so repeated slots do not invalidate the fresh-choice premise. Every
incidence still reads the same label of its original variable and factor.

The canonical construction uses the executable enumerations `FinEnum.toList` and `List.Pi.enum`.
Its total schedules have joint normalized potential no greater than the initial finite average.
Factors with empty scopes receive the specified constant label. This is an executable finite
algorithm and its mathematical correctness proof; rational bit-cost and native-machine bounds
are separate obligations.

## Main definitions

* `Cslib.BalancedSchedules.greedyLabelStepBy`, `Cslib.BalancedSchedules.greedyLabelPassBy`:
  one greedy step and a traversal for an arbitrary score.
* `Cslib.BalancedSchedules.greedyLabelStep`: fix one fresh variable or factor label.
* `Cslib.BalancedSchedules.greedyLabelPass`: traverse an explicit list of slots.
* `Cslib.BalancedSchedules.greedySchedules`: construct both complete schedule families.

## Main results

* `Cslib.BalancedSchedules.greedyLabelPassBy_spec`: the method of conditional expectations:
  completion, preservation and score monotonicity for an averaging score.
* `Cslib.BalancedSchedules.greedyLabelPass_eq_greedyLabelPassBy`: the Lemma 4.5 pass is the
  generic pass for the normalized score.
* `Cslib.BalancedSchedules.greedyLabelPass_spec`: completion, preservation and score monotonicity.
* `Cslib.BalancedSchedules.greedySchedules_candidates_length`: the exact `r ^ Q` candidate count.
* `Cslib.BalancedSchedules.greedySchedules_slots_length`: the exact number of slots.
* `Cslib.BalancedSchedules.greedySchedules_score_le`: the output beats the initial average.
* `Cslib.BalancedSchedules.greedySchedules_empty_factor`: empty-factor normalization.
* `Cslib.BalancedSchedules.greedySchedules_balanced`: both pointwise occupancy bounds.

## References

* [OpenAI2026ETH], §4.4, Lemma 4.5, printed pp. 30–31; Appendix D.4.2, Lemma D.3,
  pp. 58–59.
-/

public section

namespace Cslib.BalancedSchedules

open Finset
open scoped BigOperators

section Generic

variable {V F L : Type*} [DecidableEq V] [DecidableEq F]

/-- Fix one fresh whole label using the first candidate that minimizes `score` after the update.
Already fixed labels are retained. Empty candidate lists leave a fresh slot unassigned. -/
@[expose] def greedyLabelStepBy (score : (V → Option L) → (F → Option L) → ℚ)
    (values : List L) (assigned : (V → Option L) × (F → Option L)) (slot : V ⊕ F) :
    (V → Option L) × (F → Option L) :=
  match slot with
  | .inl v =>
    match assigned.1 v with
    | some _ => assigned
    | none => (Function.update assigned.1 v
        (values.argmin fun word => score (Function.update assigned.1 v (some word)) assigned.2),
        assigned.2)
  | .inr f =>
    match assigned.2 f with
    | some _ => assigned
    | none => (assigned.1, Function.update assigned.2 f
        (values.argmin fun word => score assigned.1 (Function.update assigned.2 f (some word))))

/-- Traverse slots in the supplied order with `greedyLabelStepBy`, retaining each selected whole
label for all later score evaluations. Repeated slots never overwrite an earlier selection. -/
@[expose] def greedyLabelPassBy (score : (V → Option L) → (F → Option L) → ℚ)
    (values : List L) (slots : List (V ⊕ F)) (assigned : (V → Option L) × (F → Option L)) :
    (V → Option L) × (F → Option L) :=
  slots.foldl (greedyLabelStepBy score values) assigned

private theorem greedyLabelStepBy_preserves (score : (V → Option L) → (F → Option L) → ℚ)
    (values : List L) (assigned : (V → Option L) × (F → Option L)) (slot query : V ⊕ F)
    (word : L) (h : Sum.elim assigned.1 assigned.2 query = some word) :
    Sum.elim (greedyLabelStepBy score values assigned slot).1
      (greedyLabelStepBy score values assigned slot).2 query = some word := by
  rcases slot with v | f
  · cases hv : assigned.1 v with
    | some _ => simpa only [greedyLabelStepBy, hv] using h
    | none =>
      rcases query with w | f
      · simpa only [greedyLabelStepBy, hv, Sum.elim_inl,
          Function.update_of_ne (fun heq : w = v => by simp [heq, hv] at h)] using h
      · simpa only [greedyLabelStepBy, hv, Sum.elim_inr] using h
  · cases hf : assigned.2 f with
    | some _ => simpa only [greedyLabelStepBy, hf] using h
    | none =>
      rcases query with v | g
      · simpa only [greedyLabelStepBy, hf, Sum.elim_inl] using h
      · simpa only [greedyLabelStepBy, hf, Sum.elim_inr,
          Function.update_of_ne (fun heq : g = f => by simp [heq, hf] at h)] using h

private theorem greedyLabelStepBy_spec [Fintype L] [Nonempty L]
    (score : (V → Option L) → (F → Option L) → ℚ)
    (hvar : ∀ a d v, a v = none → 𝔼 word, score (Function.update a v (some word)) d ≤ score a d)
    (hfac : ∀ a d f, d f = none → 𝔼 word, score a (Function.update d f (some word)) ≤ score a d)
    (values : List L) (hcover : ∀ word, word ∈ values)
    (assigned : (V → Option L) × (F → Option L)) (slot : V ⊕ F) :
    score (greedyLabelStepBy score values assigned slot).1
        (greedyLabelStepBy score values assigned slot).2 ≤ score assigned.1 assigned.2 ∧
    ∃ word, Sum.elim (greedyLabelStepBy score values assigned slot).1
      (greedyLabelStepBy score values assigned slot).2 slot = some word := by
  rcases slot with v | f
  · cases hv : assigned.1 v with
    | some word => exact ⟨by simp [greedyLabelStepBy, hv], word, by simp [greedyLabelStepBy, hv]⟩
    | none =>
      obtain ⟨word, hword, hscore⟩ := argmin_le_expect
        (fun word => score (Function.update assigned.1 v (some word)) assigned.2) values hcover
      exact ⟨by simpa [greedyLabelStepBy, hv, hword] using hscore.trans (hvar _ _ v hv),
        word, by simp [greedyLabelStepBy, hv, hword]⟩
  · cases hf : assigned.2 f with
    | some word => exact ⟨by simp [greedyLabelStepBy, hf], word, by simp [greedyLabelStepBy, hf]⟩
    | none =>
      obtain ⟨word, hword, hscore⟩ := argmin_le_expect
        (fun word => score assigned.1 (Function.update assigned.2 f (some word))) values hcover
      exact ⟨by simpa [greedyLabelStepBy, hf, hword] using hscore.trans (hfac _ _ f hf),
        word, by simp [greedyLabelStepBy, hf, hword]⟩

/-- **Method of conditional expectations.** If fixing a fresh whole label does not increase
`score` on average over the labels, the full pass never increases `score`, fills every visited
slot and preserves all initially assigned labels. Candidate coverage concerns whole labels;
duplicates are allowed. -/
theorem greedyLabelPassBy_spec [Fintype L] [Nonempty L]
    (score : (V → Option L) → (F → Option L) → ℚ)
    (hvar : ∀ a d v, a v = none → 𝔼 word, score (Function.update a v (some word)) d ≤ score a d)
    (hfac : ∀ a d f, d f = none → 𝔼 word, score a (Function.update d f (some word)) ≤ score a d)
    (values : List L) (hcover : ∀ word, word ∈ values) (slots : List (V ⊕ F))
    (assigned : (V → Option L) × (F → Option L)) :
    score (greedyLabelPassBy score values slots assigned).1
        (greedyLabelPassBy score values slots assigned).2 ≤ score assigned.1 assigned.2 ∧
    (∀ slot ∈ slots, ∃ word,
      Sum.elim (greedyLabelPassBy score values slots assigned).1
        (greedyLabelPassBy score values slots assigned).2 slot = some word) ∧
    (∀ slot word, Sum.elim assigned.1 assigned.2 slot = some word →
      Sum.elim (greedyLabelPassBy score values slots assigned).1
        (greedyLabelPassBy score values slots assigned).2 slot = some word) := by
  induction slots generalizing assigned with
  | nil => exact ⟨le_rfl, by simp, fun _ _ h => h⟩
  | cons slot slots ih =>
    obtain ⟨hstep, word, hword⟩ :=
      greedyLabelStepBy_spec score hvar hfac values hcover assigned slot
    obtain ⟨hscore, hfill, hkeep⟩ := ih (greedyLabelStepBy score values assigned slot)
    refine ⟨hscore.trans hstep, fun q hq => ?_, fun q v hv =>
      hkeep q v (greedyLabelStepBy_preserves score values assigned slot q v hv)⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨word, hkeep _ word hword⟩
    · exact hfill q hq

end Generic

section ExplicitLists

variable {E V F T G : Type*} [Fintype E] [Fintype V] [DecidableEq V]
  [DecidableEq F] [Fintype T] [DecidableEq T] [Fintype G] [DecidableEq G]

/-- Fix one fresh whole label using the first minimizing candidate. Already fixed labels are
retained. Empty candidate lists leave a fresh slot unassigned. -/
@[expose] def greedyLabelStep (edge : E → F × V) (C : ℕ) (values : List (T → G))
    (assigned : (V → Option (T → G)) × (F → Option (T → G))) (slot : V ⊕ F) :
    (V → Option (T → G)) × (F → Option (T → G)) :=
  match slot with
  | .inl v =>
    match assigned.1 v with
    | some _ => assigned
    | none => (Function.update assigned.1 v
        (bestVariableLabel edge assigned.1 assigned.2 C v values), assigned.2)
  | .inr f =>
    match assigned.2 f with
    | some _ => assigned
    | none => (assigned.1, Function.update assigned.2 f
        (bestFactorLabel edge assigned.1 assigned.2 C f values))

/-- Traverse slots in the supplied order, retaining each selected whole label for all later
score evaluations. This accepts repeated slots without overwriting an earlier selection. -/
@[expose] def greedyLabelPass (edge : E → F × V) (C : ℕ) (values : List (T → G))
    (slots : List (V ⊕ F))
    (assigned : (V → Option (T → G)) × (F → Option (T → G))) :
    (V → Option (T → G)) × (F → Option (T → G)) :=
  slots.foldl (greedyLabelStep edge C values) assigned

/-- The Lemma 4.5 pass is the generic pass for the normalized score. -/
theorem greedyLabelPass_eq_greedyLabelPassBy (edge : E → F × V) (C : ℕ)
    (values : List (T → G)) (slots : List (V ⊕ F))
    (assigned : (V → Option (T → G)) × (F → Option (T → G))) :
    greedyLabelPass edge C values slots assigned =
      greedyLabelPassBy (fun a d => normalizedPartialScore edge a d C) values slots assigned := by
  rw [greedyLabelPass, greedyLabelPassBy]
  congr 1
  funext assigned slot
  rcases slot with v | f
  · cases hv : assigned.1 v <;>
      simp only [greedyLabelStep, greedyLabelStepBy, hv, bestVariableLabel]
  · cases hf : assigned.2 f <;>
      simp only [greedyLabelStep, greedyLabelStepBy, hf, bestFactorLabel]

/-- The full pass never increases the joint score, fills every visited slot and preserves
all initially assigned labels. Candidate coverage concerns whole words; duplicates are allowed. -/
theorem greedyLabelPass_spec [Nonempty G] (edge : E → F × V) (C : ℕ)
    (values : List (T → G)) (hcover : ∀ word, word ∈ values) (slots : List (V ⊕ F))
    (assigned : (V → Option (T → G)) × (F → Option (T → G))) :
    normalizedPartialScore edge (greedyLabelPass edge C values slots assigned).1
        (greedyLabelPass edge C values slots assigned).2 C ≤
      normalizedPartialScore edge assigned.1 assigned.2 C ∧
    (∀ slot ∈ slots, ∃ word,
      Sum.elim (greedyLabelPass edge C values slots assigned).1
        (greedyLabelPass edge C values slots assigned).2 slot = some word) ∧
    (∀ slot word, Sum.elim assigned.1 assigned.2 slot = some word →
      Sum.elim (greedyLabelPass edge C values slots assigned).1
        (greedyLabelPass edge C values slots assigned).2 slot = some word) := by
  rw [greedyLabelPass_eq_greedyLabelPassBy]
  exact greedyLabelPassBy_spec (fun a d => normalizedPartialScore edge a d C)
    (fun a d v hv => (expect_normalizedPartialScore_update_variable edge a d C v hv).le)
    (fun a d f hf => (expect_normalizedPartialScore_update_factor edge a d C f hf).le)
    values hcover slots assigned

end ExplicitLists

section Enumerated

variable {E V F T G : Type*} [Fintype E] [Fintype V] [Fintype T] [Fintype G]
  [FinEnum V] [FinEnum F] [FinEnum T] [FinEnum G]

/-- The whole-label candidate list has exactly `r ^ Q` entries, including the single empty
word when `Q = 0`. -/
theorem greedySchedules_candidates_length :
    (List.Pi.enum (fun _ : T => G)).length = Fintype.card G ^ Fintype.card T := by
  have h := Multiset.card_pi (↑(FinEnum.toList T) : Multiset T)
    (fun _ => (↑(FinEnum.toList G) : Multiset G))
  rw [Multiset.pi_coe] at h
  change (List.pi (FinEnum.toList T) (fun _ => FinEnum.toList G)).length = _ at h
  simpa [List.Pi.enum, FinEnum.toList, FinEnum.card_eq_fintypeCard,
    Function.comp_def, List.map_const] using h

/-- The traversal visits exactly one slot for each variable and factor. -/
theorem greedySchedules_slots_length :
    ((FinEnum.toList V).map (Sum.inl : V → V ⊕ F) ++
      (FinEnum.toList F).map Sum.inr).length = Fintype.card V + Fintype.card F := by
  simp [FinEnum.toList, FinEnum.card_eq_fintypeCard]

/-- Construct schedules by fixing all variables, then all factors, in their explicit finite
orders. Candidate whole labels use `List.Pi.enum`; no good-label witness is supplied. Normalize
empty factors to the constant `g₀` schedule after the pass. -/
@[expose] def greedySchedules (edge : E → F × V) (C : ℕ) (g₀ : G) :
    (V → T → G) × (F → T → G) :=
  let assigned := greedyLabelPass edge C (List.Pi.enum (fun _ : T => G))
    ((FinEnum.toList V).map Sum.inl ++ (FinEnum.toList F).map Sum.inr)
    (fun _ => none, fun _ => none)
  (completeLabels assigned.1 (fun _ _ => g₀),
    normalizeEmptyFactors (fun e => (edge e).1) g₀
      (completeLabels assigned.2 (fun _ _ => g₀)))

/-- Every empty factor gets the specified constant schedule, independently of tie breaking. -/
theorem greedySchedules_empty_factor (edge : E → F × V) (C : ℕ) (g₀ : G) {f : F}
    (hf : ¬ ∃ e, (edge e).1 = f) :
    (greedySchedules (T := T) edge C g₀).2 f = fun _ => g₀ :=
  normalizeEmptyFactors_of_not_exists _ _ _ hf

/-- The complete deterministic construction has joint normalized potential at most the initial
finite-uniform average. All choices are whole schedules; repeated incidence endpoints remain
correlated. Empty index types and zero normalization denominators retain their rational meaning. -/
theorem greedySchedules_score_le (edge : E → F × V) (C : ℕ) (g₀ : G) :
    potential (fun e => ((greedySchedules (T := T) edge C g₀).1 (edge e).2,
      (greedySchedules (T := T) edge C g₀).2 (edge e).1)) / ((Fintype.card E : ℚ) * C) +
      (∑ t, potential (fun v => (greedySchedules (T := T) edge C g₀).1 v t)) /
        ((Fintype.card T : ℚ) * Fintype.card V) ≤
      𝔼 a : V → T → G, 𝔼 d : F → T → G,
        (potential (fun e => (a (edge e).2, d (edge e).1)) / ((Fintype.card E : ℚ) * C) +
          (∑ t, potential (fun v => a v t)) / ((Fintype.card T : ℚ) * Fintype.card V)) := by
  let : Nonempty G := ⟨g₀⟩
  obtain ⟨hscore, hfill, -⟩ := greedyLabelPass_spec edge C (List.Pi.enum (fun _ : T => G))
    List.Pi.mem_enum ((FinEnum.toList V).map Sum.inl ++ (FinEnum.toList F).map Sum.inr)
    (fun _ => none, fun _ => none)
  set assigned := greedyLabelPass edge C (List.Pi.enum (fun _ : T => G))
    ((FinEnum.toList V).map Sum.inl ++ (FinEnum.toList F).map Sum.inr)
    (fun _ => none, fun _ => none)
  have hvar (a : V → T → G) :
      completeLabels assigned.1 a = completeLabels assigned.1 (fun _ _ => g₀) :=
    funext fun v => by
      obtain ⟨w, hw⟩ := hfill (.inl v) (by simp)
      rw [Sum.elim_inl] at hw
      simp only [completeLabels, hw, Option.getD_some]
  have hfac (d : F → T → G) :
      completeLabels assigned.2 d = completeLabels assigned.2 (fun _ _ => g₀) :=
    funext fun f => by
      obtain ⟨w, hw⟩ := hfill (.inr f) (by simp)
      rw [Sum.elim_inr] at hw
      simp only [completeLabels, hw, Option.getD_some]
  have hout := normalizedPartialScore_eq_expect edge assigned.1 assigned.2 C
  simp only [hvar, hfac, Fintype.expect_const] at hout
  have hin := normalizedPartialScore_eq_expect (T := T) (G := G) edge
    (fun _ => none) (fun _ => none) C
  simp only [completeLabels, Option.getD_none] at hin
  have hinc : (fun e => ((greedySchedules (T := T) edge C g₀).1 (edge e).2,
      (greedySchedules (T := T) edge C g₀).2 (edge e).1)) =
      fun e => (completeLabels assigned.1 (fun _ _ => g₀) (edge e).2,
        completeLabels assigned.2 (fun _ _ => g₀) (edge e).1) :=
    funext fun e => Prod.ext rfl (normalizeEmptyFactors_factorOf _ _ _ _)
  rw [← hin, hinc]
  exact hout.symm.trans_le hscore

/-- Under the incidence degree bounds, the constructed schedules have normalized potential
at most two, by the established finite-average incidence and group estimates. -/
theorem greedySchedules_score_le_two [Nonempty T] [Nonempty V]
    (edge : E → F × V) {b w : ℕ}
    (hb : ∀ e : E, #{e' : E | (edge e').2 = (edge e).2} ≤ b)
    (hw : ∀ e : E, #{e' : E | (edge e').1 = (edge e).1} ≤ w)
    (hbw : 0 < b + w) (hE : 0 < Fintype.card E) (g₀ : G) :
    potential (fun e => ((greedySchedules (T := T) edge (b + w) g₀).1 (edge e).2,
      (greedySchedules (T := T) edge (b + w) g₀).2 (edge e).1)) /
        ((Fintype.card E : ℚ) * (b + w : ℕ)) +
      (∑ t, potential (fun v => (greedySchedules (T := T) edge (b + w) g₀).1 v t)) /
        ((Fintype.card T : ℚ) * Fintype.card V) ≤ 2 := by
  let : Nonempty G := ⟨g₀⟩
  have h1 : (𝔼 a : V → T → G, 𝔼 d : F → T → G,
      potential (fun e => (a (edge e).2, d (edge e).1)) /
        ((Fintype.card E : ℚ) * (b + w : ℕ))) ≤ 1 := by
    simp_rw [div_eq_mul_inv, ← Finset.expect_mul, ← div_eq_mul_inv]
    rw [div_le_one (by positivity)]
    have h := expect_incidence_potential_le (L := T → G) (fun e => (edge e).2)
      (fun e => (edge e).1) hb hw
    unfold incidenceLabel at h
    simpa only [Nat.cast_add] using h
  have h2 :
      (𝔼 a : V → T → G, (∑ t, potential (fun v => a v t)) /
        ((Fintype.card T : ℚ) * Fintype.card V)) ≤ 1 := by
    simp_rw [div_eq_mul_inv, ← Finset.expect_mul, ← div_eq_mul_inv]
    exact (div_le_one (by positivity)).mpr expect_group_potential_le
  refine (greedySchedules_score_le edge (b + w) g₀).trans ?_
  simp only [Finset.expect_add_distrib, Fintype.expect_const]
  linarith

/-- The actual constructed schedules satisfy both occupancy bounds of Lemma 4.5 under its
size hypotheses. Empty factors have the prescribed constant labels by
`greedySchedules_empty_factor`. This certifies the result of the program, not its bit cost. -/
theorem greedySchedules_balanced [Nonempty T] [Nonempty V]
    (edge : E → F × V) {b w : ℕ}
    (hb : ∀ e : E, #{e' : E | (edge e').2 = (edge e).2} ≤ b)
    (hw : ∀ e : E, #{e' : E | (edge e').1 = (edge e).1} ≤ w)
    (hbw : 0 < b + w)
    (hincidenceSize :
      2 * (b + w) * Fintype.card ((T → G) × (T → G)) ^ 2 ≤ Fintype.card E)
    (hgroupSize : 2 * Fintype.card T * Fintype.card G ^ 2 ≤ Fintype.card V) (g₀ : G) :
    (∀ u : (T → G) × (T → G),
      occupancy (fun e => ((greedySchedules (T := T) edge (b + w) g₀).1 (edge e).2,
          (greedySchedules (T := T) edge (b + w) g₀).2 (edge e).1)) u *
        Fintype.card ((T → G) × (T → G)) ≤ 2 * Fintype.card E) ∧
    (∀ t : T, ∀ g : G,
      occupancy (fun v => (greedySchedules (T := T) edge (b + w) g₀).1 v t) g *
        Fintype.card G ≤ 2 * Fintype.card V) := by
  let : Nonempty G := ⟨g₀⟩
  have hE : 0 < Fintype.card E :=
    (by positivity : 0 < 2 * (b + w) * Fintype.card ((T → G) × (T → G)) ^ 2).trans_le
      hincidenceSize
  exact incidence_and_group_bounds _ _ (b + w) hE hbw Fintype.card_pos Fintype.card_pos
    hincidenceSize hgroupSize
    (greedySchedules_score_le_two edge hb hw hbw hE g₀)

end Enumerated

end Cslib.BalancedSchedules
