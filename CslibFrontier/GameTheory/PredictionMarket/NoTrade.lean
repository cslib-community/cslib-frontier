/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.MixedStrategy
public import Mathlib.Order.Setoid.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Information Partitions, Agreement, Rational Expectations, and No-Trade

This module formalizes the partition model of knowledge, common knowledge, rational expectations
equilibria, Aumann's agreement theorem, and the Milgrom–Stokey no-trade theorem from
[PennockSami2007, §26.2, pp. 653–657; §26.7, pp. 671–673].

## Model and conventions

Let `Ω` be a finite state space (`[Fintype Ω]`) equipped with a nonnegative prior `P : Ω → ℝ`
(typically a probability distribution `IsMixedStrategy P`). Each agent `i : ι` observes a
partition of `Ω`, represented by an equivalence relation `π i : Setoid Ω`:

* `infoCell r ω` is the equivalence class `{ω' : Ω | r ω ω'}` containing `ω`;
* `combinedPartition π = ⨅ i, π i` is the coarsest common refinement `π̂` of the agents'
  partitions [PennockSami2007, Definition 26.1, p. 653];
* `commonKnowledgePartition π = ⨆ i, π i` is the finest common coarsening (meet partition), whose
  equivalence classes are the minimal events that are self-evident for every agent;
* `eventProb P E = ∑ ω ∈ E, P ω` and `condExp P E f = (∑ ω ∈ E, P ω * f ω) / eventProb P E`
  give event probabilities and posterior expectations.

For agreement and no-trade results, posterior hypotheses are quantified over positive-probability
states `0 < P ω` (which automatically guarantees `0 < eventProb P (infoCell (π i) ω)` and avoids
division-by-zero artifacts on null cells).

## Main definitions

* `Cslib.GameTheory.PredictionMarket.infoCell`: equivalence class `{ω' | r ω ω'}` of a partition.
* `Cslib.GameTheory.PredictionMarket.combinedPartition`: coarsest common refinement `π̂ = ⨅ i, π i`
  [PennockSami2007, Definition 26.1, p. 653].
* `Cslib.GameTheory.PredictionMarket.commonKnowledgePartition`: finest common coarsening
  `⨆ i, π i` (Aumann's meet partition).
* `Cslib.GameTheory.PredictionMarket.IsSelfEvident`,
  `Cslib.GameTheory.PredictionMarket.IsCommonKnowledgeEvent`,
  `Cslib.GameTheory.PredictionMarket.IsCommonKnowledgeAt`: self-evident and common-knowledge events.
* `Cslib.GameTheory.PredictionMarket.eventProb`, `Cslib.GameTheory.PredictionMarket.condExp`:
  event probability and conditional expectation on finite `Ω`.
* `Cslib.GameTheory.PredictionMarket.pricePartition`,
  `Cslib.GameTheory.PredictionMarket.infoWithPrice`,
  `Cslib.GameTheory.PredictionMarket.IsREE`,
  `Cslib.GameTheory.PredictionMarket.IsFullyRevealingPrice`: price-induced partitions, rational
  expectations equilibria, and fully revealing price mappings
  [PennockSami2007, Definition 26.2, pp. 656–657].

## Main results

* `Cslib.GameTheory.PredictionMarket.isCommonKnowledgeEvent_iff_commonKnowledgePartition`:
  self-evident-for-all-agents characterization of common-knowledge events.
* `Cslib.GameTheory.PredictionMarket.isCommonKnowledgeAt_iff_exists_commonKnowledgeEvent`:
  equivalence between the meet-partition and self-evident-event characterizations of common
  knowledge.
* `Cslib.GameTheory.PredictionMarket.sum_mul_condExp_infoCell_eq`,
  `Cslib.GameTheory.PredictionMarket.condExp_condExp_infoCell_eq`: law of iterated expectations
  over any self-evident event.
* `Cslib.GameTheory.PredictionMarket.aumann_agreement`,
  `Cslib.GameTheory.PredictionMarket.aumann_agreement_at`: **Aumann's Agreement Theorem** — two
  Bayesian agents with a common prior whose posteriors are common knowledge must agree
  (Aumann 1976; [PennockSami2007, §26.2.2.3 & §26.7, pp. 657, 671]).
* `Cslib.GameTheory.PredictionMarket.condExp_infoWithPrice_eq_omniscient_of_isFullyRevealing`,
  `Cslib.GameTheory.PredictionMarket.isREE_commonValue_iff_omniscient_of_isFullyRevealing`:
  in a fully revealing rational expectations equilibrium (`π_{P*} = π̂`), every agent holds the
  exact omniscient forecast `E[f | π̂(ω)]`, all agents agree, and a unanimous common-value clearing
  operator clears at the omniscient forecast [PennockSami2007, §26.2.2.3, pp. 656–657].
* `Cslib.GameTheory.PredictionMarket.milgrom_stokey_no_trade`: **Milgrom–Stokey No-Trade
  Theorem** — under a common prior, any interim individually rational zero-sum trade on a
  common-knowledge event gives every agent zero interim expected profit on every
  positive-probability state (Milgrom–Stokey 1982; [PennockSami2007, §26.2.2.3 & §26.7,
  pp. 657, 671]).
* `Cslib.GameTheory.PredictionMarket.exists_strict_zeroSum_trade_of_ne_prior`: sharpness of the
  common-prior assumption — any two distinct priors `P₁ ≠ P₂` admit a zero-sum bet with strictly
  positive expected profit for both agents.

## References

* [D. M. Pennock, R. Sami, *Computational Aspects of Prediction Markets*, Chapter 26 of
  *Algorithmic Game Theory*, §26.2, pp. 653–657, and §26.7, pp. 671–673][PennockSami2007]
-/

public section

open Finset

namespace Cslib.GameTheory.PredictionMarket

section Partitions

variable {Ω ι : Type*}

/-- The combined information partition `π̂ = ⨅ i, π i`: the coarsest common refinement of all
agents' information partitions [PennockSami2007, Definition 26.1, p. 653]. -/
@[expose] def combinedPartition (π : ι → Setoid Ω) : Setoid Ω :=
  ⨅ i, π i

theorem combinedPartition_rel {π : ι → Setoid Ω} {ω₁ ω₂ : Ω} :
    combinedPartition π ω₁ ω₂ ↔ ∀ i, π i ω₁ ω₂ := by
  change (sInf (Set.range π)) ω₁ ω₂ ↔ _
  simp only [Setoid.sInf_iff, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]

/-- The common-knowledge (meet) partition `⨆ i, π i`: the finest common coarsening of all agents'
information partitions (Aumann 1976; [PennockSami2007, §26.7, p. 671]). -/
@[expose] def commonKnowledgePartition (π : ι → Setoid Ω) : Setoid Ω :=
  ⨆ i, π i

variable [Fintype Ω]

/-- The information cell `{ω' : Ω | r ω ω'}` containing state `ω` in the partition represented
by equivalence relation `r : Setoid Ω` [PennockSami2007, Definition 26.1, p. 653]. -/
noncomputable def infoCell (r : Setoid Ω) (ω : Ω) : Finset Ω :=
  letI := Classical.decPred fun ω' : Ω => r ω ω'
  Finset.univ.filter fun ω' => r ω ω'

@[simp]
theorem mem_infoCell {r : Setoid Ω} {ω ω' : Ω} :
    ω' ∈ infoCell r ω ↔ r ω ω' := by
  classical
  simp [infoCell]

theorem mem_infoCell_self (r : Setoid Ω) (ω : Ω) : ω ∈ infoCell r ω :=
  mem_infoCell.mpr (r.refl' ω)

theorem infoCell_eq_of_rel {r : Setoid Ω} {ω₁ ω₂ : Ω} (h : r ω₁ ω₂) :
    infoCell r ω₁ = infoCell r ω₂ := by
  ext ω'
  simp only [mem_infoCell]
  exact ⟨fun h₁ => r.trans' (r.symm' h) h₁, fun h₂ => r.trans' h h₂⟩

private theorem infoCell_subset_of_le {r₁ r₂ : Setoid Ω} (h : r₁ ≤ r₂) (ω : Ω) :
    infoCell r₁ ω ⊆ infoCell r₂ ω :=
  fun _ hω' => mem_infoCell.mpr (h (mem_infoCell.mp hω'))

/-- An event `E` is **self-evident** under partition `r` if whenever `ω ∈ E`, every state
indistinguishable from `ω` under `r` also lies in `E` (equivalently, `E` is a union of
`r`-cells). -/
@[expose] def IsSelfEvident (r : Setoid Ω) (E : Finset Ω) : Prop :=
  ∀ ω ∈ E, infoCell r ω ⊆ E

/-- An event `E` is a **common-knowledge (public) event** for partition profile `π` if it is
self-evident for every agent `i`. -/
@[expose] def IsCommonKnowledgeEvent (π : ι → Setoid Ω) (E : Finset Ω) : Prop :=
  ∀ i, IsSelfEvident (π i) E

/-- An event `E` is **common knowledge at state `ω`** if the meet-partition cell containing `ω`
is contained in `E` (Aumann 1976). -/
@[expose] def IsCommonKnowledgeAt (π : ι → Setoid Ω) (E : Finset Ω) (ω : Ω) : Prop :=
  infoCell (commonKnowledgePartition π) ω ⊆ E

/-- An event is self-evident for every agent if and only if it is self-evident for the meet
partition `commonKnowledgePartition π`. -/
theorem isCommonKnowledgeEvent_iff_commonKnowledgePartition
    {π : ι → Setoid Ω} {E : Finset Ω} :
    IsCommonKnowledgeEvent π E ↔ IsSelfEvident (commonKnowledgePartition π) E := by
  constructor
  · intro hE
    let S : Setoid Ω := Setoid.ker (fun ω : Ω => ω ∈ E)
    have hle : commonKnowledgePartition π ≤ S := by
      refine iSup_le fun i ω₁ ω₂ hrel => ?_
      change (ω₁ ∈ E) = (ω₂ ∈ E)
      exact propext ⟨fun h₁ => hE i ω₁ h₁ (mem_infoCell.mpr hrel),
        fun h₂ => hE i ω₂ h₂ (mem_infoCell.mpr ((π i).symm' hrel))⟩
    intro ω hω ω' hω'
    have hS : (ω ∈ E) = (ω' ∈ E) := hle (mem_infoCell.mp hω')
    exact hS ▸ hω
  · intro hE i ω hω
    exact (infoCell_subset_of_le (le_iSup π i) ω).trans (hE ω hω)

/-- Every meet-partition cell `infoCell (commonKnowledgePartition π) ω` is a common-knowledge
event. -/
theorem isCommonKnowledgeEvent_infoCell_commonKnowledgePartition (π : ι → Setoid Ω) (ω : Ω) :
    IsCommonKnowledgeEvent π (infoCell (commonKnowledgePartition π) ω) := by
  rw [isCommonKnowledgeEvent_iff_commonKnowledgePartition]
  intro ω' hω'
  rw [infoCell_eq_of_rel ((commonKnowledgePartition π).symm' (mem_infoCell.mp hω'))]

/-- **Aumann's characterization of common knowledge at a state**: `E` is common knowledge at `ω`
if and only if there exists a common-knowledge (mutually self-evident) event `F` with `ω ∈ F`
and `F ⊆ E`. -/
theorem isCommonKnowledgeAt_iff_exists_commonKnowledgeEvent
    {π : ι → Setoid Ω} {E : Finset Ω} {ω : Ω} :
    IsCommonKnowledgeAt π E ω ↔
      ∃ F : Finset Ω, ω ∈ F ∧ F ⊆ E ∧ IsCommonKnowledgeEvent π F := by
  constructor
  · intro h
    exact ⟨infoCell (commonKnowledgePartition π) ω, mem_infoCell_self _ ω, h,
      isCommonKnowledgeEvent_infoCell_commonKnowledgePartition π ω⟩
  · rintro ⟨F, hωF, hFE, hFck⟩
    have hself := isCommonKnowledgeEvent_iff_commonKnowledgePartition.mp hFck
    exact (hself ω hωF).trans hFE

end Partitions

section Expectations

variable {Ω ι : Type*}

/-- Total prior probability `∑ ω ∈ E, P ω` of event `E` under prior `P`. -/
def eventProb (P : Ω → ℝ) (E : Finset Ω) : ℝ :=
  ∑ ω ∈ E, P ω

@[simp]
theorem eventProb_apply (P : Ω → ℝ) (E : Finset Ω) :
    eventProb P E = ∑ ω ∈ E, P ω := by
  rfl

/-- Conditional expectation `E_P[f | E] = (∑ ω ∈ E, P ω * f ω) / eventProb P E` of a real-valued
random variable `f : Ω → ℝ` given event `E` [PennockSami2007, §26.2.1, pp. 653–654]. -/
noncomputable def condExp (P : Ω → ℝ) (E : Finset Ω) (f : Ω → ℝ) : ℝ :=
  (∑ ω ∈ E, P ω * f ω) / eventProb P E

@[simp]
theorem condExp_apply (P : Ω → ℝ) (E : Finset Ω) (f : Ω → ℝ) :
    condExp P E f = (∑ ω ∈ E, P ω * f ω) / eventProb P E := by
  rfl

theorem eventProb_pos_of_mem {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) {E : Finset Ω} {ω : Ω}
    (hω : ω ∈ E) (hPω : 0 < P ω) : 0 < eventProb P E :=
  sum_pos' (fun ω' _ => hP ω') ⟨ω, hω, hPω⟩

/-- On an event of positive prior probability, if `f` equals `c` on every positive-probability state
of `E`, then `condExp P E f = c`. -/
theorem condExp_eq_const {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) {E : Finset Ω}
    (hE : 0 < eventProb P E) {f : Ω → ℝ} {c : ℝ}
    (hf : ∀ ω ∈ E, 0 < P ω → f ω = c) :
    condExp P E f = c := by
  have hnum : ∑ ω ∈ E, P ω * f ω = eventProb P E * c := by
    rw [eventProb_apply, sum_mul]
    refine sum_congr rfl fun ω hω => ?_
    rcases (hP ω).lt_or_eq with hpos | hzero
    · rw [hf ω hω hpos]
    · rw [← hzero, zero_mul, zero_mul]
  rw [condExp_apply, hnum, mul_div_cancel_left₀ _ hE.ne']

/-- Decompose a sum over any self-evident event `E` into a sum over its disjoint `r`-cells. -/
private theorem sum_over_selfEvident_eq_sum_cells [Fintype Ω] [DecidableEq Ω] {r : Setoid Ω}
    {E : Finset Ω} (hE : IsSelfEvident r E) (g : Ω → ℝ) :
    ∑ ω ∈ E, g ω = ∑ C ∈ E.image (infoCell r), ∑ ω ∈ C, g ω := by
  have hbi : (E.image (infoCell r)).biUnion id = E := by
    ext ω
    simp only [mem_biUnion, mem_image, id_eq]
    constructor
    · rintro ⟨_, ⟨ω₀, hω₀, rfl⟩, hω⟩
      exact hE ω₀ hω₀ hω
    · intro hω
      exact ⟨infoCell r ω, ⟨ω, hω, rfl⟩, mem_infoCell_self r ω⟩
  have hdisj : Set.PairwiseDisjoint (E.image (infoCell r) : Set (Finset Ω)) id := by
    intro C₁ hC₁ C₂ hC₂ hne
    change Disjoint C₁ C₂
    rw [Finset.disjoint_left]
    intro ω hω₁ hω₂
    obtain ⟨ω₁, _, rfl⟩ := mem_image.mp hC₁
    obtain ⟨ω₂, _, rfl⟩ := mem_image.mp hC₂
    have heq₁ := infoCell_eq_of_rel (mem_infoCell.mp hω₁)
    have heq₂ := infoCell_eq_of_rel (mem_infoCell.mp hω₂)
    exact hne (heq₁.trans heq₂.symm)
  conv_lhs => rw [← hbi]
  exact Finset.sum_biUnion hdisj

/-- **Weighted law of iterated expectations** over a self-evident event `E`: integrating
`condExp P (infoCell r ω) f` against `P` over `E` recovers `∑ ω ∈ E, P ω * f ω`, even when
some cells inside `E` carry zero prior mass. -/
theorem sum_mul_condExp_infoCell_eq [Fintype Ω] {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) {r : Setoid Ω}
    {E : Finset Ω} (hE : IsSelfEvident r E) (f : Ω → ℝ) :
    ∑ ω ∈ E, P ω * condExp P (infoCell r ω) f = ∑ ω ∈ E, P ω * f ω := by
  classical
  rw [sum_over_selfEvident_eq_sum_cells hE (fun ω => P ω * condExp P (infoCell r ω) f),
    sum_over_selfEvident_eq_sum_cells hE (fun ω => P ω * f ω)]
  refine sum_congr rfl fun C hC => ?_
  obtain ⟨ω₀, _, rfl⟩ := mem_image.mp hC
  have hcell : ∀ ω ∈ infoCell r ω₀, infoCell r ω = infoCell r ω₀ := fun ω hω =>
    infoCell_eq_of_rel (r.symm' (mem_infoCell.mp hω))
  calc ∑ ω ∈ infoCell r ω₀, P ω * condExp P (infoCell r ω) f
      = ∑ ω ∈ infoCell r ω₀, P ω * condExp P (infoCell r ω₀) f :=
        sum_congr rfl fun ω hω => by rw [hcell ω hω]
    _ = eventProb P (infoCell r ω₀) * condExp P (infoCell r ω₀) f := by
        rw [← sum_mul, eventProb_apply]
    _ = ∑ ω ∈ infoCell r ω₀, P ω * f ω := by
        by_cases hp : eventProb P (infoCell r ω₀) = 0
        · have hall : ∀ ω ∈ infoCell r ω₀, P ω = 0 :=
            (sum_eq_zero_iff_of_nonneg fun ω _ => hP ω).mp hp
          rw [hp, zero_mul]
          exact (sum_eq_zero fun ω hω => by rw [hall ω hω, zero_mul]).symm
        · rw [condExp_apply, mul_div_cancel₀ _ hp]

/-- **Law of iterated expectations (tower property)**: for any self-evident event `E`,
`E[E[f | r] | E] = E[f | E]`. -/
theorem condExp_condExp_infoCell_eq [Fintype Ω] {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) {r : Setoid Ω}
    {E : Finset Ω} (hE : IsSelfEvident r E) (f : Ω → ℝ) :
    condExp P E (fun ω => condExp P (infoCell r ω) f) = condExp P E f := by
  rw [condExp_apply, condExp_apply, sum_mul_condExp_infoCell_eq hP hE f]

end Expectations

/-! ### Aumann's Agreement Theorem -/

section Agreement

variable {Ω ι : Type*} [Fintype Ω]

/-- **Aumann's Agreement Theorem** (Aumann 1976; [PennockSami2007, §26.2.2.3 & §26.7,
pp. 657, 671]): under a common nonnegative prior `P`, if `E` is a common-knowledge event of
positive prior probability on which agent `i`'s posterior expectation of `f` is constant `q_i`
and agent `j`'s posterior expectation of `f` is constant `q_j` (on positive-probability states),
then `q_i = q_j` (and both equal `condExp P E f`). -/
theorem aumann_agreement {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) {π : ι → Setoid Ω}
    {E : Finset Ω} (hE : IsCommonKnowledgeEvent π E) (hE_pos : 0 < eventProb P E)
    (f : Ω → ℝ) {i j : ι} {q_i q_j : ℝ}
    (hi : ∀ ω ∈ E, 0 < P ω → condExp P (infoCell (π i) ω) f = q_i)
    (hj : ∀ ω ∈ E, 0 < P ω → condExp P (infoCell (π j) ω) f = q_j) :
    q_i = q_j ∧ q_i = condExp P E f := by
  have hqi : q_i = condExp P E f := by
    rw [← condExp_eq_const hP hE_pos hi, condExp_condExp_infoCell_eq hP (hE i) f]
  have hqj : q_j = condExp P E f := by
    rw [← condExp_eq_const hP hE_pos hj, condExp_condExp_infoCell_eq hP (hE j) f]
  exact ⟨hqi.trans hqj.symm, hqi⟩

/-- Pointwise form of **Aumann's Agreement Theorem** at a positive-probability state `ω`: if it is
common knowledge at `ω` that agent `i`'s posterior is `q_i` and agent `j`'s posterior is `q_j`,
then `q_i = q_j`. -/
theorem aumann_agreement_at {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) {π : ι → Setoid Ω}
    (f : Ω → ℝ) {ω : Ω} (hPω : 0 < P ω) {i j : ι} {q_i q_j : ℝ}
    {E_i E_j : Finset Ω}
    (hck_i : IsCommonKnowledgeAt π E_i ω) (hck_j : IsCommonKnowledgeAt π E_j ω)
    (hEi : ∀ ω' ∈ E_i, 0 < P ω' → condExp P (infoCell (π i) ω') f = q_i)
    (hEj : ∀ ω' ∈ E_j, 0 < P ω' → condExp P (infoCell (π j) ω') f = q_j) :
    q_i = q_j := by
  set M := infoCell (commonKnowledgePartition π) ω
  have hM_ck : IsCommonKnowledgeEvent π M :=
    isCommonKnowledgeEvent_infoCell_commonKnowledgePartition π ω
  have hM_pos : 0 < eventProb P M :=
    eventProb_pos_of_mem hP (mem_infoCell_self _ ω) hPω
  exact (aumann_agreement hP hM_ck hM_pos f
    (fun ω' hω' hpos => hEi ω' (hck_i hω') hpos)
    (fun ω' hω' hpos => hEj ω' (hck_j hω') hpos)).1

end Agreement

/-! ### Rational Expectations Equilibrium (§26.2.2.3, Definition 26.2, pp. 656–657) -/

section REE

variable {Ω ι : Type*}

/-- The information partition `π_{P*}` induced by observing price mapping `Pstar : Ω → ℝ`:
two states are indistinguishable under `Pstar` iff they yield the same price
[PennockSami2007, §26.2.2.3, p. 656]. -/
@[expose] def pricePartition (Pstar : Ω → ℝ) : Setoid Ω :=
  Setoid.ker Pstar

@[simp]
theorem pricePartition_rel (Pstar : Ω → ℝ) (ω₁ ω₂ : Ω) :
    pricePartition Pstar ω₁ ω₂ ↔ Pstar ω₁ = Pstar ω₂ := by
  rfl

/-- Agent `i`'s refined information `π_i ⊓ π_{P*}` after observing both her private partition
`π i` and the market price `Pstar ω` [PennockSami2007, Definition 26.2, p. 656]. -/
@[expose] def infoWithPrice (π : ι → Setoid Ω) (Pstar : Ω → ℝ) (i : ι) : Setoid Ω :=
  π i ⊓ pricePartition Pstar

/-- A price mapping `Pstar : Ω → ℝ` is **fully revealing** for partition profile `π` when the
price-induced partition equals the agents' combined information partition: `π_{P*} = π̂`
[PennockSami2007, §26.2.2.3, p. 657]. -/
@[expose] def IsFullyRevealingPrice (π : ι → Setoid Ω) (Pstar : Ω → ℝ) : Prop :=
  pricePartition Pstar = combinedPartition π

/-- When combined information identifies the true state (`π̂ = ⊥`), any injective price mapping
is fully revealing [PennockSami2007, §26.2.2.3, p. 657]. -/
theorem isFullyRevealingPrice_of_injective {π : ι → Setoid Ω} {Pstar : Ω → ℝ}
    (hfull : combinedPartition π = ⊥) (hinj : Function.Injective Pstar) :
    IsFullyRevealingPrice π Pstar := by
  rw [IsFullyRevealingPrice, pricePartition, hfull, Setoid.ker_eq_bot_iff]
  exact hinj

/-- In any fully revealing price mapping (`π_{P*} = π̂`), conditioning on `(π_i, P*)` gives every
agent the exact combined information `π̂` [PennockSami2007, §26.2.2.3, p. 657]. -/
theorem infoWithPrice_eq_combinedPartition_of_isFullyRevealing {π : ι → Setoid Ω} {Pstar : Ω → ℝ}
    (hfr : IsFullyRevealingPrice π Pstar) (i : ι) :
    infoWithPrice π Pstar i = combinedPartition π := by
  rw [infoWithPrice, hfr]
  exact inf_eq_right.mpr (iInf_le π i)

variable [Fintype Ω]

/-- **Rational Expectations Equilibrium** [PennockSami2007, Definition 26.2, p. 656]: given
valuation functions `v : ι → Ω → ℝ` and a market-clearing operator
`clearPrice : (ι → Ω → ℝ) → Ω → ℝ` computing the clearing price from agents' effective valuations
`ṽ_i(ω) = E[v_i | π_i(ω), P*(ω)]`, a price mapping `Pstar : Ω → ℝ` is a rational expectations
equilibrium if `clearPrice ṽ ω = Pstar ω` in every state `ω`. -/
@[expose] def IsREE (P : Ω → ℝ) (π : ι → Setoid Ω) (v : ι → Ω → ℝ)
    (clearPrice : (ι → Ω → ℝ) → Ω → ℝ) (Pstar : Ω → ℝ) : Prop :=
  ∀ ω : Ω,
    clearPrice (fun i ω' => condExp P (infoCell (infoWithPrice π Pstar i) ω') (v i)) ω = Pstar ω

/-- **Omniscient forecast and belief agreement under fully revealing prices**
[PennockSami2007, §26.2.2.3, p. 657]: if `Pstar` is fully revealing, then every agent `i` assigns
the exact omniscient conditional expectation `E[f | π̂(ω)]` to any security `f`, and all agents
hold identical posterior expectations. -/
theorem condExp_infoWithPrice_eq_omniscient_of_isFullyRevealing (P : Ω → ℝ) {π : ι → Setoid Ω}
    {Pstar : Ω → ℝ} (hfr : IsFullyRevealingPrice π Pstar) (f : Ω → ℝ) (i : ι) (ω : Ω) :
    condExp P (infoCell (infoWithPrice π Pstar i) ω) f =
      condExp P (infoCell (combinedPartition π) ω) f := by
  rw [infoWithPrice_eq_combinedPartition_of_isFullyRevealing hfr i]

/-- **Strong-form efficient market characterization of a fully revealing REE**
[PennockSami2007, §26.2.2.3, pp. 656–657]: for a common-value security `f` and any clearing
operator that outputs `c` whenever all agents value the security at `c`, a fully revealing price
mapping `Pstar` is a rational expectations equilibrium if and only if `Pstar ω` equals the
omniscient forecast `E[f | π̂(ω)]` in every state `ω`. -/
theorem isREE_commonValue_iff_omniscient_of_isFullyRevealing {P : Ω → ℝ} {π : ι → Setoid Ω}
    {f : Ω → ℝ} {clearPrice : (ι → Ω → ℝ) → Ω → ℝ}
    (hunanimous : ∀ (g : ι → Ω → ℝ) (ω : Ω) (c : ℝ), (∀ i, g i ω = c) → clearPrice g ω = c)
    {Pstar : Ω → ℝ} (hfr : IsFullyRevealingPrice π Pstar) :
    IsREE P π (fun _ => f) clearPrice Pstar ↔
      ∀ ω, Pstar ω = condExp P (infoCell (combinedPartition π) ω) f := by
  constructor
  · intro hree ω
    have hval := hunanimous
      (fun i ω' => condExp P (infoCell (infoWithPrice π Pstar i) ω') f) ω
      (condExp P (infoCell (combinedPartition π) ω) f)
      fun i => condExp_infoWithPrice_eq_omniscient_of_isFullyRevealing P hfr f i ω
    exact (hree ω).symm.trans hval
  · intro hP ω
    rw [hP ω]
    exact hunanimous _ ω _ fun i =>
      condExp_infoWithPrice_eq_omniscient_of_isFullyRevealing P hfr f i ω

end REE

/-! ### Milgrom–Stokey No-Trade Theorem and Sharpness (§26.2.2.3, p. 657) -/

section NoTrade

variable {Ω ι : Type*} [Fintype Ω]

/-- **Milgrom–Stokey No-Trade Theorem** (Milgrom–Stokey 1982; [PennockSami2007, §26.2.2.3 &
§26.7, pp. 657, 671]): suppose finitely many risk-neutral Bayesian agents share a nonnegative
common prior `P` and execute a trade `t : ι → Ω → ℝ` that is zero-sum on a common-knowledge event
`E` (`∀ ω ∈ E, ∑ i, t i ω = 0`). If the trade is interim individually rational for every agent
on positive-probability states of `E` (`∀ i, ∀ ω ∈ E, 0 < P ω → 0 ≤ E[t_i | π_i(ω)]`), then
every agent has **zero** interim expected gain from trade on every positive-probability state in
`E`. In particular, no strictly mutually beneficial speculative trade can occur. -/
theorem milgrom_stokey_no_trade [Fintype ι] {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω)
    {π : ι → Setoid Ω} {E : Finset Ω} (hE : IsCommonKnowledgeEvent π E)
    {t : ι → Ω → ℝ} (hzero : ∀ ω ∈ E, ∑ i : ι, t i ω = 0)
    (hir : ∀ i : ι, ∀ ω ∈ E, 0 < P ω → 0 ≤ condExp P (infoCell (π i) ω) (t i)) :
    ∀ i : ι, ∀ ω ∈ E, 0 < P ω → condExp P (infoCell (π i) ω) (t i) = 0 := by
  have hterm_nonneg (i : ι) (ω : Ω) (hω : ω ∈ E) :
      0 ≤ P ω * condExp P (infoCell (π i) ω) (t i) := by
    rcases (hP ω).lt_or_eq with hpos | hzeroP
    · exact mul_nonneg hpos.le (hir i ω hω hpos)
    · rw [← hzeroP, zero_mul]
  have hagent_nonneg (i : ι) : 0 ≤ ∑ ω ∈ E, P ω * condExp P (infoCell (π i) ω) (t i) :=
    sum_nonneg fun ω hω => hterm_nonneg i ω hω
  have hsum_zero : ∑ i : ι, ∑ ω ∈ E, P ω * condExp P (infoCell (π i) ω) (t i) = 0 := by
    calc ∑ i : ι, ∑ ω ∈ E, P ω * condExp P (infoCell (π i) ω) (t i)
        = ∑ i : ι, ∑ ω ∈ E, P ω * t i ω :=
          sum_congr rfl fun i _ => sum_mul_condExp_infoCell_eq hP (hE i) (t i)
      _ = ∑ ω ∈ E, ∑ i : ι, P ω * t i ω := sum_comm
      _ = ∑ ω ∈ E, P ω * ∑ i : ι, t i ω := sum_congr rfl fun ω _ => (mul_sum ..).symm
      _ = 0 := sum_eq_zero fun ω hω => by rw [hzero ω hω, mul_zero]
  intro i ω hω hPω
  have hi_zero : ∑ ω' ∈ E, P ω' * condExp P (infoCell (π i) ω') (t i) = 0 :=
    (sum_eq_zero_iff_of_nonneg fun j _ => hagent_nonneg j).mp hsum_zero i (mem_univ i)
  have hω_zero : P ω * condExp P (infoCell (π i) ω) (t i) = 0 :=
    (sum_eq_zero_iff_of_nonneg fun ω' hω' => hterm_nonneg i ω' hω').mp hi_zero ω hω
  exact (mul_eq_zero.mp hω_zero).resolve_left hPω.ne'

/-- **Sharpness of the common-prior hypothesis** (original mathematical companion to
[PennockSami2007, §26.2.2.3, p. 657]): whenever two agents hold distinct probability priors
`P₁ ≠ P₂` on a finite state space `Ω`, there exists a zero-sum trade `t : Fin 2 → Ω → ℝ`
(`∀ ω, t 0 ω + t 1 ω = 0`) yielding strictly positive expected profit for both agents
(equal to `(1 / 2) * ∑ ω, (P₁ ω - P₂ ω) ^ 2 > 0`), even with no private information. -/
theorem exists_strict_zeroSum_trade_of_ne_prior {P₁ P₂ : Ω → ℝ}
    (hP₁ : IsMixedStrategy P₁) (hP₂ : IsMixedStrategy P₂) (hne : P₁ ≠ P₂) :
    ∃ t : Fin 2 → Ω → ℝ, (∀ ω, t 0 ω + t 1 ω = 0) ∧
      0 < ∑ ω, P₁ ω * t 0 ω ∧ 0 < ∑ ω, P₂ ω * t 1 ω := by
  let a : ℝ := ∑ ω, P₁ ω * (P₁ ω - P₂ ω)
  let b : ℝ := ∑ ω, P₂ ω * (P₂ ω - P₁ ω)
  let c : ℝ := (a - b) / 2
  let t : Fin 2 → Ω → ℝ := ![fun ω => (P₁ ω - P₂ ω) - c, fun ω => (P₂ ω - P₁ ω) + c]
  have hne_pt : ∃ ω, P₁ ω ≠ P₂ ω := Function.ne_iff.mp hne
  obtain ⟨ω₀, hω₀⟩ := hne_pt
  have hab_eq : a + b = ∑ ω, (P₁ ω - P₂ ω) ^ 2 := by
    simp only [a, b, ← sum_add_distrib]
    exact sum_congr rfl fun ω _ => by ring
  have hab_pos : 0 < a + b := by
    rw [hab_eq]
    exact sum_pos' (fun _ _ => sq_nonneg _)
      ⟨ω₀, mem_univ ω₀, sq_pos_of_ne_zero (sub_ne_zero.mpr hω₀)⟩
  refine ⟨t, fun ω => by simp only [t, Matrix.cons_val_zero, Matrix.cons_val_one]; ring, ?_, ?_⟩
  · have h0 : ∑ ω, P₁ ω * t 0 ω = a - c := by
      simp only [t, Matrix.cons_val_zero, mul_sub, sum_sub_distrib, ← sum_mul, hP₁.sum_eq_one,
        one_mul, a]
    linarith [show a - c = (a + b) / 2 by simp only [c]; ring]
  · have h1 : ∑ ω, P₂ ω * t 1 ω = b + c := by
      simp only [t, Matrix.cons_val_one, Matrix.cons_val_zero, mul_add, sum_add_distrib, ← sum_mul,
        hP₂.sum_eq_one, one_mul, b]
    linarith [show b + c = (a + b) / 2 by simp only [c]; ring]

end NoTrade

end Cslib.GameTheory.PredictionMarket
