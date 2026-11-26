/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.Online.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Agent-independent posted-price schedules and geometric threshold online auctions

This module formalizes two online pricing constructions from [Parkes2007] (§16.3, Exercise 16.3,
and §16.3.3, locators not verified against primary PDF):

1. **Agent-independent price schedules** (`PriceSchedule`): each agent `i` faces nonnegative
   per-period prices `qᵢᵗ(θ₋ᵢ)` independent of `θᵢ`. Allocating agent `i` to the earliest active
   period `t ∈ [aᵢ, dᵢ]` with `qᵢᵗ(θ₋ᵢ) ≤ vᵢ` yields an online-monotone policy whose online
   critical value equals `⨅ t ∈ [aᵢ, dᵢ], ENNReal.ofReal (qᵢᵗ(θ₋ᵢ))`, so pairing it with critical
   payments is DSIC, IR, NPT, and loser-zero under no-early-arrival and no-late-departure
   misreports ([Parkes2007], Exercise 16.3, locator not verified against primary PDF). When the
   price schedule is nondecreasing in `t`, immediate posted-price charging at arrival `aᵢ` equals
   the critical payment and is DSIC even under *arbitrary departure* misreports
   (`IsDSICNoEarlyArrival`).
2. **Threshold-price single-item online auction** (`thresholdSingleItemMechanism`): a single
   non-expiring item is sold to the first arriving agent (ties broken by smallest index) whose
   value meets a fixed threshold `p ≥ 0`, allocated at its arrival period at price `p`. For every
   `p ≥ 0`, the mechanism is causal, allocates at most one agent, and is strongly truthful under
   arbitrary departure misreports (`IsDSICNoEarlyArrival`). Choosing `p = L · 2^k` uniformly over
   `k ∈ {0, …, m - 1}` yields a randomized strongly truthful auction that is `2m`-competitive
   (i.e. `O(log(H / L))`-competitive) for both social welfare and revenue whenever the maximum
   valuation lies in `[L, L · 2^m)`.

## Main definitions

* `PriceSchedule`, `PriceSchedule.policy`, `PriceSchedule.arrivalMechanism`.
* `ThresholdWins`, `thresholdSingleItemPolicy`, `thresholdSingleItemMechanism`: fixed-threshold
  single-item winning predicate, causal policy, and strongly truthful mechanism (scored via
  `welfare` and `revenue` from `CslibFrontier.GameTheory.Mechanism.Online.Basic`).

## Main results

* `PriceSchedule.policy_isMonotone`, `PriceSchedule.criticalValue_eq_iInf`,
  `PriceSchedule.criticalMechanism_isDSIC` ([Parkes2007], Exercise 16.3, locator not verified
  against primary PDF).
* `PriceSchedule.arrivalMechanism_isDSICNoEarlyArrival`: nondecreasing agent-independent prices
  are truthful at arrival even under arbitrary departure misreports.
* `thresholdSingleItemPolicy_isCausal`, `thresholdSingleItemPolicy_atMostOne`,
  `thresholdSingleItemMechanism_isDSICNoEarlyArrival`, `thresholdSingleItemMechanism_isIR`,
  `thresholdSingleItemMechanism_isNPT`, `thresholdSingleItemMechanism_isLoserZero`: causality,
  single-unit feasibility, truthfulness under arbitrary departures, IR, NPT, and loser-zero.
* `le_welfare_and_revenue_threshold`, `geometricThreshold_expected_welfare`,
  `geometricThreshold_expected_revenue`: `2m`-competitive welfare and revenue bounds for the
  uniform geometric threshold auction over `[L, L · 2^m)`.

## References

* [D. C. Parkes, *Online Mechanisms*][Parkes2007]
* [R. Lavi and N. Nisan, *Competitive Analysis of Incentive Compatible On-Line
  Auctions*][LaviNisan2000]
-/

open scoped BigOperators ENNReal

public section

namespace Cslib.GameTheory.OnlineMechanism

/-! ### Agent-Independent Price Schedules -/

/-- An agent-independent nonnegative online price schedule `qᵢᵗ(θ₋ᵢ)` over finite horizon `Fin T`
([Parkes2007], Exercise 16.3, locator not verified against primary PDF). -/
structure PriceSchedule (ι : Type*) [DecidableEq ι] (T : ℕ) where
  /-- Price offered to agent `i` at period `t` given others' reports `θ₋ᵢ`. -/
  price : ι → Fin T → (ι → AgentType (Fin T)) → ℝ
  /-- Prices are nonnegative. -/
  price_nonneg : ∀ i t θ, 0 ≤ price i t θ
  /-- Independence from agent `i`'s own report. -/
  price_update : ∀ i t θ θ', price i t (Function.update θ i θ') = price i t θ

namespace PriceSchedule

variable {ι : Type*} [DecidableEq ι] {T : ℕ}

open Classical in
/-- Allocation policy induced by an agent-independent price schedule: allocates agent `i` to the
earliest period `t ∈ [aᵢ, dᵢ]` at which `price i t θ ≤ vᵢ`, or `none` if no such period exists. -/
noncomputable def policy (q : PriceSchedule ι T) : Policy ι (Fin T) where
  alloc θ i :=
    let S := Finset.univ.filter fun t : Fin T => (θ i).InWindow t ∧ q.price i t θ ≤ (θ i).value
    if h : S.Nonempty then some (S.min' h) else none
  alloc_in_window θ i t ht := by
    dsimp only at ht
    split_ifs at ht with h
    · have hteq := Option.some.inj ht
      rw [← hteq]
      exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2.1

theorem policy_alloc_isSome_iff (q : PriceSchedule ι T) (θ : ι → AgentType (Fin T)) (i : ι) :
    (q.policy.alloc θ i).isSome ↔
      ∃ t : Fin T, (θ i).InWindow t ∧ q.price i t θ ≤ (θ i).value := by
  classical
  simp only [policy]
  split_ifs with h <;> simpa [Finset.Nonempty] using h

/-- Any agent-independent price schedule induces an online-monotone policy. -/
theorem policy_isMonotone (q : PriceSchedule ι T) : q.policy.IsMonotone := by
  intro i θ θ₁ θ₂ ha hd hv hwin
  rw [q.policy_alloc_isSome_iff] at hwin ⊢
  obtain ⟨t, hwin₁, hle₁⟩ := hwin
  simp only [Function.update_self, q.price_update] at hwin₁ hle₁ ⊢
  exact ⟨t, ⟨ha.trans hwin₁.1, hwin₁.2.trans hd⟩, hle₁.trans hv.le⟩

/-- The online critical value of `q.policy` on window `[a, d]` equals the minimum posted price
over `t ∈ [a, d]` ([Parkes2007], Exercise 16.3, locator not verified against primary PDF). -/
theorem criticalValue_eq_iInf (q : PriceSchedule ι T) (θ : ι → AgentType (Fin T)) (i : ι)
    (a d : Fin T) (had : a ≤ d) :
    q.policy.criticalValue θ i a d had =
      ⨅ (t : Fin T) (_ : a ≤ t ∧ t ≤ d), ENNReal.ofReal (q.price i t θ) := by
  apply le_antisymm
  · refine le_iInf₂ fun t ht => q.policy.criticalValue_le_of_isSome (q.price_nonneg i t θ) ?_
    simpa only [q.policy_alloc_isSome_iff, Function.update_self, q.price_update] using
      ⟨t, ht, le_rfl⟩
  · refine le_sInf fun _ ⟨r, _, heq, hwin⟩ => heq ▸ ?_
    obtain ⟨t, ht, hle⟩ := by
      simpa only [q.policy_alloc_isSome_iff, Function.update_self, q.price_update] using hwin
    exact iInf₂_le_of_le t ht (ENNReal.ofReal_le_ofReal hle)

/-- Pairing an agent-independent price schedule with its critical payment is DSIC under
no-early-arrival and no-late-departure misreports ([Parkes2007], Exercise 16.3, locator not
verified against primary PDF). -/
theorem criticalMechanism_isDSIC (q : PriceSchedule ι T) :
    q.policy.criticalMechanism.IsDSIC :=
  Policy.criticalMechanism_isDSIC q.policy_isMonotone

/-- Immediate arrival-time posted-price mechanism: uses `q.policy` and charges winners the
arrival-period price `q.price i (θ i).arrival θ` (and `0` to losers). -/
@[expose] noncomputable def arrivalMechanism (q : PriceSchedule ι T) : Mechanism ι (Fin T) where
  policy := q.policy
  payment θ i := if (q.policy.alloc θ i).isSome then q.price i (θ i).arrival θ else 0

/-- When an agent-independent price schedule is nondecreasing in time `t`, the arrival-time
posted-price mechanism allocates winners at arrival, charges the arrival price, and is DSIC even
under *arbitrary departure* misreports (`IsDSICNoEarlyArrival`). -/
theorem arrivalMechanism_isDSICNoEarlyArrival (q : PriceSchedule ι T)
    (hinc : ∀ i θ t₁ t₂, t₁ ≤ t₂ → q.price i t₁ θ ≤ q.price i t₂ θ) :
    q.arrivalMechanism.IsDSICNoEarlyArrival := by
  have halloc_arr (θ : ι → AgentType (Fin T)) (i : ι) :
      (q.policy.alloc θ i).isSome ↔ q.price i (θ i).arrival θ ≤ (θ i).value :=
    (q.policy_alloc_isSome_iff θ i).trans ⟨fun ⟨t, ht, hle⟩ => (hinc i θ _ t ht.1).trans hle,
      fun hle => ⟨_, ⟨le_rfl, (θ i).arrival_le_departure⟩, hle⟩⟩
  have halloc_eq (θ : ι → AgentType (Fin T)) (i : ι)
      (hle : q.price i (θ i).arrival θ ≤ (θ i).value) :
      q.policy.alloc θ i = some (θ i).arrival := by
    classical
    simp only [policy]
    set S := Finset.univ.filter fun t : Fin T => (θ i).InWindow t ∧ q.price i t θ ≤ (θ i).value
    have hmem : (θ i).arrival ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨le_rfl, (θ i).arrival_le_departure⟩, hle⟩
    have hne : S.Nonempty := ⟨(θ i).arrival, hmem⟩
    simp only [hne, ↓reduceDIte, Option.some.injEq]
    exact le_antisymm (Finset.min'_le S _ hmem) (Finset.mem_filter.mp (Finset.min'_mem S hne)).2.1.1
  intro i θ θ_true ha
  set θ_t := Function.update θ i θ_true
  -- Truthful utility is at least `max 0 (value - arrival price)`.
  have htrue : 0 ≤ q.arrivalMechanism.utility i θ_true θ_t ∧
      θ_true.value - q.price i θ_true.arrival θ ≤ q.arrivalMechanism.utility i θ_true θ_t := by
    by_cases hle : q.price i θ_true.arrival θ ≤ θ_true.value
    · have hle' : q.price i (θ_t i).arrival θ_t ≤ (θ_t i).value := by
        simpa only [θ_t, Function.update_self, q.price_update] using hle
      have hwin_arr : θ_true.InWindow θ_true.arrival := ⟨le_rfl, θ_true.arrival_le_departure⟩
      simp only [Mechanism.utility, arrivalMechanism, halloc_eq θ_t i hle', θ_t,
        Function.update_self, AgentType.realizedValue_some_of_inWindow hwin_arr,
        Option.isSome_some, ↓reduceIte, q.price_update, le_refl, and_true]
      linarith
    · have hnone : q.policy.alloc θ_t i = none := by
        rw [← Option.not_isSome_iff_eq_none, halloc_arr]
        simpa only [θ_t, Function.update_self, q.price_update] using hle
      simp only [Mechanism.utility, arrivalMechanism, hnone, AgentType.realizedValue_none,
        Option.isSome_none, Bool.false_eq_true, ↓reduceIte, sub_self, le_rfl, true_and]
      linarith
  by_cases hrep_win : q.price i (θ i).arrival θ ≤ (θ i).value
  · conv_lhs =>
      simp only [Mechanism.utility, arrivalMechanism, halloc_eq θ i hrep_win, Option.isSome_some,
        ↓reduceIte]
    linarith [θ_true.realizedValue_le_value (some (θ i).arrival),
      hinc i θ θ_true.arrival (θ i).arrival ha, htrue.2]
  · have hrep_none : q.policy.alloc θ i = none :=
      Option.not_isSome_iff_eq_none.mp ((halloc_arr θ i).not.mpr hrep_win)
    rw [Mechanism.utility_of_alloc_none _ hrep_none]
    simpa only [arrivalMechanism, hrep_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      neg_zero] using htrue.1

end PriceSchedule

/-! ### Fixed-Threshold and Randomized Geometric-Threshold Single-Item Online Auctions -/

section ThresholdSingleItemCore

variable {ι : Type*} [LinearOrder ι] {T : ℕ}

/-- Agent `i` wins the fixed-threshold single-item online auction at price `p`: `p ≤ vᵢ` and no
other qualifying agent arrives strictly earlier (or arrives simultaneously with a smaller index). -/
@[expose] def ThresholdWins (p : ℝ) (θ : ι → AgentType (Fin T)) (i : ι) : Prop :=
  p ≤ (θ i).value ∧
    ∀ j : ι, p ≤ (θ j).value →
      ¬ ((θ j).arrival < (θ i).arrival ∨ ((θ j).arrival = (θ i).arrival ∧ j < i))

theorem ThresholdWins.unique {p : ℝ} {θ : ι → AgentType (Fin T)} {i j : ι}
    (hi : ThresholdWins p θ i) (hj : ThresholdWins p θ j) : i = j := by
  by_contra hne
  rcases lt_trichotomy (θ i).arrival (θ j).arrival with h | h | h
  · exact hj.2 i hi.1 (Or.inl h)
  · rcases lt_or_gt_of_ne hne with hij | hji
    · exact hj.2 i hi.1 (Or.inr ⟨h, hij⟩)
    · exact hi.2 j hj.1 (Or.inr ⟨h.symm, hji⟩)
  · exact hi.2 j hj.1 (Or.inl h)

open Classical in
/-- Fixed-threshold single-item online allocation policy: sells one non-expiring item to the first
arriving agent whose value is at least `p`, allocating at its arrival period. -/
@[expose] noncomputable def thresholdSingleItemPolicy (p : ℝ) : Policy ι (Fin T) where
  alloc θ i := if ThresholdWins p θ i then some (θ i).arrival else none
  alloc_in_window θ i t h := by
    split_ifs at h with hw
    · have ht := Option.some.inj h
      rw [← ht]
      exact ⟨le_rfl, (θ i).arrival_le_departure⟩

/-- Fixed-threshold single-item online auction: allocates via `thresholdSingleItemPolicy p` and
charges the winner `p` (and losers `0`). -/
@[expose] noncomputable def thresholdSingleItemMechanism (p : ℝ) : Mechanism ι (Fin T) where
  policy := thresholdSingleItemPolicy p
  payment θ i := if ((thresholdSingleItemPolicy p).alloc θ i).isSome then p else 0

/-- At most one agent is allocated across all periods under `thresholdSingleItemPolicy p`. -/
theorem thresholdSingleItemPolicy_atMostOne (p : ℝ) (θ : ι → AgentType (Fin T))
    {i j : ι} {t₁ t₂ : Fin T}
    (hi : (thresholdSingleItemPolicy p).alloc θ i = some t₁)
    (hj : (thresholdSingleItemPolicy p).alloc θ j = some t₂) : i = j := by
  classical
  simp only [thresholdSingleItemPolicy] at hi hj
  split_ifs at hi with hwi
  split_ifs at hj with hwj
  exact hwi.unique hwj

private theorem thresholdSingleItemPolicy_alloc_of_agree {p : ℝ} {t : Fin T}
    {θ θ' : ι → AgentType (Fin T)}
    (hagree : ∀ j, (θ j).arrival ≤ t ∨ (θ' j).arrival ≤ t → θ j = θ' j) {i : ι}
    (h : (thresholdSingleItemPolicy p).alloc θ i = some t) :
    (thresholdSingleItemPolicy p).alloc θ' i = some t := by
  classical
  simp only [thresholdSingleItemPolicy] at h ⊢
  split_ifs at h with hwi
  have hta : (θ i).arrival = t := Option.some.inj h
  have hi_eq : θ i = θ' i := hagree i (Or.inl hta.le)
  have hwi' : ThresholdWins p θ' i := by
    refine ⟨hi_eq ▸ hwi.1, fun j hj hba => ?_⟩
    have hja : (θ' j).arrival ≤ t :=
      (hba.elim le_of_lt fun h => h.1.le).trans_eq (hi_eq ▸ hta)
    have hj_eq : θ j = θ' j := hagree j (Or.inr hja)
    exact hwi.2 j (hj_eq.symm ▸ hj) (hj_eq.symm ▸ hi_eq.symm ▸ hba)
  simp only [hwi', ↓reduceIte, ← hi_eq, hta]

/-- `thresholdSingleItemPolicy p` is online-causal: whether `i` is allocated at period `t` depends
only on agents who have arrived by period `t`. -/
theorem thresholdSingleItemPolicy_isCausal (p : ℝ) :
    (thresholdSingleItemPolicy (ι := ι) (T := T) p).IsCausal := fun _ _ _ hagree _ =>
  ⟨thresholdSingleItemPolicy_alloc_of_agree hagree,
    thresholdSingleItemPolicy_alloc_of_agree fun j hj => (hagree j hj.symm).symm⟩

theorem thresholdSingleItemMechanism_isNPT {p : ℝ} (hp : 0 ≤ p) :
    (thresholdSingleItemMechanism (ι := ι) (T := T) p).IsNPT := by
  intro i θ
  dsimp only [thresholdSingleItemMechanism]
  split_ifs <;> linarith

theorem thresholdSingleItemMechanism_isLoserZero (p : ℝ) :
    (thresholdSingleItemMechanism (ι := ι) (T := T) p).IsLoserZero := by
  intro i θ hnone
  simp_all [thresholdSingleItemMechanism]

theorem thresholdSingleItemMechanism_isIR (p : ℝ) :
    (thresholdSingleItemMechanism (ι := ι) (T := T) p).IsIR := by
  classical
  intro i θ
  by_cases hw : ThresholdWins p θ i
  · simp only [Mechanism.utility, thresholdSingleItemMechanism, thresholdSingleItemPolicy, hw,
      ↓reduceIte, Option.isSome_some]
    rw [AgentType.realizedValue_some_of_inWindow ⟨le_rfl, (θ i).arrival_le_departure⟩]
    linarith [hw.1]
  · simp only [Mechanism.utility, thresholdSingleItemMechanism, thresholdSingleItemPolicy, hw,
      ↓reduceIte, AgentType.realizedValue_none, Option.isSome_none, Bool.false_eq_true, sub_self,
      le_rfl]

/-- For every nonnegative threshold `p ≥ 0`, `thresholdSingleItemMechanism p` is strongly truthful
under *no early arrival* and *arbitrary departure* misreports (`IsDSICNoEarlyArrival`). -/
theorem thresholdSingleItemMechanism_isDSICNoEarlyArrival {p : ℝ} (hp : 0 ≤ p) :
    (thresholdSingleItemMechanism (ι := ι) (T := T) p).IsDSICNoEarlyArrival := by
  classical
  intro i θ θ_true ha
  set θ_t := Function.update θ i θ_true
  have htrue_ir : 0 ≤ (thresholdSingleItemMechanism p).utility i θ_true θ_t := by
    simpa only [θ_t, Function.update_self] using
      thresholdSingleItemMechanism_isIR (ι := ι) (T := T) p i θ_t
  by_cases hw_rep : ThresholdWins p θ i
  · by_cases hin : θ_true.InWindow (θ i).arrival
    · conv_lhs =>
        simp only [Mechanism.utility, thresholdSingleItemMechanism, thresholdSingleItemPolicy,
          hw_rep, ↓reduceIte, AgentType.realizedValue_some_of_inWindow hin, Option.isSome_some]
      by_cases hv : p ≤ θ_true.value
      · have hw_true : ThresholdWins p θ_t i := by
          refine ⟨by simpa only [θ_t, Function.update_self] using hv, fun j hj hba => ?_⟩
          by_cases hji : j = i
          · exact hba.elim (fun hlt => lt_irrefl _ (hji ▸ hlt)) fun h => lt_irrefl _ (hji ▸ h.2)
          · simp only [θ_t, Function.update_self, Function.update_of_ne hji] at hj hba
            refine hw_rep.2 j hj ?_
            rcases hba with hlt | ⟨heq, hji_lt⟩
            · exact Or.inl (lt_of_lt_of_le hlt ha)
            · exact (lt_or_eq_of_le ha).elim (fun h => Or.inl (heq ▸ h))
                (fun h => Or.inr ⟨heq.trans h, hji_lt⟩)
        have hwin_arr : θ_true.InWindow θ_true.arrival := ⟨le_rfl, θ_true.arrival_le_departure⟩
        simp only [Mechanism.utility, thresholdSingleItemMechanism, thresholdSingleItemPolicy,
          hw_true, ↓reduceIte, θ_t, Function.update_self, Option.isSome_some,
          AgentType.realizedValue_some_of_inWindow hwin_arr, le_refl]
      · linarith
    · conv_lhs =>
        simp only [Mechanism.utility, thresholdSingleItemMechanism, thresholdSingleItemPolicy,
          hw_rep, ↓reduceIte, AgentType.realizedValue_some_of_not_inWindow hin, Option.isSome_some,
          zero_sub]
      linarith
  · have hnone : (thresholdSingleItemPolicy p).alloc θ i = none := ite_eq_right hw_rep
    rwa [Mechanism.utility_of_alloc_none _ hnone,
      thresholdSingleItemMechanism_isLoserZero p i θ hnone, neg_zero]

/-- Whenever at least one agent in a finite population has value `≥ p`,
`thresholdSingleItemPolicy p` allocates to a unique winner whose value is at least `p`. -/
theorem exists_thresholdWins [Finite ι] {p : ℝ} {θ : ι → AgentType (Fin T)}
    (hex : ∃ i : ι, p ≤ (θ i).value) :
    ∃ i : ι, ThresholdWins p θ i := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set Q := Finset.univ.filter fun i : ι => p ≤ (θ i).value
  obtain ⟨i₀, hi₀⟩ := hex
  have hQne : Q.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀⟩⟩
  obtain ⟨t_min, ht_mem, ht_min⟩ := Finset.exists_min_image Q (fun i => (θ i).arrival) hQne
  set Qmin := Q.filter fun i : ι => (θ i).arrival = (θ t_min).arrival
  have hQmin_ne : Qmin.Nonempty := ⟨t_min, Finset.mem_filter.mpr ⟨ht_mem, rfl⟩⟩
  obtain ⟨hwQ, hw_arr⟩ := Finset.mem_filter.mp (Finset.min'_mem Qmin hQmin_ne)
  refine ⟨Qmin.min' hQmin_ne, (Finset.mem_filter.mp hwQ).2, fun j hj hba => ?_⟩
  have hjQ : j ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  rcases hba with hlt | ⟨heq, hji⟩
  · exact not_lt_of_ge (ht_min j hjQ) (hw_arr ▸ hlt)
  · exact not_lt_of_ge (Finset.min'_le Qmin j (Finset.mem_filter.mpr ⟨hjQ, heq.trans hw_arr⟩)) hji

end ThresholdSingleItemCore

section GeometricThreshold

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {T : ℕ}

/-- Whenever some agent has value at least `p`, the fixed-threshold single-item auction achieves
both welfare and revenue at least `p`. -/
theorem le_welfare_and_revenue_threshold {p : ℝ} (hp : 0 ≤ p)
    {θ : ι → AgentType (Fin T)} (hex : ∃ i : ι, p ≤ (θ i).value) :
    p ≤ welfare θ ((thresholdSingleItemPolicy p).alloc θ) ∧
      p ≤ revenue (thresholdSingleItemMechanism p) θ := by
  classical
  obtain ⟨w, hw⟩ := exists_thresholdWins hex
  have hw_alloc : (thresholdSingleItemPolicy p).alloc θ w = some (θ w).arrival := ite_eq_left hw
  have hw_val : (θ w).realizedValue ((thresholdSingleItemPolicy p).alloc θ w) = (θ w).value :=
    hw_alloc ▸ AgentType.realizedValue_some_of_inWindow ⟨le_rfl, (θ w).arrival_le_departure⟩
  have hw_pay : (thresholdSingleItemMechanism p).payment θ w = p := by
    simp only [thresholdSingleItemMechanism, hw_alloc, Option.isSome_some, ↓reduceIte]
  exact ⟨(hw.1.trans_eq hw_val.symm).trans
    (Finset.single_le_sum (fun i _ => (θ i).realizedValue_nonneg _) (Finset.mem_univ w)),
    hw_pay.symm.le.trans (Finset.single_le_sum
      (fun i _ => thresholdSingleItemMechanism_isNPT hp i θ) (Finset.mem_univ w))⟩

/-- Helper: every real `v ∈ [L, L · 2^m)` falls in a geometric bucket
`[L · 2^k, L · 2^(k + 1))` for some `k : Fin m`. -/
private theorem exists_geometric_bucket {L v : ℝ} {m : ℕ}
    (hlo : L ≤ v) (hhi : v < L * (2 : ℝ) ^ m) :
    ∃ k : Fin m, L * (2 : ℝ) ^ k.val ≤ v ∧ v < L * (2 : ℝ) ^ (k.val + 1) := by
  induction m with
  | zero => simp only [pow_zero, mul_one] at hhi; linarith
  | succ m ih =>
    rcases le_or_gt (L * (2 : ℝ) ^ m) v with hmid | hmid
    · exact ⟨Fin.last m, hmid, hhi⟩
    · exact (ih hmid).elim fun k hk => ⟨k.castSucc, hk⟩

/-- Shared geometric-bucket averaging step for `2m`-competitive bounds over `[L, L · 2^m)`. -/
private theorem geometricThreshold_expected_bound {L v : ℝ} (hL : 0 < L) {m : ℕ} (hm : 0 < m)
    (hlo : L ≤ v) (hhi : v < L * (2 : ℝ) ^ m) (f : ℝ → ℝ)
    (hf_nonneg : ∀ p, 0 ≤ p → 0 ≤ f p)
    (hf_ge : ∀ p, 0 ≤ p → p ≤ v → p ≤ f p) :
    v ≤ (2 * (m : ℝ)) * ((∑ k : Fin m, f (L * (2 : ℝ) ^ k.val)) / (m : ℝ)) := by
  obtain ⟨kstar, hkle, hklt⟩ := exists_geometric_bucket hlo hhi
  have hp_nonneg : ∀ k : Fin m, 0 ≤ L * (2 : ℝ) ^ k.val := fun k => by positivity
  have hsum_ge : L * (2 : ℝ) ^ kstar.val ≤ ∑ k : Fin m, f (L * (2 : ℝ) ^ k.val) :=
    (hf_ge _ (hp_nonneg kstar) hkle).trans (Finset.single_le_sum
      (fun k _ => hf_nonneg _ (hp_nonneg k)) (Finset.mem_univ kstar))
  have hpow : L * (2 : ℝ) ^ (kstar.val + 1) = 2 * (L * (2 : ℝ) ^ kstar.val) := by ring
  rw [mul_assoc, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hm.ne')]
  linarith

/-- Uniform geometric threshold single-item online auction: choosing threshold `p_k = L · 2^k`
uniformly over `k : Fin m` (`0 < L`, `0 < m`) is `2m`-competitive for social welfare against the
offline single-item optimum `v_max = max_i v_i` whenever `v_max ∈ [L, L · 2^m)`. Each realization
`k` is causal and strongly truthful even under arbitrary departure misreports
(`thresholdSingleItemMechanism_isDSICNoEarlyArrival`). -/
theorem geometricThreshold_expected_welfare {L : ℝ} (hL : 0 < L) {m : ℕ} (hm : 0 < m)
    {θ : ι → AgentType (Fin T)} {i_max : ι}
    (hlo : L ≤ (θ i_max).value) (hhi : (θ i_max).value < L * (2 : ℝ) ^ m) :
    (θ i_max).value ≤
      (2 * (m : ℝ)) *
        ((∑ k : Fin m,
            welfare θ ((thresholdSingleItemPolicy (L * (2 : ℝ) ^ k.val)).alloc θ)) /
          (m : ℝ)) :=
  geometricThreshold_expected_bound hL hm hlo hhi
    (fun p => welfare θ ((thresholdSingleItemPolicy p).alloc θ))
    (fun _ _ => welfare_nonneg _ _)
    (fun _ hp hle => (le_welfare_and_revenue_threshold hp ⟨i_max, hle⟩).1)

/-- Uniform geometric threshold single-item online auction: choosing threshold `p_k = L · 2^k`
uniformly over `k : Fin m` (`0 < L`, `0 < m`) is also `2m`-competitive for *seller revenue* against
`v_max = max_i v_i` whenever `v_max ∈ [L, L · 2^m)`. -/
theorem geometricThreshold_expected_revenue {L : ℝ} (hL : 0 < L) {m : ℕ} (hm : 0 < m)
    {θ : ι → AgentType (Fin T)} {i_max : ι}
    (hlo : L ≤ (θ i_max).value) (hhi : (θ i_max).value < L * (2 : ℝ) ^ m) :
    (θ i_max).value ≤
      (2 * (m : ℝ)) *
        ((∑ k : Fin m,
            revenue (thresholdSingleItemMechanism (L * (2 : ℝ) ^ k.val)) θ) /
          (m : ℝ)) :=
  geometricThreshold_expected_bound hL hm hlo hhi
    (fun p => revenue (thresholdSingleItemMechanism p) θ)
    (fun _ hp => revenue_nonneg (thresholdSingleItemMechanism_isNPT hp) θ)
    (fun _ hp hle => (le_welfare_and_revenue_threshold hp ⟨i_max, hle⟩).2)

end GeometricThreshold

end Cslib.GameTheory.OnlineMechanism
