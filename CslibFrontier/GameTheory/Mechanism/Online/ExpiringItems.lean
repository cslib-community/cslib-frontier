/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.Online.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Expiring-items online auctions: Greedy `Auction 2` and competitive lower bounds

In the *expiring-items* online environment ([Parkes2007], Example 16.3 & §16.3.2, locators not
verified against primary PDF), there are `T` discrete periods `Fin T` with `cap t : ℕ` identical
units available in period `t` that expire at the end of period `t` (the canonical single-unit case
has `cap = fun _ => 1`). Each agent `i : ι` wants at most one unit during `[aᵢ, dᵢ]` and derives
value `vᵢ ≥ 0`.

## Main definitions

* `IsExpiringAllocation`: window-feasible and per-period capacity-feasible allocation map.
* `optWelfare`: exact offline optimal social welfare (`welfare`, defined in
  `CslibFrontier.GameTheory.Mechanism.Online.Basic`) over all feasible expiring-items allocations.
* `greedyPolicy`, `greedyMechanism`: Lavi–Nisan / Parkes greedy expiring-items mechanism
  (`Auction 2`), which at each period `t` allocates the `cap t` expiring units to the highest-value
  currently active unallocated agents (breaking ties by smallest index) and charges online critical
  values.

## Main results

* `greedyPolicy_isExpiringFeasible`, `greedyPolicy_isCausal`, `greedyPolicy_isMonotone`:
  `Auction 2` is capacity-feasible, online-causal, and online-monotone for arbitrary period
  capacities `cap : Fin T → ℕ`.
* `greedyMechanism_isDSIC`, `greedyMechanism_isIR`, `greedyMechanism_isNPT`,
  `greedyMechanism_isLoserZero`, `optWelfare_le_two_mul_welfare_greedy`: `Auction 2` is strongly
  truthful (under no-early-arrival and no-late-departure misreports), IR, NPT, loser-zero, and
  `2`-competitive for social welfare ([Parkes2007], Theorem 16.17; [LaviNisan2000], locators not
  verified against primary PDF).
* `no_lt_two_competitive_truthful_expiring`: no deterministic causal, DSIC, IR, loser-zero
  expiring-items mechanism achieves competitive ratio `c < 2` for social welfare, even with `2`
  periods and `3` agents ([Parkes2007], Theorem 16.18, locator not verified against primary PDF).
* `no_competitive_arbitrary_departure_expiring`: when late-departure misreports are allowed
  (`IsDSICNoEarlyArrival`), no deterministic causal, truthful, IR, NPT, loser-zero expiring-items
  mechanism achieves *any* bounded competitive ratio ([Parkes2007], Theorem 16.19, locator not
  verified against primary PDF).

## References

* [D. C. Parkes, *Online Mechanisms*][Parkes2007]
* [R. Lavi and N. Nisan, *Competitive Analysis of Incentive Compatible On-Line
  Auctions*][LaviNisan2000]
* [M. T. Hajiaghayi, R. Kleinberg, and D. C. Parkes, *Adaptive Limited-Supply Online
  Auctions*][HajiaghayiKleinbergParkes2004]
-/

open scoped BigOperators ENNReal

public section

namespace Cslib.GameTheory.OnlineMechanism

section ExpiringModel

variable {ι : Type*} [Fintype ι] {T : ℕ}

/-- A feasible expiring-items allocation for profile `θ` and period capacities `cap : Fin T → ℕ`:
every allocated agent receives a period in its active window, and at most `cap t` agents are
allocated in period `t`. -/
@[expose] def IsExpiringAllocation (cap : Fin T → ℕ) (θ : ι → AgentType (Fin T))
    (f : ι → Option (Fin T)) : Prop :=
  (∀ i t, f i = some t → (θ i).InWindow t) ∧
  ∀ t, (Finset.univ.filter fun i => f i = some t).card ≤ cap t

/-- A policy is capacity-feasible for expiring items with per-period capacities `cap`. -/
@[expose] def Policy.IsExpiringFeasible (cap : Fin T → ℕ) (π : Policy ι (Fin T)) : Prop :=
  ∀ θ, IsExpiringAllocation cap θ (π.alloc θ)

open Classical in
/-- Offline optimal social welfare on profile `θ` with per-period capacities `cap`: the exact
maximum over the finite set of all feasible expiring-items allocations. -/
@[expose] noncomputable def optWelfare (cap : Fin T → ℕ) (θ : ι → AgentType (Fin T)) : ℝ :=
  (Finset.univ.filter (IsExpiringAllocation cap θ)).sup'
    ⟨fun _ => none, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨(fun _ _ h => nomatch h), fun _ => by simp⟩⟩⟩
    (welfare θ)

theorem welfare_le_optWelfare {cap : Fin T → ℕ} {θ : ι → AgentType (Fin T)}
    {f : ι → Option (Fin T)} (hf : IsExpiringAllocation cap θ f) :
    welfare θ f ≤ optWelfare cap θ := by
  classical
  unfold optWelfare
  exact Finset.le_sup' (f := welfare θ) (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf⟩)

theorem exists_optWelfare (cap : Fin T → ℕ) (θ : ι → AgentType (Fin T)) :
    ∃ f : ι → Option (Fin T), IsExpiringAllocation cap θ f ∧ welfare θ f = optWelfare cap θ := by
  classical
  unfold optWelfare
  obtain ⟨f, hfmem, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.univ.filter (IsExpiringAllocation cap θ))
    ⟨fun _ => none, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨(fun _ _ h => nomatch h), fun _ => by simp⟩⟩⟩
    (welfare θ)
  exact ⟨f, (Finset.mem_filter.mp hfmem).2, hmax.symm⟩

end ExpiringModel

/-! ### Lavi–Nisan / Parkes Greedy Expiring-Items Mechanism (`Auction 2`) -/

section TopKHelpers

variable {ι : Type*} [LinearOrder ι] {T : ℕ}

/-- Strict priority order for greedy expiring-items allocation: higher reported value wins, with
ties broken in favor of the smaller agent index. -/
private def Beats (θ : ι → AgentType (Fin T)) (i j : ι) : Prop :=
  (θ j).value < (θ i).value ∨ ((θ j).value = (θ i).value ∧ i < j)

private theorem beats_irrefl (θ : ι → AgentType (Fin T)) (i : ι) : ¬ Beats θ i i := by
  rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h

private theorem beats_trans {θ : ι → AgentType (Fin T)} {i j k : ι}
    (h1 : Beats θ i j) (h2 : Beats θ j k) : Beats θ i k := by
  rcases h1 with h1 | ⟨he1, hl1⟩ <;> rcases h2 with h2 | ⟨he2, hl2⟩
  · exact Or.inl (h2.trans h1)
  · exact Or.inl (he2 ▸ h1)
  · exact Or.inl (he1.symm ▸ h2)
  · exact Or.inr ⟨he2.trans he1, hl1.trans hl2⟩

private theorem beats_trichotomy (θ : ι → AgentType (Fin T)) {i j : ι} (hne : i ≠ j) :
    Beats θ i j ∨ Beats θ j i := by
  rcases lt_trichotomy (θ j).value (θ i).value with hlt | heq | hgt
  · exact Or.inl (Or.inl hlt)
  · rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (Or.inr ⟨heq, h⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, h⟩)
  · exact Or.inr (Or.inl hgt)

private theorem value_le_of_beats {θ : ι → AgentType (Fin T)} {i j : ι} (h : Beats θ i j) :
    (θ j).value ≤ (θ i).value := by
  rcases h with h | ⟨h, _⟩ <;> exact h.le

open Classical in
/-- The rank of agent `i` inside candidate set `A`: the number of agents in `A` that strictly
beat `i`. -/
private noncomputable def rankIn (θ : ι → AgentType (Fin T)) (A : Finset ι) (i : ι) : ℕ :=
  (A.filter fun j => Beats θ j i).card

private theorem rankIn_lt_of_beats {θ : ι → AgentType (Fin T)} {A : Finset ι} {i j : ι}
    (hi : i ∈ A) (h : Beats θ i j) : rankIn θ A i < rankIn θ A j := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨i, Finset.mem_filter.mpr ⟨hi, h⟩, fun hm => beats_irrefl θ i (Finset.mem_filter.mp hm).2⟩
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, beats_trans hx.2 h⟩

private theorem rankIn_injOn (θ : ι → AgentType (Fin T)) (A : Finset ι) :
    Set.InjOn (rankIn θ A) (A : Set ι) := by
  intro i hi j hj heq
  by_contra hne
  rcases beats_trichotomy θ hne with h | h
  · exact ne_of_lt (rankIn_lt_of_beats hi h) heq
  · exact ne_of_gt (rankIn_lt_of_beats hj h) heq

private theorem rankIn_lt_card {θ : ι → AgentType (Fin T)} {A : Finset ι} {i : ι} (hi : i ∈ A) :
    rankIn θ A i < A.card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨i, hi, fun hm => beats_irrefl θ i (Finset.mem_filter.mp hm).2⟩

private theorem image_rankIn_eq_range (θ : ι → AgentType (Fin T)) (A : Finset ι) :
    A.image (rankIn θ A) = Finset.range A.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (rankIn_lt_card hi)
  · rw [Finset.card_range, Finset.card_image_of_injOn (rankIn_injOn θ A)]

open Classical in
/-- The top `k` candidates of `A` under `Beats θ`. -/
private noncomputable def topK (θ : ι → AgentType (Fin T)) (k : ℕ) (A : Finset ι) : Finset ι :=
  A.filter fun i => rankIn θ A i < k

private theorem topK_subset (θ : ι → AgentType (Fin T)) (k : ℕ) (A : Finset ι) :
    topK θ k A ⊆ A :=
  Finset.filter_subset _ _

private theorem card_topK (θ : ι → AgentType (Fin T)) (k : ℕ) (A : Finset ι) :
    (topK θ k A).card = min k A.card := by
  classical
  have hinj : Set.InjOn (rankIn θ A) (topK θ k A : Set ι) :=
    (rankIn_injOn θ A).mono (by exact_mod_cast topK_subset θ k A)
  have himg : (topK θ k A).image (rankIn θ A) = Finset.range (min k A.card) := by
    ext n
    simp only [Finset.mem_image, topK, Finset.mem_filter, Finset.mem_range, lt_min_iff]
    constructor
    · rintro ⟨i, ⟨hi, hlt⟩, rfl⟩
      exact ⟨hlt, rankIn_lt_card hi⟩
    · rintro ⟨hnk, hna⟩
      have hmem : n ∈ A.image (rankIn θ A) := by
        rw [image_rankIn_eq_range]
        exact Finset.mem_range.mpr hna
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmem
      exact ⟨i, ⟨hi, hnk⟩, rfl⟩
  rw [← Finset.card_image_of_injOn hinj, himg, Finset.card_range]

private theorem card_topK_le (θ : ι → AgentType (Fin T)) (k : ℕ) (A : Finset ι) :
    (topK θ k A).card ≤ k := by
  rw [card_topK]
  exact min_le_left _ _

private theorem beats_of_mem_topK_of_not_mem {θ : ι → AgentType (Fin T)} {k : ℕ} {A : Finset ι}
    {g i : ι} (hg : g ∈ topK θ k A) (hi : i ∈ A) (hni : i ∉ topK θ k A) :
    Beats θ g i := by
  have hga : g ∈ A := topK_subset θ k A hg
  have hne : g ≠ i := fun h => hni (h ▸ hg)
  have hrg : rankIn θ A g < k := (Finset.mem_filter.mp hg).2
  have hri : k ≤ rankIn θ A i := by
    have : ¬ rankIn θ A i < k := fun h => hni (Finset.mem_filter.mpr ⟨hi, h⟩)
    omega
  rcases beats_trichotomy θ hne with h | h
  · exact h
  · exfalso
    have := rankIn_lt_of_beats hi h
    omega

/-- Auxiliary lemma for `topK` invariance when an agent `i` is not among the top `k` winners. -/
private theorem topK_eq_erase_of_not_mem {θ : ι → AgentType (Fin T)} {k : ℕ} {A : Finset ι}
    {i : ι} (hni : i ∉ topK θ k A) :
    topK θ k A = topK θ k (A.erase i) := by
  classical
  by_cases hiA : i ∈ A
  swap
  · rw [Finset.erase_eq_of_notMem hiA]
  have hri : k ≤ rankIn θ A i := not_lt.1 fun h => hni (Finset.mem_filter.2 ⟨hiA, h⟩)
  ext j
  by_cases hji : j = i
  · subst hji
    simp only [topK, Finset.mem_filter, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
      iff_false, not_and, not_lt]
    exact fun _ => hri
  -- Erasing `i` lowers the rank of `j` by one exactly when `i` beats `j`.
  have hrank : rankIn θ (A.erase i) j + (if Beats θ i j then 1 else 0) = rankIn θ A j := by
    unfold rankIn
    rw [Finset.filter_erase]
    split_ifs with h
    · exact Finset.card_erase_add_one (Finset.mem_filter.2 ⟨hiA, h⟩)
    · rw [add_zero]
      exact congrArg Finset.card (Finset.erase_eq_of_notMem fun hm => h (Finset.mem_filter.1 hm).2)
  have hlt : Beats θ i j → rankIn θ A i < rankIn θ A j := rankIn_lt_of_beats hiA
  simp only [topK, Finset.mem_filter, Finset.mem_erase, ne_eq, hji, not_false_eq_true, true_and]
  refine and_congr_right fun _ => ?_
  split_ifs at hrank with h
  · have := hlt h
    omega
  · omega

/-- `topK` only depends on the reported values of the candidates. -/
private theorem topK_congr {θ θ' : ι → AgentType (Fin T)} {k : ℕ} {A : Finset ι}
    (h : ∀ j ∈ A, θ j = θ' j) : topK θ k A = topK θ' k A := by
  classical
  have hr : ∀ j ∈ A, rankIn θ A j = rankIn θ' A j := fun j hj =>
    congrArg Finset.card (Finset.filter_congr fun x hx => by simp only [Beats, h x hx, h j hj])
  exact Finset.filter_congr fun j hj => by rw [hr j hj]

end TopKHelpers

section GreedyAuction

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {T : ℕ}

open Classical in
/-- State after running greedy expiring-items allocation through steps `0, …, s - 1`:
returns the set of agents already allocated before step `s`. -/
private noncomputable def greedyAllocatedBefore (cap : Fin T → ℕ)
    (θ : ι → AgentType (Fin T)) : ℕ → Finset ι
  | 0 => ∅
  | s + 1 =>
    if hs : s < T then
      let prev := greedyAllocatedBefore cap θ s
      let active := Finset.univ.filter fun i => i ∉ prev ∧ (θ i).InWindow ⟨s, hs⟩
      prev ∪ topK θ (cap ⟨s, hs⟩) active
    else
      greedyAllocatedBefore cap θ s

open Classical in
/-- The winners chosen by greedy `Auction 2` at period `t : Fin T`. -/
private noncomputable def greedyWinnersAt (cap : Fin T → ℕ)
    (θ : ι → AgentType (Fin T)) (t : Fin T) : Finset ι :=
  let prev := greedyAllocatedBefore cap θ t.val
  let active := Finset.univ.filter fun i => i ∉ prev ∧ (θ i).InWindow t
  topK θ (cap t) active

private theorem greedyAllocatedBefore_succ_eq (cap : Fin T → ℕ) (θ : ι → AgentType (Fin T))
    (t : Fin T) :
    greedyAllocatedBefore cap θ (t.val + 1) =
      greedyAllocatedBefore cap θ t.val ∪ greedyWinnersAt cap θ t := by
  simp only [greedyAllocatedBefore, t.isLt, ↓reduceDIte, greedyWinnersAt]

private theorem greedyAllocatedBefore_mono (cap : Fin T → ℕ) (θ : ι → AgentType (Fin T))
    {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) :
    greedyAllocatedBefore cap θ s₁ ⊆ greedyAllocatedBefore cap θ s₂ := by
  induction h with
  | refl => exact Finset.Subset.rfl
  | @step m _ ih =>
    refine ih.trans ?_
    simp only [greedyAllocatedBefore]
    split_ifs
    · exact Finset.subset_union_left
    · exact Finset.Subset.rfl

private theorem greedyWinnersAt_disjoint_before (cap : Fin T → ℕ) (θ : ι → AgentType (Fin T))
    (t : Fin T) {i : ι} (hi : i ∈ greedyWinnersAt cap θ t) :
    i ∉ greedyAllocatedBefore cap θ t.val := by
  classical
  exact (Finset.mem_filter.mp (topK_subset _ _ _ hi)).2.1

private theorem greedyWinnersAt_inWindow (cap : Fin T → ℕ) (θ : ι → AgentType (Fin T))
    (t : Fin T) {i : ι} (hi : i ∈ greedyWinnersAt cap θ t) :
    (θ i).InWindow t := by
  classical
  exact (Finset.mem_filter.mp (topK_subset _ _ _ hi)).2.2

private theorem greedyWinnersAt_unique (cap : Fin T → ℕ) (θ : ι → AgentType (Fin T))
    {t₁ t₂ : Fin T} {i : ι} (h₁ : i ∈ greedyWinnersAt cap θ t₁)
    (h₂ : i ∈ greedyWinnersAt cap θ t₂) : t₁ = t₂ := by
  by_contra hne
  wlog hlt : t₁ < t₂ generalizing t₁ t₂
  · exact this h₂ h₁ (Ne.symm hne) ((not_lt.1 hlt).lt_of_ne (Ne.symm hne))
  refine greedyWinnersAt_disjoint_before cap θ t₂ h₂ (greedyAllocatedBefore_mono cap θ hlt ?_)
  rw [greedyAllocatedBefore_succ_eq]
  exact Finset.mem_union_right _ h₁

private theorem mem_greedyAllocatedBefore_iff (cap : Fin T → ℕ) (θ : ι → AgentType (Fin T))
    (s : ℕ) (i : ι) :
    i ∈ greedyAllocatedBefore cap θ s ↔
      ∃ t : Fin T, t.val < s ∧ i ∈ greedyWinnersAt cap θ t := by
  induction s with
  | zero => simp [greedyAllocatedBefore]
  | succ k ih =>
    simp only [greedyAllocatedBefore]
    split_ifs with hk
    · rw [Finset.mem_union, ih]
      constructor
      · rintro (⟨t, hlt, ht⟩ | hnow)
        · exact ⟨t, by omega, ht⟩
        · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hnow⟩
      · rintro ⟨t, hlt, ht⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
        exacts [Or.inl ⟨t, hlt', ht⟩, Or.inr ht]
    · rw [ih]
      exact exists_congr fun t => and_congr_left fun _ => by omega

open Classical in
/-- The Lavi–Nisan / Parkes greedy expiring-items online allocation policy (`Auction 2`):
at each period `t`, allocates up to `cap t` expiring units to the highest-value active unallocated
agents, breaking ties by smallest index
([Parkes2007], §16.3.2, Theorem 16.17; [LaviNisan2000], locators not verified against primary PDF).
-/
noncomputable def greedyPolicy (cap : Fin T → ℕ) : Policy ι (Fin T) where
  alloc θ i :=
    if h : ∃ t : Fin T, i ∈ greedyWinnersAt cap θ t then some (Classical.choose h) else none
  alloc_in_window θ i t ht := by
    by_cases h : ∃ s : Fin T, i ∈ greedyWinnersAt cap θ s
    · simp only [h, ↓reduceDIte, Option.some.injEq] at ht
      rw [← ht]
      exact greedyWinnersAt_inWindow cap θ (Classical.choose h) (Classical.choose_spec h)
    · simp only [h, ↓reduceDIte, reduceCtorEq] at ht

private theorem greedyPolicy_alloc_eq_some_iff (cap : Fin T → ℕ) (θ : ι → AgentType (Fin T))
    (i : ι) (t : Fin T) :
    (greedyPolicy cap).alloc θ i = some t ↔ i ∈ greedyWinnersAt cap θ t := by
  classical
  simp only [greedyPolicy]
  split_ifs with hex
  · exact ⟨fun h => Option.some.inj h ▸ Classical.choose_spec hex,
      fun ht => congrArg some (greedyWinnersAt_unique cap θ (Classical.choose_spec hex) ht)⟩
  · exact ⟨nofun, fun ht => absurd ⟨t, ht⟩ hex⟩

open Classical in
/-- Period-by-period specification of `greedyPolicy`: agent `i` is allocated at period `t` if and
only if `i` was not allocated at any earlier period `s < t`, period `t` lies in `i`'s active window,
and strictly fewer than `cap t` other active unallocated agents have strictly higher priority
(higher value, or equal value and smaller index). -/
theorem greedyPolicy_alloc_eq_some_iff_priority (cap : Fin T → ℕ)
    (θ : ι → AgentType (Fin T)) (i : ι) (t : Fin T) :
    (greedyPolicy cap).alloc θ i = some t ↔
      (∀ s : Fin T, s < t → (greedyPolicy cap).alloc θ i ≠ some s) ∧
      (θ i).InWindow t ∧
      (Finset.univ.filter fun j : ι =>
        (∀ s : Fin T, s < t → (greedyPolicy cap).alloc θ j ≠ some s) ∧
        (θ j).InWindow t ∧
        ((θ i).value < (θ j).value ∨ ((θ i).value = (θ j).value ∧ j < i))).card < cap t := by
  classical
  rw [greedyPolicy_alloc_eq_some_iff]
  have hprev : ∀ j : ι,
      j ∉ greedyAllocatedBefore cap θ t.val ↔
        ∀ s : Fin T, s < t → (greedyPolicy cap).alloc θ j ≠ some s := by
    intro j
    rw [mem_greedyAllocatedBefore_iff]
    push Not
    refine forall_congr' fun s => ?_
    simp only [Fin.lt_def, ne_eq, greedyPolicy_alloc_eq_some_iff]
  have hfilt :
      ((Finset.univ.filter fun j : ι =>
          j ∉ greedyAllocatedBefore cap θ t.val ∧ (θ j).InWindow t).filter
        fun j => Beats θ j i) =
      (Finset.univ.filter fun j : ι =>
        (∀ s : Fin T, s < t → (greedyPolicy cap).alloc θ j ≠ some s) ∧
        (θ j).InWindow t ∧
        ((θ i).value < (θ j).value ∨ ((θ i).value = (θ j).value ∧ j < i))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hprev, Beats, and_assoc]
  unfold greedyWinnersAt topK rankIn
  rw [Finset.mem_filter, Finset.mem_filter, hfilt]
  simp only [Finset.mem_univ, true_and, hprev, and_assoc]

/-- Greedy `Auction 2` is capacity-feasible for expiring items. -/
theorem greedyPolicy_isExpiringFeasible (cap : Fin T → ℕ) :
    (greedyPolicy (ι := ι) cap).IsExpiringFeasible cap := by
  intro θ
  refine ⟨fun i t h => (greedyPolicy cap).alloc_in_window θ i t h, fun t => ?_⟩
  have hsub :
      Finset.univ.filter (fun i => (greedyPolicy cap).alloc θ i = some t) =
        greedyWinnersAt cap θ t := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, greedyPolicy_alloc_eq_some_iff]
  rw [hsub]
  exact card_topK_le _ _ _

private theorem greedyWinnersAt_eq_of_agree {ι : Type*} [Fintype ι] [LinearOrder ι] {T : ℕ}
    (cap : Fin T → ℕ) {θ θ' : ι → AgentType (Fin T)} (t : Fin T)
    (hprev : greedyAllocatedBefore cap θ t.val = greedyAllocatedBefore cap θ' t.val)
    (hagree : ∀ j, (θ j).arrival ≤ t ∨ (θ' j).arrival ≤ t → θ j = θ' j) :
    greedyWinnersAt cap θ t = greedyWinnersAt cap θ' t := by
  classical
  have hactive :
      (Finset.univ.filter fun j => j ∉ greedyAllocatedBefore cap θ t.val ∧ (θ j).InWindow t) =
        (Finset.univ.filter fun j =>
          j ∉ greedyAllocatedBefore cap θ' t.val ∧ (θ' j).InWindow t) := by
    refine Finset.filter_congr fun j _ => ?_
    rw [hprev]
    exact and_congr_right fun _ =>
      ⟨fun hw => hagree j (.inl hw.1) ▸ hw, fun hw => (hagree j (.inr hw.1)).symm ▸ hw⟩
  unfold greedyWinnersAt
  dsimp only
  rw [hactive]
  exact topK_congr fun j hj => hagree j (.inr (Finset.mem_filter.mp hj).2.2.1)

/-- Greedy `Auction 2` is online-causal: allocations at period `t` depend only on agents whose
reported arrival is at most `t`. -/
theorem greedyPolicy_isCausal (cap : Fin T → ℕ) : (greedyPolicy (ι := ι) cap).IsCausal := by
  classical
  suffices hstep :
      ∀ (s : ℕ) (θ θ' : ι → AgentType (Fin T)),
        (∀ j, (θ j).arrival.val < s ∨ (θ' j).arrival.val < s → θ j = θ' j) →
        greedyAllocatedBefore cap θ s = greedyAllocatedBefore cap θ' s by
    intro t θ θ' hagree i
    rw [greedyPolicy_alloc_eq_some_iff, greedyPolicy_alloc_eq_some_iff,
      greedyWinnersAt_eq_of_agree cap t
        (hstep t.val θ θ' fun j hj => hagree j (hj.imp le_of_lt le_of_lt)) hagree]
  intro s
  induction s with
  | zero => intro _ _ _; rfl
  | succ k ih =>
    intro θ θ' hagree
    by_cases hk : k < T
    · have hprev : greedyAllocatedBefore cap θ k = greedyAllocatedBefore cap θ' k :=
        ih θ θ' fun j hj => hagree j (hj.imp Nat.lt_succ_of_lt Nat.lt_succ_of_lt)
      have hagree_k : ∀ j, (θ j).arrival ≤ ⟨k, hk⟩ ∨ (θ' j).arrival ≤ ⟨k, hk⟩ → θ j = θ' j :=
        fun j hj => hagree j (hj.imp Nat.lt_succ_of_le Nat.lt_succ_of_le)
      change greedyAllocatedBefore cap θ ((⟨k, hk⟩ : Fin T).val + 1) =
        greedyAllocatedBefore cap θ' ((⟨k, hk⟩ : Fin T).val + 1)
      rw [greedyAllocatedBefore_succ_eq, greedyAllocatedBefore_succ_eq, hprev,
        greedyWinnersAt_eq_of_agree cap ⟨k, hk⟩ hprev hagree_k]
    · simp only [greedyAllocatedBefore, hk, ↓reduceDIte]
      exact ih θ θ' fun j hj => hagree j (hj.imp Nat.lt_succ_of_lt Nat.lt_succ_of_lt)

/-- Greedy `Auction 2` is online-monotone for arbitrary period capacities `cap : Fin T → ℕ`
([Parkes2007], §16.3.2, Theorem 16.17, monotonicity step, locator not verified against primary PDF).
-/
theorem greedyPolicy_isMonotone (cap : Fin T → ℕ) : (greedyPolicy (ι := ι) cap).IsMonotone := by
  classical
  intro i θ θ₁ θ₂ ha hd hv hwin₁
  obtain ⟨tstar, htstar⟩ := Option.isSome_iff_exists.mp hwin₁
  rw [greedyPolicy_alloc_eq_some_iff] at htstar
  set θ'₁ := Function.update θ i θ₁
  set θ'₂ := Function.update θ i θ₂
  by_contra hnotwin₂
  have hno₂ : ∀ t : Fin T, i ∉ greedyWinnersAt cap θ'₂ t := fun t ht =>
    hnotwin₂ (by
      rw [Option.isSome_iff_exists]
      exact ⟨t, (greedyPolicy_alloc_eq_some_iff cap θ'₂ i t).mpr ht⟩)
  have hprev_eq :
      ∀ s : ℕ, s ≤ tstar.val →
        greedyAllocatedBefore cap θ'₁ s = greedyAllocatedBefore cap θ'₂ s := by
    intro s
    induction s with
    | zero => intro _; rfl
    | succ k ih =>
      intro hks
      have hlt : k < tstar.val := Nat.lt_of_succ_le hks
      have hkT : k < T := lt_trans hlt tstar.isLt
      have hprev : greedyAllocatedBefore cap θ'₁ k = greedyAllocatedBefore cap θ'₂ k :=
        ih (le_of_lt hlt)
      set tk : Fin T := ⟨k, hkT⟩
      have hni₁ : i ∉ greedyWinnersAt cap θ'₁ tk := fun hmem =>
        ne_of_lt hlt (congrArg Fin.val (greedyWinnersAt_unique cap θ'₁ hmem htstar))
      have hni₂ : i ∉ greedyWinnersAt cap θ'₂ tk := hno₂ tk
      have hwin_eq : greedyWinnersAt cap θ'₁ tk = greedyWinnersAt cap θ'₂ tk := by
        unfold greedyWinnersAt
        rw [topK_eq_erase_of_not_mem hni₁, topK_eq_erase_of_not_mem hni₂]
        have herase :
            (Finset.univ.filter fun j =>
              j ∉ greedyAllocatedBefore cap θ'₁ k ∧ (θ'₁ j).InWindow tk).erase i =
            (Finset.univ.filter fun j =>
              j ∉ greedyAllocatedBefore cap θ'₂ k ∧ (θ'₂ j).InWindow tk).erase i := by
          ext j
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, hprev]
          exact and_congr_right fun hne => by simp only [θ'₁, θ'₂, Function.update_of_ne hne]
        rw [herase]
        exact topK_congr fun j hj => by
          simp only [θ'₁, θ'₂, Function.update_of_ne (Finset.mem_erase.mp hj).1]
      rw [greedyAllocatedBefore_succ_eq cap θ'₁ tk, greedyAllocatedBefore_succ_eq cap θ'₂ tk,
        hprev, hwin_eq]
  have hprev_star := hprev_eq tstar.val le_rfl
  have hi_not_prev₁ : i ∉ greedyAllocatedBefore cap θ'₁ tstar.val :=
    greedyWinnersAt_disjoint_before cap θ'₁ tstar htstar
  have hi_not_prev₂ : i ∉ greedyAllocatedBefore cap θ'₂ tstar.val := hprev_star ▸ hi_not_prev₁
  have hi_in_win₁ : θ₁.InWindow tstar := by
    simpa only [θ'₁, Function.update_self] using greedyWinnersAt_inWindow cap θ'₁ tstar htstar
  have hi_in_win₂ : (θ'₂ i).InWindow tstar := by
    simp only [θ'₂, Function.update_self]
    exact ⟨ha.trans hi_in_win₁.1, hi_in_win₁.2.trans hd⟩
  have hrank₁ :
      rankIn θ'₁
        (Finset.univ.filter fun j =>
          j ∉ greedyAllocatedBefore cap θ'₁ tstar.val ∧ (θ'₁ j).InWindow tstar) i < cap tstar :=
    (Finset.mem_filter.mp htstar).2
  have hrank₂_le :
      rankIn θ'₂
        (Finset.univ.filter fun j =>
          j ∉ greedyAllocatedBefore cap θ'₂ tstar.val ∧ (θ'₂ j).InWindow tstar) i ≤
      rankIn θ'₁
        (Finset.univ.filter fun j =>
          j ∉ greedyAllocatedBefore cap θ'₁ tstar.val ∧ (θ'₁ j).InWindow tstar) i := by
    apply Finset.card_le_card
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    rcases hj with ⟨hjA, hbj⟩
    have hne : j ≠ i := fun h => beats_irrefl θ'₂ i (h ▸ hbj)
    rw [Finset.mem_filter] at hjA ⊢
    refine ⟨⟨Finset.mem_univ j, hprev_star.symm ▸ hjA.2.1, ?_⟩, ?_⟩
    · simpa only [θ'₁, θ'₂, Function.update_of_ne hne] using hjA.2.2
    · have hle := value_le_of_beats hbj
      simp only [Beats, θ'₁, θ'₂, Function.update_self, Function.update_of_ne hne] at hle ⊢
      exact Or.inl (hv.trans_le hle)
  have hi_wins₂ : i ∈ greedyWinnersAt cap θ'₂ tstar :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi_not_prev₂, hi_in_win₂⟩,
      lt_of_le_of_lt hrank₂_le hrank₁⟩
  exact hno₂ tstar hi_wins₂

/-- The Lavi–Nisan / Parkes greedy expiring-items mechanism (`Auction 2`): `greedyPolicy` paired
with its online critical-value payments
([Parkes2007], Theorem 16.17; [LaviNisan2000], locators not verified against primary PDF). -/
@[expose] noncomputable def greedyMechanism (cap : Fin T → ℕ) : Mechanism ι (Fin T) :=
  (greedyPolicy cap).criticalMechanism

/-- `Auction 2` is strongly truthful (DSIC) under no-early-arrival and no-late-departure
misreports ([Parkes2007], Theorem 16.17, truthfulness part, locator not verified against primary
PDF). -/
theorem greedyMechanism_isDSIC (cap : Fin T → ℕ) : (greedyMechanism (ι := ι) cap).IsDSIC :=
  Policy.criticalMechanism_isDSIC (greedyPolicy_isMonotone (ι := ι) cap)

/-- `Auction 2` is ex-post individually rational. -/
theorem greedyMechanism_isIR (cap : Fin T → ℕ) : (greedyMechanism (ι := ι) cap).IsIR :=
  Policy.criticalMechanism_isIR (greedyPolicy (ι := ι) cap)

/-- `Auction 2` has no positive transfers. -/
theorem greedyMechanism_isNPT (cap : Fin T → ℕ) : (greedyMechanism (ι := ι) cap).IsNPT :=
  Policy.criticalMechanism_isNPT (greedyPolicy (ι := ι) cap)

/-- `Auction 2` charges unallocated agents `0`. -/
theorem greedyMechanism_isLoserZero (cap : Fin T → ℕ) :
    (greedyMechanism (ι := ι) cap).IsLoserZero :=
  Policy.criticalMechanism_isLoserZero (greedyPolicy (ι := ι) cap)

/-- `Auction 2` is `2`-competitive for social welfare with arbitrary per-period capacities
`cap : Fin T → ℕ`: `optWelfare cap θ ≤ 2 * welfare θ ((greedyPolicy cap).alloc θ)`
([Parkes2007], Theorem 16.17; [LaviNisan2000], locators not verified against primary PDF). -/
theorem optWelfare_le_two_mul_welfare_greedy (cap : Fin T → ℕ) (θ : ι → AgentType (Fin T)) :
    optWelfare cap θ ≤ 2 * welfare θ ((greedyPolicy cap).alloc θ) := by
  classical
  obtain ⟨f, hf, hfopt⟩ := exists_optWelfare cap θ
  rw [← hfopt, welfare_eq_sum_filter hf.1,
    welfare_eq_sum_filter ((greedyPolicy (ι := ι) cap).alloc_in_window θ)]
  set G := Finset.univ.filter fun i => ((greedyPolicy cap).alloc θ i).isSome
  set F := Finset.univ.filter fun i => (f i).isSome
  have hG : ∀ {i t}, i ∈ greedyWinnersAt cap θ t → i ∈ G := fun h =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Option.isSome_iff_exists.mpr ⟨_, (greedyPolicy_alloc_eq_some_iff cap θ _ _).mpr h⟩⟩
  rw [← Finset.sum_filter_add_sum_filter_not F (fun i => i ∈ G)]
  have hpart1 : ∑ i ∈ F.filter (fun i => i ∈ G), (θ i).value ≤ ∑ i ∈ G, (θ i).value :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => (Finset.mem_filter.mp hi).2)
      fun i _ _ => (θ i).value_nonneg
  set U := F.filter fun i => i ∉ G
  -- Split `U` by the period at which the optimum serves each agent, and `G` by the greedy period.
  have hU_eq :
      ∑ i ∈ U, (θ i).value =
        ∑ t : Fin T, ∑ i ∈ U.filter (fun i => f i = some t), (θ i).value := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨t, ht⟩ :=
      Option.isSome_iff_exists.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    simp only [ht, Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hG_eq :
      ∑ i ∈ G, (θ i).value =
        ∑ t : Fin T, ∑ i ∈ greedyWinnersAt cap θ t, (θ i).value := by
    have hunion : Finset.univ.biUnion (greedyWinnersAt cap θ) = G := by
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, G, Finset.mem_filter,
        Option.isSome_iff_exists, greedyPolicy_alloc_eq_some_iff]
    rw [← hunion, Finset.sum_biUnion fun t₁ _ t₂ _ hne =>
      Finset.disjoint_left.2 fun _ h₁ h₂ => hne (greedyWinnersAt_unique cap θ h₁ h₂)]
  have hpart2 : ∑ i ∈ U, (θ i).value ≤ ∑ i ∈ G, (θ i).value := by
    rw [hU_eq, hG_eq]
    refine Finset.sum_le_sum fun t _ => ?_
    set Ut := U.filter fun i => f i = some t
    set active :=
      Finset.univ.filter fun i => i ∉ greedyAllocatedBefore cap θ t.val ∧ (θ i).InWindow t
    -- An agent served at `t` by the optimum but never by greedy was active at `t` and lost.
    have hUt : ∀ i ∈ Ut, i ∈ active ∧ i ∉ greedyWinnersAt cap θ t := by
      intro i hi
      simp only [Ut, U, F, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun hprev => ?_, hf.1 i t hi.2⟩,
        fun h => hi.1.2 (hG h)⟩
      obtain ⟨s, _, hs⟩ := (mem_greedyAllocatedBefore_iff cap θ t.val i).mp hprev
      exact hi.1.2 (hG hs)
    rcases Ut.eq_empty_or_nonempty with hempty | ⟨i₀, hi₀⟩
    · rw [hempty, Finset.sum_empty]
      exact Finset.sum_nonneg fun g _ => (θ g).value_nonneg
    -- Some active agent lost at `t`, so greedy filled all `cap t` units.
    have hGt_card : (greedyWinnersAt cap θ t).card = cap t := by
      have hrank : cap t ≤ rankIn θ active i₀ := not_lt.1 fun h =>
        (hUt i₀ hi₀).2 (Finset.mem_filter.mpr ⟨(hUt i₀ hi₀).1, h⟩)
      exact (card_topK θ (cap t) active).trans
        (min_eq_left (hrank.trans (rankIn_lt_card (hUt i₀ hi₀).1).le))
    have hUt_card : Ut.card ≤ (greedyWinnersAt cap θ t).card :=
      hGt_card ▸ (Finset.card_le_card fun i hi =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩).trans (hf.2 t)
    obtain ⟨i_max, hi_max_mem, hi_max⟩ :=
      Finset.exists_max_image Ut (fun i => (θ i).value) ⟨i₀, hi₀⟩
    calc ∑ i ∈ Ut, (θ i).value ≤ Ut.card • (θ i_max).value :=
          Finset.sum_le_card_nsmul Ut _ _ hi_max
      _ ≤ (greedyWinnersAt cap θ t).card • (θ i_max).value :=
          nsmul_le_nsmul_left (θ i_max).value_nonneg hUt_card
      _ ≤ ∑ g ∈ greedyWinnersAt cap θ t, (θ g).value :=
          Finset.card_nsmul_le_sum _ _ _ fun g hg => value_le_of_beats
            (beats_of_mem_topK_of_not_mem hg (hUt i_max hi_max_mem).1 (hUt i_max hi_max_mem).2)
  linarith

end GreedyAuction

/-! ### Competitive Lower Bounds (Theorems 16.18 and 16.19) -/

section LowerBounds

/-- Helper: constructing an `AgentType (Fin T)` with `a = d = t` and nonnegative value `v`. -/
private abbrev pointType {T : ℕ} (t : Fin T) (v : ℝ) (hv : 0 ≤ v) : AgentType (Fin T) :=
  ⟨t, t, v, le_rfl, hv⟩

/-- Helper: constructing an `AgentType (Fin T)` on `[a, d]` with `a ≤ d` and `0 ≤ v`. -/
private abbrev intervalType {T : ℕ} (a d : Fin T) (had : a ≤ d) (v : ℝ) (hv : 0 ≤ v) :
    AgentType (Fin T) :=
  ⟨a, d, v, had, hv⟩

/-- In a unit-capacity expiring-items allocation, at most one agent can win period `t`. -/
private theorem eq_of_alloc_eq_some_unit {ι : Type*} [Fintype ι] {T : ℕ}
    {θ : ι → AgentType (Fin T)} {f : ι → Option (Fin T)}
    (hf : IsExpiringAllocation (fun _ => 1) θ f) {i j : ι} {t : Fin T}
    (hi : f i = some t) (hj : f j = some t) : i = j :=
  Finset.card_le_one.1 (hf.2 t) i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩) j
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)

/-- A window-feasible allocation that serves at most one agent per period is unit-capacity
feasible. -/
private theorem isExpiringAllocation_unit {ι : Type*} [Fintype ι] {T : ℕ}
    {θ : ι → AgentType (Fin T)} {f : ι → Option (Fin T)}
    (hwin : ∀ i t, f i = some t → (θ i).InWindow t)
    (hinj : ∀ i j t, f i = some t → f j = some t → i = j) :
    IsExpiringAllocation (fun _ => 1) θ f :=
  ⟨hwin, fun t => Finset.card_le_one.2 fun i hi j hj =>
    hinj i j t (Finset.mem_filter.1 hi).2 (Finset.mem_filter.1 hj).2⟩

/-- An agent whose window is the single period `t` is either unallocated or allocated at `t`. -/
private theorem alloc_eq_none_or_eq_some_of_point {ι : Type*} {T : ℕ} (π : Policy ι (Fin T))
    {θ : ι → AgentType (Fin T)} {i : ι} {t : Fin T} (ha : t ≤ (θ i).arrival)
    (hd : (θ i).departure ≤ t) : π.alloc θ i = none ∨ π.alloc θ i = some t := by
  cases h : π.alloc θ i with
  | none => exact .inl rfl
  | some s =>
    have hs := π.alloc_in_window θ i s h
    exact .inr (congrArg some (le_antisymm (hs.2.trans hd) (ha.trans hs.1)))

/-- Under unit capacities, an agent whose window is the single period `t` loses whenever another
agent wins `t`. -/
private theorem alloc_eq_none_of_point_of_eq_some {ι : Type*} [Fintype ι] {T : ℕ}
    {π : Policy ι (Fin T)} (hfeas : π.IsExpiringFeasible (fun _ => 1))
    {θ : ι → AgentType (Fin T)} {i w : ι} {t : Fin T} (ha : t ≤ (θ i).arrival)
    (hd : (θ i).departure ≤ t) (hw : π.alloc θ w = some t) (hne : i ≠ w) :
    π.alloc θ i = none :=
  (alloc_eq_none_or_eq_some_of_point π ha hd).resolve_right fun h =>
    hne (eq_of_alloc_eq_some_unit (hfeas θ) h hw)

/-- If every agent outside `S` is unallocated or has value `0`, welfare is at most the total
value of `S`. -/
private theorem welfare_le_sum_value {ι : Type*} [Fintype ι] {T : ℕ}
    {θ : ι → AgentType (Fin T)} {f : ι → Option (Fin T)} (S : Finset ι)
    (h : ∀ j ∉ S, f j = none ∨ (θ j).value = 0) : welfare θ f ≤ ∑ j ∈ S, (θ j).value := by
  classical
  unfold welfare
  rw [← Finset.sum_add_sum_compl S]
  have hS : ∑ j ∈ S, (θ j).realizedValue (f j) ≤ ∑ j ∈ S, (θ j).value :=
    Finset.sum_le_sum fun j _ => (θ j).realizedValue_le_value _
  have hSc : ∑ j ∈ Sᶜ, (θ j).realizedValue (f j) ≤ 0 := Finset.sum_nonpos fun j hj => by
    rcases h j (Finset.mem_compl.1 hj) with h | h
    · rw [h, AgentType.realizedValue_none]
    · exact h ▸ (θ j).realizedValue_le_value _
  linarith

/-- Helper: single-agent allocation feasibility for bounding `optWelfare` from below. -/
private theorem value_le_optWelfare_of_single {ι : Type*} [Fintype ι] {T : ℕ}
    (θ : ι → AgentType (Fin T)) (i : ι) :
    (θ i).value ≤ optWelfare (fun _ => 1) θ := by
  classical
  let f : ι → Option (Fin T) := fun j => if j = i then some (θ i).arrival else none
  have hwin : (θ i).InWindow (θ i).arrival := ⟨le_rfl, (θ i).arrival_le_departure⟩
  have hf : IsExpiringAllocation (fun _ => 1) θ f := by
    refine isExpiringAllocation_unit (fun j t h => ?_) fun x y t hx hy => ?_
    · simp only [f, Option.ite_none_right_eq_some, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hwin
    · simp only [f, Option.ite_none_right_eq_some] at hx hy
      exact hx.1.trans hy.1.symm
  have hwf : welfare θ f = (θ i).value := by
    unfold welfare
    rw [Fintype.sum_eq_single i fun j hne => by
      simp only [f, hne, ↓reduceIte, AgentType.realizedValue_none]]
    simp only [f, ↓reduceIte, AgentType.realizedValue_some_of_inWindow hwin]
  exact hwf ▸ welfare_le_optWelfare hf

/-- Helper: two-agent allocation on distinct periods `t₀ ≠ t₁` gives a lower bound on
`optWelfare`. -/
private theorem add_le_optWelfare_of_pair {ι : Type*} [Fintype ι] {T : ℕ}
    (θ : ι → AgentType (Fin T)) {i j : ι} {t₀ t₁ : Fin T}
    (hij : i ≠ j) (ht : t₀ ≠ t₁) (hi : (θ i).InWindow t₀) (hj : (θ j).InWindow t₁) :
    (θ i).value + (θ j).value ≤ optWelfare (fun _ => 1) θ := by
  classical
  let f : ι → Option (Fin T) := fun x => if x = i then some t₀ else if x = j then some t₁ else none
  have hf : IsExpiringAllocation (fun _ => 1) θ f := by
    refine isExpiringAllocation_unit (fun x t h => ?_) fun x y t hx hy => ?_
    · simp only [f] at h
      split_ifs at h with hxi hxj
      · subst hxi; exact (Option.some.inj h) ▸ hi
      · subst hxj; exact (Option.some.inj h) ▸ hj
    · simp only [f] at hx hy
      split_ifs at hx hy <;> grind
  have hwf : welfare θ f = (θ i).value + (θ j).value := by
    unfold welfare
    rw [Fintype.sum_eq_add i j hij fun x hx => by
      simp only [f, hx.1, hx.2, ↓reduceIte, AgentType.realizedValue_none]]
    simp only [f, ↓reduceIte, hij.symm, AgentType.realizedValue_some_of_inWindow hi,
      AgentType.realizedValue_some_of_inWindow hj]
  exact hwf ▸ welfare_le_optWelfare hf

/-- Lower bound for deterministic truthful expiring-items auctions: no deterministic, causal,
DSIC, IR, loser-zero unit-capacity expiring-items mechanism achieves competitive ratio `c < 2` for
social welfare, even with `2` periods and `3` agents
([Parkes2007], Theorem 16.18, locator not verified against primary PDF). -/
theorem no_lt_two_competitive_truthful_expiring
    (M : Mechanism (Fin 3) (Fin 2))
    (hfeas : M.policy.IsExpiringFeasible (fun _ => 1))
    (hcausal : M.policy.IsCausal)
    (hdsic : M.IsDSIC) (hir : M.IsIR) (hlz : M.IsLoserZero)
    {c : ℝ} (hc : c < 2) :
    ∃ θ : Fin 3 → AgentType (Fin 2),
      c * welfare θ (M.policy.alloc θ) < optWelfare (fun _ => 1) θ := by
  have hmono : M.policy.IsMonotone := hdsic.isMonotone hir hlz
  set δ : ℝ := (2 - c) / (4 * (|c| + 1))
  have hδpos : 0 < δ := by positivity
  have hδle : ∀ x ≤ |c| + 1, δ * x ≤ (2 - c) / 4 := fun x hx => by
    have hδc : δ * (|c| + 1) = (2 - c) / 4 := by
      dsimp only [δ]
      field_simp
    exact hδc ▸ mul_le_mul_of_nonneg_left hx hδpos.le
  have hδc1 : c * (1 + 2 * δ) < 2 + 2 * δ := by
    linarith [hδle (c - 1) (by linarith [le_abs_self c])]
  have hδc2 : c * (1 + δ) < 2 + 2 * δ := by
    linarith [hδle (c - 2) (by linarith [le_abs_self c])]
  set B : ℝ := (|c| + 1) * (2 + 2 * δ) + 1
  have hBpos : 0 < B := by positivity
  have h01 : (0 : Fin 2) ≤ (1 : Fin 2) := by decide
  set t0_1 : AgentType (Fin 2) := pointType 0 1 (by norm_num)
  set t0_1d : AgentType (Fin 2) := pointType 0 (1 + δ) (by linarith)
  set t1_0 : AgentType (Fin 2) := pointType 1 0 le_rfl
  set t1_B : AgentType (Fin 2) := pointType 1 B hBpos.le
  set θA : Fin 3 → AgentType (Fin 2) := ![t0_1, t0_1d, t1_0]
  -- Shared argument when agent `w ∈ {0, 1}` wins period `0` in `θA` and `o` is the other one.
  have hwin0_case :
      ∀ (w o : Fin 3), w ≠ o → w ≠ 2 → o ≠ 2 →
        ∀ (v_ext : ℝ) (hv_ext : 0 ≤ v_ext),
          (θA w).value < v_ext →
          v_ext + (θA o).value = 2 + 2 * δ →
          c * v_ext < 2 + 2 * δ →
          M.policy.alloc θA w = some 0 →
          ∃ θ : Fin 3 → AgentType (Fin 2),
            c * welfare θ (M.policy.alloc θ) < optWelfare (fun _ => 1) θ := by
    intro w o hwo hw2 ho2 v_ext hv_ext hgt hsum_val hc_lt hwA
    have hcover : ∀ j : Fin 3, j ≠ w → j ≠ o → j = 2 := by
      intro j; fin_cases w <;> fin_cases o <;> fin_cases j <;> simp_all
    have hθA_dep : ∀ x : Fin 3, x ≠ 2 → (θA x).departure = 0 := by
      intro x hx; fin_cases x <;> simp_all [θA, t0_1, t0_1d]
    have hcausal_upd2 : ∀ (θ : Fin 3 → AgentType (Fin 2)) (τ₂ : AgentType (Fin 2)),
        (θ 2).arrival = 1 → τ₂.arrival = 1 →
        M.policy.alloc θ w = some 0 →
        M.policy.alloc (Function.update θ 2 τ₂) w = some 0 := by
      intro θ τ₂ h2a hτ₂a hw0
      refine (hcausal 0 θ (Function.update θ 2 τ₂) (fun j hj => ?_) w).mp hw0
      rcases eq_or_ne j 2 with rfl | hj2
      · rcases hj with h | h <;> [rw [h2a] at h; rw [Function.update_self, hτ₂a] at h] <;>
          exact absurd h (by decide)
      · rw [Function.update_of_ne hj2]
    set θB : Fin 3 → AgentType (Fin 2) := Function.update θA 2 t1_B
    have hwB : M.policy.alloc θB w = some 0 :=
      hcausal_upd2 θA t1_B rfl rfl hwA
    set θC : Fin 3 → AgentType (Fin 2) :=
      Function.update θB w (intervalType 0 1 h01 v_ext hv_ext)
    have hwC_some : (M.policy.alloc θC w).isSome := by
      have hθBw : θB w = θA w := Function.update_of_ne hw2 _ _
      exact hmono w θB (θA w) (intervalType 0 1 h01 v_ext hv_ext)
        (Fin.zero_le _) (by rw [hθA_dep w hw2]; exact h01) hgt
        (by rw [← hθBw, Function.update_eq_self, hwB]; rfl)
    have hθCo : θC o = θA o := by
      simp only [θC, θB, Function.update_of_ne hwo.symm, Function.update_of_ne ho2]
    have hθCw : θC w = intervalType 0 1 h01 v_ext hv_ext := Function.update_self w _ _
    obtain ⟨tC, htC⟩ := Option.isSome_iff_exists.mp hwC_some
    fin_cases tC
    · -- `w` keeps period `0` with the wider window; lowering agent `2` leaves `o` unserved.
      set θD : Fin 3 → AgentType (Fin 2) := Function.update θC 2 t1_0
      have hwD : M.policy.alloc θD w = some 0 :=
        hcausal_upd2 θC t1_0
          (by dsimp only [θC, θB]; rw [Function.update_of_ne hw2.symm, Function.update_self])
          rfl htC
      have hθDo : θD o = θA o := by simp only [θD, Function.update_of_ne ho2, hθCo]
      have hθDw : θD w = intervalType 0 1 h01 v_ext hv_ext := by
        simp only [θD, Function.update_of_ne hw2, hθCw]
      have hθD2 : θD 2 = t1_0 := Function.update_self 2 _ _
      have hoD_none : M.policy.alloc θD o = none :=
        alloc_eq_none_of_point_of_eq_some hfeas (Fin.zero_le _)
          (by rw [hθDo, hθA_dep o ho2]) hwD hwo.symm
      have hwD_le : welfare θD (M.policy.alloc θD) ≤ v_ext := by
        refine (welfare_le_sum_value {w} fun j hj => ?_).trans_eq
          (by rw [Finset.sum_singleton, hθDw])
        rcases eq_or_ne j o with rfl | hjo
        · exact .inl hoD_none
        · exact .inr (by rw [hcover j (Finset.notMem_singleton.1 hj) hjo, hθD2])
      have hoptD : 2 + 2 * δ ≤ optWelfare (fun _ => 1) θD := by
        have h := add_le_optWelfare_of_pair θD (t₀ := 0) (t₁ := 1) hwo.symm (by decide)
          (by rw [hθDo]; exact ⟨(θA o).arrival_le_departure.trans (hθA_dep o ho2).le,
            Fin.zero_le _⟩)
          (by rw [hθDw]; exact ⟨h01, le_rfl⟩)
        rw [hθDo, hθDw] at h
        dsimp only [intervalType] at h
        linarith
      refine ⟨θD, ?_⟩
      rcases le_or_gt 0 c with hc0 | hc0
      · linarith [mul_le_mul_of_nonneg_left hwD_le hc0]
      · nlinarith [welfare_nonneg θD (M.policy.alloc θD)]
    · -- `w` moves to period `1`, so the high-value agent `2` arriving at period `1` loses.
      have hθC2 : θC 2 = t1_B := by
        simp only [θC, θB, Function.update_of_ne hw2.symm, Function.update_self]
      have h2C_none : M.policy.alloc θC 2 = none :=
        alloc_eq_none_of_point_of_eq_some hfeas (by rw [hθC2]; exact le_rfl) (Fin.le_last _) htC
          hw2.symm
      have hwC : welfare θC (M.policy.alloc θC) ≤ 2 + 2 * δ := by
        refine (welfare_le_sum_value {w, o} fun j hj => .inl ?_).trans ?_
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
          rw [hcover j hj.1 hj.2, h2C_none]
        · rw [Finset.sum_pair hwo, hθCw, hθCo]
          dsimp only [intervalType]
          linarith
      have hoptC : B ≤ optWelfare (fun _ => 1) θC := by
        simpa only [hθC2, pointType] using value_le_optWelfare_of_single θC 2
      refine ⟨θC, ?_⟩
      have hcwC : c * welfare θC (M.policy.alloc θC) ≤ |c| * (2 + 2 * δ) :=
        (mul_le_mul_of_nonneg_right (le_abs_self c) (welfare_nonneg _ _)).trans
          (mul_le_mul_of_nonneg_left hwC (abs_nonneg c))
      dsimp only [B] at hoptC
      linarith
  by_cases h1A : M.policy.alloc θA 1 = some 0
  · exact hwin0_case 1 0 (by decide) (by decide) (by decide) (1 + 2 * δ) (by linarith)
      (by dsimp [θA, t0_1d]; linarith) (by dsimp [θA, t0_1]; ring) hδc1 h1A
  by_cases h0A : M.policy.alloc θA 0 = some 0
  · exact hwin0_case 0 1 (by decide) (by decide) (by decide) (1 + δ) (by linarith)
      (by dsimp [θA, t0_1]; linarith) (by dsimp [θA, t0_1d]; ring) hδc2 h0A
  -- Neither agent `0` nor agent `1` wins period `0` in `θA`, so nobody realizes value.
  have hwA : welfare θA (M.policy.alloc θA) = 0 := by
    refine le_antisymm ((welfare_le_sum_value ∅ fun j _ => ?_).trans_eq Finset.sum_empty)
      (welfare_nonneg _ _)
    fin_cases j
    · exact .inl ((alloc_eq_none_or_eq_some_of_point M.policy le_rfl le_rfl).resolve_right h0A)
    · exact .inl ((alloc_eq_none_or_eq_some_of_point M.policy le_rfl le_rfl).resolve_right h1A)
    · exact .inr rfl
  have hoptA : 1 + δ ≤ optWelfare (fun _ => 1) θA := value_le_optWelfare_of_single θA 1
  refine ⟨θA, ?_⟩
  rw [hwA, mul_zero]
  linarith

/-- Impossibility under arbitrary departure misreports: for every `c : ℝ`, there exist a finite
horizon `T` and agent count `n` such that no deterministic, causal, unit-capacity expiring-items
mechanism that is DSIC under no-early-arrival and arbitrary departure misreports
(`IsDSICNoEarlyArrival`), IR, NPT, and loser-zero can be `c`-competitive for social welfare
([Parkes2007], Theorem 16.19, locator not verified against primary PDF). -/
theorem no_competitive_arbitrary_departure_expiring (c : ℝ) :
    ∃ (n T : ℕ), ∀ (M : Mechanism (Fin n) (Fin T)),
      M.policy.IsExpiringFeasible (fun _ => 1) →
      M.policy.IsCausal →
      M.IsDSICNoEarlyArrival → M.IsIR → M.IsNPT → M.IsLoserZero →
      ∃ θ : Fin n → AgentType (Fin T),
        c * welfare θ (M.policy.alloc θ) < optWelfare (fun _ => 1) θ := by
  set c' : ℝ := max c 1
  have hc'_pos : 0 < c' := lt_of_lt_of_le zero_lt_one (le_max_right c 1)
  have hc_le : c ≤ c' := le_max_left c 1
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * c' ^ 2)
  refine ⟨2 * m + 1, m + 1, fun M hfeas hcausal hdsic_nea hir hnpt hlz => ?_⟩
  by_contra hcomp_not
  push Not at hcomp_not
  -- `c'`-competitiveness as used below: no profile has welfare at most `w` and optimal welfare at
  -- least `o` with `c' * w < o`.
  have hcomp : ∀ (θ : Fin (2 * m + 1) → AgentType (Fin (m + 1))) {w o : ℝ},
      welfare θ (M.policy.alloc θ) ≤ w → o ≤ optWelfare (fun _ => 1) θ → c' * w < o → False :=
    fun θ _ _ hw ho hlt => by
      linarith [hcomp_not θ, mul_le_mul_of_nonneg_right hc_le (welfare_nonneg θ (M.policy.alloc θ)),
        mul_le_mul_of_nonneg_left hw hc'_pos.le]
  have hdsic : M.IsDSIC := hdsic_nea.isDSIC
  have hmono : M.policy.IsMonotone := hdsic.isMonotone hir hlz
  have hpay_eq : ∀ θ i, M.payment θ i = M.policy.criticalPayment θ i :=
    hdsic.payment_eq_criticalPayment hir hnpt hlz
  -- Agent roles in Fin (2 * m + 1):
  --   0 : anchor agent at period 0 with value 1
  --   1 .. m : main agents k at period k with value 1 / (2 * c')
  --   m + 1 .. 2 * m : blocker agents m + r at period r with value 0 (raised in proofs)
  set vlow : ℝ := 1 / (2 * c')
  have hvlow_pos : 0 < vlow := by positivity
  let periodOf : Fin (2 * m + 1) → Fin (m + 1) := fun j =>
    if h1 : j.val ≤ m then ⟨j.val, Nat.lt_succ_of_le h1⟩
    else ⟨j.val - m, by omega⟩
  have hperiod_pos : ∀ j : Fin (2 * m + 1), j ≠ 0 → 0 < (periodOf j).val := by
    intro j hj
    have hj0 : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
    have hjlt : j.val < 2 * m + 1 := j.isLt
    simp only [periodOf]
    split_ifs with h1
    · exact hj0
    · dsimp only
      omega
  let mainAgent : Fin m → Fin (2 * m + 1) := fun k => ⟨k.val + 1, by omega⟩
  let blockerAgent : Fin m → Fin (2 * m + 1) := fun k => ⟨m + k.val + 1, by omega⟩
  have hblocker_period : ∀ k : Fin m, periodOf (blockerAgent k) = ⟨k.val + 1, by omega⟩ := by
    intro k
    have hnot : ¬ (m + k.val + 1 ≤ m) := by omega
    simp only [periodOf, blockerAgent, hnot, ↓reduceDIte]
    ext
    dsimp only
    omega
  -- Main target profile θStar
  let θStar : Fin (2 * m + 1) → AgentType (Fin (m + 1)) := fun j =>
    if j.val = 0 then pointType 0 1 (by norm_num)
    else if j.val ≤ m then pointType (periodOf j) vlow hvlow_pos.le
    else pointType (periodOf j) 0 le_rfl
  -- Zeroed-future profile template: agent 0 = (0,0,1), every j ≠ 0 has pointType (periodOf j) 0
  let θBase : Fin (2 * m + 1) → AgentType (Fin (m + 1)) := fun j =>
    if j.val = 0 then pointType 0 1 (by norm_num)
    else pointType (periodOf j) 0 le_rfl
  have hStar0 : θStar 0 = pointType 0 1 (by norm_num) := by
    simp only [θStar, Fin.val_zero, ↓reduceIte]
  have hBase0 : θBase 0 = pointType 0 1 (by norm_num) := by
    simp only [θBase, Fin.val_zero, ↓reduceIte]
  have hBase : ∀ x, x ≠ 0 → θBase x = pointType (periodOf x) 0 le_rfl := fun x hx => by
    simp only [θBase, show x.val ≠ 0 from fun h => hx (Fin.ext h), ↓reduceIte]
  have hStar_arr : ∀ x, x ≠ 0 → (θStar x).arrival = periodOf x := fun x hx => by
    simp only [θStar, show x.val ≠ 0 from fun h => hx (Fin.ext h), ↓reduceIte]
    split_ifs <;> rfl
  have hStar_main : ∀ k : Fin m, θStar (mainAgent k) = pointType ⟨k.val + 1, by omega⟩ vlow
      hvlow_pos.le := fun k => by
    have hle : k.val + 1 ≤ m := k.isLt
    simp only [θStar, mainAgent, Nat.add_one_ne_zero, hle, ↓reduceIte, periodOf, ↓reduceDIte]
  -- Every mainAgent k loses in θStar!
  have hmain_loses : ∀ k : Fin m, M.policy.alloc θStar (mainAgent k) = none := by
    intro k
    set i := mainAgent k
    set tk : Fin (m + 1) := ⟨k.val + 1, by omega⟩
    have hi0 : i ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp [i, mainAgent] at this
    -- Agent `i` reporting the single period `t` can only win at `t`.
    have hpoint : ∀ (θ : Fin (2 * m + 1) → AgentType (Fin (m + 1))) (t : Fin (m + 1)) (v : ℝ)
        (hv : 0 ≤ v), M.policy.alloc (Function.update θ i (pointType t v hv)) i = none ∨
          M.policy.alloc (Function.update θ i (pointType t v hv)) i = some t := fun θ t v hv =>
      alloc_eq_none_or_eq_some_of_point M.policy (by rw [Function.update_self])
        (by rw [Function.update_self])
    -- Profiles giving agent `0` the same type and every other agent except `i` its positive
    -- period as arrival agree, after a common report of `i`, on all agents arrived by period `0`.
    have hagree0 : ∀ (θ θ' : Fin (2 * m + 1) → AgentType (Fin (m + 1)))
        (τ : AgentType (Fin (m + 1))),
        θ 0 = θ' 0 →
        (∀ x, x ≠ 0 → x ≠ i → (θ x).arrival = periodOf x ∧ (θ' x).arrival = periodOf x) →
        ∀ x, (Function.update θ i τ x).arrival ≤ 0 ∨ (Function.update θ' i τ x).arrival ≤ 0 →
          Function.update θ i τ x = Function.update θ' i τ x := by
      intro θ θ' τ h0 harr x hx
      by_cases hxi : x = i
      · subst hxi
        simp only [Function.update_self]
      simp only [Function.update_of_ne hxi] at hx ⊢
      by_cases hx0 : x = 0
      · subst hx0
        exact h0
      rw [(harr x hx0 hxi).1, (harr x hx0 hxi).2, or_self] at hx
      exact absurd hx (not_le_of_gt (hperiod_pos x hx0))
    have hagreeSB : ∀ τ x, (Function.update θStar i τ x).arrival ≤ 0 ∨
        (Function.update θBase i τ x).arrival ≤ 0 →
          Function.update θStar i τ x = Function.update θBase i τ x := fun τ =>
      hagree0 θStar θBase τ (hStar0.trans hBase0.symm) fun x hx0 _ =>
        ⟨hStar_arr x hx0, by rw [hBase x hx0]⟩
    -- Step 1: criticalValue θStar i 0 0 ≥ ENNReal.ofReal (1 / c')
    have hcv00_ge : ENNReal.ofReal (1 / c') ≤ M.policy.criticalValue θStar i 0 0 le_rfl := by
      refine le_sInf fun w hw => ?_
      obtain ⟨z, hz, rfl, hwin_z⟩ := hw
      apply ENNReal.ofReal_le_ofReal
      by_contra hlt
      push Not at hlt
      have hwin0 := (hpoint θStar 0 z hz).resolve_left (Option.isSome_iff_ne_none.mp hwin_z)
      set θz := Function.update θBase i (pointType 0 z hz)
      have hwin_θz : M.policy.alloc θz i = some 0 := (hcausal 0 _ θz (hagreeSB _) i).mp hwin0
      have hθz0 : θz 0 = pointType 0 1 (by norm_num) := by
        simp only [θz, Function.update_of_ne hi0.symm, hBase0]
      have h0_none : M.policy.alloc θz 0 = none :=
        alloc_eq_none_of_point_of_eq_some hfeas (Fin.zero_le _) (by rw [hθz0]) hwin_θz hi0.symm
      have hw_le : welfare θz (M.policy.alloc θz) ≤ z := by
        refine (welfare_le_sum_value {i} fun j hj => ?_).trans_eq
          (by simp only [θz, Finset.sum_singleton, Function.update_self, pointType])
        rcases eq_or_ne j 0 with rfl | hj0
        · exact .inl h0_none
        · exact .inr (by simp only [θz, Function.update_of_ne (Finset.notMem_singleton.1 hj),
            hBase j hj0, pointType])
      have hopt1 : 1 ≤ optWelfare (fun _ => 1) θz := by
        simpa only [hθz0, pointType] using value_le_optWelfare_of_single θz 0
      exact hcomp θz hw_le hopt1 (by rwa [lt_div_iff₀ hc'_pos, mul_comm] at hlt)
    -- Step 2: For Y := 2 * c' + 1, agent i wins at t = 0 under (0, 0, Y - 1) and (0, tk, Y)
    set Y : ℝ := 2 * c' + 1
    have hY1_nonneg : 0 ≤ Y - 1 := by dsimp [Y]; linarith
    have hY_nonneg : 0 ≤ Y := by dsimp [Y]; linarith
    have h0tk : (0 : Fin (m + 1)) ≤ tk := Fin.zero_le tk
    have hwin_big0_base :
        M.policy.alloc (Function.update θBase i (pointType 0 (Y - 1) hY1_nonneg)) i = some 0 := by
      refine (hpoint θBase 0 (Y - 1) hY1_nonneg).resolve_left fun hi_none => ?_
      set θbig := Function.update θBase i (pointType 0 (Y - 1) hY1_nonneg)
      have hw_le : welfare θbig (M.policy.alloc θbig) ≤ 1 := by
        refine (welfare_le_sum_value {0} fun j hj => ?_).trans_eq (by
          simp only [θbig, Finset.sum_singleton, Function.update_of_ne hi0.symm, hBase0, pointType])
        rcases eq_or_ne j i with rfl | hji
        · exact .inl hi_none
        · exact .inr (by simp only [θbig, Function.update_of_ne hji,
            hBase j (Finset.notMem_singleton.1 hj), pointType])
      have hoptY : Y - 1 ≤ optWelfare (fun _ => 1) θbig := by
        simpa only [θbig, Function.update_self, pointType] using
          value_le_optWelfare_of_single θbig i
      exact hcomp θbig hw_le hoptY (by dsimp only [Y]; linarith)
    -- Claim 2: Agent i MUST win at t = 0 in update θStar i (0, tk, Y)!
    have hwin_tk_at_0 :
        M.policy.alloc (Function.update θStar i (intervalType 0 tk h0tk Y hY_nonneg)) i =
          some 0 := by
      by_contra hnot0
      set θ0 := Function.update θBase i (intervalType 0 tk h0tk Y hY_nonneg)
      have hθ0_not0 : M.policy.alloc θ0 i ≠ some 0 := fun h =>
        hnot0 ((hcausal 0 _ θ0 (hagreeSB _) i).mpr h)
      -- Inductively build profiles θ_j where agent i does not win at any period ≤ j
      have hind :
          ∀ j : ℕ, j ≤ tk.val →
            ∃ θj : Fin (2 * m + 1) → AgentType (Fin (m + 1)),
              θj 0 = pointType 0 1 (by norm_num) ∧
              θj i = intervalType 0 tk h0tk Y hY_nonneg ∧
              (∀ x, x ≠ 0 → x ≠ i → (θj x).arrival = periodOf x ∧ (θj x).departure = periodOf x) ∧
              (∀ t : Fin (m + 1), t.val ≤ j → M.policy.alloc θj i ≠ some t) := by
        intro j
        induction j with
        | zero =>
          intro _
          refine ⟨θ0, ?_, ?_, ?_, ?_⟩
          · simp only [θ0, Function.update_of_ne hi0.symm, hBase0]
          · simp only [θ0, Function.update_self]
          · intro x hx0 hxi
            simp only [θ0, Function.update_of_ne hxi, hBase x hx0, pointType, and_self]
          · intro t ht
            rwa [show t = 0 from Fin.ext (Nat.le_zero.mp ht)]
        | succ r ih =>
          intro hr_le
          obtain ⟨θr, hθr0, hθri, hθr_rest, hθr_no⟩ := ih (Nat.le_of_succ_le hr_le)
          have hr_lt_m : r < m := by
            have : r + 1 ≤ k.val + 1 := hr_le
            omega
          set br : Fin (2 * m + 1) := blockerAgent ⟨r, hr_lt_m⟩
          have hbr_ne0 : br ≠ 0 := by
            intro h; have := congrArg Fin.val h; simp [br, blockerAgent] at this
          have hbr_nei : br ≠ i := by
            intro h; have := congrArg Fin.val h
            simp only [br, blockerAgent, i, mainAgent] at this
            omega
          have hbr_per : periodOf br = ⟨r + 1, by omega⟩ := hblocker_period ⟨r, hr_lt_m⟩
          set Sval : ℝ := ∑ x : Fin (2 * m + 1), (θr x).value
          have hSval_nonneg : 0 ≤ Sval := Finset.sum_nonneg fun x _ => (θr x).value_nonneg
          set Bnext : ℝ := c' * Sval + 1
          have hBnext_nonneg : 0 ≤ Bnext := by positivity
          set θnext := Function.update θr br (pointType ⟨r + 1, by omega⟩ Bnext hBnext_nonneg)
          refine ⟨θnext, ?_, ?_, ?_, ?_⟩
          · simp only [θnext, Function.update_of_ne hbr_ne0.symm, hθr0]
          · simp only [θnext, Function.update_of_ne hbr_nei.symm, hθri]
          · intro x hx0 hxi
            by_cases hxbr : x = br
            · subst hxbr
              simp only [θnext, Function.update_self, pointType, hbr_per, and_self]
            · simp only [θnext, Function.update_of_ne hxbr]
              exact hθr_rest x hx0 hxi
          · intro t ht
            rcases Nat.eq_or_lt_of_le ht with ht_eq | ht_lt
            · -- At period t = r + 1: if agent i wins, blocker br loses, contradicting c'-comp!
              intro hi_wins_t
              obtain rfl : t = ⟨r + 1, Nat.succ_lt_succ hr_lt_m⟩ := Fin.ext ht_eq
              have hbr_none : M.policy.alloc θnext br = none :=
                alloc_eq_none_of_point_of_eq_some hfeas
                  (by simp only [θnext, Function.update_self, pointType, le_refl])
                  (by simp only [θnext, Function.update_self, pointType, le_refl]) hi_wins_t hbr_nei
              have hw_le : welfare θnext (M.policy.alloc θnext) ≤ Sval := by
                refine (welfare_le_sum_value (Finset.univ.erase br) fun j hj => .inl ?_).trans ?_
                · simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_not] at hj
                  rwa [hj]
                · calc ∑ x ∈ Finset.univ.erase br, (θnext x).value
                      = ∑ x ∈ Finset.univ.erase br, (θr x).value :=
                        Finset.sum_congr rfl fun x hx => by
                          simp only [θnext, Function.update_of_ne (Finset.mem_erase.mp hx).1]
                    _ ≤ Sval := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                        fun x _ _ => (θr x).value_nonneg
              have hopt_ge : Bnext ≤ optWelfare (fun _ => 1) θnext := by
                simpa only [θnext, Function.update_self, pointType] using
                  value_le_optWelfare_of_single θnext br
              exact hcomp θnext hw_le hopt_ge (by dsimp only [Bnext]; linarith)
            · -- At period t ≤ r: causality from θr!
              have ht_le : t.val ≤ r := Nat.lt_succ_iff.mp ht_lt
              have hagree : ∀ x, (θr x).arrival ≤ t ∨ (θnext x).arrival ≤ t → θr x = θnext x := by
                intro x hx
                by_cases hxbr : x = br
                · subst hxbr
                  have h1 : (θr br).arrival = ⟨r + 1, by omega⟩ :=
                    (hθr_rest br hbr_ne0 hbr_nei).1.trans hbr_per
                  have h2 : (θnext br).arrival = ⟨r + 1, by omega⟩ := by
                    simp only [θnext, Function.update_self, pointType]
                  rw [h1, h2, or_self] at hx
                  exact absurd hx (not_le_of_gt (Nat.lt_succ_of_le ht_le))
                · simp only [θnext, Function.update_of_ne hxbr]
              exact fun hwin => hθr_no t ht_le ((hcausal t θr θnext hagree i).mpr hwin)
      obtain ⟨θk, hθk0, hθki, hθk_rest, hθk_no⟩ := hind tk.val le_rfl
      have hθk_none : M.policy.alloc θk i = none := by
        cases h : M.policy.alloc θk i with
        | none => rfl
        | some t =>
          have ht := (M.policy.alloc_in_window θk i t h).2
          rw [hθki] at ht
          exact absurd h (hθk_no t ht)
      -- Yet updating i in θk to (0, 0, Y - 1) agrees with θbig at t = 0, so i wins at t = 0!
      have hsmall_wins :
          M.policy.alloc (Function.update θk i (pointType 0 (Y - 1) hY1_nonneg)) i = some 0 :=
        (hcausal 0 _ _ (hagree0 θBase θk _ (hBase0.trans hθk0.symm) fun x hx0 hxi =>
          ⟨by rw [hBase x hx0], (hθk_rest x hx0 hxi).1⟩) i).mp hwin_big0_base
      have hθk_some : (M.policy.alloc θk i).isSome := by
        have := hmono i θk (pointType 0 (Y - 1) hY1_nonneg) (intervalType 0 tk h0tk Y hY_nonneg)
          le_rfl h0tk (by dsimp [pointType, intervalType]; linarith)
          (by rw [hsmall_wins]; rfl)
        rwa [← hθki, Function.update_eq_self] at this
      simp [hθk_none] at hθk_some
    -- Step 3: Late-departure truthfulness gives `cv(0, 0) ≤ cv(0, tk) ≤ cv(tk, tk)`
    have hwin_00_Y :
        M.policy.alloc (Function.update θStar i (pointType 0 Y hY_nonneg)) i = some 0 := by
      have hwin_00_small :
          M.policy.alloc (Function.update θStar i (pointType 0 (Y - 1) hY1_nonneg)) i = some 0 :=
        (hcausal 0 _ _ (fun x hx => (hagreeSB _ x hx.symm).symm) i).mp hwin_big0_base
      exact (hpoint θStar 0 Y hY_nonneg).resolve_left (Option.isSome_iff_ne_none.mp
        (hmono i θStar (pointType 0 (Y - 1) hY1_nonneg) (pointType 0 Y hY_nonneg) le_rfl le_rfl
          (by dsimp [pointType]; linarith) (by rw [hwin_00_small]; rfl)))
    have hcv00_le_0tk :
        M.policy.criticalValue θStar i 0 0 le_rfl ≤ M.policy.criticalValue θStar i 0 tk h0tk := by
      -- Utility of the true type `(0, 0, Y)` when `i` reports `τ` and wins at period `0`.
      have hutil : ∀ τ : AgentType (Fin (m + 1)),
          M.policy.alloc (Function.update θStar i τ) i = some 0 →
          M.utility i (pointType 0 Y hY_nonneg) (Function.update θStar i τ) =
            Y - (M.policy.criticalValue θStar i τ.arrival τ.departure
              τ.arrival_le_departure).toReal := by
        intro τ hτ
        unfold Mechanism.utility
        rw [hτ, AgentType.realizedValue_some_of_inWindow ⟨le_rfl, le_rfl⟩, hpay_eq]
        unfold Policy.criticalPayment
        simp only [hτ, Option.isSome_some, ↓reduceIte, Function.update_self,
          Policy.criticalValue_update]
      have hds := hdsic_nea i (Function.update θStar i (intervalType 0 tk h0tk Y hY_nonneg))
        (pointType 0 Y hY_nonneg) (by simp [AgentType.NoEarlyArrival])
      rw [Function.update_idem, hutil _ hwin_tk_at_0, hutil _ hwin_00_Y] at hds
      have hfin00 : M.policy.criticalValue θStar i 0 0 le_rfl ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          (M.policy.criticalValue_le_of_isSome hY_nonneg (by rw [hwin_00_Y]; rfl))
      have hfin0tk : M.policy.criticalValue θStar i 0 tk h0tk ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          (M.policy.criticalValue_le_of_isSome hY_nonneg (by rw [hwin_tk_at_0]; rfl))
      exact (ENNReal.toReal_le_toReal hfin00 hfin0tk).mp (by linarith)
    have hcv0tk_le_tktk :
        M.policy.criticalValue θStar i 0 tk h0tk ≤ M.policy.criticalValue θStar i tk tk le_rfl :=
      M.policy.criticalValue_antitone hmono le_rfl h0tk h0tk le_rfl
    have hvlow_lt : ENNReal.ofReal vlow < M.policy.criticalValue θStar i tk tk le_rfl := by
      have hlt : ENNReal.ofReal vlow < ENNReal.ofReal (1 / c') := by
        refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hvlow_pos.le).mpr ?_
        dsimp only [vlow]
        rw [div_lt_div_iff₀ (by positivity) hc'_pos]
        linarith
      exact lt_of_lt_of_le hlt ((hcv00_ge.trans hcv00_le_0tk).trans hcv0tk_le_tktk)
    by_contra hne
    have hle := M.policy.criticalValue_le_self (Option.isSome_iff_ne_none.mpr hne)
    rw [hStar_main k] at hle
    exact not_le_of_gt hvlow_lt hle
  -- Step 4: In θStar, welfare ≤ 1 while optWelfare ≥ 1 + m * vlow > c'!
  have hwStar : welfare θStar (M.policy.alloc θStar) ≤ 1 := by
    refine (welfare_le_sum_value {0} fun j hj => ?_).trans_eq (by rw [Finset.sum_singleton, hStar0])
    have hj0v : j.val ≠ 0 := fun h => Finset.notMem_singleton.1 hj (Fin.ext h)
    by_cases hjm : j.val ≤ m
    · left
      have hj_eq : j = mainAgent ⟨j.val - 1, by omega⟩ := by
        ext; simp [mainAgent]; omega
      rw [hj_eq, hmain_loses]
    · right
      simp only [θStar, hj0v, hjm, ↓reduceIte, pointType]
  have hoptStar : 1 + (m : ℝ) * vlow ≤ optWelfare (fun _ => 1) θStar := by
    let fStar : Fin (2 * m + 1) → Option (Fin (m + 1)) := fun j =>
      if h : j.val ≤ m then some ⟨j.val, Nat.lt_succ_of_le h⟩ else none
    have hfStar : IsExpiringAllocation (fun _ => 1) θStar fStar := by
      refine isExpiringAllocation_unit (fun j t h => ?_) fun x y t hx hy => ?_
      · simp only [fStar] at h
        split_ifs at h with hjm
        rw [← Option.some.inj h]
        by_cases hj0 : j.val = 0
        · simp only [θStar, hj0, ↓reduceIte, pointType, AgentType.InWindow]
          exact ⟨le_rfl, le_rfl⟩
        · simp only [θStar, hj0, hjm, ↓reduceIte, pointType, periodOf, AgentType.InWindow]
          exact ⟨le_rfl, le_rfl⟩
      · simp only [fStar] at hx hy
        split_ifs at hx hy
        exact Fin.ext ((congrArg Fin.val (Option.some.inj hx)).trans
          (congrArg Fin.val (Option.some.inj hy)).symm)
    have hrv : ∀ j : Fin (2 * m + 1), j.val ≤ m →
        (θStar j).realizedValue (fStar j) = (θStar j).value := fun j hj => by
      have h : fStar j = some ⟨j.val, Nat.lt_succ_of_le hj⟩ := by simp [fStar, hj]
      rw [h, AgentType.realizedValue_some_of_inWindow (hfStar.1 j _ h)]
    have hmain_inj : Function.Injective mainAgent := fun a b h => Fin.ext (by
      have := congrArg Fin.val h; simp only [mainAgent] at this; omega)
    have h0_notin : (0 : Fin (2 * m + 1)) ∉ Finset.univ.image mainAgent := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro k h
      have := congrArg Fin.val h
      simp [mainAgent] at this
    -- The anchor and the main agents alone already realize `1 + m * vlow` under `fStar`.
    calc 1 + (m : ℝ) * vlow
        = ∑ j ∈ insert 0 (Finset.univ.image mainAgent), (θStar j).realizedValue (fStar j) := by
          rw [Finset.sum_insert h0_notin, Finset.sum_image fun a _ b _ h => hmain_inj h,
            hrv 0 (by simp), hStar0, Fintype.sum_congr _ _ fun k => hrv (mainAgent k) k.isLt]
          simp only [hStar_main, pointType, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ ≤ welfare θStar fStar := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun j _ _ => (θStar j).realizedValue_nonneg _
      _ ≤ optWelfare (fun _ => 1) θStar := welfare_le_optWelfare hfStar
  have hstrict : c' < (m : ℝ) * vlow := by
    dsimp only [vlow]
    rw [mul_one_div, lt_div_iff₀ (by positivity)]
    linarith
  exact hcomp θStar hwStar hoptStar (by linarith)

end LowerBounds

end Cslib.GameTheory.OnlineMechanism
