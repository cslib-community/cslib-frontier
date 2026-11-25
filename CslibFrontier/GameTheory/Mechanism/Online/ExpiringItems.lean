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
  rintro (h | ⟨_, h⟩)
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

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
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

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
  ext j
  unfold topK
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hjA, hlt⟩
    have hne : j ≠ i := fun h => hni (h ▸ Finset.mem_filter.mpr ⟨hjA, hlt⟩)
    refine ⟨⟨hne, hjA⟩, ?_⟩
    unfold rankIn at hlt ⊢
    exact lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.erase_subset i A))) hlt
  · rintro ⟨⟨hne, hjA⟩, hlt⟩
    refine ⟨hjA, ?_⟩
    by_cases hiA : i ∈ A
    · have hnb : ¬ Beats θ i j := by
        intro hbi
        have hlt_ij := rankIn_lt_of_beats hiA hbi
        have hsub : A.filter (fun x => Beats θ x j) ⊆
            insert i ((A.erase i).filter (fun x => Beats θ x j)) := by
          intro x hx
          rw [Finset.mem_filter] at hx
          by_cases hxi : x = i
          · subst hxi; exact Finset.mem_insert_self x _
          · exact Finset.mem_insert_of_mem
              (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxi, hx.1⟩, hx.2⟩)
        have hcard_le : rankIn θ A j ≤ rankIn θ (A.erase i) j + 1 :=
          (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        have hri_lt : rankIn θ A i < k := by omega
        exact hni (Finset.mem_filter.mpr ⟨hiA, hri_lt⟩)
      have heq : A.filter (fun x => Beats θ x j) = (A.erase i).filter (fun x => Beats θ x j) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hxA, hbx⟩
          exact ⟨⟨fun hxi => hnb (hxi ▸ hbx), hxA⟩, hbx⟩
        · rintro ⟨⟨_, hxA⟩, hbx⟩
          exact ⟨hxA, hbx⟩
      unfold rankIn at hlt ⊢
      rwa [heq]
    · rwa [Finset.erase_eq_of_notMem hiA] at hlt

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
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · have hmem : i ∈ greedyAllocatedBefore cap θ t₂.val :=
      greedyAllocatedBefore_mono cap θ hlt (by
        rw [greedyAllocatedBefore_succ_eq]
        exact Finset.mem_union_right _ h₁)
    exact greedyWinnersAt_disjoint_before cap θ t₂ h₂ hmem
  · have hmem : i ∈ greedyAllocatedBefore cap θ t₁.val :=
      greedyAllocatedBefore_mono cap θ hgt (by
        rw [greedyAllocatedBefore_succ_eq]
        exact Finset.mem_union_right _ h₂)
    exact greedyWinnersAt_disjoint_before cap θ t₁ h₁ hmem

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
        · exact ⟨t, Nat.lt_succ_of_lt hlt, ht⟩
        · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hnow⟩
      · rintro ⟨t, hlt, ht⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
        · exact Or.inl ⟨t, hlt', ht⟩
        · have htk : (⟨k, hk⟩ : Fin T) = t := Fin.ext heq.symm
          rw [← htk] at ht
          exact Or.inr ht
    · rw [ih]
      constructor
      · rintro ⟨t, hlt, ht⟩
        exact ⟨t, Nat.lt_succ_of_lt hlt, ht⟩
      · rintro ⟨t, hlt, ht⟩
        exact ⟨t, by omega, ht⟩

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
  constructor
  · intro h
    split_ifs at h with hex
    · have ht := Option.some.inj h
      rw [← ht]
      exact Classical.choose_spec hex
  · intro ht
    have hex : ∃ s : Fin T, i ∈ greedyWinnersAt cap θ s := ⟨t, ht⟩
    simp only [hex, ↓reduceDIte, Option.some.injEq]
    exact greedyWinnersAt_unique cap θ (Classical.choose_spec hex) ht

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
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hprev]
    constructor
    · rintro ⟨hn, hw⟩
      exact ⟨hn, hagree j (Or.inl hw.1) ▸ hw⟩
    · rintro ⟨hn, hw⟩
      exact ⟨hn, (hagree j (Or.inr hw.1)).symm ▸ hw⟩
  unfold greedyWinnersAt
  dsimp only
  rw [hactive]
  ext j
  unfold topK rankIn
  rw [Finset.mem_filter]
  conv_rhs => rw [Finset.mem_filter]
  refine and_congr_right fun hj => ?_
  have hj_eq : θ j = θ' j := hagree j (Or.inr (Finset.mem_filter.mp hj).2.2.1)
  have hfilt :
      ((Finset.univ.filter fun x =>
          x ∉ greedyAllocatedBefore cap θ' t.val ∧ (θ' x).InWindow t).filter
        fun x => Beats θ x j) =
      ((Finset.univ.filter fun x =>
          x ∉ greedyAllocatedBefore cap θ' t.val ∧ (θ' x).InWindow t).filter
        fun x => Beats θ' x j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_right fun hx => ?_
    have hx_eq : θ x = θ' x := hagree x (Or.inr hx.2.1)
    simp only [Beats, hx_eq, hj_eq]
  rw [hfilt]

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
          refine and_congr_right fun hne => ?_
          simp only [θ'₁, θ'₂, Function.update_of_ne hne]
        rw [herase]
        ext j
        unfold topK rankIn
        rw [Finset.mem_filter, Finset.mem_filter]
        refine and_congr_right fun hj => ?_
        have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
        have hfilt :
            ((Finset.univ.filter fun x =>
                x ∉ greedyAllocatedBefore cap θ'₂ k ∧ (θ'₂ x).InWindow tk).erase i |>.filter
              fun x => Beats θ'₁ x j) =
            ((Finset.univ.filter fun x =>
                x ∉ greedyAllocatedBefore cap θ'₂ k ∧ (θ'₂ x).InWindow tk).erase i |>.filter
              fun x => Beats θ'₂ x j) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_erase]
          refine and_congr_right fun hx => ?_
          simp only [Beats, θ'₁, θ'₂, Function.update_of_ne hx.1, Function.update_of_ne hjne]
        rw [hfilt]
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
    · rcases hbj with hlt | ⟨heq, hji⟩
      · left
        simp only [θ'₁, θ'₂, Function.update_self, Function.update_of_ne hne] at hlt ⊢
        linarith
      · left
        simp only [θ'₁, θ'₂, Function.update_self, Function.update_of_ne hne] at heq ⊢
        linarith
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
  have hsplit :
      ∑ i ∈ F, (θ i).value =
        ∑ i ∈ F.filter (fun i => i ∈ G), (θ i).value +
        ∑ i ∈ F.filter (fun i => i ∉ G), (θ i).value :=
    (Finset.sum_filter_add_sum_filter_not F (fun i => i ∈ G) (fun i => (θ i).value)).symm
  have hpart1 : ∑ i ∈ F.filter (fun i => i ∈ G), (θ i).value ≤ ∑ i ∈ G, (θ i).value :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => (Finset.mem_filter.mp hi).2)
      fun i _ _ => (θ i).value_nonneg
  set U := F.filter fun i => i ∉ G
  have hU_eq :
      ∑ i ∈ U, (θ i).value =
        ∑ t : Fin T, ∑ i ∈ U.filter (fun i => f i = some t), (θ i).value := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨t, ht⟩ :=
      Option.isSome_iff_exists.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    rw [Finset.sum_eq_single t]
    · simp only [ht, ↓reduceIte]
    · intro s _ hne
      simp only [ht, Option.some.injEq, hne.symm, ↓reduceIte]
    · intro hnt
      exact absurd (Finset.mem_univ t) hnt
  have hG_eq :
      ∑ i ∈ G, (θ i).value =
        ∑ t : Fin T, ∑ i ∈ greedyWinnersAt cap θ t, (θ i).value := by
    have hdisj :
        Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin T)) : Set (Fin T))
          (greedyWinnersAt cap θ) := by
      intro t₁ _ t₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro i h₁ h₂
      exact hne (greedyWinnersAt_unique cap θ h₁ h₂)
    have hunion : Finset.univ.biUnion (greedyWinnersAt cap θ) = G := by
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, G, Finset.mem_filter,
        Option.isSome_iff_exists, greedyPolicy_alloc_eq_some_iff]
    rw [← hunion, Finset.sum_biUnion hdisj]
  have hpart2 : ∑ i ∈ U, (θ i).value ≤ ∑ i ∈ G, (θ i).value := by
    rw [hU_eq, hG_eq]
    refine Finset.sum_le_sum fun t _ => ?_
    set Ut := U.filter fun i => f i = some t
    set Gt := greedyWinnersAt cap θ t
    by_cases hne : Ut.Nonempty
    · obtain ⟨i₀, hi₀⟩ := hne
      have hi₀_f : f i₀ = some t := (Finset.mem_filter.mp hi₀).2
      have hi₀_notG : i₀ ∉ G := (Finset.mem_filter.mp (Finset.mem_filter.mp hi₀).1).2
      set prev := greedyAllocatedBefore cap θ t.val
      set active := Finset.univ.filter fun i => i ∉ prev ∧ (θ i).InWindow t
      have hmem_active : ∀ i ∈ Ut, i ∈ active := by
        intro i hi
        have hfi : f i = some t := (Finset.mem_filter.mp hi).2
        have hnotG : i ∉ G := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_, hf.1 i t hfi⟩
        intro hmem_prev
        obtain ⟨s, _, hs⟩ := (mem_greedyAllocatedBefore_iff cap θ t.val i).mp hmem_prev
        apply hnotG
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ i, by
          rw [Option.isSome_iff_exists]
          exact ⟨s, (greedyPolicy_alloc_eq_some_iff cap θ i s).mpr hs⟩⟩
      have hnot_topK : ∀ i ∈ Ut, i ∉ Gt := by
        intro i hi hgt
        have hnotG : i ∉ G := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
        apply hnotG
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ i, by
          rw [Option.isSome_iff_exists]
          exact ⟨t, (greedyPolicy_alloc_eq_some_iff cap θ i t).mpr hgt⟩⟩
      have hGt_card : Gt.card = cap t := by
        have hcard := card_topK θ (cap t) active
        change Gt.card = min (cap t) active.card at hcard
        have hrank_ge : cap t ≤ rankIn θ active i₀ := by
          have hni₀ : i₀ ∉ topK θ (cap t) active := hnot_topK i₀ hi₀
          have hmem₀ : i₀ ∈ active := hmem_active i₀ hi₀
          have : ¬ rankIn θ active i₀ < cap t := fun h =>
            hni₀ (Finset.mem_filter.mpr ⟨hmem₀, h⟩)
          omega
        have hlt_card : rankIn θ active i₀ < active.card := rankIn_lt_card (hmem_active i₀ hi₀)
        rw [hcard, min_eq_left (by omega)]
      have hUt_card : Ut.card ≤ Gt.card := by
        rw [hGt_card]
        refine le_trans (Finset.card_le_card ?_) (hf.2 t)
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
      obtain ⟨i_max, hi_max_mem, hi_max⟩ :=
        Finset.exists_max_image Ut (fun i => (θ i).value) ⟨i₀, hi₀⟩
      have hsum_Ut : ∑ i ∈ Ut, (θ i).value ≤ Ut.card • (θ i_max).value :=
        Finset.sum_le_card_nsmul Ut _ (θ i_max).value hi_max
      have hmax_le_Gt : ∀ g ∈ Gt, (θ i_max).value ≤ (θ g).value := fun g hg =>
        value_le_of_beats (beats_of_mem_topK_of_not_mem hg (hmem_active i_max hi_max_mem)
          (hnot_topK i_max hi_max_mem))
      have hGt_sum : Gt.card • (θ i_max).value ≤ ∑ g ∈ Gt, (θ g).value :=
        Finset.card_nsmul_le_sum Gt _ (θ i_max).value hmax_le_Gt
      have hcard_mul : Ut.card • (θ i_max).value ≤ Gt.card • (θ i_max).value := by
        simp only [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hUt_card) (θ i_max).value_nonneg
      exact (hsum_Ut.trans hcard_mul).trans hGt_sum
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      exact Finset.sum_nonneg fun g _ => (θ g).value_nonneg
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
    (hi : f i = some t) (hj : f j = some t) : i = j := by
  classical
  by_contra hne
  have hsub : ({i, j} : Finset ι) ⊆ Finset.univ.filter fun x => f x = some t := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hcard : 2 ≤ (Finset.univ.filter fun x => f x = some t).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hne] at this
  have hle : (Finset.univ.filter fun x => f x = some t).card ≤ 1 := hf.2 t
  omega

/-- Helper: single-agent allocation feasibility for bounding `optWelfare` from below. -/
private theorem value_le_optWelfare_of_single {ι : Type*} [Fintype ι] {T : ℕ}
    (θ : ι → AgentType (Fin T)) (i : ι) :
    (θ i).value ≤ optWelfare (fun _ => 1) θ := by
  classical
  let f : ι → Option (Fin T) := fun j => if j = i then some (θ i).arrival else none
  have hf : IsExpiringAllocation (fun _ => 1) θ f := by
    refine ⟨fun j t h => ?_, fun t => ?_⟩
    · simp only [f] at h
      split_ifs at h with hj
      · subst hj
        have ht := Option.some.inj h
        rw [← ht]
        exact ⟨le_rfl, (θ j).arrival_le_departure⟩
    · have hsub : (Finset.univ.filter fun j => f j = some t) ⊆ {i} := by
        intro j hj
        have hfj := (Finset.mem_filter.mp hj).2
        simp only [f] at hfj
        split_ifs at hfj with hji
        · exact Finset.mem_singleton.mpr hji
      exact (Finset.card_le_card hsub).trans (by simp)
  have hwf : welfare θ f = (θ i).value := by
    unfold welfare
    rw [Finset.sum_eq_single i]
    · simp only [f, ↓reduceIte]
      exact AgentType.realizedValue_some_of_inWindow ⟨le_rfl, (θ i).arrival_le_departure⟩
    · intro j _ hne
      simp only [f, hne, ↓reduceIte, AgentType.realizedValue_none]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
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
    refine ⟨fun x t h => ?_, fun t => ?_⟩
    · simp only [f] at h
      split_ifs at h with hxi hxj
      · subst hxi; exact (Option.some.inj h) ▸ hi
      · subst hxj; exact (Option.some.inj h) ▸ hj
    · by_cases ht0 : t = t₀
      · subst ht0
        have hsub : (Finset.univ.filter fun x => f x = some t) ⊆ {i} := by
          intro x hx
          have hfx := (Finset.mem_filter.mp hx).2
          simp only [f] at hfx
          split_ifs at hfx with hxi hxj
          · exact Finset.mem_singleton.mpr hxi
          · exact absurd (Option.some.inj hfx).symm ht
        exact (Finset.card_le_card hsub).trans (by simp)
      · by_cases ht1 : t = t₁
        · subst ht1
          have hsub : (Finset.univ.filter fun x => f x = some t) ⊆ {j} := by
            intro x hx
            have hfx := (Finset.mem_filter.mp hx).2
            simp only [f] at hfx
            split_ifs at hfx with hxi hxj
            · exact absurd (Option.some.inj hfx) ht
            · exact Finset.mem_singleton.mpr hxj
          exact (Finset.card_le_card hsub).trans (by simp)
        · have hempty : (Finset.univ.filter fun x => f x = some t) = ∅ := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false, f]
            split_ifs with hxi hxj
            · exact fun h => ht0 (Option.some.inj h).symm
            · exact fun h => ht1 (Option.some.inj h).symm
            · exact not_false
          rw [hempty]; simp
  have hwf : welfare θ f = (θ i).value + (θ j).value := by
    unfold welfare
    have hsub : ({i, j} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_pair hij]
      simp only [f, ↓reduceIte, hij.symm]
      rw [AgentType.realizedValue_some_of_inWindow hi,
        AgentType.realizedValue_some_of_inWindow hj]
    · intro x _ hx
      rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      simp only [f, hx.1, hx.2, ↓reduceIte, AgentType.realizedValue_none]
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
  have hδc1 : c * (1 + 2 * δ) < 2 + 2 * δ := by
    have h1 : c - 1 ≤ |c| + 1 := by linarith [le_abs_self c]
    have h2 : 2 * (c - 1) * δ ≤ (2 - c) / 2 := by
      have : 2 * (c - 1) * δ ≤ 2 * (|c| + 1) * δ := by nlinarith [hδpos]
      have hsimp : 2 * (|c| + 1) * δ = (2 - c) / 2 := by
        dsimp only [δ]
        have hne : (4 * (|c| + 1) : ℝ) ≠ 0 := by positivity
        field_simp [hne]
        ring
      linarith
    linarith
  have hδc2 : c * (1 + δ) < 2 + 2 * δ := by
    have h1 : c - 2 ≤ |c| + 1 := by linarith [le_abs_self c]
    have h2 : (c - 2) * δ ≤ (2 - c) / 4 := by
      have : (c - 2) * δ ≤ (|c| + 1) * δ := by nlinarith [hδpos]
      have hsimp : (|c| + 1) * δ = (2 - c) / 4 := by
        dsimp only [δ]
        have hne : (4 * (|c| + 1) : ℝ) ≠ 0 := by positivity
        field_simp [hne]
      linarith
    linarith
  set B : ℝ := (|c| + 1) * (2 + 2 * δ) + 1
  have hBpos : 0 < B := by positivity
  have h01 : (0 : Fin 2) ≤ (1 : Fin 2) := by decide
  set t0_1 : AgentType (Fin 2) := pointType 0 1 (by norm_num)
  set t0_1d : AgentType (Fin 2) := pointType 0 (1 + δ) (by linarith)
  set t1_0 : AgentType (Fin 2) := pointType 1 0 le_rfl
  set t1_B : AgentType (Fin 2) := pointType 1 B hBpos.le
  set θA : Fin 3 → AgentType (Fin 2) := ![t0_1, t0_1d, t1_0]
  have hbound_three :
      ∀ (θ : Fin 3 → AgentType (Fin 2)),
        welfare θ (M.policy.alloc θ) =
          (θ 0).realizedValue (M.policy.alloc θ 0) +
          (θ 1).realizedValue (M.policy.alloc θ 1) +
          (θ 2).realizedValue (M.policy.alloc θ 2) := fun θ => by
    simp only [welfare, Fin.sum_univ_three]
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
    have hθA_w_arr : (θA w).arrival = 0 := by fin_cases w <;> simp_all [θA, t0_1, t0_1d]
    have hθA_w_dep : (θA w).departure = 0 := by fin_cases w <;> simp_all [θA, t0_1, t0_1d]
    have hθA_o_arr : (θA o).arrival = 0 := by fin_cases o <;> simp_all [θA, t0_1, t0_1d]
    have hθA_o_dep : (θA o).departure = 0 := by fin_cases o <;> simp_all [θA, t0_1, t0_1d]
    have hbound_wo2 : ∀ (θ : Fin 3 → AgentType (Fin 2)),
        welfare θ (M.policy.alloc θ) =
          (θ w).realizedValue (M.policy.alloc θ w) +
          (θ o).realizedValue (M.policy.alloc θ o) +
          (θ 2).realizedValue (M.policy.alloc θ 2) := by
      intro θ
      rw [hbound_three θ]
      fin_cases w <;> fin_cases o <;> simp_all
      ring
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
        (by rw [hθA_w_arr]) (by rw [hθA_w_dep]; exact h01) hgt
        (by rw [← hθBw, Function.update_eq_self, hwB]; rfl)
    obtain ⟨tC, htC⟩ := Option.isSome_iff_exists.mp hwC_some
    fin_cases tC
    · set θD : Fin 3 → AgentType (Fin 2) := Function.update θC 2 t1_0
      have hwD : M.policy.alloc θD w = some 0 :=
        hcausal_upd2 θC t1_0
          (by dsimp only [θC, θB]; rw [Function.update_of_ne hw2.symm, Function.update_self])
          rfl htC
      have hθDo : θD o = θA o := by
        simp only [θD, θC, θB, Function.update_of_ne ho2, Function.update_of_ne hwo.symm]
      have hθDw : θD w = intervalType 0 1 h01 v_ext hv_ext := by
        simp only [θD, θC, Function.update_of_ne hw2, Function.update_self]
      have hθD2 : θD 2 = t1_0 := Function.update_self 2 _ _
      have hoD_none : M.policy.alloc θD o = none := by
        cases ho : M.policy.alloc θD o with
        | none => rfl
        | some s =>
          have hs0 : s = 0 := le_antisymm
            (by simpa only [hθDo, hθA_o_dep] using (M.policy.alloc_in_window θD o s ho).2)
            (Fin.zero_le s)
          rw [hs0] at ho
          exact absurd (eq_of_alloc_eq_some_unit (hfeas θD) ho hwD) hwo.symm
      have hwD_le : welfare θD (M.policy.alloc θD) ≤ v_ext := by
        rw [hbound_wo2 θD, hoD_none, AgentType.realizedValue_none, add_zero]
        have hwv : (θD w).realizedValue (M.policy.alloc θD w) ≤ v_ext := by
          have := (θD w).realizedValue_le_value (M.policy.alloc θD w)
          rwa [show (θD w).value = v_ext from congrArg AgentType.value hθDw] at this
        have h2v : (θD 2).realizedValue (M.policy.alloc θD 2) ≤ 0 := by
          have := (θD 2).realizedValue_le_value (M.policy.alloc θD 2)
          rwa [show (θD 2).value = 0 from congrArg AgentType.value hθD2] at this
        linarith
      have hoptD : 2 + 2 * δ ≤ optWelfare (fun _ => 1) θD := by
        have h := add_le_optWelfare_of_pair θD (i := o) (j := w) (t₀ := 0) (t₁ := 1)
          hwo.symm (by decide)
          (by rw [hθDo]; exact ⟨le_of_eq hθA_o_arr, le_of_eq hθA_o_dep.symm⟩)
          (by rw [hθDw]; exact ⟨h01, le_rfl⟩)
        rw [hθDo, hθDw] at h
        dsimp only [intervalType] at h
        linarith
      refine ⟨θD, ?_⟩
      by_cases hc0 : 0 ≤ c
      · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hwD_le hc0) (lt_of_lt_of_le hc_lt hoptD)
      · have hneg : c * welfare θD (M.policy.alloc θD) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc0) (welfare_nonneg _ _)
        linarith
    · have hθC2 : θC 2 = t1_B := by
        simp only [θC, θB, Function.update_of_ne hw2.symm, Function.update_self]
      have hθCo : θC o = θA o := by
        simp only [θC, θB, Function.update_of_ne hwo.symm, Function.update_of_ne ho2]
      have hθCw : θC w = intervalType 0 1 h01 v_ext hv_ext := Function.update_self w _ _
      have h2C_none : M.policy.alloc θC 2 = none := by
        cases h2 : M.policy.alloc θC 2 with
        | none => rfl
        | some s =>
          have hs1 : s = 1 := le_antisymm (Fin.le_last s)
            (by simpa only [hθC2, pointType] using (M.policy.alloc_in_window θC 2 s h2).1)
          rw [hs1] at h2
          exact absurd (eq_of_alloc_eq_some_unit (hfeas θC) h2 htC) hw2.symm
      have hwC : welfare θC (M.policy.alloc θC) ≤ 2 + 2 * δ := by
        rw [hbound_wo2 θC, h2C_none, AgentType.realizedValue_none, add_zero]
        have hwv : (θC w).realizedValue (M.policy.alloc θC w) ≤ v_ext := by
          have := (θC w).realizedValue_le_value (M.policy.alloc θC w)
          rwa [show (θC w).value = v_ext from congrArg AgentType.value hθCw] at this
        have hov : (θC o).realizedValue (M.policy.alloc θC o) ≤ (θA o).value := by
          have := (θC o).realizedValue_le_value (M.policy.alloc θC o)
          rwa [show (θC o).value = (θA o).value from congrArg AgentType.value hθCo] at this
        linarith
      have hoptC : B ≤ optWelfare (fun _ => 1) θC := by
        simpa only [hθC2, pointType] using value_le_optWelfare_of_single θC 2
      refine ⟨θC, ?_⟩
      have hcwC : c * welfare θC (M.policy.alloc θC) ≤ |c| * (2 + 2 * δ) := by
        calc c * welfare θC (M.policy.alloc θC)
            ≤ |c| * welfare θC (M.policy.alloc θC) :=
              mul_le_mul_of_nonneg_right (le_abs_self c) (welfare_nonneg _ _)
          _ ≤ |c| * (2 + 2 * δ) := mul_le_mul_of_nonneg_left hwC (abs_nonneg c)
      dsimp only [B] at hoptC
      linarith
  by_cases h1A : M.policy.alloc θA 1 = some 0
  · exact hwin0_case 1 0 (by decide) (by decide) (by decide) (1 + 2 * δ) (by linarith)
      (by dsimp [θA, t0_1d]; linarith) (by dsimp [θA, t0_1]; ring) hδc1 h1A
  · by_cases h0A : M.policy.alloc θA 0 = some 0
    · exact hwin0_case 0 1 (by decide) (by decide) (by decide) (1 + δ) (by linarith)
        (by dsimp [θA, t0_1]; linarith) (by dsimp [θA, t0_1d]; ring) hδc2 h0A
    · -- Case 3: Neither Agent 0 nor Agent 1 wins t = 0 in θA.
      have hnone_of_dep0 : ∀ i : Fin 3, (θA i).departure = 0 →
          M.policy.alloc θA i ≠ some 0 → M.policy.alloc θA i = none := by
        intro i hdep hne
        cases hi : M.policy.alloc θA i with
        | none => rfl
        | some s =>
          have hs0 : s = 0 := le_antisymm
            (hdep ▸ (M.policy.alloc_in_window θA i s hi).2) (Fin.zero_le s)
          exact absurd (hs0 ▸ hi) hne
      have h0A_none : M.policy.alloc θA 0 = none := hnone_of_dep0 0 rfl h0A
      have h1A_none : M.policy.alloc θA 1 = none := hnone_of_dep0 1 rfl h1A
      have hwA : welfare θA (M.policy.alloc θA) = 0 := by
        rw [hbound_three θA, h0A_none, h1A_none, AgentType.realizedValue_none,
          AgentType.realizedValue_none, zero_add, zero_add]
        have hge := (θA 2).realizedValue_nonneg (M.policy.alloc θA 2)
        have hle := (θA 2).realizedValue_le_value (M.policy.alloc θA 2)
        have hv2 : (θA 2).value = 0 := rfl
        linarith
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
  have hm_pos : 0 < m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    subst hm0
    simp only [Nat.cast_zero] at hm
    have : (0 : ℝ) < 2 * c' ^ 2 := by positivity
    linarith
  refine ⟨2 * m + 1, m + 1, fun M hfeas hcausal hdsic_nea hir hnpt hlz => ?_⟩
  by_contra hcomp_not
  push Not at hcomp_not
  have hcomp : ∀ θ : Fin (2 * m + 1) → AgentType (Fin (m + 1)),
      optWelfare (fun _ => 1) θ ≤ c' * welfare θ (M.policy.alloc θ) := fun θ =>
    (hcomp_not θ).trans (mul_le_mul_of_nonneg_right hc_le (welfare_nonneg _ _))
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
  have hmain_period : ∀ k : Fin m, periodOf (mainAgent k) = ⟨k.val + 1, by omega⟩ := by
    intro k
    have hle : k.val + 1 ≤ m := k.isLt
    simp only [periodOf, mainAgent, hle, ↓reduceDIte]
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
  -- Helper: if agent 0 has value 1 and every other agent either loses or has value 0, welfare ≤ 1.
  have hw_le_one :
      ∀ (θ : Fin (2 * m + 1) → AgentType (Fin (m + 1))),
        (θ 0).value = 1 →
        (∀ j : Fin (2 * m + 1), j ≠ 0 → M.policy.alloc θ j = none ∨ (θ j).value = 0) →
        welfare θ (M.policy.alloc θ) ≤ 1 := by
    intro θ h0v hrest_cond
    unfold welfare
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (2 * m + 1)))]
    have h0le : (θ 0).realizedValue (M.policy.alloc θ 0) ≤ 1 :=
      h0v ▸ (θ 0).realizedValue_le_value (M.policy.alloc θ 0)
    have hrest : ∑ j ∈ Finset.univ.erase (0 : Fin (2 * m + 1)),
        (θ j).realizedValue (M.policy.alloc θ j) ≤ 0 := by
      refine Finset.sum_nonpos fun j hj => ?_
      rcases hrest_cond j (Finset.mem_erase.mp hj).1 with hnone | hv0
      · rw [hnone, AgentType.realizedValue_none]
      · linarith [(θ j).realizedValue_le_value (M.policy.alloc θ j)]
    linarith
  -- Every mainAgent k loses in θStar!
  have hmain_loses : ∀ k : Fin m, M.policy.alloc θStar (mainAgent k) = none := by
    intro k
    set i := mainAgent k
    set tk : Fin (m + 1) := ⟨k.val + 1, by omega⟩
    have hi0 : i ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp [i, mainAgent] at this
    have hθStar_i : θStar i = pointType tk vlow hvlow_pos.le := by
      have h1 : i.val ≠ 0 := by simp [i, mainAgent]
      have h2 : i.val ≤ m := k.isLt
      simp only [θStar, h1, h2, ↓reduceIte, i, hmain_period]
      rfl
    -- Step 1: criticalValue θStar i 0 0 ≥ ENNReal.ofReal (1 / c')
    have hcv00_ge : ENNReal.ofReal (1 / c') ≤ M.policy.criticalValue θStar i 0 0 le_rfl := by
      refine le_sInf fun w hw => ?_
      obtain ⟨z, hz, rfl, hwin_z⟩ := hw
      apply ENNReal.ofReal_le_ofReal
      by_contra hlt
      push Not at hlt
      have hwin0 : M.policy.alloc (Function.update θStar i (pointType 0 z hz)) i = some 0 := by
        obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hwin_z
        have ht0 : t = 0 := le_antisymm
          (by simpa only [Function.update_self, pointType] using
            (M.policy.alloc_in_window _ i t ht).2)
          (Fin.zero_le t)
        exact ht0 ▸ ht
      set θz := Function.update θBase i (pointType 0 z hz)
      have hagree : ∀ j, ((Function.update θStar i (pointType 0 z hz)) j).arrival ≤ 0 ∨
          (θz j).arrival ≤ 0 → Function.update θStar i (pointType 0 z hz) j = θz j := by
        intro j hj
        by_cases hji : j = i
        · subst hji; simp only [θz, Function.update_self]
        · by_cases hj0 : j = 0
          · subst hj0
            simp only [θz, Function.update_of_ne hji, θStar, θBase, Fin.val_zero, ↓reduceIte]
          · exfalso
            have hp := hperiod_pos j hj0
            have h1 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
            simp only [θz, Function.update_of_ne hji, θStar, θBase, h1, ↓reduceIte] at hj
            rcases hj with h | h
            · split_ifs at h <;> exact not_lt_of_ge h hp
            · exact not_lt_of_ge h hp
      have hwin_θz : M.policy.alloc θz i = some 0 := (hcausal 0 _ θz hagree i).mp hwin0
      have h0_none : M.policy.alloc θz 0 = none := by
        cases h0 : M.policy.alloc θz 0 with
        | none => rfl
        | some s =>
          have hs0 : s = 0 := le_antisymm
            (by simpa only [θz, Function.update_of_ne hi0.symm, θBase, Fin.val_zero, ↓reduceIte,
              pointType] using (M.policy.alloc_in_window θz 0 s h0).2)
            (Fin.zero_le s)
          exact absurd (eq_of_alloc_eq_some_unit (hfeas θz) (hs0 ▸ h0) hwin_θz) hi0.symm
      have hw_le : welfare θz (M.policy.alloc θz) ≤ z := by
        unfold welfare
        have hsum : ∑ j : Fin (2 * m + 1), (θz j).realizedValue (M.policy.alloc θz j) ≤
            (θz i).realizedValue (M.policy.alloc θz i) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          have hrest :
              ∑ j ∈ Finset.univ.erase i, (θz j).realizedValue (M.policy.alloc θz j) ≤ 0 := by
            refine Finset.sum_nonpos fun j hj => ?_
            have hji : j ≠ i := (Finset.mem_erase.mp hj).1
            by_cases hj0 : j = 0
            · subst hj0; rw [h0_none, AgentType.realizedValue_none]
            · have hle := (θz j).realizedValue_le_value (M.policy.alloc θz j)
              have hval0 : (θz j).value = 0 := by
                have h1 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
                simp only [θz, Function.update_of_ne hji, θBase, h1, ↓reduceIte, pointType]
              linarith
          linarith
        have hival : (θz i).realizedValue (M.policy.alloc θz i) ≤ z := by
          have := (θz i).realizedValue_le_value (M.policy.alloc θz i)
          simpa only [θz, Function.update_self, pointType] using this
        exact hsum.trans hival
      have hopt1 : 1 ≤ optWelfare (fun _ => 1) θz := by
        have := value_le_optWelfare_of_single θz 0
        simpa only [θz, Function.update_of_ne hi0.symm, θBase, Fin.val_zero, ↓reduceIte,
          pointType] using this
      have hcz : c' * z < 1 := by
        have := (lt_div_iff₀ hc'_pos).mp hlt
        linarith
      have hccomp := hcomp θz
      have := mul_le_mul_of_nonneg_left hw_le hc'_pos.le
      linarith
    -- Step 2: For Y := 2 * c' + 1, agent i wins at t = 0 under (0, 0, Y - 1) and (0, tk, Y)
    set Y : ℝ := 2 * c' + 1
    have hY1_nonneg : 0 ≤ Y - 1 := by dsimp [Y]; linarith
    have hY_nonneg : 0 ≤ Y := by dsimp [Y]; linarith
    have h0tk : (0 : Fin (m + 1)) ≤ tk := Fin.zero_le tk
    have hwin_big0_base :
        M.policy.alloc (Function.update θBase i (pointType 0 (Y - 1) hY1_nonneg)) i = some 0 := by
      set θbig := Function.update θBase i (pointType 0 (Y - 1) hY1_nonneg)
      by_contra hne
      have hi_none : M.policy.alloc θbig i = none := by
        cases h : M.policy.alloc θbig i with
        | none => rfl
        | some s =>
          have hs0 : s = 0 := le_antisymm
            (by simpa only [θbig, Function.update_self, pointType] using
              (M.policy.alloc_in_window θbig i s h).2)
            (Fin.zero_le s)
          exact absurd (hs0 ▸ h) hne
      have hw_le : welfare θbig (M.policy.alloc θbig) ≤ 1 := by
        refine hw_le_one θbig ?_ fun j hj0 => ?_
        · simp only [θbig, Function.update_of_ne hi0.symm, θBase, Fin.val_zero, ↓reduceIte,
            pointType]
        · by_cases hji : j = i
          · exact Or.inl (hji ▸ hi_none)
          · right
            have h1 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
            simp only [θbig, Function.update_of_ne hji, θBase, h1, ↓reduceIte, pointType]
      have hoptY : Y - 1 ≤ optWelfare (fun _ => 1) θbig := by
        have := value_le_optWelfare_of_single θbig i
        simpa only [θbig, Function.update_self, pointType] using this
      have hccomp := hcomp θbig
      have := mul_le_mul_of_nonneg_left hw_le hc'_pos.le
      dsimp only [Y] at hoptY
      linarith
    -- Claim 2: Agent i MUST win at t = 0 in update θStar i (0, tk, Y)!
    have hwin_tk_at_0 :
        M.policy.alloc (Function.update θStar i (intervalType 0 tk h0tk Y hY_nonneg)) i =
          some 0 := by
      by_contra hnot0
      set θ0 := Function.update θBase i (intervalType 0 tk h0tk Y hY_nonneg)
      have hagree0 :
          ∀ j, ((Function.update θStar i (intervalType 0 tk h0tk Y hY_nonneg)) j).arrival ≤ 0 ∨
            (θ0 j).arrival ≤ 0 →
            Function.update θStar i (intervalType 0 tk h0tk Y hY_nonneg) j = θ0 j := by
        intro j hj
        by_cases hji : j = i
        · subst hji; simp only [θ0, Function.update_self]
        · by_cases hj0 : j = 0
          · subst hj0
            simp only [θ0, Function.update_of_ne hji, θStar, θBase, Fin.val_zero, ↓reduceIte]
          · exfalso
            have hp := hperiod_pos j hj0
            have h1 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
            simp only [θ0, Function.update_of_ne hji, θStar, θBase, h1, ↓reduceIte] at hj
            rcases hj with h | h
            · split_ifs at h <;> exact not_lt_of_ge h hp
            · exact not_lt_of_ge h hp
      have hθ0_not0 : M.policy.alloc θ0 i ≠ some 0 := fun h =>
        hnot0 ((hcausal 0 _ θ0 hagree0 i).mpr h)
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
          · simp only [θ0, Function.update_of_ne hi0.symm, θBase, Fin.val_zero, ↓reduceIte]
          · simp only [θ0, Function.update_self]
          · intro x hx0 hxi
            have h1 : x.val ≠ 0 := fun h => hx0 (Fin.ext h)
            simp only [θ0, Function.update_of_ne hxi, θBase, h1, ↓reduceIte, pointType, and_self]
          · intro t ht
            have ht0 : t = 0 := Fin.ext (Nat.le_zero.mp ht)
            exact ht0 ▸ hθ0_not0
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
              have ht_fin : t = ⟨r + 1, by omega⟩ := Fin.ext ht_eq
              have hbr_none : M.policy.alloc θnext br = none := by
                cases hbr : M.policy.alloc θnext br with
                | none => rfl
                | some s =>
                  have hs_win := M.policy.alloc_in_window θnext br s hbr
                  simp only [θnext, Function.update_self, pointType, AgentType.InWindow] at hs_win
                  have hs_eq : s = ⟨r + 1, by omega⟩ := le_antisymm hs_win.2 hs_win.1
                  rw [hs_eq, ← ht_fin] at hbr
                  exact absurd (eq_of_alloc_eq_some_unit (hfeas θnext) hbr hi_wins_t) hbr_nei
              have hw_le : welfare θnext (M.policy.alloc θnext) ≤ Sval := by
                unfold welfare
                rw [← Finset.add_sum_erase _ _ (Finset.mem_univ br), hbr_none,
                  AgentType.realizedValue_none, zero_add]
                calc ∑ x ∈ Finset.univ.erase br, (θnext x).realizedValue (M.policy.alloc θnext x)
                    ≤ ∑ x ∈ Finset.univ.erase br, (θnext x).value :=
                      Finset.sum_le_sum fun x _ => (θnext x).realizedValue_le_value _
                  _ = ∑ x ∈ Finset.univ.erase br, (θr x).value :=
                      Finset.sum_congr rfl fun x hx => by
                        simp only [θnext, Function.update_of_ne (Finset.mem_erase.mp hx).1]
                  _ ≤ ∑ x : Fin (2 * m + 1), (θr x).value :=
                      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                        fun x _ _ => (θr x).value_nonneg
              have hopt_ge : Bnext ≤ optWelfare (fun _ => 1) θnext := by
                have := value_le_optWelfare_of_single θnext br
                simpa only [θnext, Function.update_self, pointType] using this
              have hccomp := hcomp θnext
              have := mul_le_mul_of_nonneg_left hw_le hc'_pos.le
              dsimp only [Bnext] at hopt_ge
              linarith
            · -- At period t ≤ r: causality from θr!
              have ht_le : t.val ≤ r := Nat.lt_succ_iff.mp ht_lt
              have hagree : ∀ x, (θr x).arrival ≤ t ∨ (θnext x).arrival ≤ t → θr x = θnext x := by
                intro x hx
                by_cases hxbr : x = br
                · subst hxbr
                  exfalso
                  have h1 : (θr br).arrival = ⟨r + 1, by omega⟩ :=
                    (hθr_rest br hbr_ne0 hbr_nei).1.trans hbr_per
                  have h2 : (θnext br).arrival = ⟨r + 1, by omega⟩ := by
                    simp only [θnext, Function.update_self, pointType]
                  rcases hx with h | h
                  · rw [h1] at h; exact not_lt_of_ge h (Nat.lt_succ_of_le ht_le)
                  · rw [h2] at h; exact not_lt_of_ge h (Nat.lt_succ_of_le ht_le)
                · simp only [θnext, Function.update_of_ne hxbr]
              intro hwin
              exact hθr_no t ht_le ((hcausal t θr θnext hagree i).mpr hwin)
      obtain ⟨θk, hθk0, hθki, hθk_rest, hθk_no⟩ := hind tk.val le_rfl
      have hθk_none : M.policy.alloc θk i = none := by
        cases h : M.policy.alloc θk i with
        | none => rfl
        | some t =>
          have ht_le : t.val ≤ tk.val := by
            have := (M.policy.alloc_in_window θk i t h).2
            rw [hθki] at this
            exact this
          exact absurd h (hθk_no t ht_le)
      -- Yet updating i in θk to (0, 0, Y - 1) agrees with θbig at t = 0, so i wins at t = 0!
      set θk_small := Function.update θk i (pointType 0 (Y - 1) hY1_nonneg)
      have hagree_small :
          ∀ x, ((Function.update θBase i (pointType 0 (Y - 1) hY1_nonneg)) x).arrival ≤ 0 ∨
            (θk_small x).arrival ≤ 0 →
            Function.update θBase i (pointType 0 (Y - 1) hY1_nonneg) x = θk_small x := by
        intro x hx
        by_cases hxi : x = i
        · subst hxi; simp only [θk_small, Function.update_self]
        · by_cases hx0 : x = 0
          · subst hx0
            simp only [θk_small, Function.update_of_ne hxi, θBase, Fin.val_zero, ↓reduceIte, hθk0]
          · exfalso
            have hp := hperiod_pos x hx0
            have h1 : x.val ≠ 0 := fun h => hx0 (Fin.ext h)
            simp only [θk_small, Function.update_of_ne hxi, θBase, h1, ↓reduceIte, pointType] at hx
            rcases hx with h | h
            · exact not_lt_of_ge h hp
            · rw [(hθk_rest x hx0 hxi).1] at h
              exact not_lt_of_ge h hp
      have hsmall_wins : M.policy.alloc θk_small i = some 0 :=
        (hcausal 0 _ θk_small hagree_small i).mp hwin_big0_base
      have hθk_some : (M.policy.alloc θk i).isSome := by
        have := hmono i θk (pointType 0 (Y - 1) hY1_nonneg) (intervalType 0 tk h0tk Y hY_nonneg)
          le_rfl h0tk (by dsimp [pointType, intervalType]; linarith)
          (by rw [hsmall_wins]; rfl)
        rwa [← hθki, Function.update_eq_self] at this
      rw [hθk_none] at hθk_some
      simp only [Option.isSome_none, Bool.false_eq_true] at hθk_some
    -- Step 3: Late-departure truthfulness gives `cv(0, 0) ≤ cv(0, tk) ≤ cv(tk, tk)`
    have hwin_00_Y :
        M.policy.alloc (Function.update θStar i (pointType 0 Y hY_nonneg)) i = some 0 := by
      have hwin_00_small :
          M.policy.alloc (Function.update θStar i (pointType 0 (Y - 1) hY1_nonneg)) i = some 0 := by
        have hagree :
            ∀ x, ((Function.update θBase i (pointType 0 (Y - 1) hY1_nonneg)) x).arrival ≤ 0 ∨
              ((Function.update θStar i (pointType 0 (Y - 1) hY1_nonneg)) x).arrival ≤ 0 →
              Function.update θBase i (pointType 0 (Y - 1) hY1_nonneg) x =
                Function.update θStar i (pointType 0 (Y - 1) hY1_nonneg) x := by
          intro x hx
          by_cases hxi : x = i
          · subst hxi; simp only [Function.update_self]
          · by_cases hx0 : x = 0
            · subst hx0
              simp only [Function.update_of_ne hxi, θBase, θStar, Fin.val_zero, ↓reduceIte]
            · exfalso
              have hp := hperiod_pos x hx0
              have h1 : x.val ≠ 0 := fun h => hx0 (Fin.ext h)
              simp only [Function.update_of_ne hxi, θBase, θStar, h1, ↓reduceIte, pointType] at hx
              rcases hx with h | h
              · exact not_lt_of_ge h hp
              · split_ifs at h <;> exact not_lt_of_ge h hp
        exact (hcausal 0 _ _ hagree i).mp hwin_big0_base
      have hsome := hmono i θStar (pointType 0 (Y - 1) hY1_nonneg) (pointType 0 Y hY_nonneg)
        le_rfl le_rfl (by dsimp [pointType]; linarith) (by rw [hwin_00_small]; rfl)
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsome
      have ht0 : t = 0 := le_antisymm
        (by simpa only [Function.update_self, pointType] using
          (M.policy.alloc_in_window _ i t ht).2)
        (Fin.zero_le t)
      exact ht0 ▸ ht
    have hcv00_le_0tk :
        M.policy.criticalValue θStar i 0 0 le_rfl ≤ M.policy.criticalValue θStar i 0 tk h0tk := by
      have hds := hdsic_nea i (Function.update θStar i (intervalType 0 tk h0tk Y hY_nonneg))
        (pointType 0 Y hY_nonneg) (by simp [AgentType.NoEarlyArrival])
      rw [Function.update_idem] at hds
      have hutil_rep :
          M.utility i (pointType 0 Y hY_nonneg)
            (Function.update θStar i (intervalType 0 tk h0tk Y hY_nonneg)) =
          Y - (M.policy.criticalValue θStar i 0 tk h0tk).toReal := by
        unfold Mechanism.utility
        rw [hwin_tk_at_0, AgentType.realizedValue_some_of_inWindow ⟨le_rfl, le_rfl⟩, hpay_eq]
        unfold Policy.criticalPayment
        rw [hwin_tk_at_0]
        simp only [Option.isSome_some, ↓reduceIte, Function.update_self,
          Policy.criticalValue_update]
      have hutil_true :
          M.utility i (pointType 0 Y hY_nonneg)
            (Function.update θStar i (pointType 0 Y hY_nonneg)) =
          Y - (M.policy.criticalValue θStar i 0 0 le_rfl).toReal := by
        unfold Mechanism.utility
        rw [hwin_00_Y, AgentType.realizedValue_some_of_inWindow ⟨le_rfl, le_rfl⟩, hpay_eq]
        unfold Policy.criticalPayment
        rw [hwin_00_Y]
        simp only [Option.isSome_some, ↓reduceIte, Function.update_self,
          Policy.criticalValue_update]
      rw [hutil_rep, hutil_true] at hds
      have htoReal :
          (M.policy.criticalValue θStar i 0 0 le_rfl).toReal ≤
            (M.policy.criticalValue θStar i 0 tk h0tk).toReal := by linarith
      have hfin00 : M.policy.criticalValue θStar i 0 0 le_rfl ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          (M.policy.criticalValue_le_of_isSome hY_nonneg (by rw [hwin_00_Y]; rfl))
      have hfin0tk : M.policy.criticalValue θStar i 0 tk h0tk ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          (M.policy.criticalValue_le_of_isSome hY_nonneg (by rw [hwin_tk_at_0]; rfl))
      exact (ENNReal.toReal_le_toReal hfin00 hfin0tk).mp htoReal
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
    have hsome : (M.policy.alloc θStar i).isSome := Option.isSome_iff_ne_none.mpr hne
    have hle := M.policy.criticalValue_le_self hsome
    rw [hθStar_i] at hle
    exact not_le_of_gt hvlow_lt hle
  -- Step 4: In θStar, welfare ≤ 1 while optWelfare ≥ 1 + m * vlow > c'!
  have hwStar : welfare θStar (M.policy.alloc θStar) ≤ 1 := by
    refine hw_le_one θStar ?_ fun j hj0 => ?_
    · simp only [θStar, Fin.val_zero, ↓reduceIte, pointType]
    · have hj0v : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
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
      refine ⟨fun j t h => ?_, fun t => ?_⟩
      · simp only [fStar] at h
        split_ifs at h with hjm
        · have ht := Option.some.inj h
          rw [← ht]
          by_cases hj0 : j.val = 0
          · simp only [θStar, hj0, ↓reduceIte, pointType, AgentType.InWindow]
            exact ⟨le_rfl, le_rfl⟩
          · simp only [θStar, hj0, hjm, ↓reduceIte, pointType, periodOf, AgentType.InWindow]
            exact ⟨le_rfl, le_rfl⟩
      · have hsub :
            (Finset.univ.filter fun j : Fin (2 * m + 1) => fStar j = some t) ⊆
              {⟨t.val, by omega⟩} := by
          intro j hj
          have hfj := (Finset.mem_filter.mp hj).2
          simp only [fStar] at hfj
          split_ifs at hfj with hjm
          · have ht := congrArg Fin.val (Option.some.inj hfj)
            exact Finset.mem_singleton.mpr (Fin.ext ht)
        exact (Finset.card_le_card hsub).trans (by simp)
    have hwfStar : welfare θStar fStar = 1 + (m : ℝ) * vlow := by
      unfold welfare
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (2 * m + 1)))]
      have h0v : (θStar 0).realizedValue (fStar 0) = 1 := by
        simp only [fStar, Fin.val_zero, Nat.zero_le, ↓reduceDIte, θStar, ↓reduceIte, pointType]
        exact AgentType.realizedValue_some_of_inWindow ⟨le_rfl, le_rfl⟩
      rw [h0v]
      congr 1
      have hmain_sub :
          (Finset.univ.image mainAgent) ⊆ Finset.univ.erase (0 : Fin (2 * m + 1)) := by
        intro j hj
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_erase.mpr ⟨fun h => by
          have := congrArg Fin.val h; simp [mainAgent] at this, Finset.mem_univ _⟩
      rw [← Finset.sum_subset hmain_sub]
      · rw [Finset.sum_image (fun a _ b _ h => by
          ext; have := congrArg Fin.val h; simp [mainAgent] at this; omega)]
        have hterm :
            ∀ k : Fin m, (θStar (mainAgent k)).realizedValue (fStar (mainAgent k)) = vlow := by
          intro k
          have hk1 : (mainAgent k).val ≠ 0 := by simp [mainAgent]
          have hkm : (mainAgent k).val ≤ m := k.isLt
          simp only [fStar, hkm, ↓reduceDIte, θStar, hk1, ↓reduceIte, hmain_period, pointType]
          exact AgentType.realizedValue_some_of_inWindow ⟨le_rfl, le_rfl⟩
        simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      · intro j hj hnot
        have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
        have hnotm : ¬ j.val ≤ m := by
          intro hle
          apply hnot
          refine Finset.mem_image.mpr ⟨⟨j.val - 1, by
            have : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj0 (Fin.ext h))
            omega⟩, Finset.mem_univ _, ?_⟩
          ext
          simp only [mainAgent]
          have : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj0 (Fin.ext h))
          omega
        simp only [fStar, hnotm, ↓reduceDIte, AgentType.realizedValue_none]
    exact hwfStar ▸ welfare_le_optWelfare hfStar
  have hstrict : c' < 1 + (m : ℝ) * vlow := by
    have h1 : c' < (m : ℝ) * vlow := by
      dsimp only [vlow]
      rw [mul_one_div, lt_div_iff₀ (by positivity)]
      linarith
    linarith
  have hccomp := hcomp θStar
  have := mul_le_mul_of_nonneg_left hwStar hc'_pos.le
  linarith

end LowerBounds

end Cslib.GameTheory.OnlineMechanism
