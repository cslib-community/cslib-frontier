/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.HousingMarket.TopTradingCycles
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Cycle-selection order independence of top trading cycles

In each round on a nonempty remaining submarket `R`, `Instance.ttc` (`TopTradingCycles.lean`)
removes all simultaneous top-trading cycles `I.cycleAgents R` at once, following
[SchummerVohra2007], Definition 10.5. Standard presentations of Gale's top trading cycles algorithm
([ShapleyScarf1974]; [Roughgarden2013CS364A], Lecture 9, §3) instead pick *one* directed cycle in
each step, assign its members their pointed houses, remove them, and repeat.

This module proves that any cycle-selection rule (`Instance.CycleSelector`)—removing any nonempty
`topChoice`-closed subset of `I.cycleAgents R` per step—computes an allocation in the strict core
(`CycleSelector.inStrictCore_ttc`) and therefore produces the **exact same allocation** `I.ttc`
(`CycleSelector.ttc_eq_ttc`). In particular, sequential single-cycle elimination
(`Instance.ttcSingleCycle`, removing only the directed cycle of the smallest-indexed cycle agent at
each step) equals `I.ttc` (`Instance.ttcSingleCycle_eq_ttc`).

## Main definitions

* `Instance.cyclePerm`: the allocation trading along any `topChoice`-closed subset of
  `I.cycleAgents R` and leaving all other agents with their endowments.
* `Cslib.Algorithms.Lean.HousingMarket.Instance.CycleSelector`: a rule choosing a nonempty
  `topChoice`-closed subset of `I.cycleAgents R` in every nonempty submarket `R`.
* `Instance.CycleSelector.ttcRounds`, `Instance.CycleSelector.ttc`: rounds and full allocation of
  TTC driven by a `CycleSelector`.
* `Instance.cycleOf`, `Instance.CycleSelector.ofSeed`: directed top-trading cycle of a seed agent
  and single-cycle selector constructor from any seed rule on `I.cycleAgents R`.
* `Instance.singleCycle`, `Instance.singleCycleSelector`, `Instance.ttcSingleCycle`: canonical
  computable single-cycle TTC eliminating one directed cycle per step.

## Main results

* `Instance.CycleSelector.inStrictCore_ttc`: any `CycleSelector` execution lies in the strict core.
* `Instance.CycleSelector.ttc_eq_ttc`: any `CycleSelector` execution equals `I.ttc`.
* `Instance.ttcSingleCycle_eq_ttc`: sequential single-cycle TTC equals `I.ttc`.

## References

* [ShapleyScarf1974]
* [RothPostlewaite1977]
* [SchummerVohra2007]
* [Roughgarden2013CS364A]
-/

public section

namespace Cslib.Algorithms.Lean.HousingMarket

open Function

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- Reallocation that trades along a `topChoice`-closed subset `C ⊆ I.cycleAgents R` and fixes all
agents outside `C`. -/
@[expose] def cyclePerm {R C : Finset (Fin n)} (hC : C ⊆ I.cycleAgents R)
    (hclosed : ∀ a ∈ C, I.topChoice R a ∈ C) : Allocation n :=
  StableMatching.permOfInjective (fun a => if a ∈ C then I.topChoice R a else a) <| by
    intro a b hab
    dsimp only at hab
    by_cases ha : a ∈ C <;> by_cases hb : b ∈ C
    · rw [ite_eq_left ha, ite_eq_left hb] at hab
      exact I.topChoice_injOn_cycleAgents R (hC ha) (hC hb) hab
    · rw [ite_eq_left ha, ite_eq_right hb] at hab
      exact absurd (hab ▸ hclosed a ha) hb
    · rw [ite_eq_right ha, ite_eq_left hb] at hab
      exact absurd (hab ▸ hclosed b hb) ha
    · rwa [ite_eq_right ha, ite_eq_right hb] at hab

theorem cyclePerm_apply_of_mem {R C : Finset (Fin n)} (hC : C ⊆ I.cycleAgents R)
    (hclosed : ∀ a ∈ C, I.topChoice R a ∈ C) {a : Fin n} (ha : a ∈ C) :
    I.cyclePerm hC hclosed a = I.topChoice R a :=
  ite_eq_left ha

theorem cyclePerm_apply_of_notMem {R C : Finset (Fin n)} (hC : C ⊆ I.cycleAgents R)
    (hclosed : ∀ a ∈ C, I.topChoice R a ∈ C) {a : Fin n} (ha : a ∉ C) :
    I.cyclePerm hC hclosed a = a :=
  ite_eq_right ha

/-- A rule selecting, in every nonempty remaining submarket `R`, a nonempty subset of
`I.cycleAgents R` closed under `I.topChoice R` (for example, a single directed cycle or all
simultaneous cycles). -/
structure CycleSelector where
  /-- Agents on cycles selected to trade and exit from submarket `R`. -/
  select : Finset (Fin n) → Finset (Fin n)
  select_subset_cycleAgents : ∀ {R : Finset (Fin n)}, R.Nonempty → select R ⊆ I.cycleAgents R
  select_nonempty : ∀ {R : Finset (Fin n)}, R.Nonempty → (select R).Nonempty
  topChoice_mem_select :
    ∀ {R : Finset (Fin n)} {i : Fin n}, R.Nonempty → i ∈ select R →
      I.topChoice R i ∈ select R

namespace CycleSelector

variable {I} (sel : I.CycleSelector)

theorem select_subset {R : Finset (Fin n)} (hR : R.Nonempty) : sel.select R ⊆ R :=
  (sel.select_subset_cycleAgents hR).trans (I.cycleAgents_subset R)

theorem topChoice_injOn_select {R : Finset (Fin n)} (hR : R.Nonempty) :
    Set.InjOn (I.topChoice R) (sel.select R) :=
  (I.topChoice_injOn_cycleAgents R).mono (sel.select_subset_cycleAgents hR)

theorem card_sdiff_select_lt {R : Finset (Fin n)} (hR : R.Nonempty) :
    (R \ sel.select R).card < R.card :=
  Finset.card_lt_card (Finset.sdiff_ssubset (sel.select_subset hR) (sel.select_nonempty hR))

private theorem card_sdiff_select_le {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k + 1)
    (hR : R.Nonempty) : (R \ sel.select R).card ≤ k := by
  have := sel.card_sdiff_select_lt hR
  omega

/-- At most `k` steps of TTC driven by `sel` on remaining submarket `R`. -/
@[expose] def ttcRounds : ℕ → Finset (Fin n) → Fin n → Fin n
  | 0, _, i => i
  | k + 1, R, i =>
    if R.Nonempty then
      if i ∈ sel.select R then I.topChoice R i else ttcRounds k (R \ sel.select R) i
    else i

theorem ttcRounds_succ_of_mem {k : ℕ} {R : Finset (Fin n)} (hR : R.Nonempty) {i : Fin n}
    (hi : i ∈ sel.select R) : sel.ttcRounds (k + 1) R i = I.topChoice R i := by
  rw [ttcRounds, ite_eq_left hR, ite_eq_left hi]

theorem ttcRounds_succ_of_notMem {k : ℕ} {R : Finset (Fin n)} (hR : R.Nonempty) {i : Fin n}
    (hi : i ∉ sel.select R) :
    sel.ttcRounds (k + 1) R i = sel.ttcRounds k (R \ sel.select R) i := by
  rw [ttcRounds, ite_eq_left hR, ite_eq_right hi]

theorem ttcRounds_of_notMem {k : ℕ} {R : Finset (Fin n)} {i : Fin n} (hi : i ∉ R) :
    sel.ttcRounds k R i = i := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    by_cases hR : R.Nonempty
    · rw [sel.ttcRounds_succ_of_notMem hR fun h => hi (sel.select_subset hR h)]
      exact ih fun h => hi (Finset.sdiff_subset h)
    · rw [ttcRounds, ite_eq_right hR]

theorem ttcRounds_mem {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k) {i : Fin n} (hi : i ∈ R) :
    sel.ttcRounds k R i ∈ R := by
  induction k generalizing R with
  | zero => simp_all
  | succ k ih =>
    have hR : R.Nonempty := ⟨i, hi⟩
    by_cases hiS : i ∈ sel.select R
    · rw [sel.ttcRounds_succ_of_mem hR hiS]
      exact I.topChoice_mem hR i
    · rw [sel.ttcRounds_succ_of_notMem hR hiS]
      exact Finset.sdiff_subset
        (ih (sel.card_sdiff_select_le hk hR) (Finset.mem_sdiff.2 ⟨hi, hiS⟩))

theorem ttcRounds_injOn {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k) :
    Set.InjOn (sel.ttcRounds k R) R := by
  induction k generalizing R with
  | zero =>
    intro a ha
    simp_all
  | succ k ih =>
    intro a ha b hb hab
    have hR : R.Nonempty := ⟨a, ha⟩
    have hk' := sel.card_sdiff_select_le hk hR
    by_cases hCa : a ∈ sel.select R <;> by_cases hCb : b ∈ sel.select R
    · rw [sel.ttcRounds_succ_of_mem hR hCa, sel.ttcRounds_succ_of_mem hR hCb] at hab
      exact sel.topChoice_injOn_select hR hCa hCb hab
    · rw [sel.ttcRounds_succ_of_mem hR hCa, sel.ttcRounds_succ_of_notMem hR hCb] at hab
      exact absurd (hab ▸ sel.topChoice_mem_select hR hCa)
        (Finset.mem_sdiff.1 (sel.ttcRounds_mem hk' (Finset.mem_sdiff.2 ⟨hb, hCb⟩))).2
    · rw [sel.ttcRounds_succ_of_notMem hR hCa, sel.ttcRounds_succ_of_mem hR hCb] at hab
      exact absurd (hab ▸ sel.topChoice_mem_select hR hCb)
        (Finset.mem_sdiff.1 (sel.ttcRounds_mem hk' (Finset.mem_sdiff.2 ⟨ha, hCa⟩))).2
    · rw [sel.ttcRounds_succ_of_notMem hR hCa, sel.ttcRounds_succ_of_notMem hR hCb] at hab
      exact ih hk' (Finset.mem_sdiff.2 ⟨ha, hCa⟩) (Finset.mem_sdiff.2 ⟨hb, hCb⟩) hab

theorem ttcRounds_injective {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k) :
    Injective (sel.ttcRounds k R) := by
  intro a b hab
  by_cases ha : a ∈ R <;> by_cases hb : b ∈ R
  · exact sel.ttcRounds_injOn hk ha hb hab
  · rw [sel.ttcRounds_of_notMem hb] at hab
    exact absurd (hab ▸ sel.ttcRounds_mem hk ha) hb
  · rw [sel.ttcRounds_of_notMem ha] at hab
    exact absurd (hab ▸ sel.ttcRounds_mem hk hb) ha
  · rwa [sel.ttcRounds_of_notMem ha, sel.ttcRounds_of_notMem hb] at hab

/-- The full allocation computed by `n` steps of `sel` starting from `Finset.univ`. -/
@[expose] def ttc : Allocation n :=
  StableMatching.permOfInjective (sel.ttcRounds n Finset.univ)
    (sel.ttcRounds_injective (by rw [Finset.card_univ, Fintype.card_fin]))

@[simp] theorem ttc_apply (i : Fin n) : sel.ttc i = sel.ttcRounds n Finset.univ i := rfl

private theorem eq_ttcRounds_of_le {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k)
    (ν : Allocation n) (S : Finset (Fin n)) (hSR : S ⊆ R) (hS : ∀ i ∈ S, ν i ∈ S)
    (hle : ∀ i ∈ S, I.rank i (ν i) ≤ I.rank i (sel.ttcRounds k R i)) :
    ∀ i ∈ S, ν i = sel.ttcRounds k R i := by
  induction k generalizing R S with
  | zero =>
    intro i hi
    have := hSR hi
    simp_all
  | succ k ih =>
    intro i hi
    have hR : R.Nonempty := ⟨i, hSR hi⟩
    have hk' := sel.card_sdiff_select_le hk hR
    set C := sel.select R
    have hC : ∀ a ∈ S, a ∈ C → ν a = I.topChoice R a := by
      intro a ha haC
      have h1 := hle a ha
      rw [sel.ttcRounds_succ_of_mem hR haC] at h1
      exact I.rank_injective a (le_antisymm h1 (I.rank_topChoice_le (hSR (hS a ha)) a))
    by_cases hiC : i ∈ C
    · rw [sel.ttcRounds_succ_of_mem hR hiC, hC i hi hiC]
    rw [sel.ttcRounds_succ_of_notMem hR hiC]
    have hmaps : ∀ a ∈ S ∩ C, ν a ∈ S ∩ C := by
      intro a ha
      obtain ⟨haS, haC⟩ := Finset.mem_inter.1 ha
      rw [Finset.mem_inter, hC a haS haC]
      exact ⟨hC a haS haC ▸ hS a haS, sel.topChoice_mem_select hR haC⟩
    have hS' : ∀ a ∈ S \ C, ν a ∈ S \ C := by
      intro a ha
      obtain ⟨haS, haC⟩ := Finset.mem_sdiff.1 ha
      refine Finset.mem_sdiff.2 ⟨hS a haS, fun hνC => haC ?_⟩
      exact (Finset.mem_inter.1 (mem_of_apply_mem ν hmaps (Finset.mem_inter.2 ⟨hS a haS, hνC⟩))).2
    refine ih hk' (S \ C) (Finset.sdiff_subset_sdiff hSR le_rfl) hS' (fun a ha => ?_) i
      (Finset.mem_sdiff.2 ⟨hi, hiC⟩)
    have h1 := hle a (Finset.sdiff_subset ha)
    rwa [sel.ttcRounds_succ_of_notMem hR (Finset.mem_sdiff.1 ha).2] at h1

/-- Any `CycleSelector` execution produces an allocation in the strict core. -/
theorem inStrictCore_ttc : I.InStrictCore sel.ttc := by
  rintro S ⟨ν, hS, hle, i, hi, hlt⟩
  have h := sel.eq_ttcRounds_of_le (by simp) ν S (Finset.subset_univ S) hS hle i hi
  rw [ttc_apply, h] at hlt
  exact lt_irrefl _ hlt

/-- **Cycle-selection order independence of TTC**: any `CycleSelector` execution yields the unique
strict-core allocation `I.ttc`. -/
theorem ttc_eq_ttc : sel.ttc = I.ttc :=
  sel.inStrictCore_ttc.eq_ttc

end CycleSelector

/-! ### Directed single-cycle orbits and canonical single-cycle TTC -/

/-- The directed `topChoice R`-orbit of `i₀` within `n` steps. When `i₀ ∈ I.cycleAgents R`, this is
the unique directed top-trading cycle through `i₀` in submarket `R`. -/
@[expose] def cycleOf (R : Finset (Fin n)) (i₀ : Fin n) : Finset (Fin n) :=
  (Finset.range n).image fun k => (I.topChoice R)^[k] i₀

variable {I} in
theorem iterate_mem_cycleAgents {R : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ I.cycleAgents R) : ∀ k : ℕ, (I.topChoice R)^[k] i ∈ I.cycleAgents R
  | 0 => hi
  | k + 1 => by
    rw [iterate_succ_apply']
    exact I.topChoice_mem_cycleAgents (iterate_mem_cycleAgents hi k)

variable {I} in
theorem cycleOf_subset_cycleAgents {R : Finset (Fin n)} {i₀ : Fin n}
    (hi₀ : i₀ ∈ I.cycleAgents R) : I.cycleOf R i₀ ⊆ I.cycleAgents R := by
  rintro a ha
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 ha
  exact I.iterate_mem_cycleAgents hi₀ k

theorem mem_cycleOf_self (R : Finset (Fin n)) (i₀ : Fin n) : i₀ ∈ I.cycleOf R i₀ := by
  have h0 : (I.topChoice R)^[0] i₀ = i₀ := rfl
  exact h0 ▸ Finset.mem_image_of_mem _ (Finset.mem_range.2 i₀.pos)

variable {I} in
theorem topChoice_mem_cycleOf {R : Finset (Fin n)} {i₀ i : Fin n} (hR : R.Nonempty)
    (hi₀ : i₀ ∈ I.cycleAgents R) (hi : i ∈ I.cycleOf R i₀) :
    I.topChoice R i ∈ I.cycleOf R i₀ := by
  have hper : i₀ ∈ periodicPts (I.topChoice R) := (I.mem_cycleAgents hR).1 hi₀
  set p := minimalPeriod (I.topChoice R) i₀
  have hp_pos : 0 < p := minimalPeriod_pos_of_mem_periodicPts hper
  have hp_le : p ≤ n := by
    simpa only [Fintype.card_fin] using minimalPeriod_le_card (f := I.topChoice R) (x := i₀)
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hi
  rw [← iterate_succ_apply' (I.topChoice R), ← Function.iterate_mod_minimalPeriod_eq]
  exact Finset.mem_image_of_mem _ (Finset.mem_range.2 ((Nat.mod_lt _ hp_pos).trans_le hp_le))

variable {I} in
/-- Constructs a single-cycle `CycleSelector` from any rule picking one seed agent inside
`I.cycleAgents R` for each nonempty submarket `R`. -/
@[expose] def CycleSelector.ofSeed (seed : ∀ R : Finset (Fin n), R.Nonempty → Fin n)
    (hseed : ∀ (R : Finset (Fin n)) (hR : R.Nonempty), seed R hR ∈ I.cycleAgents R) :
    I.CycleSelector where
  select R := if hR : R.Nonempty then I.cycleOf R (seed R hR) else ∅
  select_subset_cycleAgents {R} hR := by
    rw [dite_eq_left hR]
    exact I.cycleOf_subset_cycleAgents (hseed R hR)
  select_nonempty {R} hR := by
    rw [dite_eq_left hR]
    exact ⟨seed R hR, I.mem_cycleOf_self R (seed R hR)⟩
  topChoice_mem_select {R i} hR hi := by
    rw [dite_eq_left hR] at hi ⊢
    exact I.topChoice_mem_cycleOf hR (hseed R hR) hi

/-- The single directed cycle in `R` starting at `(I.cycleAgents R).min'` (`∅` when `R = ∅`). -/
@[expose] def singleCycle (R : Finset (Fin n)) : Finset (Fin n) :=
  if hR : R.Nonempty then
    I.cycleOf R ((I.cycleAgents R).min' (I.cycleAgents_nonempty hR))
  else ∅

/-- The canonical `CycleSelector` eliminating one directed cycle (`I.singleCycle R`) per step. -/
@[expose] def singleCycleSelector : I.CycleSelector :=
  CycleSelector.ofSeed (fun R hR => (I.cycleAgents R).min' (I.cycleAgents_nonempty hR))
    (fun R hR => (I.cycleAgents R).min'_mem (I.cycleAgents_nonempty hR))

/-- Sequential single-cycle top trading cycles allocation, eliminating one directed cycle per step.
-/
@[expose] def ttcSingleCycle : Allocation n :=
  I.singleCycleSelector.ttc

/-- Removing top-trading cycles one at a time yields the same allocation as removing all cycles of
each round simultaneously. -/
theorem ttcSingleCycle_eq_ttc : I.ttcSingleCycle = I.ttc :=
  I.singleCycleSelector.ttc_eq_ttc

end Instance

end Cslib.Algorithms.Lean.HousingMarket
