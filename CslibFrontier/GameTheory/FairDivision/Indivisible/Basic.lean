/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Indivisible-goods allocations, fairness hierarchy, and Round-Robin EF1

This module establishes the foundational model for fair division of `m` indivisible goods (`Fin m`)
among `n` agents (`Fin n`), covering both general monotone bundle valuations (`MonotoneValuation`)
and nonnegative additive valuations (`AdditiveValuation`):

* **Bundle allocations (`BundleAllocation n m`):** pairwise-disjoint bundle assignments supporting
  both partial allocations (used by sequential and envy-graph algorithms) and complete allocations
  (`BundleAllocation.IsComplete`), together with single-good insertion (`giveGood`), bundle
  permutation (`relabel`), and single-good transfer (`transferGood`).
* **Fairness and efficiency hierarchy (`MonotoneValuation.IsEnvyFree`, `IsEFX`, `IsEF1`,
  `IsParetoOptimal`):** exact envy-freeness implies strong envy-freeness up to any good (`IsEFX`,
  [PlautRoughgarden2020]), which implies envy-freeness up to one good (`IsEF1`, [Budish2011];
  [CaragiannisKurokawaMoulinProcacciaShahWang2019]), which in turn implies the maximum-marginal-envy
  bound of [LiptonMarkakisMosselSaberi2004] (`IsEF1.val_le_add_maxMarginal`).
* **Round-Robin (`AdditiveValuation.roundRobin`):** sequential picking in cyclic agent order
  `0, 1, …, n - 1` produces a complete `EF1` allocation for every nonnegative additive valuation
  profile (`AdditiveValuation.isComplete_roundRobin`, `AdditiveValuation.isEF1_roundRobin`;
  [CaragiannisKurokawaMoulinProcacciaShahWang2019]).

## Main definitions

* `Cslib.GameTheory.FairDivision.Indivisible.BundleAllocation`: pairwise-disjoint assignment of
  bundles `Fin n → Finset (Fin m)`, with `empty`, `allocatedGoods`, `IsComplete`, `ofAssignment`,
  `completeAllocations`, `giveGood`, `relabel`, and `transferGood`.
* `Cslib.GameTheory.FairDivision.Indivisible.MonotoneValuation`: profile of monotone bundle
  valuations `Fin n → Finset (Fin m) → R`, with `IsEnvyFree`, `IsEFX`, `IsEF1`, `IsParetoOptimal`,
  and `maxMarginal`.
* `Cslib.GameTheory.FairDivision.Indivisible.AdditiveValuation`: profile of nonnegative item weights
  `Fin n → Fin m → R`, inducing `bundleVal`, `toMonotoneValuation`, and `roundRobin`.

## Main results

* `Cslib.GameTheory.FairDivision.Indivisible.MonotoneValuation.IsEnvyFree.isEFX`,
  `Cslib.GameTheory.FairDivision.Indivisible.MonotoneValuation.IsEFX.isEF1`: implication hierarchy
  `IsEnvyFree → IsEFX → IsEF1` for arbitrary monotone valuations.
* `Cslib.GameTheory.FairDivision.Indivisible.MonotoneValuation.IsEF1.val_le_add_maxMarginal`:
  every `EF1` allocation bounds each agent's envy by that agent's maximum marginal item utility
  ([LiptonMarkakisMosselSaberi2004]).
* `Cslib.GameTheory.FairDivision.Indivisible.AdditiveValuation.isComplete_roundRobin`,
  `Cslib.GameTheory.FairDivision.Indivisible.AdditiveValuation.isEF1_roundRobin`: the Round-Robin
  picking sequence produces a complete `EF1` allocation for all nonnegative additive valuations.

## References

* [LiptonMarkakisMosselSaberi2004]
* [Budish2011]
* [CaragiannisKurokawaMoulinProcacciaShahWang2019]
* [PlautRoughgarden2020]
-/

public section

namespace Cslib.GameTheory.FairDivision.Indivisible

/-! ### Part 1: Partial and complete bundle allocations -/

/-- A (possibly partial) allocation of `m` indivisible goods among `n` agents, assigning pairwise
disjoint bundles `bundle i : Finset (Fin m)` to agents `i : Fin n`. -/
@[ext]
structure BundleAllocation (n m : ℕ) where
  /-- Bundle of goods held by each agent. -/
  bundle : Fin n → Finset (Fin m)
  /-- Distinct agents hold disjoint bundles of goods. -/
  pairwiseDisjoint : Pairwise fun i j => Disjoint (bundle i) (bundle j)

instance instDecidableEqBundleAllocation {n m : ℕ} : DecidableEq (BundleAllocation n m) :=
  fun A B => decidable_of_iff (∀ i : Fin n, A.bundle i = B.bundle i)
    ⟨fun h => BundleAllocation.ext (funext h),
      fun h i => congrFun (congrArg BundleAllocation.bundle h) i⟩

namespace BundleAllocation

variable {n m : ℕ}

/-- The empty allocation in which every agent holds `∅`. -/
@[expose] def empty : BundleAllocation n m where
  bundle _ := ∅
  pairwiseDisjoint _ _ _ := Finset.disjoint_empty_left _

@[simp] theorem empty_bundle (i : Fin n) : (empty : BundleAllocation n m).bundle i = ∅ := rfl

/-- If `g` belongs to both `A.bundle i` and `A.bundle j`, then `i = j`. -/
theorem eq_of_mem_bundle {A : BundleAllocation n m} {i j : Fin n} {g : Fin m}
    (hi : g ∈ A.bundle i) (hj : g ∈ A.bundle j) : i = j := by
  by_contra hij
  exact Finset.disjoint_left.1 (A.pairwiseDisjoint hij) hi hj

/-- Set of goods currently assigned to some agent under `A`. -/
@[expose] def allocatedGoods (A : BundleAllocation n m) : Finset (Fin m) :=
  Finset.univ.biUnion A.bundle

@[simp] theorem mem_allocatedGoods {A : BundleAllocation n m} {g : Fin m} :
    g ∈ A.allocatedGoods ↔ ∃ i : Fin n, g ∈ A.bundle i := by
  simp [allocatedGoods]

@[simp] theorem allocatedGoods_empty : (empty : BundleAllocation n m).allocatedGoods = ∅ := by
  ext g
  simp [allocatedGoods]

/-- An allocation is complete when every good `g : Fin m` is assigned to some agent. -/
@[expose] def IsComplete (A : BundleAllocation n m) : Prop :=
  ∀ g : Fin m, ∃ i : Fin n, g ∈ A.bundle i

instance instDecidableIsComplete (A : BundleAllocation n m) : Decidable A.IsComplete :=
  inferInstanceAs (Decidable (∀ g : Fin m, ∃ i : Fin n, g ∈ A.bundle i))

theorem isComplete_iff_allocatedGoods_eq_univ {A : BundleAllocation n m} :
    A.IsComplete ↔ A.allocatedGoods = Finset.univ := by
  simp [IsComplete, Finset.ext_iff]

/-- Complete bundle allocation induced by an item-to-agent assignment `f : Fin m → Fin n`. -/
@[expose] def ofAssignment (f : Fin m → Fin n) : BundleAllocation n m where
  bundle i := Finset.univ.filter fun g => f g = i
  pairwiseDisjoint i j hij := Finset.disjoint_left.2 fun g hgi hgj => by
    have hi : f g = i := (Finset.mem_filter.1 hgi).2
    have hj : f g = j := (Finset.mem_filter.1 hgj).2
    exact hij (hi.symm.trans hj)

@[simp] theorem mem_ofAssignment {f : Fin m → Fin n} {i : Fin n} {g : Fin m} :
    g ∈ (ofAssignment f).bundle i ↔ f g = i := by
  simp [ofAssignment]

theorem isComplete_ofAssignment (f : Fin m → Fin n) : (ofAssignment f).IsComplete :=
  fun g => ⟨f g, by simp⟩

/-- Exhaustive computable list of all item-to-agent assignments `Fin m → Fin n`. -/
@[expose] def allAssignments (n : ℕ) : ∀ m : ℕ, List (Fin m → Fin n)
  | 0 => [Fin.elim0]
  | m + 1 =>
    (List.finRange n).flatMap fun i =>
      (allAssignments n m).map fun f => Fin.cons i f

theorem mem_allAssignments {n : ℕ} : ∀ {m : ℕ} (f : Fin m → Fin n), f ∈ allAssignments n m
  | 0, f => by
    have hf : f = Fin.elim0 := Subsingleton.elim f Fin.elim0
    simp [allAssignments, hf]
  | m + 1, f => by
    rw [allAssignments, List.mem_flatMap]
    refine ⟨f 0, List.mem_finRange (f 0), List.mem_map.2 ⟨Fin.tail f, mem_allAssignments _, ?_⟩⟩
    exact Fin.cons_self_tail f

/-- Exhaustive computable list of all complete allocations of `m` goods among `n` agents. -/
@[expose] def completeAllocationList (n m : ℕ) : List (BundleAllocation n m) :=
  (allAssignments n m).map ofAssignment

/-- Finite enumeration of all complete allocations of `m` goods among `n` agents. -/
@[expose] def completeAllocations (n m : ℕ) : Finset (BundleAllocation n m) :=
  (completeAllocationList n m).toFinset

theorem mem_completeAllocationList_iff {A : BundleAllocation n m} :
    A ∈ completeAllocationList n m ↔ A.IsComplete := by
  rw [completeAllocationList, List.mem_map]
  refine ⟨fun ⟨f, _, h⟩ => h ▸ isComplete_ofAssignment f, fun hA => ?_⟩
  have hne (g : Fin m) : (Finset.univ.filter fun i => g ∈ A.bundle i).Nonempty := by
    obtain ⟨i, hi⟩ := hA g
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
  refine ⟨fun g => (Finset.univ.filter fun i => g ∈ A.bundle i).min' (hne g),
    mem_allAssignments _, BundleAllocation.ext (funext fun i => Finset.ext fun g => ?_)⟩
  have hmem :=
    (Finset.mem_filter.1 ((Finset.univ.filter fun j => g ∈ A.bundle j).min'_mem (hne g))).2
  exact ⟨fun h => (mem_ofAssignment.1 h) ▸ hmem,
    fun hgi => mem_ofAssignment.2 (A.eq_of_mem_bundle hmem hgi)⟩

theorem mem_completeAllocations_iff {A : BundleAllocation n m} :
    A ∈ completeAllocations n m ↔ A.IsComplete := by
  rw [completeAllocations, List.mem_toFinset, mem_completeAllocationList_iff]

/-- Assigns an unallocated good `g ∉ A.allocatedGoods` to agent `i`. -/
@[expose] def giveGood (A : BundleAllocation n m) (i : Fin n) (g : Fin m)
    (hg : g ∉ A.allocatedGoods) : BundleAllocation n m where
  bundle j := if j = i then insert g (A.bundle i) else A.bundle j
  pairwiseDisjoint x y hxy := by
    dsimp only
    have hg_not : ∀ k : Fin n, g ∉ A.bundle k := fun k hk =>
      hg (mem_allocatedGoods.2 ⟨k, hk⟩)
    by_cases hxi : x = i <;> by_cases hyi : y = i
    · exact absurd (hxi.trans hyi.symm) hxy
    · rw [ite_eq_left hxi, ite_eq_right hyi]
      exact Finset.disjoint_insert_left.2 ⟨hg_not y, hxi ▸ A.pairwiseDisjoint hxy⟩
    · rw [ite_eq_right hxi, ite_eq_left hyi]
      exact Finset.disjoint_insert_right.2 ⟨hg_not x, hyi ▸ A.pairwiseDisjoint hxy⟩
    · rw [ite_eq_right hxi, ite_eq_right hyi]
      exact A.pairwiseDisjoint hxy

@[simp] theorem giveGood_bundle_self (A : BundleAllocation n m) (i : Fin n) (g : Fin m)
    (hg : g ∉ A.allocatedGoods) :
    (A.giveGood i g hg).bundle i = insert g (A.bundle i) :=
  ite_eq_left rfl

theorem giveGood_bundle_of_ne (A : BundleAllocation n m) {i j : Fin n} (g : Fin m)
    (hg : g ∉ A.allocatedGoods) (hji : j ≠ i) :
    (A.giveGood i g hg).bundle j = A.bundle j :=
  ite_eq_right hji

@[simp] theorem allocatedGoods_giveGood (A : BundleAllocation n m) (i : Fin n) (g : Fin m)
    (hg : g ∉ A.allocatedGoods) :
    (A.giveGood i g hg).allocatedGoods = insert g A.allocatedGoods := by
  ext x
  simp only [mem_allocatedGoods, Finset.mem_insert, giveGood]
  refine ⟨?_, ?_⟩
  · rintro ⟨j, hj⟩
    by_cases hji : j = i
    · subst hji
      rw [ite_eq_left rfl] at hj
      exact (Finset.mem_insert.1 hj).imp id fun hx => ⟨j, hx⟩
    · rw [ite_eq_right hji] at hj
      exact Or.inr ⟨j, hj⟩
  · rintro (rfl | ⟨j, hj⟩)
    · exact ⟨i, by simp⟩
    · by_cases hji : j = i
      · subst hji
        exact ⟨j, by simp [hj]⟩
      · exact ⟨j, by simp [hji, hj]⟩

/-- Permutes bundles across agents via `σ : Equiv.Perm (Fin n)` (`i` receives `A.bundle (σ i)`). -/
@[expose] def relabel (A : BundleAllocation n m) (σ : Equiv.Perm (Fin n)) :
    BundleAllocation n m where
  bundle i := A.bundle (σ i)
  pairwiseDisjoint _ _ hij := A.pairwiseDisjoint (σ.injective.ne hij)

@[simp] theorem relabel_bundle (A : BundleAllocation n m) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (A.relabel σ).bundle i = A.bundle (σ i) := rfl

@[simp] theorem allocatedGoods_relabel (A : BundleAllocation n m) (σ : Equiv.Perm (Fin n)) :
    (A.relabel σ).allocatedGoods = A.allocatedGoods := by
  ext g
  simp only [mem_allocatedGoods, relabel_bundle]
  exact ⟨fun ⟨i, hi⟩ => ⟨σ i, hi⟩, fun ⟨j, hj⟩ => ⟨σ.symm j, by simpa using hj⟩⟩

@[simp] theorem isComplete_relabel {A : BundleAllocation n m} (σ : Equiv.Perm (Fin n)) :
    (A.relabel σ).IsComplete ↔ A.IsComplete := by
  rw [isComplete_iff_allocatedGoods_eq_univ, isComplete_iff_allocatedGoods_eq_univ,
    allocatedGoods_relabel]

/-- Transfers a single good `g ∈ A.bundle j` from agent `j` to agent `i`. -/
@[expose] def transferGood (A : BundleAllocation n m) (j i : Fin n) (g : Fin m)
    (hg : g ∈ A.bundle j) : BundleAllocation n m where
  bundle k :=
    if k = i then insert g (A.bundle i)
    else if k = j then A.bundle j \ {g}
    else A.bundle k
  pairwiseDisjoint x y hxy := by
    dsimp only
    by_cases hxi : x = i
    · subst hxi
      have hyi : y ≠ x := Ne.symm hxy
      rw [ite_eq_left rfl, ite_eq_right hyi]
      by_cases hyj : y = j
      · subst hyj
        rw [ite_eq_left rfl]
        refine Finset.disjoint_insert_left.2 ⟨by simp, ?_⟩
        exact (A.pairwiseDisjoint hxy).mono_right Finset.sdiff_subset
      · rw [ite_eq_right hyj]
        refine Finset.disjoint_insert_left.2 ⟨fun hgy => hyj (A.eq_of_mem_bundle hgy hg), ?_⟩
        exact A.pairwiseDisjoint hxy
    · rw [ite_eq_right hxi]
      by_cases hyi : y = i
      · subst hyi
        rw [ite_eq_left rfl]
        by_cases hxj : x = j
        · subst hxj
          rw [ite_eq_left rfl]
          refine Finset.disjoint_insert_right.2 ⟨by simp, ?_⟩
          exact (A.pairwiseDisjoint hxy).mono_left Finset.sdiff_subset
        · rw [ite_eq_right hxj]
          refine Finset.disjoint_insert_right.2 ⟨fun hgx => hxj (A.eq_of_mem_bundle hgx hg), ?_⟩
          exact A.pairwiseDisjoint hxy
      · rw [ite_eq_right hyi]
        by_cases hxj : x = j <;> by_cases hyj : y = j
        · exact absurd (hxj.trans hyj.symm) hxy
        · rw [ite_eq_left hxj, ite_eq_right hyj]
          exact (hxj ▸ A.pairwiseDisjoint hxy).mono_left Finset.sdiff_subset
        · rw [ite_eq_right hxj, ite_eq_left hyj]
          exact (hyj ▸ A.pairwiseDisjoint hxy).mono_right Finset.sdiff_subset
        · rw [ite_eq_right hxj, ite_eq_right hyj]
          exact A.pairwiseDisjoint hxy

@[simp] theorem transferGood_bundle_target (A : BundleAllocation n m) (j i : Fin n) (g : Fin m)
    (hg : g ∈ A.bundle j) :
    (A.transferGood j i g hg).bundle i = insert g (A.bundle i) :=
  ite_eq_left rfl

theorem transferGood_bundle_source (A : BundleAllocation n m) {j i : Fin n} (g : Fin m)
    (hg : g ∈ A.bundle j) (hji : j ≠ i) :
    (A.transferGood j i g hg).bundle j = A.bundle j \ {g} := by
  dsimp only [transferGood]
  rw [ite_eq_right hji, ite_eq_left rfl]

theorem transferGood_bundle_other (A : BundleAllocation n m) {j i k : Fin n} (g : Fin m)
    (hg : g ∈ A.bundle j) (hki : k ≠ i) (hkj : k ≠ j) :
    (A.transferGood j i g hg).bundle k = A.bundle k := by
  dsimp only [transferGood]
  rw [ite_eq_right hki, ite_eq_right hkj]

theorem isComplete_transferGood {A : BundleAllocation n m} (j i : Fin n) (g : Fin m)
    (hg : g ∈ A.bundle j) (hA : A.IsComplete) :
    (A.transferGood j i g hg).IsComplete := fun x => by
  by_cases hxg : x = g
  · subst hxg
    exact ⟨i, by simp⟩
  · obtain ⟨k, hkx⟩ := hA x
    by_cases hki : k = i
    · subst hki
      exact ⟨k, by simp [hkx]⟩
    · refine ⟨k, ?_⟩
      by_cases hkj : k = j
      · subst hkj
        rw [transferGood_bundle_source A g hg hki]
        exact Finset.mem_sdiff.2 ⟨hkx, Finset.notMem_singleton.2 hxg⟩
      · rwa [transferGood_bundle_other A g hg hki hkj]

end BundleAllocation

/-! ### Part 2: Monotone valuations and the EF / EFX / EF1 / PO hierarchy -/

/-- A profile of monotone bundle valuations `val i : Finset (Fin m) → R` for `n` agents over `m`
indivisible goods: enlarging a bundle never decreases its value. -/
structure MonotoneValuation (n m : ℕ) (R : Type*) [Preorder R] where
  /-- Agent `i`'s valuation of bundle `S`. -/
  val : Fin n → Finset (Fin m) → R
  /-- Free disposal / monotonicity: `S ⊆ T` implies `val i S ≤ val i T`. -/
  mono : ∀ (i : Fin n) {S T : Finset (Fin m)}, S ⊆ T → val i S ≤ val i T

namespace MonotoneValuation

section LinearOrder

variable {n m : ℕ} {R : Type*} [LinearOrder R] (V : MonotoneValuation n m R)

/-- Exact envy-freeness (`EF`): no agent strictly prefers another agent's bundle to its own. -/
@[expose] def IsEnvyFree (A : BundleAllocation n m) : Prop :=
  ∀ i j : Fin n, V.val i (A.bundle j) ≤ V.val i (A.bundle i)

instance instDecidableIsEnvyFree (A : BundleAllocation n m) : Decidable (V.IsEnvyFree A) :=
  inferInstanceAs (Decidable (∀ i j : Fin n, V.val i (A.bundle j) ≤ V.val i (A.bundle i)))

/-- Strong envy-freeness up to any good (`EFX`, [PlautRoughgarden2020]): removing *any* good from
agent `j`'s bundle eliminates agent `i`'s envy toward `j`. When marginal values of goods are
strictly positive, this coincides with [CaragiannisKurokawaMoulinProcacciaShahWang2019]. -/
@[expose] def IsEFX (A : BundleAllocation n m) : Prop :=
  ∀ i j : Fin n, ∀ g ∈ A.bundle j, V.val i (A.bundle j \ {g}) ≤ V.val i (A.bundle i)

instance instDecidableIsEFX (A : BundleAllocation n m) : Decidable (V.IsEFX A) :=
  inferInstanceAs
    (Decidable (∀ i j : Fin n, ∀ g ∈ A.bundle j, V.val i (A.bundle j \ {g}) ≤ V.val i (A.bundle i)))

/-- Envy-freeness up to one good (`EF1`, [Budish2011];
[CaragiannisKurokawaMoulinProcacciaShahWang2019]): for every pair of agents `i, j`, either `i` does
not envy `j`, or removing some single good `g ∈ A.bundle j` eliminates `i`'s envy. -/
@[expose] def IsEF1 (A : BundleAllocation n m) : Prop :=
  ∀ i j : Fin n,
    V.val i (A.bundle j) ≤ V.val i (A.bundle i) ∨
      ∃ g ∈ A.bundle j, V.val i (A.bundle j \ {g}) ≤ V.val i (A.bundle i)

instance instDecidableIsEF1 (A : BundleAllocation n m) : Decidable (V.IsEF1 A) :=
  inferInstanceAs (Decidable (∀ i j : Fin n,
    V.val i (A.bundle j) ≤ V.val i (A.bundle i) ∨
      ∃ g ∈ A.bundle j, V.val i (A.bundle j \ {g}) ≤ V.val i (A.bundle i)))

/-- Pareto optimality (`PO`) among complete allocations: `A` is complete and no complete allocation
`B` makes every agent weakly better off and at least one agent strictly better off. -/
@[expose] def IsParetoOptimal (A : BundleAllocation n m) : Prop :=
  A.IsComplete ∧
    ¬ ∃ B : BundleAllocation n m,
      B.IsComplete ∧
      (∀ i : Fin n, V.val i (A.bundle i) ≤ V.val i (B.bundle i)) ∧
      ∃ i₀ : Fin n, V.val i₀ (A.bundle i₀) < V.val i₀ (B.bundle i₀)

instance instDecidableIsParetoOptimal (A : BundleAllocation n m) :
    Decidable (V.IsParetoOptimal A) := by
  have hiff : V.IsParetoOptimal A ↔
      A.IsComplete ∧
        ¬ ∃ B ∈ BundleAllocation.completeAllocationList n m,
          (∀ i : Fin n, V.val i (A.bundle i) ≤ V.val i (B.bundle i)) ∧
          ∃ i₀ : Fin n, V.val i₀ (A.bundle i₀) < V.val i₀ (B.bundle i₀) := by
    simp only [IsParetoOptimal, BundleAllocation.mem_completeAllocationList_iff]
  exact decidable_of_iff' _ hiff

variable {V}

/-- Every envy-free allocation is `EFX`. -/
theorem IsEnvyFree.isEFX {A : BundleAllocation n m} (hEF : V.IsEnvyFree A) : V.IsEFX A :=
  fun i j _ _ => (V.mono i Finset.sdiff_subset).trans (hEF i j)

/-- Every `EFX` allocation is `EF1`. -/
theorem IsEFX.isEF1 {A : BundleAllocation n m} (hEFX : V.IsEFX A) : V.IsEF1 A := by
  intro i j
  rcases (A.bundle j).eq_empty_or_nonempty with hEmpty | ⟨g, hg⟩
  · left
    rw [hEmpty]
    exact V.mono i (Finset.empty_subset _)
  · exact Or.inr ⟨g, hg, hEFX i j g hg⟩

theorem isEnvyFree_empty : V.IsEnvyFree BundleAllocation.empty :=
  fun _ _ => le_rfl

theorem isEF1_empty : V.IsEF1 BundleAllocation.empty :=
  V.isEnvyFree_empty.isEFX.isEF1

end LinearOrder

section MaxMarginal

variable {n m : ℕ} {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
  (V : MonotoneValuation n m R)

/-- Agent `i`'s maximum marginal utility for adding a single good to any bundle `S ⊆ Fin m`
([LiptonMarkakisMosselSaberi2004]), equal to `0` when `m = 0`. -/
@[expose] def maxMarginal (i : Fin n) : R :=
  (insert (0 : R)
    ((Finset.univ : Finset (Finset (Fin m) × Fin m)).image fun p =>
      V.val i (insert p.2 p.1) - V.val i p.1)).max' (Finset.insert_nonempty _ _)

omit [IsOrderedAddMonoid R] in
theorem maxMarginal_nonneg (i : Fin n) : 0 ≤ V.maxMarginal i :=
  Finset.le_max' _ 0 (Finset.mem_insert_self _ _)

omit [IsOrderedAddMonoid R] in
theorem sub_le_maxMarginal (i : Fin n) (S : Finset (Fin m)) (g : Fin m) :
    V.val i (insert g S) - V.val i S ≤ V.maxMarginal i := by
  refine Finset.le_max' _ _ (Finset.mem_insert_of_mem ?_)
  exact Finset.mem_image.2 ⟨(S, g), Finset.mem_univ _, rfl⟩

/-- Every `EF1` allocation satisfies the maximum-marginal-envy bound of
[LiptonMarkakisMosselSaberi2004]: agent `i`'s envy toward any agent `j` is at most
`V.maxMarginal i`. -/
theorem IsEF1.val_le_add_maxMarginal {V : MonotoneValuation n m R} {A : BundleAllocation n m}
    (hEF1 : V.IsEF1 A) (i j : Fin n) :
    V.val i (A.bundle j) ≤ V.val i (A.bundle i) + V.maxMarginal i := by
  rcases hEF1 i j with hle | ⟨g, hg, hle⟩
  · exact hle.trans (le_add_of_nonneg_right (V.maxMarginal_nonneg i))
  · have hmarg : V.val i (A.bundle j) - V.val i (A.bundle j \ {g}) ≤ V.maxMarginal i := by
      simpa only [Finset.sdiff_singleton_eq_erase, Finset.insert_erase hg] using
        V.sub_le_maxMarginal i (A.bundle j \ {g}) g
    simpa only [add_comm (V.val i (A.bundle j \ {g})), sub_add_cancel] using add_le_add hle hmarg

end MaxMarginal

end MonotoneValuation

/-! ### Part 3: Nonnegative additive valuations and Round-Robin EF1 -/

/-- A profile of nonnegative additive item valuations `weight i g ≥ 0` for `n` agents and `m`
indivisible goods. -/
structure AdditiveValuation (n m : ℕ) (R : Type*) [AddCommMonoid R] [PartialOrder R] where
  /-- Marginal utility `weight i g` of good `g` to agent `i`. -/
  weight : Fin n → Fin m → R
  /-- Goods (not chores): every item has nonnegative marginal value to every agent. -/
  weight_nonneg : ∀ (i : Fin n) (g : Fin m), 0 ≤ weight i g

namespace AdditiveValuation

section Basic

variable {n m : ℕ} {R : Type*} [AddCommMonoid R] [PartialOrder R]
  (W : AdditiveValuation n m R)

/-- Additive bundle utility `∑ g ∈ S, W.weight i g`. -/
@[expose] def bundleVal (i : Fin n) (S : Finset (Fin m)) : R :=
  ∑ g ∈ S, W.weight i g

@[simp] theorem bundleVal_empty (i : Fin n) : W.bundleVal i ∅ = 0 :=
  Finset.sum_empty

@[simp] theorem bundleVal_singleton (i : Fin n) (g : Fin m) :
    W.bundleVal i {g} = W.weight i g :=
  Finset.sum_singleton _ _

theorem bundleVal_insert {i : Fin n} {g : Fin m} {S : Finset (Fin m)} (hg : g ∉ S) :
    W.bundleVal i (insert g S) = W.bundleVal i S + W.weight i g := by
  rw [bundleVal, Finset.sum_insert hg, add_comm]
  rfl

theorem bundleVal_sdiff_singleton_add {i : Fin n} {g : Fin m} {S : Finset (Fin m)} (hg : g ∈ S) :
    W.bundleVal i (S \ {g}) + W.weight i g = W.bundleVal i S := by
  have h := W.bundleVal_insert (i := i) (g := g) (S := S \ {g}) (by simp)
  have hins : insert g (S \ {g}) = S := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.insert_erase hg]
  rw [hins] at h
  exact h.symm

end Basic

section RoundRobinDefs

variable {n m : ℕ} {R : Type*} [AddCommMonoid R] [LinearOrder R]
  (W : AdditiveValuation n m R)

/-- Canonical highest-value good for agent `i` in a nonempty remaining set `rem`, breaking ties by
smallest item index. -/
@[expose] def bestGood (i : Fin n) (rem : Finset (Fin m)) (hrem : rem.Nonempty) : Fin m :=
  let maxW := (rem.image (W.weight i)).max' (hrem.image _)
  (rem.filter fun g => W.weight i g = maxW).min' <| by
    obtain ⟨g, hg, hgw⟩ := Finset.mem_image.1 ((rem.image (W.weight i)).max'_mem (hrem.image _))
    exact ⟨g, Finset.mem_filter.2 ⟨hg, hgw⟩⟩

private theorem bestGood_spec (i : Fin n) (rem : Finset (Fin m)) (hrem : rem.Nonempty) :
    W.bestGood i rem hrem ∈ rem ∧
      W.weight i (W.bestGood i rem hrem) = (rem.image (W.weight i)).max' (hrem.image _) := by
  let maxW := (rem.image (W.weight i)).max' (hrem.image _)
  have hne : (rem.filter fun g => W.weight i g = maxW).Nonempty := by
    obtain ⟨g, hg, hgw⟩ := Finset.mem_image.1 ((rem.image (W.weight i)).max'_mem (hrem.image _))
    exact ⟨g, Finset.mem_filter.2 ⟨hg, hgw⟩⟩
  exact Finset.mem_filter.1 ((rem.filter fun g => W.weight i g = maxW).min'_mem hne)

theorem bestGood_mem (i : Fin n) (rem : Finset (Fin m)) (hrem : rem.Nonempty) :
    W.bestGood i rem hrem ∈ rem :=
  (W.bestGood_spec i rem hrem).1

theorem weight_le_bestGood (i : Fin n) {rem : Finset (Fin m)} (hrem : rem.Nonempty)
    {g : Fin m} (hg : g ∈ rem) :
    W.weight i g ≤ W.weight i (W.bestGood i rem hrem) := by
  rw [(W.bestGood_spec i rem hrem).2]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hg)

/-- Remaining unallocated goods after `t` Round-Robin turns (`0 ≤ t`). -/
@[expose] def rrRemaining (hn : 0 < n) : ℕ → Finset (Fin m)
  | 0 => Finset.univ
  | t + 1 =>
    if h : (rrRemaining hn t).Nonempty then
      rrRemaining hn t \ {W.bestGood ⟨t % n, Nat.mod_lt t hn⟩ (rrRemaining hn t) h}
    else
      ∅

private theorem card_rrRemaining (hn : 0 < n) :
    ∀ t ≤ m, (W.rrRemaining hn t).card = m - t
  | 0, _ => by simp [rrRemaining]
  | t + 1, ht => by
    have ih := card_rrRemaining hn t (by omega)
    have hne : (W.rrRemaining hn t).Nonempty := Finset.card_pos.1 (by omega)
    rw [rrRemaining, dite_eq_left hne]
    have hmem := W.bestGood_mem ⟨t % n, Nat.mod_lt t hn⟩ (W.rrRemaining hn t) hne
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 hmem), Finset.card_singleton, ih]
    omega

private theorem rrRemaining_antitone (hn : 0 < n) :
    ∀ {s t : ℕ}, s ≤ t → W.rrRemaining hn t ⊆ W.rrRemaining hn s := by
  intro s t hst
  induction hst with
  | refl => exact Finset.Subset.rfl
  | step _ ih =>
    refine Finset.Subset.trans ?_ ih
    rw [rrRemaining]
    split_ifs
    · exact Finset.sdiff_subset
    · exact Finset.empty_subset _

theorem rrRemaining_nonempty (hn : 0 < n) (t : Fin m) :
    (W.rrRemaining hn t.val).Nonempty := by
  have hc := W.card_rrRemaining hn t.val t.isLt.le
  exact Finset.card_pos.1 (by have := t.isLt; omega)

/-- The good picked at turn `t : Fin m` of Round-Robin. -/
@[expose] def rrPick (hn : 0 < n) (t : Fin m) : Fin m :=
  W.bestGood ⟨t.val % n, Nat.mod_lt t.val hn⟩ (W.rrRemaining hn t.val) (W.rrRemaining_nonempty hn t)

private theorem rrPick_mem_of_le (hn : 0 < n) {s t : Fin m} (hst : s ≤ t) :
    W.rrPick hn t ∈ W.rrRemaining hn s.val :=
  W.rrRemaining_antitone hn hst
    (W.bestGood_mem _ (W.rrRemaining hn t.val) (W.rrRemaining_nonempty hn t))

private theorem rrPick_mem_succ_of_lt (hn : 0 < n) {s t : Fin m} (hst : s < t) :
    W.rrPick hn t ∈ W.rrRemaining hn (s.val + 1) :=
  W.rrRemaining_antitone hn hst
    (W.bestGood_mem _ (W.rrRemaining hn t.val) (W.rrRemaining_nonempty hn t))

theorem rrPick_injective (hn : 0 < n) : Function.Injective (W.rrPick hn) := by
  have hlt_ne {a b : Fin m} (h : a < b) (heq : W.rrPick hn a = W.rrPick hn b) : False := by
    have hmem := W.rrPick_mem_succ_of_lt hn h
    rw [rrRemaining, dite_eq_left (W.rrRemaining_nonempty hn a)] at hmem
    exact (Finset.mem_sdiff.1 hmem).2 (Finset.mem_singleton.2 heq.symm)
  intro s t hst
  rcases lt_trichotomy s t with hlt | rfl | hgt
  · exact False.elim (hlt_ne hlt hst)
  · rfl
  · exact False.elim (hlt_ne hgt hst.symm)

private theorem weight_rrPick_le_of_le (hn : 0 < n) {s t : Fin m} (hst : s ≤ t) :
    W.weight ⟨s.val % n, Nat.mod_lt s.val hn⟩ (W.rrPick hn t) ≤
      W.weight ⟨s.val % n, Nat.mod_lt s.val hn⟩ (W.rrPick hn s) :=
  W.weight_le_bestGood _ (W.rrRemaining_nonempty hn s) (W.rrPick_mem_of_le hn hst)

/-- Turns `t : Fin m` at which agent `i : Fin n` picks (`t.val % n = i.val`). -/
@[expose] def rrTurns (n m : ℕ) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun t : Fin m => t.val % n = i.val

/-- Round-Robin allocation in cyclic agent order `0, 1, …, n - 1`. -/
@[expose] def roundRobin (hn : 0 < n) : BundleAllocation n m where
  bundle i := (rrTurns n m i).image (W.rrPick hn)
  pairwiseDisjoint i j hij := by
    dsimp only
    refine Finset.disjoint_left.2 fun g hgi hgj => ?_
    obtain ⟨ti, hti, rfl⟩ := Finset.mem_image.1 hgi
    obtain ⟨tj, htj, hEq⟩ := Finset.mem_image.1 hgj
    have htEq : tj = ti := W.rrPick_injective hn hEq
    rw [htEq] at htj
    have hi_mod : ti.val % n = i.val := (Finset.mem_filter.1 hti).2
    have hj_mod : ti.val % n = j.val := (Finset.mem_filter.1 htj).2
    exact hij (Fin.ext (hi_mod.symm.trans hj_mod))

/-- Round-Robin allocates every good (`IsComplete`). -/
theorem isComplete_roundRobin (hn : 0 < n) : (W.roundRobin hn).IsComplete := by
  intro g
  obtain ⟨t, rfl⟩ := (Finite.injective_iff_bijective.1 (W.rrPick_injective hn)).2 g
  refine ⟨⟨t.val % n, Nat.mod_lt t.val hn⟩, ?_⟩
  exact Finset.mem_image.2 ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ t, rfl⟩, rfl⟩

private theorem bundleVal_roundRobin (hn : 0 < n) (i j : Fin n) :
    W.bundleVal i ((W.roundRobin hn).bundle j) =
      ∑ t ∈ rrTurns n m j, W.weight i (W.rrPick hn t) := by
  dsimp only [roundRobin, bundleVal]
  exact Finset.sum_image fun x _ y _ hxy => W.rrPick_injective hn hxy

end RoundRobinDefs

section Monoid

variable {n m : ℕ} {R : Type*} [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R]
  (W : AdditiveValuation n m R)

theorem bundleVal_nonneg (i : Fin n) (S : Finset (Fin m)) : 0 ≤ W.bundleVal i S :=
  Finset.sum_nonneg fun g _ => W.weight_nonneg i g

/-- Canonical monotone bundle valuation induced by nonnegative additive weights. -/
@[expose] def toMonotoneValuation : MonotoneValuation n m R where
  val := W.bundleVal
  mono i {_ _} hST := Finset.sum_le_sum_of_subset_of_nonneg hST fun g _ _ => W.weight_nonneg i g

@[simp] theorem toMonotoneValuation_val (i : Fin n) (S : Finset (Fin m)) :
    W.toMonotoneValuation.val i S = W.bundleVal i S := rfl

private theorem sum_rrTurns_le_of_injOn (hn : 0 < n) {i : Fin n} {T : Finset (Fin m)}
    {φ : Fin m → Fin m} (hmem : ∀ t ∈ T, φ t ∈ rrTurns n m i) (hinj : Set.InjOn φ T)
    (hle : ∀ t ∈ T, φ t ≤ t) :
    ∑ t ∈ T, W.weight i (W.rrPick hn t) ≤
      ∑ s ∈ rrTurns n m i, W.weight i (W.rrPick hn s) := by
  have hterm : ∀ t ∈ T, W.weight i (W.rrPick hn t) ≤ W.weight i (W.rrPick hn (φ t)) := by
    intro t ht
    have hagent : (⟨(φ t).val % n, Nat.mod_lt (φ t).val hn⟩ : Fin n) = i :=
      Fin.ext (Finset.mem_filter.1 (hmem t ht)).2
    simpa only [hagent] using W.weight_rrPick_le_of_le hn (hle t ht)
  calc
    ∑ t ∈ T, W.weight i (W.rrPick hn t)
        ≤ ∑ t ∈ T, W.weight i (W.rrPick hn (φ t)) := Finset.sum_le_sum hterm
    _ = ∑ s ∈ T.image φ, W.weight i (W.rrPick hn s) :=
        (Finset.sum_image (f := fun s => W.weight i (W.rrPick hn s)) hinj).symm
    _ ≤ ∑ s ∈ rrTurns n m i, W.weight i (W.rrPick hn s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.2 hmem)
          fun _ _ _ => W.weight_nonneg i _

/-- **Round-Robin is `EF1`** ([CaragiannisKurokawaMoulinProcacciaShahWang2019]): for every
nonnegative additive valuation profile and `0 < n`, `W.roundRobin hn` is envy-free up to one good.
-/
theorem isEF1_roundRobin (hn : 0 < n) : W.toMonotoneValuation.IsEF1 (W.roundRobin hn) := by
  intro i j
  simp only [toMonotoneValuation_val]
  have hmap (T : Finset (Fin m)) (q : Fin m → ℕ)
      (hmod : ∀ t ∈ T, t.val % n = j.val)
      (hq_inj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, q t₁ = q t₂ → t₁.val / n = t₂.val / n)
      (hle : ∀ t ∈ T, n * q t + i.val ≤ t.val) :
      ∑ t ∈ T, W.weight i (W.rrPick hn t) ≤
        ∑ s ∈ rrTurns n m i, W.weight i (W.rrPick hn s) := by
    let φ : Fin m → Fin m := fun t =>
      if h : n * q t + i.val < m then ⟨n * q t + i.val, h⟩ else t
    have hlt : ∀ t ∈ T, n * q t + i.val < m := fun t ht => lt_of_le_of_lt (hle t ht) t.isLt
    have hmem : ∀ t ∈ T, φ t ∈ rrTurns n m i := fun t ht => by
      simp only [φ, dite_eq_left (hlt t ht), rrTurns, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt i.isLt]
    have hinj : Set.InjOn φ T := fun t₁ ht₁ t₂ ht₂ hEq => by
      simp only [φ, dite_eq_left (hlt t₁ ht₁), dite_eq_left (hlt t₂ ht₂), Fin.ext_iff] at hEq
      have hdiv := hq_inj t₁ ht₁ t₂ ht₂ (Nat.eq_of_mul_eq_mul_left hn (Nat.add_right_cancel hEq))
      exact Fin.ext (by
        rw [← Nat.div_add_mod t₁.val n, ← Nat.div_add_mod t₂.val n, hdiv, hmod t₁ ht₁, hmod t₂ ht₂])
    refine W.sum_rrTurns_le_of_injOn hn hmem hinj fun t ht => ?_
    simp only [φ, dite_eq_left (hlt t ht), Fin.le_iff_val_le_val]
    exact hle t ht
  by_cases hij : i.val ≤ j.val
  · left
    rw [W.bundleVal_roundRobin hn i j, W.bundleVal_roundRobin hn i i]
    refine hmap (rrTurns n m j) (fun t => t.val / n)
      (fun t ht => (Finset.mem_filter.1 ht).2) (fun _ _ _ _ h => h) fun t ht => ?_
    have hmod : t.val % n = j.val := (Finset.mem_filter.1 ht).2
    have hdiv := Nat.div_add_mod t.val n
    omega
  · by_cases hjm : j.val < m
    · right
      let t₀ : Fin m := ⟨j.val, hjm⟩
      have ht₀ : t₀ ∈ rrTurns n m j := by simp [t₀, rrTurns, Nat.mod_eq_of_lt j.isLt]
      refine ⟨W.rrPick hn t₀, Finset.mem_image_of_mem _ ht₀, ?_⟩
      let T' := (rrTurns n m j) \ {t₀}
      have hsdiff : (W.roundRobin hn).bundle j \ {W.rrPick hn t₀} = T'.image (W.rrPick hn) := by
        ext x
        simp only [T', roundRobin, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_image]
        refine ⟨?_, ?_⟩
        · rintro ⟨⟨t, ht, rfl⟩, hne⟩
          exact ⟨t, ⟨ht, fun h => hne (congrArg _ h)⟩, rfl⟩
        · rintro ⟨t, ⟨ht, hne⟩, rfl⟩
          exact ⟨⟨t, ht, rfl⟩, fun h => hne (W.rrPick_injective hn h)⟩
      have hsum_img : W.bundleVal i (T'.image (W.rrPick hn)) =
          ∑ t ∈ T', W.weight i (W.rrPick hn t) :=
        Finset.sum_image fun _ _ _ _ h => W.rrPick_injective hn h
      rw [hsdiff, W.bundleVal_roundRobin hn i i, hsum_img]
      have hq_pos : ∀ t ∈ T', 1 ≤ t.val / n := fun t ht => by
        obtain ⟨ht_turn, ht_ne⟩ := Finset.mem_sdiff.1 ht
        have hmod : t.val % n = j.val := (Finset.mem_filter.1 ht_turn).2
        have hne_val : t.val ≠ j.val := fun hv =>
          Finset.notMem_singleton.1 ht_ne (Fin.ext hv)
        have hdiv := Nat.div_add_mod t.val n
        rcases Nat.eq_zero_or_pos (t.val / n) with hq0 | hpos
        · rw [hq0, Nat.mul_zero, zero_add, hmod] at hdiv
          exact absurd hdiv.symm hne_val
        · exact hpos
      refine hmap T' (fun t => t.val / n - 1)
        (fun t ht => (Finset.mem_filter.1 (Finset.mem_sdiff.1 ht).1).2)
        (fun t₁ ht₁ t₂ ht₂ h => by
          have := hq_pos t₁ ht₁
          have := hq_pos t₂ ht₂
          omega)
        fun t ht => ?_
      have hlt_step : n * (t.val / n - 1) + i.val < n * (t.val / n) := by
        calc n * (t.val / n - 1) + i.val
            < n * (t.val / n - 1) + n := Nat.add_lt_add_left i.isLt _
          _ = n * (t.val / n) := by rw [← Nat.mul_add_one, Nat.sub_add_cancel (hq_pos t ht)]
      exact hlt_step.le.trans (Nat.mul_div_le t.val n)
    · left
      have hEmpty : rrTurns n m j = ∅ := Finset.filter_eq_empty_iff.mpr fun t _ hmod => by
        have := Nat.mod_le t.val n
        have := t.isLt
        omega
      simp only [roundRobin, hEmpty, Finset.image_empty, W.bundleVal_empty]
      exact W.bundleVal_nonneg i _

end Monoid

end AdditiveValuation

end Cslib.GameTheory.FairDivision.Indivisible
