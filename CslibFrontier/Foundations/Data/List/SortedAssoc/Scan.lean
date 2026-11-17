/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.SortedAssoc
public import Cslib.Foundations.Control.Monad.IsMonadHom

/-!
# Comparator-polymorphic scans of sorted association lists

The queries of `Cslib.SortedAssoc` written as left-to-right scans over an arbitrary monad `m`,
with a comparator `le : α → α → m Bool` and no order instance in scope, so that every comparison
of keys goes through `le`. Instantiating `m` then decides what a comparison costs: the identity
monad gives the pure query, and a query monad counts comparisons. This is the shape of CSLib's
`List.mergeSortM` and `List.idRun_mergeSortM`.

Each scan stops as early as a sorted list allows. `lookupM`, `rankM` and `predM` stop at the
first key that is not below the query; `succM` stops at the first key above it; `rangeM` skips
the keys below the lower bound and then takes keys up to the upper bound with `takeUpToM`.

`rankM`, `predM` and `succM` ask one question per entry up to and including the one where they
stop. `lookupM` asks one more where it stops, to tell equality from a strictly larger key.
`rangeM` runs two phases: one question against the lower bound per entry up to and including the
first key that is not below it, then one question against the upper bound per entry from that
same key up to and including the first key above the upper bound. The first entry that is not
below the lower bound is therefore compared twice, once in each phase.

With the comparator `Cslib.SortedAssoc.leI` of a linear order, the identity-monad instance of
each scan is the corresponding function of `Cslib.SortedAssoc` on a sorted list (`idRun_lookupM`
and its siblings). The scan for the successor needs no sortedness. The others do, because they
stop early: on an unsorted list they may miss entries that the model function, a filter, finds.

`map_lookupM` and its siblings say that a monad morphism commutes with each scan, which is how
an instrumented instance is related to the pure one.

A leaf of a B+-tree is a sorted association list, and these scans are its queries.

## Main definitions

* `Cslib.SortedAssoc.lookupM`, `rankM`, `predM`, `succM`: lookup, rank, strict predecessor and
  strict successor.
* `Cslib.SortedAssoc.takeUpToM`, `rangeM`: the prefix of keys up to a bound, and restriction to a
  closed interval.

## Main results

* `Cslib.SortedAssoc.idRun_lookupM`, `idRun_rankM`, `idRun_predM`, `idRun_succM`,
  `idRun_rangeM`: the pure instances are `List.lookup`, `rank`, `pred?`, `succ?` and `range`.
* `Cslib.SortedAssoc.map_lookupM`, `map_rankM`, `map_predM`, `map_succM`, `map_takeUpToM`,
  `map_rangeM`: a monad morphism commutes with each scan.
-/

public section

universe w

namespace Cslib.SortedAssoc

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Lookup by a scan: stop at the first key not below `k` and test it for equality with a second
comparison. -/
@[expose] def lookupM (le : α → α → m Bool) (k : α) : List (α × β) → m (Option β)
  | [] => pure none
  | (k', v) :: l => do
    if ← le k k' then
      if ← le k' k then pure (some v) else pure none
    else lookupM le k l

/-- Rank by a scan: the number of entries before the first key not below `k`. -/
@[expose] def rankM (le : α → α → m Bool) (k : α) : List (α × β) → m ℕ
  | [] => pure 0
  | (k', _) :: l => do
    if ← le k k' then pure 0 else return (← rankM le k l) + 1

/-- Strict predecessor by a scan: the last entry before the first key not below `k`. -/
@[expose] def predM (le : α → α → m Bool) (k : α) : List (α × β) → m (Option (α × β))
  | [] => pure none
  | p :: l => do
    if ← le k p.1 then pure none else return (← predM le k l).or (some p)

/-- Strict successor by a scan: the first entry whose key is not at most `k`. -/
@[expose] def succM (le : α → α → m Bool) (k : α) : List (α × β) → m (Option (α × β))
  | [] => pure none
  | p :: l => do
    if ← le p.1 k then succM le k l else pure (some p)

/-- The entries before the first key that is not at most `hi`. -/
@[expose] def takeUpToM (le : α → α → m Bool) (hi : α) : List (α × β) → m (List (α × β))
  | [] => pure []
  | p :: l => do
    if ← le p.1 hi then return p :: (← takeUpToM le hi l) else pure []

/-- Restriction to the closed interval `[lo, hi]` by a scan: skip the keys below `lo`, then take
the keys up to `hi`. -/
@[expose] def rangeM (le : α → α → m Bool) (lo hi : α) : List (α × β) → m (List (α × β))
  | [] => pure []
  | p :: l => do
    if ← le lo p.1 then takeUpToM le hi (p :: l) else rangeM le lo hi l

end Polymorphic

section Transfer

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the lookup scan. -/
theorem map_lookupM (hf : IsMonadHom m n f) (le : α → α → m Bool) (k : α) (l : List (α × β)) :
    f (lookupM le k l) = lookupM (fun a b => f (le a b)) k l := by
  induction l with
  | nil => simp [lookupM, hf.map_pure]
  | cons p l ih =>
    obtain ⟨k', v⟩ := p
    simp [lookupM, hf.map_bind, hf.map_pure, apply_ite f, ih]

/-- A monad morphism commutes with the rank scan. -/
theorem map_rankM (hf : IsMonadHom m n f) (le : α → α → m Bool) (k : α) (l : List (α × β)) :
    f (rankM le k l) = rankM (fun a b => f (le a b)) k l := by
  induction l with
  | nil => simp [rankM, hf.map_pure]
  | cons p l ih =>
    obtain ⟨k', v⟩ := p
    simp [rankM, hf.map_bind, hf.map_pure, apply_ite f, ih]

/-- A monad morphism commutes with the predecessor scan. -/
theorem map_predM (hf : IsMonadHom m n f) (le : α → α → m Bool) (k : α) (l : List (α × β)) :
    f (predM le k l) = predM (fun a b => f (le a b)) k l := by
  induction l with
  | nil => simp [predM, hf.map_pure]
  | cons p l ih => simp [predM, hf.map_bind, hf.map_pure, apply_ite f, ih]

/-- A monad morphism commutes with the successor scan. -/
theorem map_succM (hf : IsMonadHom m n f) (le : α → α → m Bool) (k : α) (l : List (α × β)) :
    f (succM le k l) = succM (fun a b => f (le a b)) k l := by
  induction l with
  | nil => simp [succM, hf.map_pure]
  | cons p l ih => simp [succM, hf.map_bind, hf.map_pure, apply_ite f, ih]

/-- A monad morphism commutes with taking the keys up to a bound. -/
theorem map_takeUpToM (hf : IsMonadHom m n f) (le : α → α → m Bool) (hi : α)
    (l : List (α × β)) : f (takeUpToM le hi l) = takeUpToM (fun a b => f (le a b)) hi l := by
  induction l with
  | nil => simp [takeUpToM, hf.map_pure]
  | cons p l ih => simp [takeUpToM, hf.map_bind, hf.map_pure, apply_ite f, ih]

/-- A monad morphism commutes with the range scan. -/
theorem map_rangeM (hf : IsMonadHom m n f) (le : α → α → m Bool) (lo hi : α)
    (l : List (α × β)) : f (rangeM le lo hi l) = rangeM (fun a b => f (le a b)) lo hi l := by
  induction l with
  | nil => simp [rangeM, hf.map_pure]
  | cons p l ih =>
    simp [rangeM, hf.map_bind, apply_ite f, ih, map_takeUpToM hf]

end Transfer

section Pure

variable {α β : Type} [LinearOrder α] {l : List (α × β)} {k k' lo hi : α} {v : β} {p : α × β}

/-- The pure lookup scan at an entry: stop at a key not below `k`, and move on otherwise. -/
theorem idRun_lookupM_cons :
    Id.run (lookupM leI k ((k', v) :: l)) =
      if k ≤ k' then (if k' ≤ k then some v else none) else Id.run (lookupM leI k l) := by
  by_cases h₁ : k ≤ k' <;> by_cases h₂ : k' ≤ k <;> simp [lookupM, leI, h₁, h₂]

/-- The pure rank scan at an entry: stop at a key not below `k`, and count it otherwise. -/
theorem idRun_rankM_cons :
    Id.run (rankM leI k (p :: l)) = if k ≤ p.1 then 0 else Id.run (rankM leI k l) + 1 := by
  by_cases h : k ≤ p.1 <;> simp [rankM, leI, h]

/-- The pure predecessor scan at an entry: stop at a key not below `k`, and otherwise keep the
entry as the fallback. -/
theorem idRun_predM_cons :
    Id.run (predM leI k (p :: l)) =
      if k ≤ p.1 then none else (Id.run (predM leI k l)).or (some p) := by
  by_cases h : k ≤ p.1 <;> simp [predM, leI, h]

/-- The pure successor scan at an entry: pass a key that is at most `k`, and stop otherwise. -/
theorem idRun_succM_cons :
    Id.run (succM leI k (p :: l)) = if p.1 ≤ k then Id.run (succM leI k l) else some p := by
  by_cases h : p.1 ≤ k <;> simp [succM, leI, h]

/-- The pure scan up to a bound is `List.takeWhile`, on any list. -/
theorem idRun_takeUpToM (hi : α) (l : List (α × β)) :
    Id.run (takeUpToM leI hi l) = l.takeWhile fun p => decide (p.1 ≤ hi) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    by_cases h : p.1 ≤ hi
    · simp [takeUpToM, leI, h, ← ih]
    · simp [takeUpToM, leI, h]

/-- The pure range scan at an entry: at a key not below `lo`, take the keys up to `hi`; otherwise
move on. -/
theorem idRun_rangeM_cons :
    Id.run (rangeM leI lo hi (p :: l)) =
      if lo ≤ p.1 then Id.run (takeUpToM leI hi (p :: l)) else Id.run (rangeM leI lo hi l) := by
  by_cases h : lo ≤ p.1 <;> simp [rangeM, leI, h]

/-- On a sorted list the pure lookup scan is `List.lookup`. -/
theorem idRun_lookupM (h : l.IsSortedAssoc) (k : α) :
    Id.run (lookupM leI k l) = List.lookup k l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k', v⟩ := p
    rw [List.isSortedAssoc_cons_iff] at h
    rw [idRun_lookupM_cons]
    by_cases h₁ : k ≤ k'
    · by_cases h₂ : k' ≤ k
      · obtain rfl := le_antisymm h₁ h₂
        simp
      · have hk : k < k' := lt_of_le_of_ne h₁ fun e => h₂ (e ▸ le_rfl)
        simp only [h₁, h₂, ↓reduceIte]
        refine (List.lookup_eq_none_of_forall_ne fun q hq => ?_).symm
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hk.ne'
        · exact (hk.trans (h.1 q hq)).ne'
    · simp only [h₁, ↓reduceIte]
      rw [List.lookup_cons_of_ne (lt_of_not_ge h₁).ne', ih h.2]

/-- On a sorted list the pure rank scan is `rank`. -/
theorem idRun_rankM (h : l.IsSortedAssoc) (k : α) : Id.run (rankM leI k l) = rank k l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.isSortedAssoc_cons_iff] at h
    rw [idRun_rankM_cons]
    by_cases h₁ : k ≤ p.1
    · simp only [h₁, ↓reduceIte]
      refine (rank_eq_zero_iff.2 fun q hq => ?_).symm
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h₁
      · exact h₁.trans (h.1 q hq).le
    · simp only [h₁, ↓reduceIte, rank_cons, lt_of_not_ge h₁, ih h.2]

/-- On a sorted list the pure predecessor scan is `pred?`. -/
theorem idRun_predM (h : l.IsSortedAssoc) (k : α) : Id.run (predM leI k l) = pred? k l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k', v⟩ := p
    rw [List.isSortedAssoc_cons_iff] at h
    rw [idRun_predM_cons]
    by_cases h₁ : k ≤ k'
    · simp only [h₁, ↓reduceIte]
      refine (pred?_eq_none_iff.2 fun q hq => ?_).symm
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h₁
      · exact h₁.trans (h.1 q hq).le
    · simp only [h₁, ↓reduceIte, pred?_cons, lt_of_not_ge h₁, ih h.2]

/-- The pure successor scan is `succ?`, on any list. -/
theorem idRun_succM (k : α) (l : List (α × β)) : Id.run (succM leI k l) = succ? k l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k', v⟩ := p
    rw [idRun_succM_cons, succ?_cons, ih]
    by_cases h₁ : k' ≤ k
    · simp only [h₁, ↓reduceIte, not_lt.2 h₁]
    · simp only [h₁, ↓reduceIte, lt_of_not_ge h₁]

/-- On a sorted list whose keys are all at least `lo`, restriction to `[lo, hi]` is the prefix of
keys up to `hi`. -/
theorem range_eq_takeWhile (h : l.IsSortedAssoc) (hlo : ∀ p ∈ l, lo ≤ p.1) :
    range lo hi l = l.takeWhile fun p => decide (p.1 ≤ hi) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.isSortedAssoc_cons_iff] at h
    have hp := hlo p List.mem_cons_self
    rw [range_cons, List.takeWhile_cons]
    by_cases h₁ : p.1 ≤ hi
    · simp only [hp, h₁, and_self, ↓reduceIte, decide_true]
      rw [ih h.2 fun q hq => hlo q (List.mem_cons_of_mem _ hq)]
    · simp only [h₁, and_false, ↓reduceIte, decide_false, Bool.false_eq_true]
      exact range_eq_nil_iff.2 fun q hq => Or.inr ((lt_of_not_ge h₁).trans (h.1 q hq))

/-- On a sorted list the pure range scan is `range`. -/
theorem idRun_rangeM (h : l.IsSortedAssoc) (lo hi : α) :
    Id.run (rangeM leI lo hi l) = range lo hi l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hs := h
    rw [List.isSortedAssoc_cons_iff] at hs
    rw [idRun_rangeM_cons]
    by_cases h₁ : lo ≤ p.1
    · simp only [h₁, ↓reduceIte]
      rw [idRun_takeUpToM]
      refine (range_eq_takeWhile h fun q hq => ?_).symm
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h₁
      · exact h₁.trans (hs.1 q hq).le
    · simp only [h₁, ↓reduceIte, range_cons, false_and, ih hs.2]

end Pure

end Cslib.SortedAssoc
