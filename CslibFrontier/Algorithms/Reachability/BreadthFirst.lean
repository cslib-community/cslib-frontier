/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Nodup
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Relation
public import Mathlib.Order.Lattice.Nat

/-!
# Breadth-first search by rounds

A round of breadth-first search (`Cslib.Reachability.expand`) appends to the list of the elements
found so far every successor of one of them that has not been found yet. The found elements stay
distinct, a round only appends, and a round adds nothing exactly when the found elements are
closed under successors. So if at most `N` distinct elements are reachable from `start`, after
`N` rounds from `[start]` (`Cslib.Reachability.search`) the found elements are exactly the
reachable ones (`Cslib.Reachability.mem_search_iff`): each round before closure finds a new
element. The number of rounds, not a search for a fixed point, keeps the algorithm a plain
iteration, as polynomial-time certificates need. When no bound on the number of reachable
elements is known in advance, the search runs until a round adds nothing: the closing round
(`Cslib.Reachability.closingRound`) is the least number of rounds after which the found elements
are closed, and they are then exactly the reachable ones
(`Cslib.Reachability.mem_search_iff_of_closed`).

## Main definitions

* `Cslib.Reachability.insertNew`: append an element to a list if not already present.
* `Cslib.Reachability.expand`: one round of breadth-first search.
* `Cslib.Reachability.search`: a number of rounds from a start element.
* `Cslib.Reachability.closingRound`: the least number of rounds after which the search is closed.

## Main results

* `Cslib.Reachability.nodup_search`: the found elements are distinct.
* `Cslib.Reachability.reflTransGen_of_mem_search`: the found elements are reachable.
* `Cslib.Reachability.mem_search_iff_of_closed`: once a round adds nothing, the found elements are
  the reachable ones.
* `Cslib.Reachability.expand_search_eq_of_bound`, `Cslib.Reachability.mem_search_iff`: after as many
  rounds as there are reachable elements, the search is closed and the found elements are the
  reachable ones.
* `Cslib.Reachability.closingRound_le`, `Cslib.Reachability.expand_search_ne_of_lt_closingRound`:
  the closing round is the least round after which the search is closed.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 7.14][Sipser2013]
-/

@[expose] public section

namespace Cslib.Reachability

variable {α : Type*} [DecidableEq α] {succ : α → List α}

/-- Append an element unless it is already in the list. -/
def insertNew (found : List α) (a : α) : List α := if a ∈ found then found else found ++ [a]

/-- **One round of breadth-first search**: append, in order, every successor of a found element
that has not been found yet. -/
def expand (succ : α → List α) (found : List α) : List α :=
  (found.flatMap succ).foldl insertNew found

/-- `rounds` rounds of breadth-first search from `start`. -/
def search (succ : α → List α) (rounds : ℕ) (start : α) : List α :=
  (expand succ)^[rounds] [start]

/-- Zero rounds of breadth-first search return the singleton list `[start]`. -/
@[simp] theorem search_zero (start : α) : search succ 0 start = [start] := rfl

/-- `rounds + 1` rounds of breadth-first search apply `expand` to the result of `rounds` rounds. -/
theorem search_succ (rounds : ℕ) (start : α) :
    search succ (rounds + 1) start = expand succ (search succ rounds start) :=
  Function.iterate_succ_apply' _ _ _

private theorem prefix_foldl_insertNew (l found : List α) : found <+: l.foldl insertNew found := by
  induction l generalizing found with
  | nil => exact List.prefix_refl _
  | cons a l ih =>
    refine List.IsPrefix.trans ?_ (ih _)
    unfold insertNew; split_ifs <;> [exact List.prefix_refl _; exact List.prefix_append _ _]

private theorem mem_foldl_insertNew {l found : List α} {a : α} :
    a ∈ l.foldl insertNew found ↔ a ∈ found ∨ a ∈ l := by
  induction l generalizing found with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih, List.mem_cons]
    by_cases hb : b ∈ found <;> simp only [insertNew, hb, ↓reduceIte, List.mem_append,
      List.mem_singleton]
    · exact ⟨Or.imp_right Or.inr,
        fun | .inl h => .inl h | .inr (.inl h) => .inl (h ▸ hb) | .inr (.inr h) => .inr h⟩
    · exact or_assoc

private theorem nodup_foldl_insertNew {l found : List α} (h : found.Nodup) :
    (l.foldl insertNew found).Nodup := by
  induction l generalizing found with
  | nil => exact h
  | cons a l ih =>
    refine ih ?_
    unfold insertNew; split_ifs with ha
    · exact h
    · exact List.nodup_append.mpr ⟨h, List.nodup_singleton a, by rintro _ hb _ hc rfl; simp_all⟩

/-- A round only appends. -/
theorem prefix_expand (found : List α) : found <+: expand succ found :=
  prefix_foldl_insertNew _ _

/-- The elements found after a round are those found before and their successors. -/
theorem mem_expand {found : List α} {a : α} :
    a ∈ expand succ found ↔ a ∈ found ∨ ∃ b ∈ found, a ∈ succ b := by
  rw [expand, mem_foldl_insertNew, List.mem_flatMap]

/-- A round keeps the found elements distinct. -/
theorem nodup_expand {found : List α} (h : found.Nodup) : (expand succ found).Nodup :=
  nodup_foldl_insertNew h

/-- A round adds nothing exactly when the found elements are closed under successors. -/
theorem expand_eq_self_iff {found : List α} :
    expand succ found = found ↔ ∀ b ∈ found, ∀ a ∈ succ b, a ∈ found := by
  refine ⟨fun h b hb a ha => h ▸ mem_expand.mpr (.inr ⟨b, hb, ha⟩), fun h => ?_⟩
  suffices ∀ l : List α, (∀ a ∈ l, a ∈ found) → l.foldl insertNew found = found from
    this _ fun a ha => let ⟨b, hb, hab⟩ := List.mem_flatMap.mp ha; h b hb a hab
  intro l hl
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons, insertNew, hl a List.mem_cons_self, ↓reduceIte]
    exact ih fun b hb => hl b (List.mem_cons_of_mem _ hb)

/-- A round that adds something makes the list longer. -/
private theorem length_lt_expand {found : List α} (h : expand succ found ≠ found) :
    found.length < (expand succ found).length := by
  rcases prefix_expand (succ := succ) found with ⟨_ | ⟨a, rest⟩, hrest⟩
  · exact absurd (by simpa using hrest.symm) h
  · simp [← hrest]

/-- The rounds only append. -/
theorem prefix_search {i j : ℕ} (hij : i ≤ j) (start : α) :
    search succ i start <+: search succ j start := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => exact List.prefix_refl _
  | succ d ih =>
    exact (ih (Nat.le_add_right _ _)).trans
      (by rw [← Nat.add_assoc, search_succ]; exact prefix_expand _)

theorem start_mem_search (rounds : ℕ) (start : α) : start ∈ search succ rounds start :=
  (prefix_search (Nat.zero_le rounds) start).subset (by simp)

/-- **The found elements are distinct.** -/
theorem nodup_search (rounds : ℕ) (start : α) : (search succ rounds start).Nodup := by
  induction rounds with
  | zero => exact List.nodup_singleton start
  | succ _ ih => exact search_succ (succ := succ) _ _ ▸ nodup_expand ih

/-- **The found elements are reachable.** -/
theorem reflTransGen_of_mem_search {rounds : ℕ} {start a : α}
    (h : a ∈ search succ rounds start) : Relation.ReflTransGen (fun b c => c ∈ succ b) start a := by
  induction rounds generalizing a with
  | zero => exact List.mem_singleton.mp h ▸ .refl
  | succ rounds ih =>
    exact (mem_expand.mp (search_succ rounds start ▸ h)).elim ih fun ⟨_, hb, ha⟩ =>
      (ih hb).tail ha

/-- Each round before the found elements are closed finds a new element. -/
private theorem succ_le_length_search_or_closed (rounds : ℕ) (start : α) :
    rounds + 1 ≤ (search succ rounds start).length ∨
      expand succ (search succ rounds start) = search succ rounds start := by
  induction rounds with
  | zero => exact .inl (by simp)
  | succ rounds ih =>
    have hsucc := search_succ (succ := succ) rounds start
    by_cases hfix : expand succ (search succ rounds start) = search succ rounds start
    · exact .inr (by rw [hsucc, hfix, hfix])
    · rcases ih with ih | ih
      · exact .inl (by rw [hsucc]; have := length_lt_expand hfix; omega)
      · exact absurd ih hfix

/-- **A closed round finds every reachable element**: once a round adds nothing, the found elements
are exactly those reachable from `start`. -/
theorem mem_search_iff_of_closed {rounds : ℕ} {start a : α}
    (hclosed : expand succ (search succ rounds start) = search succ rounds start) :
    a ∈ search succ rounds start ↔ Relation.ReflTransGen (fun b c => c ∈ succ b) start a := by
  refine ⟨reflTransGen_of_mem_search, fun h => ?_⟩
  induction h with
  | refl => exact start_mem_search rounds start
  | tail _ hstep ih => exact expand_eq_self_iff.mp hclosed _ ih _ hstep

/-- **Breadth-first search closes within as many rounds as there are reachable elements**: if every
list of distinct elements reachable from `start` has at most `bound` entries, a round after at least
`bound` rounds adds nothing. -/
theorem expand_search_eq_of_bound {rounds bound : ℕ} {start : α}
    (hbound : ∀ l : List α, l.Nodup →
      (∀ b ∈ l, Relation.ReflTransGen (fun b c => c ∈ succ b) start b) → l.length ≤ bound)
    (hrounds : bound ≤ rounds) :
    expand succ (search succ rounds start) = search succ rounds start := by
  refine (succ_le_length_search_or_closed rounds start).resolve_left fun hlen => ?_
  have := hbound _ (nodup_search rounds start) fun b hb => reflTransGen_of_mem_search hb
  omega

/-- **After as many rounds as there are reachable elements, the found elements are the reachable
ones.** If every list of distinct elements reachable from `start` has at most `bound` entries, then
after at least `bound` rounds the found elements are closed under successors, so they include
every reachable element. -/
theorem mem_search_iff {rounds bound : ℕ} {start a : α}
    (hbound : ∀ l : List α, l.Nodup →
      (∀ b ∈ l, Relation.ReflTransGen (fun b c => c ∈ succ b) start b) → l.length ≤ bound)
    (hrounds : bound ≤ rounds) :
    a ∈ search succ rounds start ↔ Relation.ReflTransGen (fun b c => c ∈ succ b) start a :=
  mem_search_iff_of_closed (expand_search_eq_of_bound hbound hrounds)

/-! ### Searching until closed -/

/-- **The closing round**: the least number of rounds after which a round from `start` adds nothing,
or `0` if the search never closes. Searching until closed takes this many rounds, a number that
need not be known in advance. -/
noncomputable def closingRound (succ : α → List α) (start : α) : ℕ :=
  sInf {rounds | expand succ (search succ rounds start) = search succ rounds start}

/-- The search is closed after the closing round, if it ever closes. -/
theorem expand_search_closingRound {rounds : ℕ} {start : α}
    (h : expand succ (search succ rounds start) = search succ rounds start) :
    expand succ (search succ (closingRound succ start) start) =
      search succ (closingRound succ start) start :=
  Nat.sInf_mem (s := {rounds | expand succ (search succ rounds start) = search succ rounds start})
    ⟨rounds, h⟩

/-- The closing round is at most any round after which the search is closed. -/
theorem closingRound_le {rounds : ℕ} {start : α}
    (h : expand succ (search succ rounds start) = search succ rounds start) :
    closingRound succ start ≤ rounds :=
  Nat.sInf_le (s := {rounds | expand succ (search succ rounds start) = search succ rounds start}) h

/-- Before the closing round, every round finds a new element. -/
theorem expand_search_ne_of_lt_closingRound {rounds : ℕ} {start : α}
    (h : rounds < closingRound succ start) :
    expand succ (search succ rounds start) ≠ search succ rounds start :=
  fun hclosed => absurd (closingRound_le hclosed) (Nat.not_le.mpr h)

end Cslib.Reachability
