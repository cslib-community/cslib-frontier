/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.Swap
public import Mathlib.Data.List.Sort
import CslibFrontier.Foundations.Data.List.Blocks
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Range

/-!
# A computed stable adjacent-exchange trace

`AdjacentSortTrace.compute` instruments the existing `List.orderedInsert`: sort the tail,
shift its requests, then move the original head past strictly smaller keys. Equal keys are
never crossed. Requests act on arbitrary accompanying payloads, not changing variable names.

The first substantive property is `replay_compute`: the actual computed requests replay the
existing stable insertion sort on any payload/key map. `components_compute` supplies valid
indices and a triangular bound; `indices_payload` identifies the actual original-index
permutation. This is original trace instrumentation, reusing the library's sorting proofs.
-/

public section

open List

namespace Cslib.AdjacentSortTrace

/-- The actual accumulator and output: sorted original binary keys, followed by the adjacent
positions to execute in order. Repeated keys remain repeated occurrences. -/
structure Result where
  /-- Original keys in stable nondecreasing order. -/
  sortedKeys : List ℕ
  /-- Binary positions of adjacent exchanges, in execution order. -/
  requests : List ℕ

/-- Insert one original head key. The existing tail trace is shifted below it; the new
requests cross exactly the strictly smaller prefix, and hence never cross equal keys. -/
@[expose] def insert (a : ℕ) (r : Result) : Result :=
  ⟨List.orderedInsert (· ≤ ·) a r.sortedKeys,
    r.requests.map Nat.succ ++
      List.range (r.sortedKeys.takeWhile (fun b => b<a)).length⟩

/-- Compute a stable trace by a literal fold over the original keys from right to left.
All traversal clocks come from lists; binary key magnitudes are only compared. -/
@[expose] def compute (keys : List ℕ) : Result :=
  keys.reverse.foldl (fun r a => insert a r) ⟨[], []⟩

private theorem compute_cons (a : ℕ) (keys : List ℕ) :
    compute (a::keys) = insert a (compute keys) := by
  simp [compute, List.reverse_cons, List.foldl_append]

private theorem shifted_replay {α : Type*} (js : List ℕ) (a : α) (xs : List α) :
    (js.map Nat.succ).foldl (fun ys j => ys.swap j (j+1)) (a::xs) =
      a :: js.foldl (fun ys j => ys.swap j (j+1)) xs := by
  rw [List.foldl_map]
  exact List.foldl_hom (List.cons a) (fun ys j => List.swap_cons (a := a))

private theorem range_replay {α : Type*} (a : α) (xs : List α) (t : ℕ)
    (ht : t ≤ xs.length) :
    (List.range t).foldl (fun ys j => ys.swap j (j+1)) (a::xs) =
      xs.take t ++ a :: xs.drop t := by
  induction t generalizing xs with
  | zero => simp
  | succ t ih =>
    rcases xs with _ | ⟨b, xs⟩
    · simp at ht
    · rw [List.range_succ_eq_map, List.foldl_cons]
      simp only [List.swap, List.getElem?_cons_zero, Option.getD_some, List.set_cons_zero]
      rw [shifted_replay, ih xs (Nat.le_of_succ_le_succ ht)]
      simp

/-- Exact sorted original keys, at most `choose P 2` requests, and every emitted request
valid for the original length `P`. These facts hold for every raw binary key list. -/
theorem components_compute (keys : List ℕ) :
    (compute keys).sortedKeys = keys.insertionSort (· ≤ ·) ∧
      (compute keys).requests.length ≤ keys.length.choose 2 ∧
      ∀ j ∈ (compute keys).requests, j+1<keys.length := by
  induction keys with
  | nil => simp [compute]
  | cons a keys ih =>
    rw [compute_cons]
    have ht : ((compute keys).sortedKeys.takeWhile (· < a)).length ≤ keys.length :=
      (List.takeWhile_sublist _).length_le.trans (ih.1 ▸ List.length_insertionSort ..).le
    refine ⟨?_, ?_, fun j hj => ?_⟩
    · change List.orderedInsert (· ≤ ·) a (compute keys).sortedKeys = _
      rw [ih.1, List.insertionSort_cons]
    · simp only [insert, List.length_append, List.length_map, List.length_range, List.length_cons]
      rw [Nat.choose_succ_succ keys.length 1, Nat.choose_one_right]
      change _ ≤ keys.length + keys.length.choose 2
      have := ih.2.1
      omega
    · simp only [insert, List.mem_append, List.mem_map, List.mem_range] at hj
      rcases hj with ⟨k, hk, rfl⟩ | hj
      · exact Nat.succ_lt_succ (ih.2.2 k hk)
      · exact Nat.succ_lt_succ (lt_of_lt_of_le hj ht)

/-- The literal requests replay stable insertion sort on any accompanying payload. Only
its original key map is inspected; payloads, including equal-key occurrences, are retained. -/
theorem replay_compute {α : Type*} (key : α → ℕ) (xs : List α) :
    (compute (xs.map key)).requests.foldl (fun ys j => ys.swap j (j+1)) xs =
      xs.insertionSort (fun a b => key a ≤ key b) := by
  induction xs with
  | nil => simp [compute]
  | cons a xs ih =>
    rw [List.map_cons, compute_cons]
    simp only [insert, List.foldl_append, shifted_replay, ih, (components_compute (xs.map key)).1,
      ← List.map_insertionSort (fun a b => key a ≤ key b) (· ≤ ·) key xs (fun _ _ _ _ => Iff.rfl),
      List.takeWhile_map, List.length_map, Function.comp_def]
    rw [range_replay a _ _ (List.takeWhile_sublist _).length_le, List.insertionSort_cons,
      List.orderedInsert_eq_take_drop]
    simp only [Nat.not_le, List.takeWhile_eq_take_findIdx_not, List.dropWhile_eq_drop_findIdx_not,
      List.length_take, Nat.min_eq_left List.findIdx_le_length]

/-- The computed index word is a permutation of all original indices. Applying the SAME
requests to any indexed payload gives that word mapped by the payload, not a chosen sorting
permutation. Equal-key original-index pairs remain sublists, by the existing
`List.pair_sublist_insertionSort` stability theorem. -/
theorem indices_payload (keys : List ℕ) :
    let ids := (compute keys).requests.foldl (fun ys j => ys.swap j (j+1))
      (List.range keys.length)
    ids.Perm (List.range keys.length) ∧
      (∀ {α : Type*} (f : ℕ → α),
        (compute keys).requests.foldl (fun ys j => ys.swap j (j+1))
          ((List.range keys.length).map f) = ids.map f) ∧
      ∀ i j, [i,j] <+ List.range keys.length → keys.getD i 0=keys.getD j 0 →
        [i,j] <+ ids := by
  refine ⟨?_, fun f => List.foldl_hom (List.map f) fun ys j => (List.map_swap f ys j (j + 1)).symm,
    fun i j hp he => ?_⟩
  · suffices ∀ (js xs : List ℕ), (js.foldl (fun ys k => ys.swap k (k + 1)) xs).Perm xs from
      this _ _
    intro js
    induction js with
    | nil => exact fun _ => .refl _
    | cons k ks ih => exact fun xs => (ih _).trans (List.swap_perm xs k (k + 1))
  · have hr := replay_compute (keys.getD · 0) (List.range keys.length)
    rw [List.map_getD_range keys 0] at hr
    exact hr.symm ▸ List.pair_sublist_insertionSort (by simp only [he, le_refl]) hp

/-- Already sorted keys produce no requests at all; execution therefore preserves the
ENTIRE raw payload State, rather than just canceling its value permutation. -/
theorem requests_eq_nil_of_pairwise (keys : List ℕ) (h : keys.Pairwise (· ≤ ·)) :
    (compute keys).requests = [] := by
  induction keys with
  | nil => rfl
  | cons a keys ih =>
    obtain ⟨ha, hk⟩ := List.pairwise_cons.mp h
    rw [compute_cons]
    simp only [insert, ih hk, (components_compute keys).1, hk.insertionSort_eq, List.map_nil,
      List.nil_append, List.range_eq_nil, List.length_eq_zero_iff]
    rcases keys with _ | ⟨b, keys⟩
    · rfl
    · simp [Nat.not_lt.mpr (ha b List.mem_cons_self)]

end Cslib.AdjacentSortTrace
