/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.System

/-! # Two watched literals

The watch store of the CDCL solver with watched literals (`CDCL.Watched`): an array of numbered
clauses without repetitions, each with at least two literals, whose first two literals are its
watches, and an array of watch lists indexed by literal (`watchIndex`).

`WatchStore.Inv F M Q` relates the store to the database `F`, the trail `M` and the queue `Q`: its
clauses are clauses of `F` up to repetition and order, every clause of `F` with two different
literals is stored, every clause is on the watch lists of its watches, and no clause has both
watches falsified by processed literals (`Processed`). With an empty queue, no clause with two
different literals is false (`WatchStore.Inv.not_falsifies`).

`WatchStore.visit` is the step of visiting one clause on the watch list of a falsified literal,
with its specification `WatchStore.visit_spec`.
-/

public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL

/-- The index of the watch list of a literal: `2 * v` for `¬v` and `2 * v + 1` for `v`. -/
@[expose] def watchIndex (l : Literal ℕ) : ℕ := 2 * l.1 + if l.2 then 1 else 0

/-- The watch list at index `i`, empty past the end of the array. -/
@[expose] def watchList (W : Array (List ℕ)) (i : ℕ) : List ℕ := W.getD i []

/-- Applying `f` to the watch list at index `i`, growing the array if needed. -/
@[expose] def modifyWatch (W : Array (List ℕ)) (i : ℕ) (f : List ℕ → List ℕ) : Array (List ℕ) :=
  let W' := if i < W.size then W else W ++ Array.replicate (i + 1 - W.size) []
  W'.modify i f

/-- Adding `k` to the watch list at index `i`, growing the array if needed. -/
@[expose] def addWatch (W : Array (List ℕ)) (i k : ℕ) : Array (List ℕ) :=
  modifyWatch W i (k :: ·)

/-- Replacing the watch list at index `i`, growing the array if needed. -/
@[expose] def setWatch (W : Array (List ℕ)) (i : ℕ) (L : List ℕ) : Array (List ℕ) :=
  modifyWatch W i fun _ => L

theorem watchList_grow (W : Array (List ℕ)) (i j : ℕ) :
    watchList (if i < W.size then W else W ++ Array.replicate (i + 1 - W.size) []) j =
      watchList W j := by
  unfold watchList
  split
  · rfl
  · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
    split
    · rfl
    · rename_i h
      simp only [Array.getElem?_replicate]
      split <;> simp [Array.getElem?_eq_none (by omega : W.size ≤ j)]

theorem i_lt_size_grow (W : Array (List ℕ)) (i : ℕ) :
    i < (if i < W.size then W else W ++ Array.replicate (i + 1 - W.size) []).size := by
  split
  · assumption
  · simp; omega

theorem watchList_modifyWatch (W : Array (List ℕ)) (i : ℕ) (f : List ℕ → List ℕ) (j : ℕ) :
    watchList (modifyWatch W i f) j = if j = i then f (watchList W i) else watchList W j := by
  unfold modifyWatch
  have hlt := i_lt_size_grow W i
  generalize hW' : (if i < W.size then W else W ++ Array.replicate (i + 1 - W.size) []) = W' at hlt
  have hgrow : ∀ j, watchList W' j = watchList W j := fun j => hW' ▸ watchList_grow W i j
  rw [← hgrow, ← hgrow]
  unfold watchList
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  split
  · subst j; simp [Array.getElem?_eq_getElem hlt]
  · rename_i hne
    simp [Ne.symm hne]

@[simp] theorem watchList_addWatch (W : Array (List ℕ)) (i k j : ℕ) :
    watchList (addWatch W i k) j = if j = i then k :: watchList W i else watchList W j :=
  watchList_modifyWatch W i _ j

@[simp] theorem watchList_setWatch (W : Array (List ℕ)) (i : ℕ) (L : List ℕ) (j : ℕ) :
    watchList (setWatch W i L) j = if j = i then L else watchList W j :=
  watchList_modifyWatch W i _ j

/-- **The watch store**: the clauses with at least two literals, each with its watched literals
first, and the watch lists, giving for each literal the clauses that may watch it. -/
structure WatchStore where
  /-- The numbered clauses, watched literals first. -/
  clauses : Array (ℕ × Clause ℕ)
  /-- The watch lists, by `watchIndex`: positions in `clauses`. -/
  watches : Array (List ℕ)

/-- A literal is *processed* if it is on the trail and no longer in the propagation queue. -/
@[expose] def Processed (M : Trail) (Q : List (Literal ℕ)) (x : Literal ℕ) : Prop :=
  x ∈ Trail.lits M ∧ x ∉ Q

/-- **The invariant of the watch store** for the numbered clauses `F`, the trail `M` and the
queue `Q`: its clauses are the clauses of `F` with at least two different literals, without
repetitions and up to order; each is on
the watch lists of its two watched literals; and no clause has both watched literals falsified by
processed literals. -/
structure WatchStore.Inv (F : List (ℕ × Clause ℕ)) (M : Trail) (Q : List (Literal ℕ))
    (S : WatchStore) : Prop where
  sound : ∀ e ∈ S.clauses, ∃ c, (e.1, c) ∈ F ∧ ∀ l, l ∈ e.2 ↔ l ∈ c
  nodup : ∀ e ∈ S.clauses, e.2.Nodup
  long : ∀ e ∈ S.clauses, 2 ≤ e.2.length
  covers : ∀ e ∈ F, 2 ≤ e.2.dedup.length → ∃ e' ∈ S.clauses, e'.1 = e.1 ∧ ∀ l, l ∈ e'.2 ↔ l ∈ e.2
  listed : ∀ (k : ℕ) (hk : k < S.clauses.size), ∀ w ∈ S.clauses[k].2.take 2,
    k ∈ watchList S.watches (watchIndex w)
  notBoth : ∀ e ∈ S.clauses, ∀ w₁ w₂ rest, e.2 = w₁ :: w₂ :: rest →
    ¬ (Processed M Q w₁.negate ∧ Processed M Q w₂.negate)

/-- **With the queue empty, no clause of at least two literals is false.** -/
theorem WatchStore.Inv.not_falsifies {F : List (ℕ × Clause ℕ)} {M : Trail} {S : WatchStore}
    (h : S.Inv F M []) {e : ℕ × Clause ℕ} (he : e ∈ F) (hlen : 2 ≤ e.2.dedup.length) :
    ¬ Trail.Falsifies M e.2 := by
  intro hfalse
  obtain ⟨e', he', -, hperm⟩ := h.covers e he hlen
  have hlen' := h.long e' he'
  match hc : e'.2, hlen' with
  | w₁ :: w₂ :: rest, _ =>
    refine h.notBoth e' he' w₁ w₂ rest hc ⟨⟨?_, List.not_mem_nil⟩, ⟨?_, List.not_mem_nil⟩⟩
    · exact hfalse w₁ ((hperm w₁).1 (hc ▸ List.mem_cons_self))
    · exact hfalse w₂ ((hperm w₂).1 (hc ▸ List.mem_cons_of_mem _ List.mem_cons_self))

/-! ### Visiting a watching clause -/

/-- The outcome of visiting the clause at position `k` of the store when its watched literal `u`
has become false. -/
inductive Visit
  /-- The other watched literal is true: the clause stays on the watch list of `u`. -/
  | keep
  /-- A literal that is not false replaces `u` as a watched literal. -/
  | move (S : WatchStore)
  /-- Every literal but the other watched literal `l` is false, and `l` is undefined: the clause
  numbered `id` is unit. -/
  | unit (l : Literal ℕ) (id : ℕ)
  /-- Every literal is false: the clause numbered `id` is in conflict. -/
  | conflict (id : ℕ)
  /-- The clause no longer watches `u`. -/
  | drop

/-- **Visiting the clause at position `k`** when its watched literal `u` has become false on the
trail `M`. -/
@[expose] def WatchStore.visit (S : WatchStore) (M : Trail) (u : Literal ℕ) (k : ℕ) : Visit :=
  match S.clauses[k]? with
  | some (id, w₁ :: w₂ :: rest) =>
    if w₁ = u ∨ w₂ = u then
      let other := if w₁ = u then w₂ else w₁
      if (Trail.lits M).contains other then .keep
      else
        match rest.find? (fun x => !(Trail.lits M).contains x.negate) with
        | some x =>
          .move ⟨S.clauses.setIfInBounds k (id, other :: x :: u :: rest.erase x),
            addWatch S.watches (watchIndex x) k⟩
        | none => if (Trail.lits M).contains other.negate then .conflict id else .unit other id
    else .drop
  | _ => .drop

/-- The other watched literal of a clause watching `u` with watched literals `w₁` and `w₂`. -/
@[expose] def otherWatch (u w₁ w₂ : Literal ℕ) : Literal ℕ := if w₁ = u then w₂ else w₁

/-- **What a visit finds**, by outcome. -/
@[expose] def VisitSpec (S : WatchStore) (M : Trail) (u : Literal ℕ) (k : ℕ) : Visit → Prop
  | .keep => ∃ (hk : k < S.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.clauses[k].2 = w₁ :: w₂ :: rest ∧ (w₁ = u ∨ w₂ = u) ∧ otherWatch u w₁ w₂ ∈ Trail.lits M
  | .move S' => ∃ (hk : k < S.clauses.size) (id : ℕ) (w₁ w₂ x : Literal ℕ) (rest : Clause ℕ),
      S.clauses[k] = (id, w₁ :: w₂ :: rest) ∧ (w₁ = u ∨ w₂ = u) ∧ x ∈ rest ∧
      x.negate ∉ Trail.lits M ∧
      S' = ⟨S.clauses.setIfInBounds k (id, otherWatch u w₁ w₂ :: x :: u :: rest.erase x),
        addWatch S.watches (watchIndex x) k⟩
  | .unit l id => ∃ (hk : k < S.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.clauses[k] = (id, w₁ :: w₂ :: rest) ∧ (w₁ = u ∨ w₂ = u) ∧ l = otherWatch u w₁ w₂ ∧
      l ∉ Trail.lits M ∧ l.negate ∉ Trail.lits M ∧ ∀ x ∈ rest, x.negate ∈ Trail.lits M
  | .conflict id => ∃ (hk : k < S.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.clauses[k] = (id, w₁ :: w₂ :: rest) ∧ (w₁ = u ∨ w₂ = u) ∧
      (otherWatch u w₁ w₂).negate ∈ Trail.lits M ∧ ∀ x ∈ rest, x.negate ∈ Trail.lits M
  | .drop => ∀ (hk : k < S.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.clauses[k].2 = w₁ :: w₂ :: rest → w₁ ≠ u ∧ w₂ ≠ u

/-- **The visit meets its specification.** -/
theorem WatchStore.visit_spec (S : WatchStore) (M : Trail) (u : Literal ℕ) (k : ℕ) :
    VisitSpec S M u k (S.visit M u k) := by
  unfold visit
  split
  · rename_i id w₁ w₂ rest hk
    obtain ⟨hk', hget⟩ := Array.getElem?_eq_some_iff.1 hk
    by_cases hu : w₁ = u ∨ w₂ = u
    · simp only [hu, ↓reduceIte]
      by_cases htrue : (Trail.lits M).contains (if w₁ = u then w₂ else w₁) = true
      · simp only [htrue, ↓reduceIte]
        exact ⟨hk', w₁, w₂, rest, by rw [hget], hu, by simpa [otherWatch] using htrue⟩
      · simp only [htrue, Bool.false_eq_true, ↓reduceIte]
        split
        · rename_i x hx
          have hxmem := List.mem_of_find?_eq_some hx
          have hxval := List.find?_some hx
          exact ⟨hk', id, w₁, w₂, x, rest, hget, hu, hxmem, by simpa using hxval, rfl⟩
        · rename_i hnone
          have hall : ∀ x ∈ rest, x.negate ∈ Trail.lits M := fun x hx => by
            simpa using List.find?_eq_none.1 hnone x hx
          by_cases hfalse : (Trail.lits M).contains
              (Std.Sat.Literal.negate (if w₁ = u then w₂ else w₁)) = true
          · simp only [hfalse, ↓reduceIte]
            exact ⟨hk', w₁, w₂, rest, hget, hu, by simpa [otherWatch] using hfalse, hall⟩
          · simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
            exact ⟨hk', w₁, w₂, rest, hget, hu, rfl, by simpa [otherWatch] using htrue,
              by simpa [otherWatch] using hfalse, hall⟩
    · simp only [hu, ↓reduceIte]
      intro hk'' v₁ v₂ rest' hc
      rw [hget] at hc
      simp only [List.cons.injEq] at hc
      obtain ⟨rfl, rfl, -⟩ := hc
      push Not at hu
      exact hu
  · rename_i hne
    intro hk' v₁ v₂ rest' hc
    exact absurd (by rw [Array.getElem?_eq_getElem hk', ← hc]) (hne (S.clauses[k].1) v₁ v₂ rest')

/-! ### Changing the trail and the clauses -/

/-- The invariant survives a trail and queue with fewer processed literals. -/
theorem WatchStore.Inv.weaken {F : List (ℕ × Clause ℕ)} {M M' : Trail}
    {Q Q' : List (Literal ℕ)} {S : WatchStore} (h : S.Inv F M Q)
    (hproc : ∀ x, Processed M' Q' x → Processed M Q x) : S.Inv F M' Q' :=
  ⟨h.sound, h.nodup, h.long, h.covers, h.listed, fun e he w₁ w₂ rest hc ⟨h₁, h₂⟩ =>
    h.notBoth e he w₁ w₂ rest hc ⟨hproc _ h₁, hproc _ h₂⟩⟩

/-- A short clause added to the database leaves the store unchanged. -/
theorem WatchStore.Inv.consShort {F : List (ℕ × Clause ℕ)} {M : Trail} {Q : List (Literal ℕ)}
    {S : WatchStore} (h : S.Inv F M Q) (e : ℕ × Clause ℕ) (hshort : e.2.dedup.length < 2) :
    S.Inv (e :: F) M Q :=
  ⟨fun e' he' => by
      obtain ⟨c, hc, hm⟩ := h.sound e' he'
      exact ⟨c, List.mem_cons_of_mem _ hc, hm⟩,
    h.nodup, h.long, fun e' he' hlen => by
      rcases List.mem_cons.1 he' with rfl | he'
      · omega
      · exact h.covers e' he' hlen,
    h.listed, h.notBoth⟩

/-- Adding a clause without repetitions to the store, watching its first two literals. -/
@[expose] def WatchStore.addClause (S : WatchStore) (id : ℕ) (c : Clause ℕ) : WatchStore :=
  match c with
  | w₁ :: w₂ :: _ =>
    ⟨S.clauses.push (id, c), addWatch (addWatch S.watches (watchIndex w₁) S.clauses.size)
      (watchIndex w₂) S.clauses.size⟩
  | _ => S

/-- Adding a clause of the database, without repetitions, whose first watched literal is not
falsified by a processed literal. -/
theorem WatchStore.Inv.addClause {F : List (ℕ × Clause ℕ)} {M : Trail} {Q : List (Literal ℕ)}
    {S : WatchStore} (h : S.Inv F M Q) {id : ℕ} {C : Clause ℕ} {w₁ w₂ : Literal ℕ}
    {rest : Clause ℕ} (hnd : (w₁ :: w₂ :: rest).Nodup)
    (hmem : ∀ l, l ∈ w₁ :: w₂ :: rest ↔ l ∈ C) (hw₁ : ¬ Processed M Q w₁.negate) :
    (S.addClause id (w₁ :: w₂ :: rest)).Inv ((id, C) :: F) M Q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e' he'
    rcases Array.mem_push.1 he' with he' | rfl
    · obtain ⟨c, hc', hp⟩ := h.sound e' he'
      exact ⟨c, List.mem_cons_of_mem _ hc', hp⟩
    · exact ⟨C, List.mem_cons_self, hmem⟩
  · intro e' he'
    rcases Array.mem_push.1 he' with he' | rfl
    · exact h.nodup e' he'
    · exact hnd
  · intro e' he'
    rcases Array.mem_push.1 he' with he' | rfl
    · exact h.long e' he'
    · simp
  · intro e' he' hlen
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨_, Array.mem_push_self, rfl, hmem⟩
    · obtain ⟨e'', he'', h1, h2⟩ := h.covers e' he' hlen
      exact ⟨e'', Array.mem_push_of_mem _ he'', h1, h2⟩
  · intro k hk w hw
    simp only [WatchStore.addClause, Array.size_push] at hk
    simp only [WatchStore.addClause, watchList_addWatch]
    by_cases hks : k = S.clauses.size
    · subst hks
      simp only [WatchStore.addClause, Array.getElem_push_eq, List.take_succ_cons, List.take_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> split_ifs <;> simp_all
    · have hk' : k < S.clauses.size := by omega
      simp only [WatchStore.addClause] at hw
      rw [Array.getElem_push_lt hk'] at hw
      have := h.listed k hk' w hw
      split
      · exact List.mem_cons_of_mem _ (by split <;> simp_all)
      · split
        · exact List.mem_cons_of_mem _ (by simp_all)
        · exact this
  · intro e' he' v₁ v₂ rest' hc' hboth
    rcases Array.mem_push.1 he' with he' | rfl
    · exact h.notBoth e' he' v₁ v₂ rest' hc' hboth
    · simp only [List.cons.injEq] at hc'
      obtain ⟨rfl, -, -⟩ := hc'
      exact hw₁ hboth.1

/-- The watch store of the numbered clauses `F`: every clause with at least two different literals,
without repetitions, watching its first two literals. It adds the clauses with
`Cslib.Algorithms.Lean.CDCL.WatchStore.addClause`, as learning does. -/
@[expose] def WatchStore.build : List (ℕ × Clause ℕ) → WatchStore
  | [] => ⟨#[], #[]⟩
  | e :: F => (WatchStore.build F).addClause e.1 e.2.dedup

/-- The watch store built from `F` satisfies the invariant with the empty trail. -/
theorem WatchStore.build_inv : ∀ F : List (ℕ × Clause ℕ), (WatchStore.build F).Inv F [] []
  | [] => ⟨by simp [build], by simp [build], by simp [build], fun e he => by simp at he,
      fun k hk => by simp [build] at hk, by simp [build]⟩
  | ⟨id, c⟩ :: F => by
    have ih := build_inv F
    simp only [build]
    match hc : c.dedup with
    | w₁ :: w₂ :: rest =>
      exact ih.addClause (hc ▸ List.nodup_dedup c) (fun l => by rw [← hc, List.mem_dedup])
        (by simp [Processed, Trail.lits])
    | [] => exact ih.consShort (id, c) (by simp [hc])
    | [_] => exact ih.consShort (id, c) (by simp [hc])

end Cslib.Algorithms.Lean.CDCL
