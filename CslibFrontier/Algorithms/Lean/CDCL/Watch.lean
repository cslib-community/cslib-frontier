/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.Assign

/-! # Two watched literals

The watch store of the CDCL solver: an array of numbered clauses without repetitions, each with
at least two literals, whose first two literals are its watches, and an array of watch lists
indexed by literal (`litKey`). A watch list holds *watchers* (`Watcher`): the position of a
clause and a *blocker*, a literal of the clause. As in MiniSat, a watcher whose blocker is true is
skipped without reading its clause.

`WatchStore.Inv F M Q` relates the store to the database `F`, the trail `M` and the queue `Q`: its
clauses are clauses of `F` up to repetition and order, every clause of `F` with two different
literals is stored, every clause is on the watch lists of its watches, every blocker is a literal
of its clause, and a clause with both watches falsified by processed literals (`Processed`) has a
*supported* literal (`Supported`): a true literal that stays true after any backjump keeping both
watches false. Support needs no decision levels: it quantifies over the splits of the trail at a
decision, and survives extending the trail (`Supported.cons`) and backjumping
(`Supported.backjump`). With an empty queue, no clause with two different literals is false
(`WatchStore.Inv.not_falsifies`).

`WatchStore.visit` is the step of visiting one watcher on the watch list of a falsified literal,
with its specification `WatchStore.visit_spec`; it reads the values of literals from an assignment
indexed by variable (`Assign`) agreeing with the trail. `WatchStore.build` builds a store on a
trail, watching literals that are not false, so that it satisfies the invariant with every literal
of the trail processed as long as no clause is false (`WatchStore.build_inv`).
-/

public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL

/-- **A watcher**: a clause of the store, by position, and its *blocker*, a literal of the clause.
When the blocker is true, the clause is satisfied and is skipped without being read. -/
structure Watcher where
  /-- The position of the clause in the store. -/
  clause : ℕ
  /-- A literal of the clause. -/
  blocker : Literal ℕ

/-- The positions of the clauses of a list of watchers. -/
abbrev clauseIds (L : List Watcher) : List ℕ := L.map Watcher.clause

/-- The watch list at index `i`, empty past the end of the array. -/
@[expose] def watchList (W : Array (List Watcher)) (i : ℕ) : List Watcher := W.getD i []

/-- Applying `f` to the watch list at index `i`, growing the array if needed. -/
@[expose] def modifyWatch (W : Array (List Watcher)) (i : ℕ) (f : List Watcher → List Watcher) :
    Array (List Watcher) :=
  let W' := if i < W.size then W else W ++ Array.replicate (i + 1 - W.size) []
  W'.modify i f

/-- Adding the watcher `k` to the watch list at index `i`, growing the array if needed. -/
@[expose] def addWatch (W : Array (List Watcher)) (i : ℕ) (k : Watcher) : Array (List Watcher) :=
  modifyWatch W i (k :: ·)

/-- Replacing the watch list at index `i`, growing the array if needed. -/
@[expose]
def setWatch (W : Array (List Watcher)) (i : ℕ) (L : List Watcher) : Array (List Watcher) :=
  modifyWatch W i fun _ => L

theorem watchList_grow (W : Array (List Watcher)) (i j : ℕ) :
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

theorem i_lt_size_grow (W : Array (List Watcher)) (i : ℕ) :
    i < (if i < W.size then W else W ++ Array.replicate (i + 1 - W.size) []).size := by
  split
  · assumption
  · simp; omega

theorem watchList_modifyWatch (W : Array (List Watcher)) (i : ℕ) (f : List Watcher → List Watcher)
    (j : ℕ) :
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

@[simp] theorem watchList_addWatch (W : Array (List Watcher)) (i : ℕ) (k : Watcher) (j : ℕ) :
    watchList (addWatch W i k) j = if j = i then k :: watchList W i else watchList W j :=
  watchList_modifyWatch W i _ j

theorem mem_watchList_addWatch {W : Array (List Watcher)} {i j : ℕ} {k x : Watcher}
    (h : x ∈ watchList (addWatch W i k) j) : x = k ∨ x ∈ watchList W j := by
  rw [watchList_addWatch] at h
  split at h
  · rename_i hj
    subst hj
    exact List.mem_cons.1 h
  · exact .inr h

@[simp] theorem watchList_setWatch (W : Array (List Watcher)) (i : ℕ) (L : List Watcher) (j : ℕ) :
    watchList (setWatch W i L) j = if j = i then L else watchList W j :=
  watchList_modifyWatch W i _ j

/-- **The watch store**: the clauses with at least two literals, each with its watched literals
first, and the watch lists, giving for each literal the clauses that may watch it. -/
structure WatchStore where
  /-- The numbered clauses, watched literals first. -/
  clauses : Array (ℕ × Clause ℕ)
  /-- The watch lists, by `litKey`. -/
  watches : Array (List Watcher)

/-- A literal is *processed* if it is on the trail and no longer in the propagation queue. -/
@[expose] def Processed (M : Trail) (Q : List (Literal ℕ)) (x : Literal ℕ) : Prop :=
  x ∈ Trail.lits M ∧ x ∉ Q

/-- A literal `b` of a clause with watched literals `w₁` and `w₂` is *supported* on the trail `M`
when it is true and stays true after any backjump that keeps both watched literals false: for
every split `M = N ++ dᵈ :: M₀` at a decision `d`, not only the newest, with `w₁` and `w₂` false in
`M₀`, `b` is true in `M₀`. Quantifying over every decision lets support survive repeated
backjumps. -/
@[expose] def Supported (M : Trail) (b w₁ w₂ : Literal ℕ) : Prop :=
  b ∈ Trail.lits M ∧ ∀ N d M₀, M = N ++ ⟨d, true⟩ :: M₀ →
    w₁.negate ∈ Trail.lits M₀ → w₂.negate ∈ Trail.lits M₀ → b ∈ Trail.lits M₀

/-- Support survives extending the trail. -/
theorem Supported.cons {M : Trail} {b w₁ w₂ : Literal ℕ} (h : Supported M b w₁ w₂) (x : Entry) :
    Supported (x :: M) b w₁ w₂ := by
  refine ⟨List.mem_cons_of_mem _ h.1, fun N d M₀ hN h₁ h₂ => ?_⟩
  cases N with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at hN
    exact hN.2 ▸ h.1
  | cons y N =>
    simp only [List.cons_append, List.cons.injEq] at hN
    exact h.2 N d M₀ hN.2 h₁ h₂

/-- Support survives going back below a decision, to a trail where both watched literals are
false. -/
theorem Supported.truncate {M M₀ N : Trail} {d : Literal ℕ} {b w₁ w₂ : Literal ℕ}
    (h : Supported M b w₁ w₂) (hM : M = N ++ ⟨d, true⟩ :: M₀) (h₁ : w₁.negate ∈ Trail.lits M₀)
    (h₂ : w₂.negate ∈ Trail.lits M₀) : Supported M₀ b w₁ w₂ :=
  ⟨h.2 N d M₀ hM h₁ h₂, fun N' d' M₁ hN' h₁' h₂' =>
    h.2 (N ++ ⟨d, true⟩ :: N') d' M₁ (by rw [hM, hN']; simp) h₁' h₂'⟩

/-- Support survives a backjump below a decision that keeps both watched literals false. -/
theorem Supported.backjump {M M₀ N : Trail} {d : Literal ℕ} {b w₁ w₂ : Literal ℕ}
    (h : Supported M b w₁ w₂) (hM : M = N ++ ⟨d, true⟩ :: M₀) (h₁ : w₁.negate ∈ Trail.lits M₀)
    (h₂ : w₂.negate ∈ Trail.lits M₀) (x : Entry) : Supported (x :: M₀) b w₁ w₂ :=
  (h.truncate hM h₁ h₂).cons x

/-- **The invariant of the watch store** for the numbered clauses `F`, the trail `M` and the
queue `Q`: its clauses are the clauses of `F` with at least two different literals, without
repetitions and up to order; each is on the watch lists of its two watched literals; every
blocker is a literal of its clause; and a clause with both watched literals falsified by processed
literals has a supported literal. -/
structure WatchStore.Inv (F : List (ℕ × Clause ℕ)) (M : Trail) (Q : List (Literal ℕ))
    (S : WatchStore) : Prop where
  sound : ∀ e ∈ S.clauses, ∃ c, (e.1, c) ∈ F ∧ ∀ l, l ∈ e.2 ↔ l ∈ c
  nodup : ∀ e ∈ S.clauses, e.2.Nodup
  long : ∀ e ∈ S.clauses, 2 ≤ e.2.length
  covers : ∀ e ∈ F, 2 ≤ e.2.dedup.length → ∃ e' ∈ S.clauses, e'.1 = e.1 ∧ ∀ l, l ∈ e'.2 ↔ l ∈ e.2
  listed : ∀ (k : ℕ) (hk : k < S.clauses.size), ∀ w ∈ S.clauses[k].2.take 2,
    k ∈ clauseIds (watchList S.watches (litKey w))
  blocker_mem : ∀ i, ∀ x ∈ watchList S.watches i, ∃ (hk : x.clause < S.clauses.size),
    x.blocker ∈ S.clauses[x.clause].2
  covered : ∀ e ∈ S.clauses, ∀ w₁ w₂ rest, e.2 = w₁ :: w₂ :: rest →
    Processed M Q w₁.negate → Processed M Q w₂.negate → ∃ b ∈ e.2, Supported M b w₁ w₂

/-- **With the queue empty, no clause of at least two literals is false.** -/
theorem WatchStore.Inv.not_falsifies {F : List (ℕ × Clause ℕ)} {M : Trail} {S : WatchStore}
    (h : S.Inv F M []) (hM : (Trail.vars M).Nodup) {e : ℕ × Clause ℕ} (he : e ∈ F)
    (hlen : 2 ≤ e.2.dedup.length) : ¬ Trail.Falsifies M e.2 := by
  intro hfalse
  obtain ⟨e', he', -, hperm⟩ := h.covers e he hlen
  have hlen' := h.long e' he'
  match hc : e'.2, hlen' with
  | w₁ :: w₂ :: rest, _ =>
    obtain ⟨b, hb, hsupp⟩ := h.covered e' he' w₁ w₂ rest hc
      ⟨hfalse w₁ ((hperm w₁).1 (hc ▸ List.mem_cons_self)), List.not_mem_nil⟩
      ⟨hfalse w₂ ((hperm w₂).1 (hc ▸ List.mem_cons_of_mem _ List.mem_cons_self)),
        List.not_mem_nil⟩
    exact Trail.negate_not_mem hM hsupp.1 (hfalse b ((hperm b).1 (hc ▸ hb)))

/-! ### Visiting a watching clause -/

/-- The outcome of visiting a watcher of the store when its watched literal `u` has become
false. -/
inductive Visit
  /-- The blocker is true: the watcher stays on the watch list of `u`, and the clause is not
  read. -/
  | skip
  /-- The other watched literal `b` is true: the clause stays on the watch list of `u`, with `b` as
  blocker. -/
  | keep (b : Literal ℕ)
  /-- A literal `x` that is not false replaces `u` as a watched literal: the clause becomes `c`,
  watching `x` with the blocker `b` (`Cslib.Algorithms.Lean.CDCL.WatchStore.moveTo`). -/
  | move (c : ℕ × Clause ℕ) (x b : Literal ℕ)
  /-- Every literal but the other watched literal `l` is false, and `l` is undefined: the clause
  numbered `id` is unit. -/
  | unit (l : Literal ℕ) (id : ℕ)
  /-- Every literal is false: the clause numbered `id` is in conflict. -/
  | conflict (id : ℕ)
  /-- The clause no longer watches `u`. -/
  | drop

/-- **Visiting a watcher** when its watched literal `u` has become false under the assignment `A`:
it is skipped if its blocker is true; otherwise its clause is read. -/
@[expose]
def WatchStore.visit (S : WatchStore) (A : Assign) (u : Literal ℕ) (w : Watcher) : Visit :=
  if A.holds w.blocker then .skip
  else
    match S.clauses[w.clause]? with
    | some (id, w₁ :: w₂ :: rest) =>
      if w₁ = u ∨ w₂ = u then
        let other := if w₁ = u then w₂ else w₁
        if A.holds other then .keep other
        else
          match rest.find? (fun x => !A.holds x.negate) with
          | some x => .move (id, other :: x :: u :: rest.erase x) x other
          | none =>
            if A.holds other.negate then .conflict id else .unit other id
      else .drop
    | _ => .drop

/-- **Moving a watch**: the clause at position `k` becomes `c`, and the watch list of `x` gets a
watcher of it with the blocker `b`. The two arrays are taken out of the store first, so that they
are updated in place when the store is not shared. -/
@[expose] def WatchStore.moveTo (S : WatchStore) (k : ℕ) (c : ℕ × Clause ℕ) (x b : Literal ℕ) :
    WatchStore :=
  let clauses := S.clauses
  let watches := S.watches
  ⟨clauses.setIfInBounds k c, addWatch watches (litKey x) ⟨k, b⟩⟩

/-- The other watched literal of a clause watching `u` with watched literals `w₁` and `w₂`. -/
@[expose] def otherWatch (u w₁ w₂ : Literal ℕ) : Literal ℕ := if w₁ = u then w₂ else w₁

/-- **What a visit of the watcher `w` finds**, by outcome. -/
@[expose] def VisitSpec (S : WatchStore) (M : Trail) (u : Literal ℕ) (w : Watcher) : Visit → Prop
  | .skip => w.blocker ∈ Trail.lits M
  | .keep b => ∃ (hk : w.clause < S.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.clauses[w.clause].2 = w₁ :: w₂ :: rest ∧ (w₁ = u ∨ w₂ = u) ∧ b = otherWatch u w₁ w₂ ∧
      b ∈ Trail.lits M
  | .move c x b => ∃ (hk : w.clause < S.clauses.size) (id : ℕ) (w₁ w₂ : Literal ℕ)
      (rest : Clause ℕ),
      S.clauses[w.clause] = (id, w₁ :: w₂ :: rest) ∧ (w₁ = u ∨ w₂ = u) ∧ x ∈ rest ∧
      x.negate ∉ Trail.lits M ∧ c = (id, otherWatch u w₁ w₂ :: x :: u :: rest.erase x) ∧
      b = otherWatch u w₁ w₂
  | .unit l id => ∃ (hk : w.clause < S.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.clauses[w.clause] = (id, w₁ :: w₂ :: rest) ∧ (w₁ = u ∨ w₂ = u) ∧
      l = otherWatch u w₁ w₂ ∧ l ∉ Trail.lits M ∧ l.negate ∉ Trail.lits M ∧
      ∀ x ∈ rest, x.negate ∈ Trail.lits M
  | .conflict id => ∃ (hk : w.clause < S.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.clauses[w.clause] = (id, w₁ :: w₂ :: rest) ∧ (w₁ = u ∨ w₂ = u) ∧
      (otherWatch u w₁ w₂).negate ∈ Trail.lits M ∧ ∀ x ∈ rest, x.negate ∈ Trail.lits M
  | .drop => ∀ (hk : w.clause < S.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.clauses[w.clause].2 = w₁ :: w₂ :: rest → w₁ ≠ u ∧ w₂ ≠ u

/-- **The visit meets its specification**, under an assignment agreeing with the trail. -/
theorem WatchStore.visit_spec (S : WatchStore) {A : Assign} {M : Trail} (hA : A.Agrees M)
    (u : Literal ℕ) (w : Watcher) : VisitSpec S M u w (S.visit A u w) := by
  unfold visit
  simp only [hA.holds_iff, ← List.contains_iff_mem]
  by_cases hb : (Trail.lits M).contains w.blocker = true
  · simp only [hb, ↓reduceIte, VisitSpec]
    simpa using hb
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i id w₁ w₂ rest hk
    obtain ⟨hk', hget⟩ := Array.getElem?_eq_some_iff.1 hk
    by_cases hu : w₁ = u ∨ w₂ = u
    · simp only [hu, ↓reduceIte]
      by_cases htrue : (Trail.lits M).contains (if w₁ = u then w₂ else w₁) = true
      · simp only [htrue, ↓reduceIte]
        exact ⟨hk', w₁, w₂, rest, by rw [hget], hu, rfl, by simpa [otherWatch] using htrue⟩
      · simp only [htrue, Bool.false_eq_true, ↓reduceIte]
        split
        · rename_i x hx
          have hxmem := List.mem_of_find?_eq_some hx
          have hxval := List.find?_some hx
          exact ⟨hk', id, w₁, w₂, rest, hget, hu, hxmem,
            fun h => by simp [(hA.holds_iff _).2 h] at hxval, rfl, rfl⟩
        · rename_i hnone
          have hall : ∀ x ∈ rest, x.negate ∈ Trail.lits M := fun x hx => by
            simpa [hA.holds_iff] using List.find?_eq_none.1 hnone x hx
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
    exact absurd (by rw [Array.getElem?_eq_getElem hk', ← hc])
      (hne (S.clauses[w.clause].1) v₁ v₂ rest')

/-! ### Changing the trail and the clauses -/

/-- The invariant survives a change of trail and queue that processes no new literal and keeps
the support of the clauses with both watched literals falsified by processed literals. -/
theorem WatchStore.Inv.weaken {F : List (ℕ × Clause ℕ)} {M M' : Trail}
    {Q Q' : List (Literal ℕ)} {S : WatchStore} (h : S.Inv F M Q)
    (hproc : ∀ x, Processed M' Q' x → Processed M Q x)
    (hsupp : ∀ b w₁ w₂, Processed M' Q' w₁.negate → Processed M' Q' w₂.negate →
      Supported M b w₁ w₂ → Supported M' b w₁ w₂) : S.Inv F M' Q' :=
  ⟨h.sound, h.nodup, h.long, h.covers, h.listed, h.blocker_mem, fun e he w₁ w₂ rest hc h₁ h₂ => by
    obtain ⟨b, hb, hs⟩ := h.covered e he w₁ w₂ rest hc (hproc _ h₁) (hproc _ h₂)
    exact ⟨b, hb, hsupp b w₁ w₂ h₁ h₂ hs⟩⟩

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
    h.listed, h.blocker_mem, h.covered⟩

/-- Adding a clause without repetitions to the store, watching its first two literals, each with
the other as blocker. -/
@[expose] def WatchStore.addClause (S : WatchStore) (id : ℕ) (c : Clause ℕ) : WatchStore :=
  match c with
  | w₁ :: w₂ :: _ =>
    ⟨S.clauses.push (id, c), addWatch (addWatch S.watches (litKey w₁) ⟨S.clauses.size, w₂⟩)
      (litKey w₂) ⟨S.clauses.size, w₁⟩⟩
  | _ => S

/-- Adding a clause of the database, without repetitions, whose first watched literal is not
falsified by a processed literal. -/
theorem WatchStore.Inv.addClause {F : List (ℕ × Clause ℕ)} {M : Trail} {Q : List (Literal ℕ)}
    {S : WatchStore} (h : S.Inv F M Q) {id : ℕ} {C : Clause ℕ} {w₁ w₂ : Literal ℕ}
    {rest : Clause ℕ} (hnd : (w₁ :: w₂ :: rest).Nodup)
    (hmem : ∀ l, l ∈ w₁ :: w₂ :: rest ↔ l ∈ C) (hw₁ : ¬ Processed M Q w₁.negate) :
    (S.addClause id (w₁ :: w₂ :: rest)).Inv ((id, C) :: F) M Q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro i x hx
    simp only [WatchStore.addClause] at hx
    have hold : ∀ x ∈ watchList S.watches i,
        ∃ (hk : x.clause < (S.clauses.push (id, w₁ :: w₂ :: rest)).size),
          x.blocker ∈ (S.clauses.push (id, w₁ :: w₂ :: rest))[x.clause].2 :=
      fun x hx => by
        obtain ⟨hk, hb⟩ := h.blocker_mem i x hx
        exact ⟨by simp; omega, by rw [Array.getElem_push_lt hk]; exact hb⟩
    have hnew : ∀ b ∈ w₁ :: w₂ :: rest, ∃ (hk : S.clauses.size < (S.clauses.push
        (id, w₁ :: w₂ :: rest)).size),
        b ∈ (S.clauses.push (id, w₁ :: w₂ :: rest))[S.clauses.size].2 :=
      fun b hb => ⟨by simp, by simpa using hb⟩
    rcases mem_watchList_addWatch hx with rfl | hx
    · exact hnew _ (by simp)
    rcases mem_watchList_addWatch hx with rfl | hx
    · exact hnew _ (by simp)
    exact hold x hx
  · intro e' he' v₁ v₂ rest' hc' h₁ h₂
    rcases Array.mem_push.1 he' with he' | rfl
    · obtain ⟨b, hb, hs⟩ := h.covered e' he' v₁ v₂ rest' hc' h₁ h₂
      exact ⟨b, hb, hs⟩
    · simp only [List.cons.injEq] at hc'
      obtain ⟨rfl, -, -⟩ := hc'
      exact absurd h₁ hw₁

/-- The empty store. -/
theorem WatchStore.inv_empty (M : Trail) (Q : List (Literal ℕ)) :
    (⟨#[], #[]⟩ : WatchStore).Inv [] M Q :=
  ⟨by simp, by simp, by simp, fun e he => by simp at he, fun k hk => by simp at hk,
    fun i x hx => by simp [watchList] at hx, by simp⟩

/-- A clause with its literals that are not false under the assignment `A` first, so that they are
the ones watched. -/
@[expose] def watchOrder (A : Assign) (c : Clause ℕ) : Clause ℕ :=
  c.filter (fun l => !A.holds l.negate) ++ c.filter (fun l => A.holds l.negate)

theorem watchOrder_perm (A : Assign) (c : Clause ℕ) : (watchOrder A c).Perm c := by
  have := List.filter_append_perm (fun l => !A.holds l.negate) c
  simpa [watchOrder] using this

/-- If the first literal of `watchOrder A c` is false, every literal of `c` is. -/
theorem falsifies_of_watchOrder {A : Assign} {M : Trail} (hA : A.Agrees M) {c rest : Clause ℕ}
    {w : Literal ℕ} (h : watchOrder A c = w :: rest) (hw : w.negate ∈ Trail.lits M) :
    Trail.Falsifies M c := by
  intro l hl
  by_contra hne
  have hmem : l ∈ c.filter (fun l => !A.holds l.negate) :=
    List.mem_filter.2 ⟨hl, by
      rw [Bool.not_eq_true', ← Bool.not_eq_true, hA.holds_iff]; exact hne⟩
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  rw [watchOrder, hx, List.cons_append, List.cons.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have := (List.mem_filter.1 (hx ▸ List.mem_cons_self : x ∈ _)).2
  rw [Bool.not_eq_true', ← Bool.not_eq_true, hA.holds_iff] at this
  exact this hw

/-- **The watch store** of the numbered clauses `F` under the assignment `A`: every clause with at
least two different literals, without repetitions, watching its first two literals once those that
are not false under `A` are put first. It adds the clauses with
`Cslib.Algorithms.Lean.CDCL.WatchStore.addClause`, as learning does, which leaves the store
unchanged for fewer than two literals. -/
@[expose] def WatchStore.build (A : Assign) : List (ℕ × Clause ℕ) → WatchStore
  | [] => ⟨#[], #[]⟩
  | e :: F => (build A F).addClause e.1 (watchOrder A e.2.dedup)

/-- The watch store built from `F` under an assignment agreeing with the trail `M`, none of whose
clauses `M` falsifies, satisfies the invariant with every literal of `M` processed: a clause whose
**first** watched literal is false has every literal false. (Its second watched literal may be
false while the clause is still open, as in a binary clause with one false and one unassigned
literal.) -/
theorem WatchStore.build_inv {A : Assign} {M : Trail} (hA : A.Agrees M) :
    ∀ F : List (ℕ × Clause ℕ),
    (∀ e ∈ F, 2 ≤ e.2.dedup.length → ¬ Trail.Falsifies M e.2) → (WatchStore.build A F).Inv F M []
  | [], _ => WatchStore.inv_empty M []
  | e :: F, hF => by
    have ih := build_inv hA F fun e' he' => hF e' (List.mem_cons_of_mem _ he')
    have hperm := watchOrder_perm A e.2.dedup
    simp only [build]
    match hc : watchOrder A e.2.dedup with
    | w₁ :: w₂ :: rest =>
      rw [hc] at hperm
      have hlen : 2 ≤ e.2.dedup.length := by simp [← hperm.length_eq]
      refine ih.addClause (id := e.1) (C := e.2) (hperm.nodup_iff.2 (List.nodup_dedup e.2))
        (fun l => by rw [hperm.mem_iff, List.mem_dedup]) fun hp => ?_
      exact hF e List.mem_cons_self hlen fun l hl =>
        falsifies_of_watchOrder hA hc hp.1 l (List.mem_dedup.2 hl)
    | [] =>
      rw [hc] at hperm
      exact ih.consShort e (by simp [← hperm.length_eq])
    | [_] =>
      rw [hc] at hperm
      exact ih.consShort e (by simp [← hperm.length_eq])

end Cslib.Algorithms.Lean.CDCL
