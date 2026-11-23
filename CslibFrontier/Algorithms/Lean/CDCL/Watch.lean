/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.Assign

/-! # Two watched literals

The watch store of the CDCL solver: an array of numbered clauses without repetitions, each an
array of at least two literals, whose first two literals are its watches, and an array of watch
lists indexed by literal (`litKey`). A watch list is an array of *watchers* (`Watcher`): the
position of a clause and a *blocker*, a literal of the clause. As in MiniSat, a watcher whose
blocker is true is skipped without reading its clause. The invariants are stated on lists: the
literals of a clause (`Array.toList`) and the watch list read backwards (`watchList`), so that a
watcher pushed at the end of the array is the head of the list.

Moving a watch, as in MiniSat, writes into the clause's array in place: its first two literals
become the other watched literal and the new one, which takes the place of the literal no longer
watched (`WatchStore.moveTo`), so that propagation allocates no clause.

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
reading its clause by position (`findFree`), with its specification `WatchStore.visit_spec`; it
reads the values of literals from an assignment
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

/-- **The watch lists**: for each index (`litKey`), an array of watchers. -/
abbrev Watches : Type := Array (Array Watcher)

/-- The watch list at index `i`, as a list, empty past the end of the array. The list is the array
read backwards, so that adding a watcher at the end of the array (`Array.push`, in place) adds it
at the head of the list, and the solver visits the array from its end. The invariants are stated
on these lists. -/
@[expose] def watchList (W : Watches) (i : ℕ) : List Watcher := (W.getD i #[]).toList.reverse

/-- Applying `f` to the watch list at index `i`, growing the array if needed. The list is taken out
of the array first (`Array.modify`), so that `f` updates it in place. -/
@[expose, inline]
def modifyWatch (W : Watches) (i : ℕ) (f : Array Watcher → Array Watcher) : Watches :=
  let W' := if i < W.size then W else W ++ Array.replicate (i + 1 - W.size) #[]
  W'.modify i f

/-- Adding the watcher `k` to the watch list at index `i`, at the end of its array, growing the
array of lists if needed. -/
@[expose] def addWatch (W : Watches) (i : ℕ) (k : Watcher) : Watches :=
  modifyWatch W i (·.push k)

/-- Replacing the watch list at index `i`, growing the array if needed. -/
@[expose]
def setWatch (W : Watches) (i : ℕ) (L : Array Watcher) : Watches :=
  modifyWatch W i fun _ => L

theorem getD_grow (W : Watches) (i j : ℕ) :
    (if i < W.size then W else W ++ Array.replicate (i + 1 - W.size) #[]).getD j #[] =
      W.getD j #[] := by
  split
  · rfl
  · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
    split
    · rfl
    · rename_i h
      simp only [Array.getElem?_replicate]
      split <;> simp [Array.getElem?_eq_none (by omega : W.size ≤ j)]

theorem i_lt_size_grow (W : Watches) (i : ℕ) :
    i < (if i < W.size then W else W ++ Array.replicate (i + 1 - W.size) #[]).size := by
  split
  · assumption
  · simp; omega

theorem getD_modifyWatch (W : Watches) (i : ℕ) (f : Array Watcher → Array Watcher) (j : ℕ) :
    (modifyWatch W i f).getD j #[] = if j = i then f (W.getD i #[]) else W.getD j #[] := by
  unfold modifyWatch
  have hlt := i_lt_size_grow W i
  generalize hW' : (if i < W.size then W else W ++ Array.replicate (i + 1 - W.size) #[]) = W'
    at hlt
  have hgrow : ∀ j, W'.getD j #[] = W.getD j #[] := fun j => hW' ▸ getD_grow W i j
  rw [← hgrow, ← hgrow]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  split
  · subst j; simp [Array.getElem?_eq_getElem hlt]
  · rename_i hne
    simp [Ne.symm hne]

theorem size_modifyWatch (W : Watches) (i : ℕ) (f : Array Watcher → Array Watcher) :
    (modifyWatch W i f).size = max W.size (i + 1) := by
  unfold modifyWatch
  split <;> simp <;> omega

/-- Two arrays of watch lists of the same size with the same lists are equal. -/
theorem watches_ext {W W' : Watches} (hs : W.size = W'.size)
    (h : ∀ j, W.getD j #[] = W'.getD j #[]) : W = W' := by
  apply Array.ext hs
  intro j h₁ h₂
  have := h j
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h₁,
    Array.getElem?_eq_getElem h₂, Option.getD_some] at this
  exact this

/-- Modifying the same watch list twice is modifying it once. -/
theorem modifyWatch_modifyWatch (W : Watches) (i : ℕ) (f g : Array Watcher → Array Watcher) :
    modifyWatch (modifyWatch W i f) i g = modifyWatch W i (g ∘ f) := by
  apply watches_ext
  · simp only [size_modifyWatch]; omega
  · intro j
    simp only [getD_modifyWatch]
    split <;> rfl

/-- Modifying two different watch lists, in either order. -/
theorem modifyWatch_comm (W : Watches) {i j : ℕ} (hij : i ≠ j)
    (f g : Array Watcher → Array Watcher) :
    modifyWatch (modifyWatch W i f) j g = modifyWatch (modifyWatch W j g) i f := by
  apply watches_ext
  · simp only [size_modifyWatch]; omega
  · intro k
    simp only [getD_modifyWatch]
    by_cases hk : k = j
    · subst hk; simp [Ne.symm hij]
    · simp [hk, hij]

/-- Adding a watcher to a list just replaced is replacing it with the longer array. -/
theorem addWatch_setWatch (W : Watches) (i : ℕ) (L : Array Watcher) (k : Watcher) :
    addWatch (setWatch W i L) i k = setWatch W i (L.push k) :=
  modifyWatch_modifyWatch W i _ _

/-- Replacing a watch list and adding a watcher to another, in either order. -/
theorem addWatch_setWatch_comm (W : Watches) {i j : ℕ} (hij : i ≠ j) (L : Array Watcher)
    (k : Watcher) : addWatch (setWatch W i L) j k = setWatch (addWatch W j k) i L :=
  modifyWatch_comm W hij _ _

/-- Replacing a watch list twice. -/
theorem setWatch_setWatch (W : Watches) (i : ℕ) (L L' : Array Watcher) :
    setWatch (setWatch W i L) i L' = setWatch W i L' :=
  modifyWatch_modifyWatch W i _ _

@[simp] theorem watchList_addWatch (W : Watches) (i : ℕ) (k : Watcher) (j : ℕ) :
    watchList (addWatch W i k) j = if j = i then k :: watchList W i else watchList W j := by
  unfold watchList addWatch
  rw [getD_modifyWatch]
  split <;> simp

theorem mem_watchList_addWatch {W : Watches} {i j : ℕ} {k x : Watcher}
    (h : x ∈ watchList (addWatch W i k) j) : x = k ∨ x ∈ watchList W j := by
  rw [watchList_addWatch] at h
  split at h
  · rename_i hj
    subst hj
    exact List.mem_cons.1 h
  · exact .inr h

/-- A watcher of a list is still on it after one is added. -/
theorem mem_clauseIds_addWatch {W : Watches} {i j k : ℕ} {x : Watcher}
    (h : k ∈ clauseIds (watchList W j)) : k ∈ clauseIds (watchList (addWatch W i x) j) := by
  rw [watchList_addWatch]
  split
  · rename_i hj; subst hj; exact List.mem_cons_of_mem _ h
  · exact h

/-- The clause of the watcher added is on the list it is added to. -/
theorem mem_clauseIds_addWatch_self (W : Watches) (i : ℕ) (x : Watcher) :
    x.clause ∈ clauseIds (watchList (addWatch W i x) i) := by
  simp [clauseIds]

@[simp] theorem watchList_setWatch (W : Watches) (i : ℕ) (L : Array Watcher) (j : ℕ) :
    watchList (setWatch W i L) j = if j = i then L.toList.reverse else watchList W j := by
  unfold watchList setWatch
  rw [getD_modifyWatch]
  split <;> rfl

/-- **The watch store**: the clauses with at least two literals, each with its watched literals
first, and the watch lists, giving for each literal the clauses that may watch it. -/
structure WatchStore where
  /-- The numbered clauses, watched literals first, each an array of literals, so that moving a
  watch updates it in place. -/
  clauses : Array (ℕ × Array (Literal ℕ))
  /-- The watch lists, by `litKey`. -/
  watches : Watches

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
  sound : ∀ e ∈ S.clauses, ∃ c, (e.1, c) ∈ F ∧ ∀ l, l ∈ e.2.toList ↔ l ∈ c
  nodup : ∀ e ∈ S.clauses, e.2.toList.Nodup
  long : ∀ e ∈ S.clauses, 2 ≤ e.2.size
  covers : ∀ e ∈ F, 2 ≤ e.2.dedup.length →
    ∃ e' ∈ S.clauses, e'.1 = e.1 ∧ ∀ l, l ∈ e'.2.toList ↔ l ∈ e.2
  listed : ∀ (k : ℕ) (hk : k < S.clauses.size), ∀ w ∈ S.clauses[k].2.toList.take 2,
    k ∈ clauseIds (watchList S.watches (litKey w))
  blocker_mem : ∀ i, ∀ x ∈ watchList S.watches i, ∃ (hk : x.clause < S.clauses.size),
    x.blocker ∈ S.clauses[x.clause].2.toList
  covered : ∀ e ∈ S.clauses, ∀ w₁ w₂ rest, e.2.toList = w₁ :: w₂ :: rest →
    Processed M Q w₁.negate → Processed M Q w₂.negate → ∃ b ∈ e.2.toList, Supported M b w₁ w₂

/-- **With the queue empty, no clause of at least two literals is false.** -/
theorem WatchStore.Inv.not_falsifies {F : List (ℕ × Clause ℕ)} {M : Trail} {S : WatchStore}
    (h : S.Inv F M []) (hM : (Trail.vars M).Nodup) {e : ℕ × Clause ℕ} (he : e ∈ F)
    (hlen : 2 ≤ e.2.dedup.length) : ¬ Trail.Falsifies M e.2 := by
  intro hfalse
  obtain ⟨e', he', -, hperm⟩ := h.covers e he hlen
  have hlen' : 2 ≤ e'.2.toList.length := by simpa using h.long e' he'
  match hc : e'.2.toList, hlen' with
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
  /-- The literal `x` at position `j`, not false, replaces `u` as a watched literal, watching with
  the blocker `b`, the other watched literal (`Cslib.Algorithms.Lean.CDCL.WatchStore.moveTo`). -/
  | move (j : ℕ) (x b : Literal ℕ)
  /-- Every literal but the other watched literal `l` is false, and `l` is undefined: the clause
  numbered `id` is unit. -/
  | unit (l : Literal ℕ) (id : ℕ)
  /-- Every literal is false: the clause numbered `id` is in conflict. -/
  | conflict (id : ℕ)
  /-- The clause no longer watches `u`. -/
  | drop

/-- **The first position from `i` on, among `n`, of a literal of `c` that is not false** under
`A`, if any. -/
@[expose] def findFree (A : Assign) (c : Array (Literal ℕ)) : (n i : ℕ) → Option ℕ
  | 0, _ => none
  | n + 1, i => if h : i < c.size then (if A.isFalse c[i] then findFree A c n (i + 1) else some i)
    else none

theorem findFree_some {A : Assign} {c : Array (Literal ℕ)} :
    ∀ {n i j : ℕ}, findFree A c n i = some j → ∃ (h : j < c.size), i ≤ j ∧ A.isFalse c[j] = false
  | 0, _, _, h => by simp [findFree] at h
  | n + 1, i, j, h => by
    unfold findFree at h
    split at h
    · split at h
      · obtain ⟨hj, hij, hf⟩ := findFree_some h
        exact ⟨hj, by omega, hf⟩
      · rename_i hi hf
        cases h
        exact ⟨hi, le_rfl, by simpa using hf⟩
    · simp at h

theorem findFree_none {A : Assign} {c : Array (Literal ℕ)} :
    ∀ {n i : ℕ}, findFree A c n i = none → c.size ≤ i + n →
      ∀ j (h : j < c.size), i ≤ j → A.isFalse c[j] = true
  | 0, i, _, hn, j, hj, hij => by omega
  | n + 1, i, h, hn, j, hj, hij => by
    unfold findFree at h
    split at h
    · split at h
      · rename_i hi hf
        by_cases hji : j = i
        · subst hji; exact hf
        · exact findFree_none h (by omega) j hj (by omega)
      · simp at h
    · omega

/-- **Visiting a watcher** when its watched literal `u` has become false under the assignment `A`:
it is skipped if its blocker is true; otherwise its clause is read, by position. Inlined, so that
the outcome is matched on without being built. -/
@[expose, inline]
def WatchStore.visit (S : WatchStore) (A : Assign) (u : Literal ℕ) (w : Watcher) : Visit :=
  if A.holds w.blocker then .skip
  else if hk : w.clause < S.clauses.size then
    let c := S.clauses[w.clause].2
    if h2 : 2 ≤ c.size then
      let w₁ := c[0]
      let w₂ := c[1]
      if Assign.litEq w₁ u || Assign.litEq w₂ u then
        let other := if Assign.litEq w₁ u then w₂ else w₁
        if A.holds other then .keep other
        else
          match hj : findFree A c (c.size - 2) 2 with
          | some j => .move j (c[j]'(findFree_some hj).1) other
          | none =>
            if A.isFalse other then .conflict S.clauses[w.clause].1
            else .unit other S.clauses[w.clause].1
      else .drop
    else .drop
  else .drop

/-- **Moving a watch** of the clause at position `k`, from `u` to the literal `x` at position `j`,
with the other watched literal `o` as blocker: as MiniSat does, the clause becomes `o`, `x`, then
the others with `u` in place of `x`, written into its array in place, and the watch list of `x`
gets the watcher. The arrays are taken out of the store first, so that they are updated in place
when the store is not shared. -/
@[expose] def WatchStore.moveTo (S : WatchStore) (k j : ℕ) (o x u : Literal ℕ) : WatchStore :=
  let clauses := S.clauses
  let watches := S.watches
  ⟨clauses.modify k (fun e => (e.1, ((e.2.setIfInBounds 0 o).setIfInBounds 1 x).setIfInBounds j u)),
    addWatch watches (litKey x) ⟨k, o⟩⟩

/-- The other watched literal of a clause watching `u` with watched literals `w₁` and `w₂`. -/
@[expose] def otherWatch (u w₁ w₂ : Literal ℕ) : Literal ℕ := if w₁ = u then w₂ else w₁

/-- **What a visit of the watcher `w` finds**, by outcome, on the list of the clause's literals. -/
@[expose] def VisitSpec (S : WatchStore) (M : Trail) (u : Literal ℕ) (w : Watcher) : Visit → Prop
  | .skip => w.blocker ∈ Trail.lits M
  | .keep b => ∃ (hk : w.clause < S.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.clauses[w.clause].2.toList = w₁ :: w₂ :: rest ∧ (w₁ = u ∨ w₂ = u) ∧
      b = otherWatch u w₁ w₂ ∧ b ∈ Trail.lits M
  | .move j x b => ∃ (hk : w.clause < S.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ)
      (i : ℕ), S.clauses[w.clause].2.toList = w₁ :: w₂ :: rest ∧ (w₁ = u ∨ w₂ = u) ∧
      j = i + 2 ∧ rest[i]? = some x ∧ x.negate ∉ Trail.lits M ∧ b = otherWatch u w₁ w₂
  | .unit l id => ∃ (hk : w.clause < S.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.clauses[w.clause].1 = id ∧ S.clauses[w.clause].2.toList = w₁ :: w₂ :: rest ∧
      (w₁ = u ∨ w₂ = u) ∧ l = otherWatch u w₁ w₂ ∧ l ∉ Trail.lits M ∧
      l.negate ∉ Trail.lits M ∧ ∀ x ∈ rest, x.negate ∈ Trail.lits M
  | .conflict id => ∃ (hk : w.clause < S.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.clauses[w.clause].1 = id ∧ S.clauses[w.clause].2.toList = w₁ :: w₂ :: rest ∧
      (w₁ = u ∨ w₂ = u) ∧ (otherWatch u w₁ w₂).negate ∈ Trail.lits M ∧
      ∀ x ∈ rest, x.negate ∈ Trail.lits M
  | .drop => ∀ (hk : w.clause < S.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.clauses[w.clause].2.toList = w₁ :: w₂ :: rest → w₁ ≠ u ∧ w₂ ≠ u

/-- An array of at least two elements, as a list: its first two, then the others. -/
theorem toList_eq_cons_cons {α : Type} {c : Array α} (h : 2 ≤ c.size) :
    c.toList = c[0] :: c[1] :: c.toList.drop 2 := by
  obtain ⟨l⟩ := c
  match l, h with
  | a :: b :: rest, _ => rfl

/-- **The visit meets its specification**, under an assignment agreeing with the trail. -/
theorem WatchStore.visit_spec (S : WatchStore) {A : Assign} {M : Trail} (hA : A.Agrees M)
    (u : Literal ℕ) (w : Watcher) : VisitSpec S M u w (S.visit A u w) := by
  unfold visit
  by_cases hb : A.holds w.blocker = true
  · simp only [hb, ↓reduceIte, VisitSpec]
    exact (hA.holds_iff _).1 hb
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  by_cases hk : w.clause < S.clauses.size
  swap
  · simp only [hk, ↓reduceDIte, VisitSpec]
    exact fun hk' => hk'.elim
  simp only [hk, ↓reduceDIte]
  by_cases h2 : 2 ≤ S.clauses[w.clause].2.size
  swap
  · simp only [h2, ↓reduceDIte, VisitSpec]
    intro _ v₁ v₂ rest' hc'
    have := congrArg List.length hc'
    simp only [Array.length_toList, List.length_cons] at this
    omega
  simp only [h2, ↓reduceDIte]
  have hlist := toList_eq_cons_cons h2
  generalize hw₁ : S.clauses[w.clause].2[0] = w₁ at hlist ⊢
  generalize hw₂ : S.clauses[w.clause].2[1] = w₂ at hlist ⊢
  simp only [Assign.litEq_eq_decide, Bool.or_eq_true, decide_eq_true_eq]
  by_cases hu : w₁ = u ∨ w₂ = u
  swap
  · simp only [hu, ↓reduceIte, VisitSpec]
    intro _ v₁ v₂ rest' hc
    rw [hlist] at hc
    simp only [List.cons.injEq] at hc
    obtain ⟨rfl, rfl, -⟩ := hc
    push Not at hu
    exact hu
  simp only [hu, ↓reduceIte]
  have hother : (if w₁ = u then w₂ else w₁) = otherWatch u w₁ w₂ := rfl
  rw [hother]
  by_cases htrue : A.holds (otherWatch u w₁ w₂) = true
  · simp only [htrue, ↓reduceIte, VisitSpec]
    exact ⟨hk, w₁, w₂, _, hlist, hu, rfl, (hA.holds_iff _).1 htrue⟩
  simp only [htrue, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i j hj
    obtain ⟨hjs, h2j, hfree⟩ := findFree_some hj
    simp only [VisitSpec]
    refine ⟨hk, w₁, w₂, _, j - 2, hlist, hu, by omega, ?_, fun h => ?_, rfl⟩
    · rw [List.getElem?_drop, show 2 + (j - 2) = j by omega, Array.getElem?_toList,
        Array.getElem?_eq_getElem hjs]
    · rw [(hA.isFalse_iff _).2 h] at hfree
      exact absurd hfree (by decide)
  · rename_i hj
    have hall : ∀ x ∈ S.clauses[w.clause].2.toList.drop 2, x.negate ∈ Trail.lits M := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
      simp only [List.getElem_drop, Array.getElem_toList]
      rw [← hA.isFalse_iff]
      exact findFree_none hj (by omega) _ _ (by omega)
    by_cases hfalse : A.isFalse (otherWatch u w₁ w₂) = true
    · simp only [hfalse, ↓reduceIte, VisitSpec]
      exact ⟨hk, w₁, w₂, _, trivial, hlist, hu, (hA.isFalse_iff _).1 hfalse, hall⟩
    · simp only [hfalse, Bool.false_eq_true, ↓reduceIte, VisitSpec]
      refine ⟨hk, w₁, w₂, _, trivial, hlist, hu, rfl, fun h => htrue ((hA.holds_iff _).2 h),
        fun h => hfalse ((hA.isFalse_iff _).2 h), hall⟩

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
    -- the position is read and the arrays taken out of the store first, so that the push and the
    -- watch lists update them in place when the store is not shared
    let k := S.clauses.size
    let clauses := S.clauses
    let watches := S.watches
    ⟨clauses.push (id, c.toArray), addWatch (addWatch watches (litKey w₁) ⟨k, w₂⟩) (litKey w₂)
      ⟨k, w₁⟩⟩
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
    · exact ⟨C, List.mem_cons_self, by simpa using hmem⟩
  · intro e' he'
    rcases Array.mem_push.1 he' with he' | rfl
    · exact h.nodup e' he'
    · simpa using hnd
  · intro e' he'
    rcases Array.mem_push.1 he' with he' | rfl
    · exact h.long e' he'
    · simp
  · intro e' he' hlen
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨_, Array.mem_push_self, rfl, by simpa using hmem⟩
    · obtain ⟨e'', he'', h1, h2⟩ := h.covers e' he' hlen
      exact ⟨e'', Array.mem_push_of_mem _ he'', h1, h2⟩
  · intro k hk w hw
    simp only [WatchStore.addClause, Array.size_push] at hk
    simp only [WatchStore.addClause, watchList_addWatch]
    by_cases hks : k = S.clauses.size
    · subst hks
      simp only [WatchStore.addClause, Array.getElem_push_eq, List.toList_toArray,
        List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
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
        ∃ (hk : x.clause < (S.clauses.push (id, (w₁ :: w₂ :: rest).toArray)).size),
          x.blocker ∈ (S.clauses.push (id, (w₁ :: w₂ :: rest).toArray))[x.clause].2.toList :=
      fun x hx => by
        obtain ⟨hk, hb⟩ := h.blocker_mem i x hx
        exact ⟨by simp; omega, by rw [Array.getElem_push_lt hk]; exact hb⟩
    have hnew : ∀ b ∈ w₁ :: w₂ :: rest, ∃ (hk : S.clauses.size < (S.clauses.push
        (id, (w₁ :: w₂ :: rest).toArray)).size),
        b ∈ (S.clauses.push (id, (w₁ :: w₂ :: rest).toArray))[S.clauses.size].2.toList :=
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
  | e :: F => (build A F).addClause e.1 (watchOrder A (dedupLits e.2))

/-- The literals of a clause without repetitions, removed in linear time (`dedupLits`), are those
of `List.dedup`, up to order. -/
theorem dedupLits_perm (c : Clause ℕ) : (dedupLits c).Perm c.dedup :=
  (List.perm_ext_iff_of_nodup (nodup_dedupKey litKey_injective c) (List.nodup_dedup c)).2
    fun l => by rw [mem_dedupKey litKey_injective, List.mem_dedup]

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
    have hperm := (watchOrder_perm A (dedupLits e.2)).trans (dedupLits_perm e.2)
    simp only [build]
    match hc : watchOrder A (dedupLits e.2) with
    | w₁ :: w₂ :: rest =>
      rw [hc] at hperm
      have hlen : 2 ≤ e.2.dedup.length := by simp [← hperm.length_eq]
      refine ih.addClause (id := e.1) (C := e.2) (hperm.nodup_iff.2 (List.nodup_dedup e.2))
        (fun l => by rw [hperm.mem_iff, List.mem_dedup]) fun hp => ?_
      exact hF e List.mem_cons_self hlen fun l hl =>
        falsifies_of_watchOrder hA hc hp.1 l ((mem_dedupKey litKey_injective).2 hl)
    | [] =>
      rw [hc] at hperm
      exact ih.consShort e (by simp [← hperm.length_eq])
    | [_] =>
      rw [hc] at hperm
      exact ih.consShort e (by simp [← hperm.length_eq])

end Cslib.Algorithms.Lean.CDCL
