/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.Assign

/-! # Two watched literals

The watch store of the CDCL solver: an array of numbered clauses without repetitions, each of at
least two literals, whose first two literals are its watches, and an array of watch lists indexed
by literal (its key `litCode`). A watch list holds *watchers* (`Watcher`): the position of a
clause and a *blocker*, a literal of the clause. As in MiniSat, a watcher whose blocker is true is
skipped without reading its clause.

The store holds numbers only, so that the solver follows no pointer to read a literal, and moving a
watch or keeping a watcher makes no object for the watcher or the literal. This holds for numbers
in the scalar range of Lean's runtime: a larger number is boxed. The arrays are written in place
when they are not shared and have room; otherwise `Array.push` grows or copies them, and adding a
watch may also grow the array of watch lists (`addWatch`). A literal is its key `2 * v + b`
(the word code `Cslib.Algorithms.WordRAM.ClauseCode.litCode`), decoded by `litOfKey`, a
bijection between literals and numbers. A clause is an array of numbers: the keys of its literals,
then its number (`WatchStore.codes`). A watch list is an array of numbers, two per watcher: the
position of the clause and the key of the blocker.

The invariants are stated on the store read back (the representation): its clauses, numbered
arrays of literals (`WatchStore.clauses`, by `decodeClause`), and the watchers of a watch list,
read backwards (`watchList`, by `unpackWatchers`), so that a watcher pushed at the end of the array
is the head of the list. The operations of the solver have representation lemmas
(`WatchStore.clauses_moveTo`, `WatchStore.clauses_addClause`, `watchList_addWatch`,
`watchList_setWatch`), and `WatchStore.visit`, which reads the numbers, is specified on the
literals read back (`WatchStore.visit_spec`, through `KeyVisit.lits`).

Moving a watch, as in MiniSat, writes into the clause's array in place: its first two literals
become the other watched literal and the new one, which takes the place of the literal no longer
watched (`WatchStore.moveTo`).

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
reads the values of literals, on their keys, from an assignment indexed by variable (`Assign`)
agreeing with the trail. `WatchStore.build` builds a store on a
trail, watching literals that are not false, so that it satisfies the invariant with every literal
of the trail processed as long as no clause is false (`WatchStore.build_inv`).
-/

public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL
open Cslib.Algorithms.WordRAM.ClauseCode (litCode litCode_injective)

/-- **A watcher**: a clause of the store, by position, and its *blocker*, a literal of the clause.
When the blocker is true, the clause is satisfied and is skipped without being read. The store
holds a watcher as two numbers of its watch list (`Watches`), and the invariants read them back as
watchers (`unpackWatchers`). -/
structure Watcher where
  /-- The position of the clause in the store. -/
  clause : ℕ
  /-- A literal of the clause. -/
  blocker : Literal ℕ

/-- The positions of the clauses of a list of watchers. -/
abbrev clauseIds (L : List Watcher) : List ℕ := L.map Watcher.clause

/-- **The watch lists**: for each index (`litCode`), an array of numbers, two for each watcher: the
position of its clause, then the key of its blocker (`litCode`). Numbers in the scalar range are
unboxed at run time, so a watch list of them holds no pointers, and keeping or adding a watcher
makes no object of its own. Pushing writes in place only when the array is not shared and has
room, and otherwise grows or copies it. -/
abbrev Watches : Type := Array (Array ℕ)

/-- **The watchers of a watch list read backwards**: two numbers each, the key of the blocker and
then the position of the clause (`litOfKey`). A number left over at the end is not read. -/
@[expose] def unpackWatchers : List ℕ → List Watcher
  | b :: k :: rest => ⟨k, litOfKey b⟩ :: unpackWatchers rest
  | _ => []

@[simp] theorem unpackWatchers_cons_cons (b k : ℕ) (rest : List ℕ) :
    unpackWatchers (b :: k :: rest) = ⟨k, litOfKey b⟩ :: unpackWatchers rest := rfl

/-- The watchers of an array of numbers read backwards: pushing a watcher, its clause then its
blocker, adds it in front. -/
theorem unpackWatchers_push (a : Array ℕ) (k b : ℕ) :
    unpackWatchers ((a.push k).push b).toList.reverse = ⟨k, litOfKey b⟩ ::
      unpackWatchers a.toList.reverse := by
  simp

/-- A number alone is not a watcher. -/
theorem unpackWatchers_of_length_le_one {A : List ℕ} (h : A.length ≤ 1) :
    unpackWatchers A = [] := by
  match A, h with
  | [], _ => rfl
  | [_], _ => rfl

/-- The watchers of two lists of numbers, the first of even length. -/
theorem unpackWatchers_append : ∀ {A : List ℕ} (B : List ℕ), A.length % 2 = 0 →
    unpackWatchers (A ++ B) = unpackWatchers A ++ unpackWatchers B
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | b :: k :: A, B, h => by
    simp only [List.cons_append, unpackWatchers_cons_cons, List.cons.injEq, true_and]
    exact unpackWatchers_append B (by simp at h; omega)

/-- The watch list at index `i`, as a list of watchers, empty past the end of the array. The list
is the array read backwards, so that adding a watcher at the end of the array (`Array.push`, in
place) adds it at the head of the list, and the solver visits the array from its end. The
invariants are stated on these lists. -/
@[expose] def watchList (W : Watches) (i : ℕ) : List Watcher :=
  unpackWatchers (W.getD i #[]).toList.reverse

/-- Applying `f` to the watch list at index `i`, growing the array if needed. The list is taken out
of the array first (`Array.modify`), so that `f` updates it in place. -/
@[expose, inline]
def modifyWatch (W : Watches) (i : ℕ) (f : Array ℕ → Array ℕ) : Watches :=
  let W' := if i < W.size then W else W ++ Array.replicate (i + 1 - W.size) #[]
  W'.modify i f

/-- Adding the watcher of the clause at position `k` with the blocker of key `b` to the watch list
at index `i`, at the end of its array, growing the array of lists if needed. -/
@[expose] def addWatch (W : Watches) (i k b : ℕ) : Watches :=
  modifyWatch W i fun a => (a.push k).push b

/-- Replacing the watch list at index `i`, growing the array if needed. -/
@[expose]
def setWatch (W : Watches) (i : ℕ) (L : Array ℕ) : Watches :=
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

theorem getD_modifyWatch (W : Watches) (i : ℕ) (f : Array ℕ → Array ℕ) (j : ℕ) :
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

theorem size_modifyWatch (W : Watches) (i : ℕ) (f : Array ℕ → Array ℕ) :
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
theorem modifyWatch_modifyWatch (W : Watches) (i : ℕ) (f g : Array ℕ → Array ℕ) :
    modifyWatch (modifyWatch W i f) i g = modifyWatch W i (g ∘ f) := by
  apply watches_ext
  · simp only [size_modifyWatch]; omega
  · intro j
    simp only [getD_modifyWatch]
    split <;> rfl

/-- Modifying two different watch lists, in either order. -/
theorem modifyWatch_comm (W : Watches) {i j : ℕ} (hij : i ≠ j)
    (f g : Array ℕ → Array ℕ) :
    modifyWatch (modifyWatch W i f) j g = modifyWatch (modifyWatch W j g) i f := by
  apply watches_ext
  · simp only [size_modifyWatch]; omega
  · intro k
    simp only [getD_modifyWatch]
    by_cases hk : k = j
    · subst hk; simp [Ne.symm hij]
    · simp [hk, hij]

/-- Adding a watcher to a list just replaced is replacing it with the longer array. -/
theorem addWatch_setWatch (W : Watches) (i : ℕ) (L : Array ℕ) (k b : ℕ) :
    addWatch (setWatch W i L) i k b = setWatch W i ((L.push k).push b) :=
  modifyWatch_modifyWatch W i _ _

/-- Replacing a watch list and adding a watcher to another, in either order. -/
theorem addWatch_setWatch_comm (W : Watches) {i j : ℕ} (hij : i ≠ j) (L : Array ℕ)
    (k b : ℕ) : addWatch (setWatch W i L) j k b = setWatch (addWatch W j k b) i L :=
  modifyWatch_comm W hij _ _

/-- Replacing a watch list twice. -/
theorem setWatch_setWatch (W : Watches) (i : ℕ) (L L' : Array ℕ) :
    setWatch (setWatch W i L) i L' = setWatch W i L' :=
  modifyWatch_modifyWatch W i _ _

@[simp] theorem watchList_addWatch (W : Watches) (i k b : ℕ) (j : ℕ) :
    watchList (addWatch W i k b) j =
      if j = i then ⟨k, litOfKey b⟩ :: watchList W i else watchList W j := by
  unfold watchList addWatch
  rw [getD_modifyWatch]
  split <;> simp

theorem mem_watchList_addWatch {W : Watches} {i j k b : ℕ} {x : Watcher}
    (h : x ∈ watchList (addWatch W i k b) j) : x = ⟨k, litOfKey b⟩ ∨ x ∈ watchList W j := by
  rw [watchList_addWatch] at h
  split at h
  · rename_i hj
    subst hj
    exact List.mem_cons.1 h
  · exact .inr h

/-- A watcher of a list is still on it after one is added. -/
theorem mem_clauseIds_addWatch {W : Watches} {i j k k' b : ℕ}
    (h : k ∈ clauseIds (watchList W j)) : k ∈ clauseIds (watchList (addWatch W i k' b) j) := by
  rw [watchList_addWatch]
  split
  · rename_i hj; subst hj; exact List.mem_cons_of_mem _ h
  · exact h

/-- The clause of the watcher added is on the list it is added to. -/
theorem mem_clauseIds_addWatch_self (W : Watches) (i k b : ℕ) :
    k ∈ clauseIds (watchList (addWatch W i k b) i) := by
  simp [clauseIds]

@[simp] theorem watchList_setWatch (W : Watches) (i : ℕ) (L : Array ℕ) (j : ℕ) :
    watchList (setWatch W i L) j =
      if j = i then unpackWatchers L.toList.reverse else watchList W j := by
  unfold watchList setWatch
  rw [getD_modifyWatch]
  split <;> rfl

/-- **The watch store**: the clauses with at least two literals, each with its watched literals
first, and the watch lists, giving for each literal the clauses that may watch it. -/
structure WatchStore where
  /-- The numbered clauses, each an array of numbers: the keys of its literals (`litCode`), watched
  literals first, then its number. Moving a watch updates the array in place, and reading a literal
  follows no pointer. -/
  codes : Array (Array ℕ)
  /-- The watch lists, by `litCode`. -/
  watches : Watches

/-- The number of a clause of the store: the last number of its array. -/
@[expose] def clauseId (a : Array ℕ) : ℕ := a.getD (a.size - 1) 0

/-- A clause of the store read back: its number, and its literals decoded from their keys, all the
numbers of its array but the last. -/
@[expose] def decodeClause (a : Array ℕ) : ℕ × Array (Literal ℕ) := (clauseId a, a.pop.map litOfKey)

/-- **The clauses of the store**, read back as numbered arrays of literals (`decodeClause`). The
invariants are stated on them; the solver reads `WatchStore.codes`. -/
@[expose] def WatchStore.clauses (S : WatchStore) : Array (ℕ × Array (Literal ℕ)) :=
  S.codes.map decodeClause

theorem WatchStore.size_clauses (S : WatchStore) : S.clauses.size = S.codes.size :=
  Array.size_map ..

theorem WatchStore.getElem_clauses (S : WatchStore) {k : ℕ} (hk : k < S.codes.size) :
    S.clauses[k]'(by rw [S.size_clauses]; exact hk) = decodeClause S.codes[k] :=
  Array.getElem_map ..

/-- Encoding the literals of a clause, then its number, and decoding them gives them back. -/
theorem decodeClause_encode (id : ℕ) (c : Clause ℕ) :
    decodeClause ((c.map litCode).toArray.push id) = (id, c.toArray) := by
  simp [decodeClause, clauseId, Function.comp_def]

/-- Writing into an array and dropping its last element, in either order. -/
theorem pop_setIfInBounds (a : Array ℕ) (i v : ℕ) :
    (a.setIfInBounds i v).pop = a.pop.setIfInBounds i v := by
  apply Array.ext (by simp)
  intro j h₁ h₂
  rw [Array.getElem_pop, Array.getElem_setIfInBounds, Array.getElem_setIfInBounds,
    Array.getElem_pop]
  simpa using h₂

@[simp] theorem clauseId_push (a : Array ℕ) (id : ℕ) : clauseId (a.push id) = id := by
  simp [clauseId]

/-- Writing before the last element keeps the number of a clause. -/
theorem clauseId_setIfInBounds (a : Array ℕ) {i : ℕ} (v : ℕ) (h : i + 1 < a.size) :
    clauseId (a.setIfInBounds i v) = clauseId a := by
  simp only [clauseId, Array.size_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  split <;> simp_all
  omega

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
    k ∈ clauseIds (watchList S.watches (litCode w))
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

/-- **What a visit finds, on the keys**: `Visit` with the literals as their keys (`litCode`), so
that the solver decodes none of them but the one it propagates. -/
inductive KeyVisit
  /-- The blocker is true. -/
  | skip
  /-- The other watched literal, of key `b`, is true. -/
  | keep (b : ℕ)
  /-- The literal of key `x` at position `j` replaces the watch, with blocker of key `b`. -/
  | move (j x b : ℕ)
  /-- The clause numbered `id` is unit, on the other watched literal, of key `l`. -/
  | unit (l : ℕ) (id : ℕ)
  /-- The clause numbered `id` is in conflict. -/
  | conflict (id : ℕ)
  /-- The clause no longer watches the literal. -/
  | drop

/-- The outcome with its literals decoded from their keys (`litOfKey`). -/
@[expose] def KeyVisit.lits : KeyVisit → Visit
  | .skip => .skip
  | .keep b => .keep (litOfKey b)
  | .move j x b => .move j (litOfKey x) (litOfKey b)
  | .unit l id => .unit (litOfKey l) id
  | .conflict id => .conflict id
  | .drop => .drop

/-- **The first position from `i` on, among `n`, of a literal of `c` that is not false** under
`A`, read on the keys, or the size of `c` if there is none. -/
@[expose] def findFree (A : Assign) (c : Array ℕ) : (n i : ℕ) → ℕ
  | 0, _ => c.size
  | n + 1, i => if h : i < c.size then (if A.isFalseKey c[i] then findFree A c n (i + 1) else i)
    else c.size

theorem findFree_lt {A : Assign} {c : Array ℕ} :
    ∀ {n i : ℕ} (h : findFree A c n i < c.size), i ≤ findFree A c n i ∧
      findFree A c n i < i + n ∧ A.isFalseKey (c[findFree A c n i]'h) = false
  | 0, _, h => by simp [findFree] at h
  | n + 1, i, h => by
    unfold findFree at h ⊢
    split
    · split
      · rename_i hi hf
        simp only [hi, ↓reduceDIte, hf, ↓reduceIte] at h
        obtain ⟨hij, hlt, hfree⟩ := findFree_lt h
        exact ⟨by omega, by omega, hfree⟩
      · rename_i hi hf
        exact ⟨le_rfl, by omega, by simpa using hf⟩
    · rename_i hi
      simp [hi] at h

theorem findFree_none {A : Assign} {c : Array ℕ} :
    ∀ {n i : ℕ}, ¬ findFree A c n i < c.size →
      ∀ j (h : j < c.size), i ≤ j → j < i + n → A.isFalseKey c[j] = true
  | 0, i, _, j, hj, hij, hjn => by omega
  | n + 1, i, h, j, hj, hij, hjn => by
    unfold findFree at h
    split at h
    · split at h
      · rename_i hi hf
        by_cases hji : j = i
        · subst hji; exact hf
        · exact findFree_none h j hj (by omega) (by omega)
      · rename_i hi _
        exact absurd hi h
    · omega

/-- **Visiting a watcher**, of the clause at position `k` with the blocker of key `b`, when the
watched literal of key `u` has become false under the assignment `A`: it is skipped if its blocker
is true; otherwise its clause is read, by position. Everything is read on the keys
(`Assign.holdsKey`, `Assign.isFalseKey`), and the literals are compared as numbers. Inlined, so
that the outcome is matched on without being built. -/
@[expose, inline]
def WatchStore.visit (S : WatchStore) (A : Assign) (u k b : ℕ) : KeyVisit :=
  if A.holdsKey b then .skip
  else if hk : k < S.codes.size then
    let c := S.codes[k]
    if h2 : 3 ≤ c.size then
      let w₁ := c[0]
      let w₂ := c[1]
      if w₁ == u || w₂ == u then
        let other := if w₁ == u then w₂ else w₁
        if A.holdsKey other then .keep other
        else
          -- the literals but the watched ones, before the clause's number
          let j := findFree A c (c.size - 3) 2
          if hj : j < c.size then .move j c[j] other
          else if A.isFalseKey other then .conflict (clauseId c)
          else .unit other (clauseId c)
      else .drop
    else .drop
  else .drop

/-- **Moving a watch** of the clause at position `k`, from the literal of key `u` to the one of
key `x` at position `j`, with the other watched literal, of key `o`, as blocker: as MiniSat does,
the clause becomes `o`, `x`, then the others with `u` in place of `x`, written into its array in
place, and the watch list of `x` gets the watcher. The arrays are taken out of the store first, so
that they are updated in place when the store is not shared.

The position `j` must be one of the clause's literals but the watched ones: `1 < j` and
`j + 1 < a.size` for the array `a` of the clause at `k`, as `WatchStore.visit` finds it and
`WatchStore.clauses_moveTo` assumes. The last number of `a` is the clause's number, which
`j = a.size - 1` would overwrite; nothing here checks the bound. -/
@[expose] def WatchStore.moveTo (S : WatchStore) (k j o x u : ℕ) : WatchStore :=
  let codes := S.codes
  let watches := S.watches
  ⟨codes.modify k (fun a => ((a.setIfInBounds 0 o).setIfInBounds 1 x).setIfInBounds j u),
    addWatch watches x k o⟩

/-- **The clauses after moving a watch**, read back: the literals of the keys written, at positions
before the clause's number. -/
theorem WatchStore.clauses_moveTo (S : WatchStore) (k j o x u : ℕ)
    (hj : ∀ hk : k < S.codes.size, 1 < j ∧ j + 1 < S.codes[k].size) :
    (S.moveTo k j o x u).clauses = S.clauses.modify k (fun e => (e.1,
      ((e.2.setIfInBounds 0 (litOfKey o)).setIfInBounds 1 (litOfKey x)).setIfInBounds j
        (litOfKey u))) := by
  simp only [moveTo, clauses]
  apply Array.ext (by simp)
  intro i h₁ h₂
  simp only [Array.getElem_map, Array.getElem_modify]
  split
  · rename_i hik; subst hik
    have := hj (by simpa using h₁)
    simp only [decodeClause, pop_setIfInBounds, Array.map_setIfInBounds, Prod.mk.injEq, and_true]
    rw [clauseId_setIfInBounds _ _ (by simp; omega), clauseId_setIfInBounds _ _ (by simp; omega),
      clauseId_setIfInBounds _ _ (by omega)]
  · rfl

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

/-- Comparing a key with the key of a literal is comparing the literals. -/
theorem beq_litCode (n : ℕ) (u : Literal ℕ) : (n == litCode u) = decide (litOfKey n = u) := by
  by_cases h : litOfKey n = u
  · subst h; simp
  · have : n ≠ litCode u := fun h' => h (by rw [h', litOfKey_litCode])
    simp [h, this]

/-- **The visit meets its specification**, under an assignment agreeing with the trail, for the
watcher read back from the two numbers and the outcome read back from the keys. -/
theorem WatchStore.visit_spec (S : WatchStore) {A : Assign} {M : Trail} (hA : A.Agrees M)
    (u : Literal ℕ) (k b : ℕ) :
    VisitSpec S M u ⟨k, litOfKey b⟩ (S.visit A (litCode u) k b).lits := by
  unfold visit
  rw [Assign.holdsKey_eq]
  by_cases hb : A.holds (litOfKey b) = true
  · simp only [hb, ↓reduceIte, KeyVisit.lits, VisitSpec]
    exact (hA.holds_iff _).1 hb
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  by_cases hk : k < S.codes.size
  swap
  · simp only [hk, ↓reduceDIte, KeyVisit.lits, VisitSpec]
    exact fun hk' => absurd (S.size_clauses ▸ hk') hk
  simp only [hk, ↓reduceDIte]
  have hk' : k < S.clauses.size := by rw [S.size_clauses]; exact hk
  have hck : S.clauses[k] = decodeClause S.codes[k] := S.getElem_clauses hk
  have hcl : S.clauses[k].2.toList = S.codes[k].pop.toList.map litOfKey := by
    rw [hck]; simp [decodeClause]
  have hid : S.clauses[k].1 = clauseId S.codes[k] := by rw [hck]; rfl
  by_cases h2 : 3 ≤ S.codes[k].size
  swap
  · simp only [h2, ↓reduceDIte, KeyVisit.lits, VisitSpec]
    intro _ v₁ v₂ rest' hc'
    have := congrArg List.length (hcl.symm.trans hc')
    simp only [List.length_map, Array.length_toList, Array.size_pop, List.length_cons] at this
    omega
  simp only [h2, ↓reduceDIte]
  have h2' : 2 ≤ S.codes[k].pop.size := by simp; omega
  have hlist : S.clauses[k].2.toList = litOfKey S.codes[k][0] :: litOfKey S.codes[k][1] ::
      (S.codes[k].pop.toList.drop 2).map litOfKey := by
    rw [hcl, toList_eq_cons_cons h2']; simp
  simp only [beq_litCode, Bool.or_eq_true, decide_eq_true_eq]
  generalize hw₁ : litOfKey S.codes[k][0] = w₁ at hlist ⊢
  generalize hw₂ : litOfKey S.codes[k][1] = w₂ at hlist ⊢
  by_cases hu : w₁ = u ∨ w₂ = u
  swap
  · simp only [hu, ↓reduceIte, KeyVisit.lits, VisitSpec]
    intro _ v₁ v₂ rest' hc
    rw [hlist] at hc
    simp only [List.cons.injEq] at hc
    obtain ⟨rfl, rfl, -⟩ := hc
    push Not at hu
    exact hu
  simp only [hu, ↓reduceIte]
  have hother : litOfKey (if w₁ = u then S.codes[k][1] else S.codes[k][0]) =
      otherWatch u w₁ w₂ := by
    unfold otherWatch; split <;> simp [hw₁, hw₂]
  generalize (if w₁ = u then S.codes[k][1] else S.codes[k][0]) = oc at hother
  rw [Assign.holdsKey_eq, hother]
  by_cases htrue : A.holds (otherWatch u w₁ w₂) = true
  · simp only [htrue, ↓reduceIte, KeyVisit.lits, VisitSpec, hother]
    exact ⟨hk', w₁, w₂, _, hlist, hu, rfl, (hA.holds_iff _).1 htrue⟩
  simp only [htrue, Bool.false_eq_true, ↓reduceIte]
  generalize hjdef : findFree A S.codes[k] (S.codes[k].size - 3) 2 = j
  split
  · rename_i hj
    obtain ⟨h2j, hjn, hfree⟩ := findFree_lt (hjdef ▸ hj)
    simp only [hjdef] at h2j hjn hfree
    simp only [KeyVisit.lits, VisitSpec, hother]
    refine ⟨hk', w₁, w₂, _, j - 2, hlist, hu, by omega, ?_, fun h => ?_, rfl⟩
    · rw [List.getElem?_map, List.getElem?_drop, show 2 + (j - 2) = j by omega,
        Array.getElem?_toList, Array.getElem?_pop]
      simp only [show j < S.codes[k].size - 1 by omega, ↓reduceIte,
        Array.getElem?_eq_getElem hj]
      rfl
    · rw [Assign.isFalseKey_eq, (hA.isFalse_iff _).2 h] at hfree
      exact absurd hfree (by decide)
  · rename_i hj
    have hall : ∀ x ∈ (S.codes[k].pop.toList.drop 2).map litOfKey, x.negate ∈ Trail.lits M := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hy
      simp only [List.getElem_drop, Array.getElem_toList, Array.getElem_pop]
      rw [← hA.isFalse_iff, ← Assign.isFalseKey_eq]
      simp only [List.length_drop, Array.length_toList, Array.size_pop] at hm
      exact findFree_none (hjdef ▸ hj) _ _ (by omega) (by omega)
    rw [Assign.isFalseKey_eq, hother]
    by_cases hfalse : A.isFalse (otherWatch u w₁ w₂) = true
    · simp only [hfalse, ↓reduceIte, KeyVisit.lits, VisitSpec]
      exact ⟨hk', w₁, w₂, _, hid, hlist, hu, (hA.isFalse_iff _).1 hfalse, hall⟩
    · simp only [hfalse, Bool.false_eq_true, ↓reduceIte, KeyVisit.lits, VisitSpec, hother]
      refine ⟨hk', w₁, w₂, _, hid, hlist, hu, rfl,
        fun h => htrue ((hA.holds_iff _).2 h), fun h => hfalse ((hA.isFalse_iff _).2 h), hall⟩

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
    let k := S.codes.size
    let codes := S.codes
    let watches := S.watches
    -- `List.map`, not `Array.map`, so that the kernel and `decide` evaluate it
    ⟨codes.push ((c.map litCode).toArray.push id),
      addWatch (addWatch watches (litCode w₁) k (litCode w₂)) (litCode w₂) k (litCode w₁)⟩
  | _ => S

/-- **The clauses after adding one**, read back: the clause added, with its literals. -/
theorem WatchStore.clauses_addClause (S : WatchStore) (id : ℕ) (c : Clause ℕ) :
    (S.addClause id c).clauses = match c with
      | _ :: _ :: _ => S.clauses.push (id, c.toArray)
      | _ => S.clauses := by
  unfold addClause
  split
  · simp only [clauses, Array.map_push, decodeClause_encode]
  · rfl

/-- Adding a clause of the database, without repetitions, whose first watched literal is not
falsified by a processed literal. -/
theorem WatchStore.Inv.addClause {F : List (ℕ × Clause ℕ)} {M : Trail} {Q : List (Literal ℕ)}
    {S : WatchStore} (h : S.Inv F M Q) {id : ℕ} {C : Clause ℕ} {w₁ w₂ : Literal ℕ}
    {rest : Clause ℕ} (hnd : (w₁ :: w₂ :: rest).Nodup)
    (hmem : ∀ l, l ∈ w₁ :: w₂ :: rest ↔ l ∈ C) (hw₁ : ¬ Processed M Q w₁.negate) :
    (S.addClause id (w₁ :: w₂ :: rest)).Inv ((id, C) :: F) M Q := by
  suffices H : ∀ T : WatchStore, T.clauses = S.clauses.push (id, (w₁ :: w₂ :: rest).toArray) →
      T.watches = addWatch (addWatch S.watches (litCode w₁) S.clauses.size (litCode w₂))
        (litCode w₂) S.clauses.size (litCode w₁) → T.Inv ((id, C) :: F) M Q from
    H _ (S.clauses_addClause id _) (by simp [WatchStore.addClause, WatchStore.size_clauses])
  intro T hcl hW
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hcl] <;> (try rw [hW])
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
    simp only [Array.size_push] at hk
    simp only [watchList_addWatch]
    by_cases hks : k = S.clauses.size
    · subst hks
      simp only [Array.getElem_push_eq, List.toList_toArray,
        List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
      clear hcl hW
      rcases hw with rfl | rfl <;> split_ifs <;> simp_all
    · have hk' : k < S.clauses.size := by omega
      rw [Array.getElem_push_lt hk'] at hw
      have := h.listed k hk' w hw
      split
      · exact List.mem_cons_of_mem _ (by split <;> simp_all)
      · split
        · exact List.mem_cons_of_mem _ (by simp_all)
        · exact this
  · intro i x hx
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
  ⟨by simp [WatchStore.clauses], by simp [WatchStore.clauses], by simp [WatchStore.clauses],
    fun e he => by simp at he, fun k hk => by simp [WatchStore.clauses] at hk,
    fun i x hx => by simp [watchList, unpackWatchers] at hx, by simp [WatchStore.clauses]⟩

/-- A clause with its literals that are not false under the assignment `A` first, so that they are
the ones watched. -/
@[expose] def watchOrder (A : Assign) (c : Clause ℕ) : Clause ℕ :=
  c.filter (fun l => !A.isFalse l) ++ c.filter (fun l => A.isFalse l)

theorem watchOrder_perm (A : Assign) (c : Clause ℕ) : (watchOrder A c).Perm c := by
  have := List.filter_append_perm (fun l => !A.isFalse l) c
  simpa [watchOrder] using this

/-- If the first literal of `watchOrder A c` is false, every literal of `c` is. -/
theorem falsifies_of_watchOrder {A : Assign} {M : Trail} (hA : A.Agrees M) {c rest : Clause ℕ}
    {w : Literal ℕ} (h : watchOrder A c = w :: rest) (hw : w.negate ∈ Trail.lits M) :
    Trail.Falsifies M c := by
  intro l hl
  by_contra hne
  have hmem : l ∈ c.filter (fun l => !A.isFalse l) :=
    List.mem_filter.2 ⟨hl, by
      rw [Bool.not_eq_true', ← Bool.not_eq_true, hA.isFalse_iff]; exact hne⟩
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  rw [watchOrder, hx, List.cons_append, List.cons.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have := (List.mem_filter.1 (hx ▸ List.mem_cons_self : x ∈ _)).2
  rw [Bool.not_eq_true', ← Bool.not_eq_true, hA.isFalse_iff] at this
  exact this hw

/-- The literals of a clause without repetitions, removed in linear time (`dedupLits`), are those
of `List.dedup`, up to order. -/
theorem dedupLits_perm (c : Clause ℕ) : (dedupLits c).Perm c.dedup :=
  (List.perm_ext_iff_of_nodup (nodup_dedupKey litCode_injective c) (List.nodup_dedup c)).2
    fun l => by rw [mem_dedupKey litCode_injective, List.mem_dedup]

/-! #### Removing repetitions with a shared array -/

/-- Clearing the marks of the literals `L`. -/
@[expose] def clearKeys (L : Clause ℕ) (m : Array Bool) : Array Bool :=
  L.foldl (fun m x => m.setIfInBounds (litCode x) false) m

/-- Clearing the marks of `L`, which include every literal marked, leaves no mark. -/
theorem clearKeys_clean : ∀ (L : Clause ℕ) (m : Array Bool),
    (∀ y, m.getD (litCode y) false = true → y ∈ L) →
    ∀ y, (clearKeys L m).getD (litCode y) false = false
  | [], m, hm => fun y => by
    cases h : m.getD (litCode y) false
    · exact h
    · exact absurd (hm y h) List.not_mem_nil
  | x :: L, m, hm => by
    refine clearKeys_clean L _ fun y hy => ?_
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at hy
    by_cases hyx : litCode x = litCode y
    · rw [ite_eq_left hyx] at hy
      split at hy <;> simp at hy
    · rw [ite_eq_right hyx] at hy
      have := hm y (by simpa [Array.getD_eq_getD_getElem?] using hy)
      exact (List.mem_cons.1 this).resolve_left fun h => hyx (h ▸ rfl)

/-- **Removing the repetitions of `c`** with the marks `m`, which mark nothing and are cleared
again: the array is not allocated per clause, as `dedupLits` allocates it. If a literal of `c`
lies beyond the array, `dedupLits` is used instead. -/
@[expose] def dedupWith (m : Array Bool) (c : Clause ℕ) : Clause ℕ × Array Bool :=
  if c.all fun l => decide (litCode l < m.size) then
    let r := dedupKeyGo litCode c m []
    (r.1, clearKeys r.1 r.2)
  else (dedupLits c, m)

theorem dedupWith_spec (m : Array Bool) (c : Clause ℕ)
    (hm : ∀ y, m.getD (litCode y) false = false) :
    (dedupWith m c).1.Perm c.dedup ∧ ∀ y, (dedupWith m c).2.getD (litCode y) false = false := by
  unfold dedupWith
  split
  · rename_i hall
    have hsize : ∀ x ∈ c, litCode x < m.size := by simpa using hall
    have hm0 : ∀ y, m.getD (litCode y) false = true ↔ y ∈ ([] : Clause ℕ) := by simp [hm]
    obtain ⟨h₁, h₂, h₃⟩ := dedupKeyGo_spec litCode_injective c m [] hsize hm0 List.nodup_nil
    exact ⟨(List.perm_ext_iff_of_nodup h₂ (List.nodup_dedup c)).2 fun l => by
      rw [h₁, List.mem_dedup]; simp, clearKeys_clean _ _ fun y hy => (h₃ y).1 hy⟩
  · exact ⟨dedupLits_perm c, hm⟩

/-- The watch store of `F`, as `WatchStore.build`, removing repetitions with the marks `m`, which
are returned cleared. -/
@[expose] def WatchStore.buildWith (A : Assign) :
    List (ℕ × Clause ℕ) → Array Bool → WatchStore × Array Bool
  | [], m => (⟨#[], #[]⟩, m)
  | e :: F, m =>
    let r := buildWith A F m
    let d := dedupWith r.2 e.2
    (r.1.addClause e.1 (watchOrder A d.1), d.2)

/-- One past the greatest literal code of `F`: the size of the marks for its repetitions. -/
@[expose] def keyBound (F : List (ℕ × Clause ℕ)) : ℕ :=
  F.foldl (fun n e => e.2.foldl (fun n l => max n (litCode l + 1)) n) 0

/-- **The watch store** of the numbered clauses `F` under the assignment `A`: every clause with at
least two different literals, without repetitions, watching its first two literals once those that
are not false under `A` are put first. It adds the clauses with
`Cslib.Algorithms.Lean.CDCL.WatchStore.addClause`, as learning does, which leaves the store
unchanged for fewer than two literals. Repetitions are removed with one array of marks for all the
clauses (`Cslib.Algorithms.Lean.CDCL.dedupWith`). -/
@[expose] def WatchStore.build (A : Assign) (F : List (ℕ × Clause ℕ)) : WatchStore :=
  (WatchStore.buildWith A F (Array.replicate (keyBound F) false)).1

theorem WatchStore.buildWith_inv {A : Assign} {M : Trail} (hA : A.Agrees M) :
    ∀ (F : List (ℕ × Clause ℕ)) (m : Array Bool), (∀ y, m.getD (litCode y) false = false) →
    (∀ e ∈ F, 2 ≤ e.2.dedup.length → ¬ Trail.Falsifies M e.2) →
    (WatchStore.buildWith A F m).1.Inv F M [] ∧
      ∀ y, (WatchStore.buildWith A F m).2.getD (litCode y) false = false
  | [], m, hm, _ => ⟨WatchStore.inv_empty M [], hm⟩
  | e :: F, m, hm, hF => by
    obtain ⟨ih, hm'⟩ := buildWith_inv hA F m hm fun e' he' => hF e' (List.mem_cons_of_mem _ he')
    have hd := dedupWith_spec _ e.2 hm'
    have hperm := (watchOrder_perm A _).trans hd.1
    simp only [buildWith]
    refine ⟨?_, hd.2⟩
    match hc : watchOrder A (dedupWith (buildWith A F m).2 e.2).1 with
    | w₁ :: w₂ :: rest =>
      rw [hc] at hperm
      have hlen : 2 ≤ e.2.dedup.length := by simp [← hperm.length_eq]
      refine ih.addClause (id := e.1) (C := e.2) (hperm.nodup_iff.2 (List.nodup_dedup e.2))
        (fun l => by rw [hperm.mem_iff, List.mem_dedup]) fun hp => ?_
      exact hF e List.mem_cons_self hlen fun l hl =>
        falsifies_of_watchOrder hA hc hp.1 l (hd.1.mem_iff.2 (List.mem_dedup.2 hl))
    | [] =>
      rw [hc] at hperm
      exact ih.consShort e (by simp [← hperm.length_eq])
    | [_] =>
      rw [hc] at hperm
      exact ih.consShort e (by simp [← hperm.length_eq])

/-- The watch store built from `F` under an assignment agreeing with the trail `M`, none of whose
clauses `M` falsifies, satisfies the invariant with every literal of `M` processed: a clause whose
**first** watched literal is false has every literal false. (Its second watched literal may be
false while the clause is still open, as in a binary clause with one false and one unassigned
literal.) -/
theorem WatchStore.build_inv {A : Assign} {M : Trail} (hA : A.Agrees M) (F : List (ℕ × Clause ℕ))
    (hF : ∀ e ∈ F, 2 ≤ e.2.dedup.length → ¬ Trail.Falsifies M e.2) :
    (WatchStore.build A F).Inv F M [] :=
  (WatchStore.buildWith_inv hA F _ (fun y => by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> simp) hF).1

end Cslib.Algorithms.Lean.CDCL
