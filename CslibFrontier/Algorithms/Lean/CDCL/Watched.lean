/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.Naive
public import CslibFrontier.Algorithms.Lean.CDCL.Watch
import Mathlib.Tactic.Linarith

/-! # CDCL with two watched literals

The naive solver (`CDCL.Naive`) scans every clause of the database for a conflict or a unit after
each move. This solver finds them with two watched literals per clause instead, as MiniSat
does. Each trail literal is queued when it is assigned; processing it visits the
clauses watching its negation, which either find another watch, are satisfied by their other
watch, become unit, or are false.

The state `WExec` extends the naive solver's state `Exec` with the watch store, the queue, and the
clauses with fewer than two different literals, which cannot be watched and are scanned when the
queue is empty. Its invariant `WExec.Inv` adds to `Exec.Inv`:

* the watch store's invariant `WatchStore.Inv`: every clause with two different literals is
  stored, and no stored clause has both watches falsified by *processed* literals (literals of the
  trail not on the queue);
* the queue is on the trail, without repetitions, and above the newest decision.

The last condition makes the invariant survive Backjump without decision levels: the literals
removed are exactly those above the newest decision, so every processed literal kept was processed
before. With the queue empty, no clause of the database is false unless a short one is
(`WExec.Inv.noConflict`), so the loop finds conflicts and units among long clauses without
scanning them. Choosing the next decision variable, or seeing that every variable is assigned and
returning the model, still searches the variables of the database (`CNF.vars`), which can traverse
every literal occurrence.

Every move of the loop is a move of the naive solver, so the theorems of `CDCL.Naive` carry over:
`solveWatched_sat`, `solveWatched_unsat` and `isSat_solveWatched_iff`. Termination uses the naive
solver's rank, times the number of variables plus two, plus the length of the queue.

Blockers, which need an invariant over decision levels, are not part of this module.
-/

public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL Cslib.Logic.PL.CNF

variable {φ : CNF ℕ}

/-- The state of the solver with watched literals: the state of the naive solver, the watch store,
the queue of trail literals whose watch lists are still to be visited, and the clauses with fewer
than two different literals. -/
structure WExec (φ : CNF ℕ) where
  /-- The trail, database and log. -/
  exec : Exec φ
  /-- The watch store. -/
  store : WatchStore
  /-- The literals still to be processed. -/
  queue : List (Literal ℕ)
  /-- The clauses with fewer than two different literals. -/
  short : List (ℕ × Clause ℕ)

/-- The abstract trail. -/
abbrev WExec.M (S : WExec φ) : Trail := XTrail.trail S.exec.trail

/-- **The invariant of the solver with watched literals**: the invariant of the naive solver, the
invariant of the watch store, the short clauses, and a queue of distinct trail literals above the
newest decision. -/
structure WExec.Inv (S : WExec φ) : Prop where
  exec : S.exec.Inv
  store : S.store.Inv S.exec.db S.M S.queue
  short_mem : ∀ e ∈ S.short, e ∈ S.exec.db
  short_covers : ∀ e ∈ S.exec.db, e.2.dedup.length < 2 → e ∈ S.short
  queue_nodup : S.queue.Nodup
  queue_trail : ∀ x ∈ S.queue, x ∈ Trail.lits S.M
  queue_above : ∀ x ∈ S.queue, ∀ N d M₀, S.M = N ++ ⟨d, true⟩ :: M₀ → x ∉ Trail.lits M₀

/-- The initial state. -/
@[expose] def WExec.init (φ : CNF ℕ) : WExec φ :=
  ⟨Exec.init φ, WatchStore.build φ.lratDB, [], φ.lratDB.filter fun e => e.2.dedup.length < 2⟩

theorem WExec.init_inv (φ : CNF ℕ) : (WExec.init φ).Inv where
  exec := Exec.init_inv φ
  store := WatchStore.build_inv φ.lratDB
  short_mem e he := (List.mem_filter.1 he).1
  short_covers e he hlen := List.mem_filter.2 ⟨he, by simpa using hlen⟩
  queue_nodup := List.nodup_nil
  queue_trail _ h := absurd h List.not_mem_nil
  queue_above _ h := absurd h List.not_mem_nil

/-- The number of variables of `φ`, bounding the length of the trail. -/
abbrev nvars (φ : CNF ℕ) : ℕ := φ.vars.dedup.length

/-- The measure of a state: the rank of its abstract state, weighted above the length of the
queue. -/
@[expose]
def WExec.measure (S : WExec φ) : ℕ := rank φ.vars S.exec.state * (nvars φ + 2) + S.queue.length

theorem WExec.Inv.queue_length_le {S : WExec φ} (h : S.Inv) : S.queue.length ≤ nvars φ := by
  have h₁ : S.queue.length ≤ (Trail.lits S.M).length :=
    List.Nodup.length_le_of_subset h.queue_nodup h.queue_trail
  have h₂ := h.exec.run.length_le
  simp only [Trail.lits, List.length_map, WExec.M] at h₁
  simp only [nvars]
  omega

theorem watchIndex_inj {a b : Literal ℕ} (h : watchIndex a = watchIndex b) : a = b := by
  obtain ⟨v, x⟩ := a
  obtain ⟨w, y⟩ := b
  simp only [watchIndex] at h
  cases x <;> cases y <;> simp at h ⊢ <;> omega

/-! ### Processing a literal -/

/-- The invariant while visiting the watch list of `t.negate`, with the positions `L` still to be
visited: as `WExec.Inv`, except that a clause watching `t.negate` may be among `L` instead of on
its watch list, and every clause put back on that list has its other watched literal true. -/
structure WExec.ProcInv (S : WExec φ) (t : Literal ℕ) (L : List ℕ) : Prop where
  exec : S.exec.Inv
  sound : ∀ e ∈ S.store.clauses, ∃ c, (e.1, c) ∈ S.exec.db ∧ ∀ l, l ∈ e.2 ↔ l ∈ c
  nodup : ∀ e ∈ S.store.clauses, e.2.Nodup
  long : ∀ e ∈ S.store.clauses, 2 ≤ e.2.length
  covers : ∀ e ∈ S.exec.db, 2 ≤ e.2.dedup.length →
    ∃ e' ∈ S.store.clauses, e'.1 = e.1 ∧ ∀ l, l ∈ e'.2 ↔ l ∈ e.2
  listed : ∀ (k : ℕ) (hk : k < S.store.clauses.size), ∀ w ∈ S.store.clauses[k].2.take 2,
    k ∈ watchList S.store.watches (watchIndex w) ∨ (w = t.negate ∧ k ∈ L)
  visited : ∀ k ∈ watchList S.store.watches (watchIndex t.negate), ∀ (hk : k < S.store.clauses.size)
    (w₁ w₂ : Literal ℕ) (rest : Clause ℕ), S.store.clauses[k].2 = w₁ :: w₂ :: rest →
    (w₁ = t.negate → w₂ ∈ Trail.lits S.M) ∧ (w₂ = t.negate → w₁ ∈ Trail.lits S.M)
  notBoth : ∀ e ∈ S.store.clauses, ∀ w₁ w₂ rest, e.2 = w₁ :: w₂ :: rest →
    ¬ (Processed S.M S.queue w₁.negate ∧ Processed S.M S.queue w₂.negate)
  short_mem : ∀ e ∈ S.short, e ∈ S.exec.db
  short_covers : ∀ e ∈ S.exec.db, e.2.dedup.length < 2 → e ∈ S.short
  queue_nodup : S.queue.Nodup
  queue_trail : ∀ x ∈ S.queue, x ∈ Trail.lits S.M
  queue_above : ∀ x ∈ S.queue, ∀ N d M₀, S.M = N ++ ⟨d, true⟩ :: M₀ → x ∉ Trail.lits M₀
  t_mem : t ∈ S.queue

/-- Starting to process `t`: its negation's watch list is emptied and becomes the list to visit. -/
@[expose] def WExec.start (S : WExec φ) (t : Literal ℕ) : WExec φ :=
  { S with store := { S.store with
      watches := setWatch S.store.watches (watchIndex t.negate) [] } }

theorem WExec.start_procInv {S : WExec φ} (h : S.Inv) {t : Literal ℕ} (ht : t ∈ S.queue) :
    (S.start t).ProcInv t (watchList S.store.watches (watchIndex t.negate)) where
  exec := h.exec
  sound := h.store.sound
  nodup := h.store.nodup
  long := h.store.long
  covers := h.store.covers
  listed k hk w hw := by
    have := h.store.listed k hk w hw
    simp only [WExec.start, watchList_setWatch]
    by_cases hw' : w = t.negate
    · exact .inr ⟨hw', hw' ▸ this⟩
    · have hne : ¬ watchIndex w = watchIndex t.negate := fun h => hw' (watchIndex_inj h)
      exact .inl (by simp only [hne, ↓reduceIte]; exact this)
  visited k hk := by simp [WExec.start] at hk
  notBoth := h.store.notBoth
  short_mem := h.short_mem
  short_covers := h.short_covers
  queue_nodup := h.queue_nodup
  queue_trail := h.queue_trail
  queue_above := h.queue_above
  t_mem := ht

/-- Finishing the processing of `t`: removing it from the queue. -/
@[expose]
def WExec.finish (S : WExec φ) (t : Literal ℕ) : WExec φ := { S with queue := S.queue.erase t }

theorem WExec.finish_inv {S : WExec φ} {t : Literal ℕ} (h : S.ProcInv t []) :
    (S.finish t).Inv ∧ (S.finish t).measure < S.measure := by
  have hnodupM := h.exec.run.nodup
  have hprocessed : ∀ x, Processed S.M (S.queue.erase t) x → Processed S.M S.queue x ∨ x = t :=
    fun x ⟨hx, hxq⟩ => by
      by_cases hxt : x = t
      · exact .inr hxt
      · exact .inl ⟨hx, fun hq => hxq ((List.mem_erase_of_ne hxt).2 hq)⟩
  -- a watched literal falsified by `t` has its other watched literal true
  have hother : ∀ e ∈ S.store.clauses, ∀ w₁ w₂ rest, e.2 = w₁ :: w₂ :: rest →
      (w₁.negate = t → w₂ ∈ Trail.lits S.M) ∧ (w₂.negate = t → w₁ ∈ Trail.lits S.M) := by
    intro e he w₁ w₂ rest hc
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 he
    refine ⟨fun h₁ => ?_, fun h₂ => ?_⟩
    · have hu : w₁ = t.negate := by rw [← h₁, negate_negate]
      have := h.listed k hk w₁ (by simp [hc])
      rcases this with hl | ⟨-, hL⟩
      · exact (h.visited k (hu ▸ hl) hk w₁ w₂ rest hc).1 hu
      · simp at hL
    · have hu : w₂ = t.negate := by rw [← h₂, negate_negate]
      have := h.listed k hk w₂ (by simp [hc])
      rcases this with hl | ⟨-, hL⟩
      · exact (h.visited k (hu ▸ hl) hk w₁ w₂ rest hc).2 hu
      · simp at hL
  refine ⟨⟨h.exec, ⟨h.sound, h.nodup, h.long, h.covers, fun k hk w hw => ?_, ?_⟩, h.short_mem,
    h.short_covers, h.queue_nodup.erase t, fun x hx => h.queue_trail x (List.mem_of_mem_erase hx),
    fun x hx => h.queue_above x (List.mem_of_mem_erase hx)⟩, ?_⟩
  · rcases h.listed k hk w hw with hl | ⟨-, hL⟩
    · exact hl
    · simp at hL
  · intro e he w₁ w₂ rest hc ⟨h₁, h₂⟩
    obtain ⟨ho₁, ho₂⟩ := hother e he w₁ w₂ rest hc
    rcases hprocessed _ h₁ with h₁ | h₁ <;> rcases hprocessed _ h₂ with h₂ | h₂
    · exact h.notBoth e he w₁ w₂ rest hc ⟨h₁, h₂⟩
    · exact Trail.negate_not_mem hnodupM (ho₂ h₂) h₁.1
    · exact Trail.negate_not_mem hnodupM (ho₁ h₁) h₂.1
    · exact Trail.negate_not_mem hnodupM (ho₁ h₁) (h₂ ▸ h.queue_trail t h.t_mem)
  · simp only [WExec.measure, WExec.finish]
    have := List.length_erase_of_mem h.t_mem
    have : 0 < S.queue.length := List.length_pos_of_mem h.t_mem
    omega

private theorem watchInj_mem {W : Array (List ℕ)} {a b : Literal ℕ} {k : ℕ}
    (h : watchIndex a = watchIndex b) (hk : k ∈ watchList W (watchIndex a)) :
    k ∈ watchList W (watchIndex b) := h ▸ hk

theorem otherWatch_spec {u w₁ w₂ : Literal ℕ} (hne : w₁ ≠ w₂) :
    (w₁ = u → otherWatch u w₁ w₂ = w₂) ∧ (w₂ = u → otherWatch u w₁ w₂ = w₁) := by
  refine ⟨fun h => by simp [otherWatch, h], fun h => ?_⟩
  have : w₁ ≠ u := fun h' => hne (h'.trans h.symm)
  simp [otherWatch, this]

/-- Putting the clause `k` just visited back on the watch list of `t.negate` keeps every watched
clause listed, with `L` left to visit. -/
private theorem WExec.ProcInv.listed_addWatch {S : WExec φ} {t : Literal ℕ} {k : ℕ} {L : List ℕ}
    (h : S.ProcInv t (k :: L)) (k' : ℕ) (hk' : k' < S.store.clauses.size)
    (w : Literal ℕ) (hw : w ∈ S.store.clauses[k'].2.take 2) :
    k' ∈ watchList (addWatch S.store.watches (watchIndex t.negate) k) (watchIndex w) ∨
      (w = t.negate ∧ k' ∈ L) := by
  simp only [watchList_addWatch]
  rcases h.listed k' hk' w hw with hl | ⟨rfl, hL⟩
  · split
    · rename_i hi
      exact .inl (List.mem_cons_of_mem _ (watchInj_mem hi hl))
    · exact .inl hl
  · rcases List.mem_cons.1 hL with rfl | hL
    · exact .inl (by simp)
    · exact .inr ⟨rfl, hL⟩

/-- **Keeping** a clause whose other watched literal is true: it goes back on the watch list. -/
theorem WExec.ProcInv.keep {S : WExec φ} {t : Literal ℕ} {k : ℕ} {L : List ℕ}
    (h : S.ProcInv t (k :: L)) (hv : VisitSpec S.store S.M t.negate k .keep) :
    ({ S with store := { S.store with
      watches := addWatch S.store.watches (watchIndex t.negate) k } } : WExec φ).ProcInv t L := by
  obtain ⟨hk, w₁, w₂, rest, hc, hu, hother⟩ := hv
  refine ⟨h.exec, h.sound, h.nodup, h.long, h.covers, fun k' hk' w hw => ?_, ?_, h.notBoth,
    h.short_mem, h.short_covers, h.queue_nodup, h.queue_trail, h.queue_above, h.t_mem⟩
  · exact h.listed_addWatch k' hk' w hw
  · intro k' hk'' hk' v₁ v₂ rest' hc'
    simp only [watchList_addWatch, ↓reduceIte, List.mem_cons] at hk''
    rcases hk'' with rfl | hk''
    · rw [hc] at hc'
      simp only [List.cons.injEq] at hc'
      obtain ⟨rfl, rfl, -⟩ := hc'
      have hnd := h.nodup _ (Array.getElem_mem hk)
      rw [hc] at hnd
      have hne : w₁ ≠ w₂ := fun he => (List.nodup_cons.1 hnd).1 (he ▸ List.mem_cons_self)
      obtain ⟨h₁, h₂⟩ := otherWatch_spec (u := t.negate) hne
      exact ⟨fun hv => h₁ hv ▸ hother, fun hv => h₂ hv ▸ hother⟩
    · exact h.visited k' hk'' hk' v₁ v₂ rest' hc'

/-- A stored clause has two watched literals. -/
theorem WExec.ProcInv.exists_cons {S : WExec φ} {t : Literal ℕ} {L : List ℕ} (h : S.ProcInv t L)
    {k : ℕ} (hk : k < S.store.clauses.size) :
    ∃ w₁ w₂ rest, S.store.clauses[k].2 = w₁ :: w₂ :: rest := by
  have := h.long _ (Array.getElem_mem hk)
  match hc : S.store.clauses[k].2, this with
  | w₁ :: w₂ :: rest, _ => exact ⟨w₁, w₂, rest, rfl⟩

/-- **Dropping** a clause that no longer watches the literal. -/
theorem WExec.ProcInv.drop {S : WExec φ} {t : Literal ℕ} {k : ℕ} {L : List ℕ}
    (h : S.ProcInv t (k :: L)) (hv : VisitSpec S.store S.M t.negate k .drop) :
    S.ProcInv t L := by
  refine ⟨h.exec, h.sound, h.nodup, h.long, h.covers, fun k' hk' w hw => ?_, h.visited,
    h.notBoth, h.short_mem, h.short_covers, h.queue_nodup, h.queue_trail, h.queue_above, h.t_mem⟩
  rcases h.listed k' hk' w hw with hl | ⟨rfl, hL⟩
  · exact .inl hl
  · rcases List.mem_cons.1 hL with rfl | hL
    · obtain ⟨w₁, w₂, rest, hc⟩ := h.exists_cons hk'
      obtain ⟨h₁, h₂⟩ := hv hk' w₁ w₂ rest hc
      rw [hc] at hw
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      rcases hw with hw | hw
      · exact absurd hw.symm h₁
      · exact absurd hw.symm h₂
    · exact .inr ⟨rfl, hL⟩

private theorem mem_setIfInBounds_cases {α : Type} {a : Array α} {k : ℕ} {x e : α}
    (he : e ∈ a.setIfInBounds k x) : e = x ∨ e ∈ a := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 he
  have hi' : i < a.size := by simpa using hi
  by_cases hik : k = i
  · subst hik; left; simp
  · right; rw [Array.getElem_setIfInBounds_ne hi' hik]; exact Array.getElem_mem _

/-- **Moving** a watch to a literal that is not false. -/
theorem WExec.ProcInv.move {S : WExec φ} {t : Literal ℕ} {k : ℕ} {L : List ℕ} {S' : WatchStore}
    (h : S.ProcInv t (k :: L)) (hv : VisitSpec S.store S.M t.negate k (.move S')) :
    ({ S with store := S' } : WExec φ).ProcInv t L := by
  obtain ⟨hk, id, w₁, w₂, x, rest, hc, hu, hx, hxf, rfl⟩ := hv
  set u := t.negate
  set o := otherWatch u w₁ w₂
  have hnd := h.nodup _ (Array.getElem_mem hk)
  rw [hc] at hnd
  have hne : w₁ ≠ w₂ := fun he => (List.nodup_cons.1 hnd).1 (he ▸ List.mem_cons_self)
  obtain ⟨ho₁, ho₂⟩ := otherWatch_spec (u := u) hne
  -- the new clause is a permutation of the old one
  have hxu : x ≠ u := by
    rintro rfl
    exact hxf (by rw [negate_negate]; exact h.queue_trail t h.t_mem)
  have hperm : (o :: x :: u :: rest.erase x).Perm (w₁ :: w₂ :: rest) := by
    have hrest : (x :: rest.erase x).Perm rest := (List.perm_cons_erase hx).symm
    rcases hu with h₁ | h₂
    · have : o = w₂ := ho₁ h₁
      rw [this, h₁]
      exact ((List.Perm.swap u x _).cons w₂).trans
        ((List.Perm.swap u w₂ _).trans ((hrest.cons w₂).cons u))
    · have : o = w₁ := ho₂ h₂
      rw [this, h₂]
      exact List.Perm.cons _ ((List.Perm.swap _ _ _).trans (List.Perm.cons _ hrest))
  have hold : S.store.clauses[k] = (id, w₁ :: w₂ :: rest) := hc
  have hmem : ∀ e ∈ S.store.clauses.setIfInBounds k (id, o :: x :: u :: rest.erase x),
      e = (id, o :: x :: u :: rest.erase x) ∨ e ∈ S.store.clauses :=
    fun e he => mem_setIfInBounds_cases he
  have hsize : (S.store.clauses.setIfInBounds k (id, o :: x :: u :: rest.erase x)).size =
      S.store.clauses.size := by simp
  have hou : o ≠ u := by
    change otherWatch u w₁ w₂ ≠ u
    rcases hu with h₁ | h₂
    · rw [ho₁ h₁]; exact fun h₂ => hne (h₁.trans h₂.symm)
    · rw [ho₂ h₂]; exact fun h₁ => hne (h₁.trans h₂.symm)
  have hotake : o ∈ (S.store.clauses[k].2).take 2 := by
    change otherWatch u w₁ w₂ ∈ _
    rw [hold]
    rcases hu with h₁ | h₂
    · simp [ho₁ h₁]
    · simp [ho₂ h₂]
  have hidx : watchIndex u ≠ watchIndex x := fun h => hxu (watchIndex_inj h).symm
  have hnew : ∀ (hk' : k < (S.store.clauses.setIfInBounds k
      (id, o :: x :: u :: rest.erase x)).size),
      (S.store.clauses.setIfInBounds k (id, o :: x :: u :: rest.erase x))[k] =
        (id, o :: x :: u :: rest.erase x) := fun _ => by simp
  have hothers : ∀ i (hi : i < S.store.clauses.size), i ≠ k →
      (S.store.clauses.setIfInBounds k (id, o :: x :: u :: rest.erase x))[i]'(by simpa using hi) =
        S.store.clauses[i] := fun i hi hik => Array.getElem_setIfInBounds_ne hi (Ne.symm hik)
  refine ⟨h.exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.short_mem, h.short_covers, h.queue_nodup,
    h.queue_trail, h.queue_above, h.t_mem⟩
  · intro e he
    rcases hmem e he with rfl | he
    · obtain ⟨c, hcdb, hceq⟩ := h.sound _ (Array.getElem_mem hk)
      rw [hold] at hcdb hceq
      exact ⟨c, hcdb, fun l => (hperm.mem_iff).trans (hceq l)⟩
    · exact h.sound e he
  · intro e he
    rcases hmem e he with rfl | he
    · exact hperm.nodup_iff.2 hnd
    · exact h.nodup e he
  · intro e he
    rcases hmem e he with rfl | he
    · simp
    · exact h.long e he
  · intro e he hlen
    obtain ⟨e', he', hid, heq⟩ := h.covers e he hlen
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 he'
    by_cases hik : i = k
    · subst hik
      refine ⟨(id, o :: x :: u :: rest.erase x), Array.mem_iff_getElem.2
        ⟨i, by simpa using hi, by simp⟩, ?_, fun l => ?_⟩
      · rw [← hid, hold]
      · rw [← heq l, hold]; exact hperm.mem_iff
    · exact ⟨_, Array.mem_iff_getElem.2 ⟨i, by simpa using hi, hothers i hi hik⟩, hid, heq⟩
  · intro k' hk' w hw
    simp only [watchList_addWatch]
    have hk'' : k' < S.store.clauses.size := by simpa using hk'
    by_cases hkk : k' = k
    · subst hkk
      simp only [hnew, List.take_succ_cons, List.take_zero, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with hw | hw
      · rw [hw]
        rcases h.listed k' hk'' _ hotake with hl | ⟨hw', -⟩
        · left; split
          · exact List.mem_cons_of_mem _ (by rename_i hi; exact hi ▸ hl)
          · exact hl
        · exact absurd hw' hou
      · rw [hw]; simp
    · simp only [hothers k' hk'' hkk] at hw ⊢
      rcases h.listed k' hk'' w hw with hl | ⟨hw', hL⟩
      · left; split
        · exact List.mem_cons_of_mem _ (by rename_i hi; exact hi ▸ hl)
        · exact hl
      · exact .inr ⟨hw', (List.mem_cons.1 hL).resolve_left hkk⟩
  · intro k' hk' hk'' v₁ v₂ rest' hc'
    simp only [watchList_addWatch] at hk'
    replace hk' : k' ∈ watchList S.store.watches (watchIndex t.negate) := by
      split at hk'
      · exact absurd ‹_› hidx
      · exact hk'
    have hk''' : k' < S.store.clauses.size := by simpa using hk''
    by_cases hkk : k' = k
    · subst hkk
      rw [hnew] at hc'
      simp only [List.cons.injEq] at hc'
      obtain ⟨rfl, rfl, -⟩ := hc'
      exact ⟨fun h => absurd h hou, fun h => absurd h hxu⟩
    · rw [hothers k' hk''' hkk] at hc'
      exact h.visited k' hk' hk''' v₁ v₂ rest' hc'
  · intro e he v₁ v₂ rest' hc' hboth
    rcases hmem e he with rfl | he
    · simp only [List.cons.injEq] at hc'
      obtain ⟨-, rfl, -⟩ := hc'
      exact hxf hboth.2.1
    · exact h.notBoth e he v₁ v₂ rest' hc' hboth

/-- A variable of the trail has a literal on it. -/
theorem Trail.mem_lits_of_mem_vars {M : Trail} {v : ℕ} (h : v ∈ Trail.vars M) :
    (v, true) ∈ Trail.lits M ∨ (v, false) ∈ Trail.lits M := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
  obtain ⟨⟨w, b⟩, d⟩ := e
  have : (w, b) ∈ Trail.lits M := List.mem_map.2 ⟨_, he, rfl⟩
  cases b
  · exact .inr this
  · exact .inl this

/-- A literal that is neither true nor false is over an unassigned variable. -/
theorem not_mem_vars_of_undef {M : Trail} {l : Literal ℕ} (h₁ : l ∉ Trail.lits M)
    (h₂ : l.negate ∉ Trail.lits M) : l.1 ∉ Trail.vars M := by
  intro hv
  obtain ⟨v, b⟩ := l
  rcases Trail.mem_lits_of_mem_vars hv with h | h <;> cases b <;>
    simp_all [Std.Sat.Literal.negate]

/-- **A unit clause**: its other watched literal is propagated, with the clause as its reason, and
queued; the clause goes back on the watch list. -/
@[expose] def WExec.propagateUnit (S : WExec φ) (t l : Literal ℕ) (id k : ℕ) : WExec φ :=
  { S with
    exec := S.exec.propagate (id, []) l
    queue := l :: S.queue
    store := { S.store with watches := addWatch S.store.watches (watchIndex t.negate) k } }

theorem WExec.ProcInv.unit {S : WExec φ} {t l : Literal ℕ} {id k : ℕ} {L : List ℕ}
    (h : S.ProcInv t (k :: L)) (hv : VisitSpec S.store S.M t.negate k (.unit l id)) :
    (S.propagateUnit t l id k).ProcInv t L ∧ (S.propagateUnit t l id k).measure < S.measure := by
  obtain ⟨hk, w₁, w₂, rest, hc, hu, rfl, hl, hln, hrest⟩ := hv
  set u := t.negate
  have hnd := h.nodup _ (Array.getElem_mem hk)
  rw [hc] at hnd
  have hne : w₁ ≠ w₂ := fun he => (List.nodup_cons.1 hnd).1 (he ▸ List.mem_cons_self)
  obtain ⟨ho₁, ho₂⟩ := otherWatch_spec (u := u) hne
  obtain ⟨c, hcdb, hceq⟩ := h.sound _ (Array.getElem_mem hk)
  rw [hc] at hcdb hceq
  have hu' : u.negate ∈ Trail.lits S.M := by
    rw [negate_negate]; exact h.queue_trail t h.t_mem
  -- every literal of the clause but the propagated one is false
  have hfalse : ∀ y ∈ c, y ≠ otherWatch u w₁ w₂ → y.negate ∈ Trail.lits S.M := by
    intro y hy hne'
    rcases List.mem_cons.1 ((hceq y).2 hy) with rfl | hy
    · rcases hu with h₁ | h₂
      · exact h₁ ▸ hu'
      · exact absurd (ho₂ h₂).symm hne'
    · rcases List.mem_cons.1 hy with rfl | hy
      · rcases hu with h₁ | h₂
        · exact absurd (ho₁ h₁).symm hne'
        · exact h₂ ▸ hu'
      · exact hrest y hy
  have hmemc : otherWatch u w₁ w₂ ∈ c := by
    refine (hceq _).1 ?_
    rcases hu with h₁ | h₂
    · rw [ho₁ h₁]; simp
    · rw [ho₂ h₂]; simp
  have hspec := Exec.propagate_spec' h.exec hcdb hmemc (not_mem_vars_of_undef hl hln) hfalse
  have hM : (S.propagateUnit t (otherWatch u w₁ w₂) id k).M =
      ⟨otherWatch u w₁ w₂, false⟩ :: S.M := rfl
  have hlits : Trail.lits (S.propagateUnit t (otherWatch u w₁ w₂) id k).M =
      otherWatch u w₁ w₂ :: Trail.lits S.M := by rw [hM]; rfl
  refine ⟨⟨hspec.1, h.sound, h.nodup, h.long, h.covers, fun k' hk' w hw => ?_, ?_, ?_,
    h.short_mem, h.short_covers, ?_, ?_, ?_, List.mem_cons_of_mem _ h.t_mem⟩, ?_⟩
  · exact h.listed_addWatch k' hk' w hw
  · intro k' hk'' hk' v₁ v₂ rest' hc'
    rw [hlits]
    simp only [WExec.propagateUnit, watchList_addWatch, ↓reduceIte, List.mem_cons] at hk''
    rcases hk'' with rfl | hk''
    · have hc'' : w₁ :: w₂ :: rest = v₁ :: v₂ :: rest' := (congrArg Prod.snd hc).symm.trans hc'
      simp only [List.cons.injEq] at hc''
      obtain ⟨rfl, rfl, -⟩ := hc''
      exact ⟨fun h₁ => by rw [ho₁ h₁]; simp, fun h₂ => by rw [ho₂ h₂]; simp⟩
    · obtain ⟨h₁, h₂⟩ := h.visited k' hk'' hk' v₁ v₂ rest' hc'
      exact ⟨fun hv => List.mem_cons_of_mem _ (h₁ hv), fun hv => List.mem_cons_of_mem _ (h₂ hv)⟩
  · intro e he v₁ v₂ rest' hc' ⟨hp₁, hp₂⟩
    have hproc : ∀ x, Processed (S.propagateUnit t (otherWatch u w₁ w₂) id k).M
        (S.propagateUnit t (otherWatch u w₁ w₂) id k).queue x → Processed S.M S.queue x := by
      intro x ⟨hx, hxq⟩
      rw [hlits] at hx
      simp only [WExec.propagateUnit, List.mem_cons, not_or] at hxq
      exact ⟨(List.mem_cons.1 hx).resolve_left hxq.1, hxq.2⟩
    exact h.notBoth e he v₁ v₂ rest' hc' ⟨hproc _ hp₁, hproc _ hp₂⟩
  · exact List.nodup_cons.2 ⟨fun hq => hl (h.queue_trail _ hq), h.queue_nodup⟩
  · intro x hx
    rw [hlits]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h.queue_trail x hx)
  · intro x hx N d M₀ hN
    cases N with
    | nil => simp [hM] at hN
    | cons y N =>
      rw [hM] at hN
      simp only [List.cons_append, List.cons.injEq] at hN
      rcases List.mem_cons.1 hx with rfl | hx
      · intro hxM₀
        apply hl
        rw [hN.2, lits_append]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ hxM₀)
      · exact h.queue_above x hx N d M₀ hN.2
  · have := hspec.2
    simp only [WExec.measure, WExec.propagateUnit, List.length_cons]
    have : rank φ.vars (S.exec.propagate (id, []) (otherWatch u w₁ w₂)).state <
        rank φ.vars S.exec.state := hspec.2
    nlinarith

/-- Restoring the watch list of `t.negate` after a conflict at position `k`, with `L` still to be
visited. -/
@[expose] def WExec.restore (S : WExec φ) (t : Literal ℕ) (k : ℕ) (L : List ℕ) : WExec φ :=
  let i := watchIndex t.negate
  let W := setWatch S.store.watches i (k :: L ++ watchList S.store.watches i)
  { S with store := { S.store with watches := W } }

theorem WExec.ProcInv.restore_inv {S : WExec φ} {t : Literal ℕ} {k : ℕ} {L : List ℕ}
    (h : S.ProcInv t (k :: L)) : (S.restore t k L).Inv ∧ (S.restore t k L).measure = S.measure := by
  refine ⟨⟨h.exec, ⟨h.sound, h.nodup, h.long, h.covers, fun k' hk' w hw => ?_, h.notBoth⟩,
    h.short_mem, h.short_covers, h.queue_nodup, h.queue_trail, h.queue_above⟩, rfl⟩
  simp only [WExec.restore, watchList_setWatch]
  rcases h.listed k' hk' w hw with hl | ⟨rfl, hL⟩
  · split
    · rename_i hi
      exact List.mem_append_right _ (watchInj_mem hi hl)
    · exact hl
  · simp only [↓reduceIte]
    exact List.mem_append_left _ hL

/-- **A conflict**: the clause numbered `id` is a clause of the database, the log names it, and the
trail falsifies it. -/
theorem WExec.ProcInv.conflict_clause {S : WExec φ} {t : Literal ℕ} {k : ℕ} {L : List ℕ}
    {id : ℕ} (h : S.ProcInv t (k :: L)) (hv : VisitSpec S.store S.M t.negate k (.conflict id)) :
    ∃ c, (id, c) ∈ S.exec.db ∧ S.exec.log.clause? id = some c ∧ Trail.Falsifies S.M c := by
  obtain ⟨hk, w₁, w₂, rest, hc, hu, hoth, hrest⟩ := hv
  obtain ⟨c, hcdb, hceq⟩ := h.sound _ (Array.getElem_mem hk)
  rw [hc] at hcdb hceq
  have hnd := h.nodup _ (Array.getElem_mem hk)
  rw [hc] at hnd
  have hne : w₁ ≠ w₂ := fun he => (List.nodup_cons.1 hnd).1 (he ▸ List.mem_cons_self)
  obtain ⟨ho₁, ho₂⟩ := otherWatch_spec (u := t.negate) hne
  have hu' : t.negate.negate ∈ Trail.lits S.M := by
    rw [negate_negate]; exact h.queue_trail t h.t_mem
  refine ⟨c, hcdb, h.exec.db_log _ hcdb, fun y hy => ?_⟩
  rcases List.mem_cons.1 ((hceq y).2 hy) with rfl | hy
  · rcases hu with h₁ | h₂
    · exact h₁ ▸ hu'
    · rw [← ho₂ h₂]; exact hoth
  · rcases List.mem_cons.1 hy with rfl | hy
    · rcases hu with h₁ | h₂
      · rw [← ho₁ h₁]; exact hoth
      · exact h₂ ▸ hu'
    · exact hrest y hy

/-- The result of visiting a watch list from the state `S₀`: done, or a conflict. -/
inductive ProcResult (φ : CNF ℕ) (S₀ : WExec φ) (t : Literal ℕ) : Type
  /-- Every clause on the list was visited. -/
  | done (S : WExec φ) (h : S.ProcInv t []) (hm : S.measure ≤ S₀.measure)
  /-- A clause of the database is false. -/
  | conflict (S : WExec φ) (h : S.Inv) (e : ℕ × Clause ℕ) (he : e ∈ S.exec.db)
      (hconf : Trail.Falsifies S.M e.2) (hm : S.measure ≤ S₀.measure)

/-- A result from a state of smaller measure is a result from `S₀`. -/
@[expose] def ProcResult.weaken {S₀ S₁ : WExec φ} {t : Literal ℕ} (hle : S₁.measure ≤ S₀.measure) :
    ProcResult φ S₁ t → ProcResult φ S₀ t
  | .done S h hm => .done S h (hm.trans hle)
  | .conflict S h e he hc hm => .conflict S h e he hc (hm.trans hle)

/-- **Visiting a watch list**: every clause on `L` is visited in turn, until a conflict. -/
@[expose] def WExec.processList (t : Literal ℕ) : (L : List ℕ) → (S : WExec φ) → S.ProcInv t L →
    ProcResult φ S t
  | [], S, h => .done S h le_rfl
  | k :: L, S, h =>
    match hv : S.store.visit S.M t.negate k with
    | .keep =>
      have hs : VisitSpec S.store S.M t.negate k .keep := hv ▸ S.store.visit_spec S.M t.negate k
      (WExec.processList t L _ (h.keep hs)).weaken (S₀ := S) (by exact le_rfl)
    | .move S' =>
      have hs : VisitSpec S.store S.M t.negate k (.move S') :=
        hv ▸ S.store.visit_spec S.M t.negate k
      (WExec.processList t L _ (h.move hs)).weaken (S₀ := S) (by exact le_rfl)
    | .unit l id =>
      have hs : VisitSpec S.store S.M t.negate k (.unit l id) :=
        hv ▸ S.store.visit_spec S.M t.negate k
      have hu := h.unit hs
      (WExec.processList t L _ hu.1).weaken hu.2.le
    | .conflict id =>
      have hs : VisitSpec S.store S.M t.negate k (.conflict id) :=
        hv ▸ S.store.visit_spec S.M t.negate k
      match hc : S.exec.log.clause? id with
      | some c =>
        have hcc := h.conflict_clause hs
        have hr := h.restore_inv
        .conflict (S.restore t k L) hr.1 (id, c)
          (by obtain ⟨c', hc', hlog, -⟩ := hcc; rw [hlog] at hc; cases hc; exact hc')
          (by obtain ⟨c', -, hlog, hf⟩ := hcc; rw [hlog] at hc; cases hc; exact hf) hr.2.le
      | none => absurd hc (by obtain ⟨c', -, hlog, -⟩ := h.conflict_clause hs; simp [hlog])
    | .drop =>
      have hs : VisitSpec S.store S.M t.negate k .drop := hv ▸ S.store.visit_spec S.M t.negate k
      (WExec.processList t L S (h.drop hs)).weaken le_rfl

/-! ### Moves at the top level -/

/-- The literals below a decision of a trail are on the trail. -/
theorem lits_below {N M₀ : Trail} {d : Literal ℕ} {x : Literal ℕ}
    (hx : x ∈ Trail.lits M₀) : x ∈ Trail.lits (N ++ ⟨d, true⟩ :: M₀) := by
  rw [lits_append]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)

/-- The learned clause without repetitions, its asserting literal first. -/
@[expose] def learnedWatched (C : Clause ℕ) (l : Literal ℕ) : Clause ℕ := l :: C.dedup.erase l

theorem learnedWatched_perm {C : Clause ℕ} {l : Literal ℕ} (hl : l ∈ C) :
    (learnedWatched C l).Perm C.dedup :=
  (List.perm_cons_erase (List.mem_dedup.2 hl)).symm

/-- **Backjump and Learn with watches**: the state after the conflict, with the learned clause in
the store, watching its asserting literal, or among the short clauses, and the asserting literal
queued. -/
@[expose] def WExec.afterConflict (S : WExec φ) (sp : Split) (L : S.exec.LearnedAt sp) : WExec φ :=
  if 2 ≤ L.clause.dedup.length then
    ⟨S.exec.afterConflict sp L, S.store.addClause L.id (learnedWatched L.clause L.lit), [L.lit],
      S.short⟩
  else ⟨S.exec.afterConflict sp L, S.store, [L.lit], (L.id, L.clause) :: S.short⟩

theorem WExec.afterConflict_spec {S : WExec φ} (hS : S.Inv) {e : ℕ × Clause ℕ}
    (he : e ∈ S.exec.db) (hconf : Trail.Falsifies S.M e.2) {sp : Split}
    (hsp : XTrail.split S.exec.trail = some sp) (L : S.exec.LearnedAt sp) :
    (S.afterConflict sp L).Inv ∧ (S.afterConflict sp L).measure < S.measure := by
  have hspec := Exec.afterConflict_spec hS.exec he hconf hsp L
  have hsplit := XTrail.trail_of_split hsp
  have hM' : XTrail.trail (S.exec.afterConflict sp L).trail =
      ⟨L.lit, false⟩ :: XTrail.trail sp.below := rfl
  have hdb' : (S.exec.afterConflict sp L).db = (L.id, L.clause) :: S.exec.db := rfl
  have hnodup' := hspec.1.run.nodup
  rw [hM'] at hnodup'
  have hlitM' : L.lit ∈ Trail.lits (⟨L.lit, false⟩ :: XTrail.trail sp.below) :=
    List.mem_cons_self
  -- the processed literals after backjumping are below the decision, hence processed before
  have hproc : ∀ x, Processed (⟨L.lit, false⟩ :: XTrail.trail sp.below) [L.lit] x →
      Processed S.M S.queue x := by
    intro x ⟨hx, hxq⟩
    have hx' : x ∈ Trail.lits (XTrail.trail sp.below) :=
      (List.mem_cons.1 hx).resolve_left (by simpa using hxq)
    refine ⟨by rw [WExec.M, hsplit]; exact lits_below hx', fun hq => ?_⟩
    exact hS.queue_above x hq _ _ _ hsplit hx'
  have hstore := hS.store.weaken hproc
  have hlitneg : ¬ Processed (⟨L.lit, false⟩ :: XTrail.trail sp.below) [L.lit] L.lit.negate :=
    fun h => Trail.negate_not_mem hnodup' hlitM' h.1
  have hqueue : ∀ x ∈ [L.lit], ∀ N d M₀,
      (⟨L.lit, false⟩ :: XTrail.trail sp.below : Trail) = N ++ ⟨d, true⟩ :: M₀ →
      x ∉ Trail.lits M₀ := by
    intro x hx N d M₀ hN hxM₀
    rw [List.mem_singleton] at hx
    subst hx
    cases N with
    | nil => simp at hN
    | cons y N =>
      simp only [List.cons_append, List.cons.injEq] at hN
      apply L.undef
      rw [congrArg Trail.vars hN.2]
      exact Trail.mem_vars_of_mem_lits (lits_below hxM₀)
  have hmeasure : rank φ.vars (S.exec.afterConflict sp L).state * (nvars φ + 2) + 1 <
      S.measure := by
    have := hspec.2
    simp only [WExec.measure]
    nlinarith
  unfold WExec.afterConflict
  split
  · rename_i hlen
    have hperm := learnedWatched_perm (C := L.clause) L.mem
    have hlen' : 2 ≤ (learnedWatched L.clause L.lit).length := hperm.length_eq ▸ hlen
    obtain ⟨y, rest, hc⟩ : ∃ y rest, learnedWatched L.clause L.lit = L.lit :: y :: rest := by
      match h : learnedWatched L.clause L.lit, hlen' with
      | a :: y :: rest, _ =>
        exact ⟨y, rest, by simp only [learnedWatched, List.cons.injEq] at h; rw [← h.1]⟩
    have hnd : (L.lit :: y :: rest).Nodup := hc ▸ hperm.nodup_iff.2 (List.nodup_dedup _)
    have hmem : ∀ l, l ∈ L.lit :: y :: rest ↔ l ∈ L.clause := fun l => by
      rw [← hc, hperm.mem_iff, List.mem_dedup]
    refine ⟨⟨hspec.1, ?_, fun e' he' => ?_, fun e' he' hl => ?_, List.nodup_singleton _,
      fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact hlitM', hqueue⟩, ?_⟩
    · have := hstore.addClause (id := L.id) (C := L.clause) hnd hmem hlitneg
      rw [← hc] at this
      exact this
    · exact hdb' ▸ List.mem_cons_of_mem _ (hS.short_mem e' he')
    · rw [hdb'] at he'
      rcases List.mem_cons.1 he' with rfl | he'
      · simp only at hl; omega
      · exact hS.short_covers e' he' hl
    · simpa [WExec.measure] using hmeasure
  · rename_i hlen
    refine ⟨⟨hspec.1, ?_, fun e' he' => ?_, fun e' he' hl => ?_, List.nodup_singleton _,
      fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact hlitM', hqueue⟩, ?_⟩
    · exact hstore.consShort (L.id, L.clause) (by simp only; omega)
    · rw [hdb']
      rcases List.mem_cons.1 he' with rfl | he'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hS.short_mem e' he')
    · rw [hdb'] at he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hS.short_covers e' he' hl)
    · simpa [WExec.measure] using hmeasure

/-- Adding a literal over an unassigned variable to the trail and the empty queue. -/
theorem WExec.Inv.push {S S' : WExec φ} (hS : S.Inv) (hq : S.queue = []) {l : Literal ℕ}
    {b : Bool} (hexec : S'.exec.Inv) (hM : S'.M = ⟨l, b⟩ :: S.M) (hq' : S'.queue = [l])
    (hdb : S'.exec.db = S.exec.db) (hstore : S'.store = S.store) (hshort : S'.short = S.short)
    (hundef : l.1 ∉ Trail.vars S.M) : S'.Inv := by
  have hl : l ∉ Trail.lits S.M := fun h => hundef (Trail.mem_vars_of_mem_lits h)
  have hproc : ∀ x, Processed S'.M S'.queue x → Processed S.M S.queue x := by
    intro x ⟨hx, hxq⟩
    rw [hM] at hx
    rw [hq'] at hxq
    exact ⟨(List.mem_cons.1 hx).resolve_left (by simpa using hxq), by simp [hq]⟩
  refine ⟨hexec, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstore, hdb]; exact hS.store.weaken hproc
  · rw [hshort, hdb]; exact hS.short_mem
  · rw [hshort, hdb]; exact hS.short_covers
  · rw [hq']; exact List.nodup_singleton _
  · rw [hq', hM]; intro x hx; rw [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self
  · rw [hq', hM]
    intro x hx N d M₀ hN hxM₀
    rw [List.mem_singleton] at hx
    subst hx
    cases N with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hN
      exact hl (hN.2 ▸ hxM₀)
    | cons y N =>
      simp only [List.cons_append, List.cons.injEq] at hN
      exact hl (hN.2 ▸ lits_below hxM₀)

/-- The measure falls when the rank falls and one literal is queued on an empty queue. -/
theorem WExec.measure_push_lt {S S' : WExec φ} (hq : S.queue = []) (hq' : S'.queue.length = 1)
    (hrank : rank φ.vars S'.exec.state < rank φ.vars S.exec.state) : S'.measure < S.measure := by
  simp only [WExec.measure, hq, hq', List.length_nil]
  nlinarith

/-- **UnitPropagate from a short clause**, at an empty queue. -/
@[expose] def WExec.propagateShort (S : WExec φ) (e : ℕ × Clause ℕ) (l : Literal ℕ) : WExec φ :=
  { S with exec := S.exec.propagate e l, queue := [l] }

/-- **Decide**, at an empty queue. -/
@[expose] def WExec.decide (S : WExec φ) (x : ℕ) : WExec φ :=
  { S with exec := S.exec.decide x, queue := [(x, true)] }

/-- With the queue empty, no clause of the database is false if no short clause is. -/
theorem WExec.Inv.noConflict {S : WExec φ} (hS : S.Inv) (hq : S.queue = [])
    (hshort : ∀ e ∈ S.short, ¬ Trail.Falsifies S.M e.2) :
    ∀ c ∈ S.exec.clauses, ¬ Trail.Falsifies S.M c := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
  by_cases hlen : 2 ≤ e.2.dedup.length
  · exact (hq ▸ hS.store).not_falsifies he hlen
  · exact hshort e (hS.short_covers e he (by omega))

/-- **The CDCL loop with watched literals.** While the queue is not empty, the watch list of the
negation of its first literal is visited; a conflict is analysed, followed by Backjump and Learn,
or ends with a certificate when there is no decision. With the queue empty, the short clauses are
checked for a conflict or a unit, then the first unassigned variable of the database is decided,
or the trail is returned as a model. -/
@[expose] def wloop (φ : CNF ℕ) : (fuel : ℕ) → (S : WExec φ) → S.Inv → S.measure < fuel → Answer φ
  | 0, _, _, hfuel => absurd hfuel (Nat.not_lt_zero _)
  | fuel + 1, S, hS, hfuel =>
    -- a conflict on a database clause
    let onConflict (S : WExec φ) (hS : S.Inv) (e : ℕ × Clause ℕ) (he : e ∈ S.exec.db)
        (hconf : Trail.Falsifies S.M e.2) (hm : S.measure ≤ fuel) : Answer φ :=
      match hsp : XTrail.split S.exec.trail with
      | none =>
        let r := refute S.exec.trail S.exec.log e.1 e.2 (hS.exec.db_log e he) hS.exec.reasons
          (XTrail.split_eq_none hsp) hconf
        .unsat r.cert (LRATLog.checkLRAT_finish r.clause?_eq)
      | some sp =>
        let L := analyze S.exec.log sp.decision sp.below
          (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) sp.above (fun _ h => h) S.exec.log
          (LRATLog.Extends.refl _) e.1 e.2 (hS.exec.db_log e he) (hS.exec.split_reasons hsp)
          (XTrail.split_eq_some hsp).2 (XTrail.falsifies_of_split hsp hconf)
          (hS.exec.split_cur hsp he hconf) (hS.exec.split_nodup hsp)
        have hspec := WExec.afterConflict_spec hS he hconf hsp L
        wloop φ fuel (S.afterConflict sp L) hspec.1 (by omega)
    match hq : S.queue with
    | t :: _ =>
      have ht : t ∈ S.queue := hq ▸ List.mem_cons_self
      match (S.start t).processList t (watchList S.store.watches (watchIndex t.negate))
          (WExec.start_procInv hS ht) with
      | .done S' h hm =>
        have hfin := WExec.finish_inv h
        wloop φ fuel (S'.finish t) hfin.1 (by
          have : (S.start t).measure = S.measure := rfl
          omega)
      | .conflict S' h e he hconf hm =>
        onConflict S' h e he hconf (by have : (S.start t).measure = S.measure := rfl; omega)
    | [] =>
      match hc : S.short.find? (fun e => decide (Trail.Falsifies S.M e.2)) with
      | some e =>
        onConflict S hS e (hS.short_mem e (List.mem_of_find?_eq_some hc))
          (by simpa using List.find?_some hc) (by omega)
      | none =>
        have hshort : ∀ e ∈ S.short, ¬ Trail.Falsifies S.M e.2 := fun e he hf =>
          List.find?_eq_none.1 hc e he (decide_eq_true hf)
        have hnoconf := hS.noConflict hq hshort
        match hu : findUnit S.M S.short with
        | some (e, l) =>
          have ⟨he, hl, hundef, hfalse⟩ := findUnit_spec hu
          have hspec := Exec.propagate_spec' hS.exec (hS.short_mem e he) hl hundef hfalse
          wloop φ fuel (S.propagateShort e l) (hS.push hq hspec.1 rfl rfl rfl rfl rfl hundef)
            (by have := WExec.measure_push_lt (S' := S.propagateShort e l) hq rfl hspec.2; omega)
        | none =>
          match hx : S.exec.clauses.vars.find? (fun x => !(Trail.vars S.M).contains x) with
          | some x =>
            have hundef : x ∉ Trail.vars S.M := by simpa using List.find?_some hx
            have hspec := Exec.decide_spec hS.exec hnoconf (List.mem_of_find?_eq_some hx) hundef
            wloop φ fuel (S.decide x) (hS.push hq hspec.1 rfl rfl rfl rfl rfl hundef)
              (by have := WExec.measure_push_lt (S' := S.decide x) hq rfl hspec.2; omega)
          | none =>
            .sat (Trail.assignment S.M) (hS.exec.run.eval_model hnoconf fun x hxV => by
              simpa using List.find?_eq_none.1 hx x hxV)

/-- **CDCL with watched literals**: the loop from the initial state, with enough fuel. -/
@[expose] def solveWatched (φ : CNF ℕ) : DPLL.Result :=
  match wloop φ ((WExec.init φ).measure + 1) (WExec.init φ) (WExec.init_inv φ)
      (Nat.lt_succ_self _) with
  | .sat σ _ => .sat σ
  | .unsat cert _ => .unsat cert

/-- **The models returned by the watched solver are models.** -/
theorem solveWatched_sat {φ : CNF ℕ} {σ : ℕ → Bool} (h : solveWatched φ = .sat σ) :
    φ.eval σ = true := by
  unfold solveWatched at h
  split at h
  · rename_i hσ _
    cases h
    exact hσ
  · cases h

/-- **The certificates returned by the watched solver are accepted by the LRAT checker.** -/
theorem solveWatched_unsat {φ : CNF ℕ} {cert : Array Std.Tactic.BVDecide.LRAT.IntAction}
    (h : solveWatched φ = .unsat cert) : φ.checkLRAT cert = true := by
  unfold solveWatched at h
  split at h
  · cases h
  · rename_i hcert _
    cases h
    exact hcert

/-- **The watched solver decides satisfiability.** -/
theorem isSat_solveWatched_iff (φ : CNF ℕ) : (solveWatched φ).isSat = true ↔ φ.Satisfiable :=
  DPLL.Result.isSat_iff (fun _ => solveWatched_sat) (fun _ => solveWatched_unsat)

end Cslib.Algorithms.Lean.CDCL
