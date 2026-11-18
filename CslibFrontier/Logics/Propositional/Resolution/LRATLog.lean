/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Resolution.LRAT

/-! # LRAT certificates built by resolution, step by step

A solver that learns clauses builds its certificate as it runs. `Cslib.Logic.PL.CNF.LRATLog φ` is a
certificate under construction for `φ`: the steps so far, the numbered clauses they lead to, an
index of them by number, which `Cslib.Logic.PL.CNF.LRATLog.clause?` reads in constant time
instead of searching the database (`Cslib.Logic.PL.CNF.LRATLog.clause?_eq`), and the next unused
number, together with the facts that
the checker passes the steps (`Cslib.Logic.PL.CNF.LRATLog.run`) and that every clause of the
database holds in every model of `φ` (`Cslib.Logic.PL.CNF.LRATLog.implied`).

The log grows by resolution (`Cslib.Logic.PL.CNF.LRATLog.resolve`): the resolvent of two clauses of
the database is added under the next number, as a RUP step hinting the two
(`Cslib.Logic.PL.CNF.propagateHints_resolvent`). A resolvent of any two clauses is a RUP clause of
them, whether or not the variable occurs in them with opposite signs, so every resolution step keeps
the log correct, and a solver that learns clauses by resolution needs no further proof that its
certificate is accepted. Any clause with the literals of the resolvent will do, for instance one
without repeated literals (`Cslib.Logic.PL.CNF.LRATLog.addResolventAs`), since unit propagation
reads the negated clause only through membership (`Cslib.Logic.PL.CNF.propagateHints_congr`). Any
RUP clause can be added with its hints, once the checker's unit propagation has succeeded on them
(`Cslib.Logic.PL.CNF.LRATLog.addRup`), which `Cslib.Logic.PL.CNF.LRATLog.propagate` runs on the
index. Clauses can be deleted (`Cslib.Logic.PL.CNF.LRATLog.delete`), which clears their index
entries in place but still filters the database list. Once the database contains the
empty clause, closing the log with an empty-clause step hinting it gives a certificate that the
checker accepts (`Cslib.Logic.PL.CNF.LRATLog.checkLRAT_finish`).

## Main definitions

* `Cslib.Logic.PL.CNF.LRATLog`: a certificate under construction.
* `Cslib.Logic.PL.CNF.LRATLog.init`, `Cslib.Logic.PL.CNF.LRATLog.resolve`,
  `Cslib.Logic.PL.CNF.LRATLog.addRup`, `Cslib.Logic.PL.CNF.LRATLog.delete`,
  `Cslib.Logic.PL.CNF.LRATLog.finish`: starting, resolving, adding a RUP clause, deleting and
  closing.

## Main results

* `Cslib.Logic.PL.CNF.LRATLog.checkLRAT_finish`: a closed log is accepted by the checker.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

open Std.Tactic.BVDecide (LRAT.IntAction)

/-- Setting the entry `i` of an array of options to `x`, growing the array with `none` if needed. -/
def optSet {α : Type} (a : Array (Option α)) (i : ℕ) (x : Option α) : Array (Option α) :=
  if i < a.size then a.set! i x else (a ++ Array.replicate (i - a.size) none).push x

theorem getD_optSet {α : Type} (a : Array (Option α)) (i j : ℕ) (x : Option α) :
    (optSet a i x).getD j none = if j = i then x else a.getD j none := by
  unfold optSet
  split
  · rename_i hi
    simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds]
    by_cases hj : j = i
    · subst hj; simp [hi]
    · simp [hj, Ne.symm hj]
  · rename_i hi
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.size_append,
      Array.size_replicate, Array.getElem?_append, Array.getElem?_replicate]
    by_cases hj : j = i
    · subst hj; simp only [↓reduceIte]; split <;> first | rfl | omega
    · have : ¬ j = a.size + (i - a.size) := by omega
      simp only [hj, this, ↓reduceIte]
      by_cases hlt : j < a.size
      · simp [hlt]
      · simp only [hlt, ↓reduceIte, Array.getElem?_eq_none (by omega : a.size ≤ j)]
        split <;> rfl

/-- Clearing the entries `is` within the bounds of the array. -/
theorem getD_foldl_setIfInBounds_none {α : Type} (is : List ℕ) (a : Array (Option α)) (j : ℕ) :
    (is.foldl (fun a i => a.setIfInBounds i none) a).getD j none =
      if j ∈ is then none else a.getD j none := by
  induction is generalizing a with
  | nil => simp
  | cons i is ih =>
    rw [List.foldl_cons, ih]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, List.mem_cons]
    by_cases h₁ : j ∈ is <;> by_cases h₂ : j = i
    · simp [h₁]
    · simp [h₁]
    · subst h₂; simp [h₁]; split <;> rfl
    · simp [h₁, h₂, Ne.symm h₂]

/-- The index of numbered clauses: the clause of each number, the first one listed. -/
def indexOf {α : Type} : List (ℕ × α) → Array (Option α)
  | [] => #[]
  | e :: db => optSet (indexOf db) e.1 (some e.2)

theorem getD_indexOf {α : Type} : ∀ (db : List (ℕ × α)) (i : ℕ),
    (indexOf db).getD i none = (db.find? (·.1 == i)).map (·.2)
  | [], i => by simp [indexOf]
  | e :: db, i => by
    rw [indexOf, getD_optSet, getD_indexOf db i, List.find?_cons]
    by_cases h : i = e.1
    · subst h; simp
    · simp only [h, ↓reduceIte]
      rw [show (e.1 == i) = false by simpa using Ne.symm h]

/-- **A certificate under construction** for `φ`: the steps so far, newest first, the numbered
clauses they lead to, indexed by number, and the next unused number. -/
structure LRATLog (φ : CNF ℕ) where
  /-- The steps so far, newest first. -/
  steps : List LRAT.IntAction
  /-- The numbered clauses after the steps. -/
  db : List (ℕ × Clause ℕ)
  /-- The first number not yet used. -/
  next : ℕ
  /-- The checker passes the steps and reaches the database. -/
  run : ∀ rest, checkLRATAux φ.lratDB (steps.reverse ++ rest) = checkLRATAux db rest
  /-- Every number in the database is below `next`. -/
  lt_next : ∀ e ∈ db, e.1 < next
  /-- Every clause of the database holds in every model of `φ`. -/
  implied : ∀ σ, φ.eval σ = true → ∀ e ∈ db, e.2.eval σ = true
  /-- Every clause of the database uses variables of `φ`. -/
  vars_mem : ∀ e ∈ db, ∀ l ∈ e.2, l.1 ∈ φ.vars
  /-- The clauses of the database by number, `none` past the end. -/
  index : Array (Option (Clause ℕ))
  /-- The index names the clauses of the database. -/
  index_eq : ∀ i, index.getD i none = (db.find? (·.1 == i)).map (·.2)

namespace LRATLog

variable {φ : CNF ℕ}

/-- The empty log: the clauses of `φ`, numbered from `1`. -/
def init (φ : CNF ℕ) : LRATLog φ where
  steps := []
  db := φ.lratDB
  next := φ.length + 1
  run _ := rfl
  lt_next e he := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    have := List.snd_lt_add_of_mem_zipIdx hp
    simp only at this ⊢
    omega
  implied σ hσ e he := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact (CNF.eval_eq_true_iff σ φ).1 hσ _
      (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp))
  vars_mem e he l hl := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact CNF.mem_vars.2 ⟨_, List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp), l.2, hl⟩
  index := indexOf φ.lratDB
  index_eq := getD_indexOf φ.lratDB

/-- **The clause numbered `i`**, if any, read from the index. -/
def clause? (log : LRATLog φ) (i : ℕ) : Option (Clause ℕ) := log.index.getD i none

/-- The clause numbered `i` is the first of that number in the database. -/
theorem clause?_eq (log : LRATLog φ) (i : ℕ) :
    log.clause? i = (log.db.find? (·.1 == i)).map (·.2) :=
  log.index_eq i

theorem find?_of_clause? {log : LRATLog φ} {i : ℕ} {c : Clause ℕ} (h : log.clause? i = some c) :
    log.db.find? (·.1 == i) = some (i, c) := by
  simp only [clause?_eq, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have := List.find?_some he
  simp only [beq_iff_eq] at this
  rw [he, ← this]

/-- A clause of the log uses variables of `φ`. -/
theorem vars_mem_of_clause? {log : LRATLog φ} {i : ℕ} {c : Clause ℕ} (h : log.clause? i = some c) :
    ∀ l ∈ c, l.1 ∈ φ.vars :=
  log.vars_mem (i, c) (List.mem_of_find?_eq_some (find?_of_clause? h))

/-- A clause of the log holds in every model of `φ`. -/
theorem eval_of_clause? {log : LRATLog φ} {i : ℕ} {c : Clause ℕ} (h : log.clause? i = some c)
    {σ : ℕ → Bool} (hσ : φ.eval σ = true) : c.eval σ = true :=
  log.implied σ hσ (i, c) (List.mem_of_find?_eq_some (find?_of_clause? h))

/-- A log extends another if every number of the other still names the same clause. -/
def Extends (log log' : LRATLog φ) : Prop :=
  ∀ i c, log.clause? i = some c → log'.clause? i = some c

theorem Extends.refl (log : LRATLog φ) : log.Extends log := fun _ _ h => h

theorem Extends.trans {log₁ log₂ log₃ : LRATLog φ} (h₁ : log₁.Extends log₂)
    (h₂ : log₂.Extends log₃) : log₁.Extends log₃ := fun i c h => h₂ i c (h₁ i c h)

/-- A number naming a clause is below `next`. -/
theorem lt_next_of_clause? {log : LRATLog φ} {i : ℕ} {c : Clause ℕ} (h : log.clause? i = some c) :
    i < log.next :=
  log.lt_next (i, c) (List.mem_of_find?_eq_some (find?_of_clause? h))

/-- **Adding a RUP clause**: `c`, over variables of `φ`, under the next number, hinting `hints`,
given that unit propagation along the hints from the negation of `c` reaches a conflict. -/
def addRup (log : LRATLog φ) (c : Clause ℕ) (hints : List ℕ)
    (hprop : propagateHints log.db (c.map Std.Sat.Literal.negate) hints = true)
    (hvars : ∀ l ∈ c, l.1 ∈ φ.vars) : LRATLog φ where
  steps := .addRup log.next c.toDIMACS hints.toArray :: log.steps
  db := (log.next, c) :: log.db
  next := log.next + 1
  run rest := by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [log.run]
    simp only [checkLRATAux, Clause.ofDIMACS_toDIMACS, hprop, Bool.true_and]
  lt_next e he := by
    rcases List.mem_cons.1 he with rfl | he
    · simp
    · have := log.lt_next e he; omega
  implied σ hσ e he := by
    rcases List.mem_cons.1 he with rfl | he
    · exact eval_of_propagateHints (log.implied σ hσ) hprop
    · exact log.implied σ hσ e he
  vars_mem e he l hl := by
    rcases List.mem_cons.1 he with rfl | he
    · exact hvars l hl
    · exact log.vars_mem e he l hl
  index := optSet log.index log.next (some c)
  index_eq i := by
    rw [getD_optSet, log.index_eq, List.find?_cons]
    by_cases h : i = log.next
    · subst h; simp
    · simp only [h, ↓reduceIte]
      rw [show (log.next == i) = false by simpa using Ne.symm h]

/-- After adding a RUP clause, the new number names it. -/
theorem clause?_addRup {log : LRATLog φ} {c : Clause ℕ} {hints : List ℕ}
    {hprop : propagateHints log.db (c.map Std.Sat.Literal.negate) hints = true}
    {hvars : ∀ l ∈ c, l.1 ∈ φ.vars} :
    (log.addRup c hints hprop hvars).clause? log.next = some c := by
  simp [clause?_eq, addRup]

/-- Adding a RUP clause extends the log. -/
theorem extends_addRup {log : LRATLog φ} {c : Clause ℕ} {hints : List ℕ}
    {hprop : propagateHints log.db (c.map Std.Sat.Literal.negate) hints = true}
    {hvars : ∀ l ∈ c, l.1 ∈ φ.vars} : log.Extends (log.addRup c hints hprop hvars) := by
  intro i c' h
  have hi := lt_next_of_clause? h
  rw [clause?_eq] at h ⊢
  simp only [addRup, List.find?_cons]
  rw [show (log.next == i) = false by simp; omega]
  exact h

/-- Adding a clause `c` with the literals of the resolvent of the clauses numbered `i₁` and `i₂` on
`v`, given those clauses, for instance the resolvent without repeated literals: a RUP step hinting
the two clauses (`Cslib.Logic.PL.CNF.LRATLog.addRup`). -/
def addResolventAs (log : LRATLog φ) (i₁ i₂ v : ℕ) (c₁ c₂ : Clause ℕ)
    (h₁ : log.clause? i₁ = some c₁) (h₂ : log.clause? i₂ = some c₂) (c : Clause ℕ)
    (hc : ∀ l, l ∈ c ↔ l ∈ c₁.resolvent c₂ v) : LRATLog φ :=
  log.addRup c [i₁, i₂]
    (by
      have hprop := propagateHints_resolvent (v := v) (find?_of_clause? h₁) (find?_of_clause? h₂)
      rw [propagateHints_congr _ (t' := c.map Std.Sat.Literal.negate) (fun l => by
        simp only [List.mem_map, hc])] at hprop
      exact hprop)
    fun l hl => by
      rcases Clause.mem_resolvent.1 ((hc l).1 hl) with ⟨hl, -⟩ | ⟨hl, -⟩
      · exact vars_mem_of_clause? h₁ l hl
      · exact vars_mem_of_clause? h₂ l hl

/-- After adding a clause with the literals of a resolvent, the new number names it. -/
theorem clause?_addResolventAs {log : LRATLog φ} {i₁ i₂ v : ℕ} {c₁ c₂ : Clause ℕ}
    {h₁ : log.clause? i₁ = some c₁} {h₂ : log.clause? i₂ = some c₂} {c : Clause ℕ}
    {hc : ∀ l, l ∈ c ↔ l ∈ c₁.resolvent c₂ v} :
    (log.addResolventAs i₁ i₂ v c₁ c₂ h₁ h₂ c hc).clause? log.next = some c :=
  clause?_addRup

/-- Adding a clause with the literals of a resolvent extends the log. -/
theorem extends_addResolventAs {log : LRATLog φ} {i₁ i₂ v : ℕ} {c₁ c₂ : Clause ℕ}
    {h₁ : log.clause? i₁ = some c₁} {h₂ : log.clause? i₂ = some c₂} {c : Clause ℕ}
    {hc : ∀ l, l ∈ c ↔ l ∈ c₁.resolvent c₂ v} :
    log.Extends (log.addResolventAs i₁ i₂ v c₁ c₂ h₁ h₂ c hc) :=
  extends_addRup

/-- Adding the resolvent of the clauses numbered `i₁` and `i₂` on `v`, given those clauses. -/
def addResolvent (log : LRATLog φ) (i₁ i₂ v : ℕ) (c₁ c₂ : Clause ℕ)
    (h₁ : log.clause? i₁ = some c₁) (h₂ : log.clause? i₂ = some c₂) : LRATLog φ :=
  log.addResolventAs i₁ i₂ v c₁ c₂ h₁ h₂ (c₁.resolvent c₂ v) fun _ => Iff.rfl

/-- After adding a resolvent, the new number names it. -/
theorem clause?_addResolvent {log : LRATLog φ} {i₁ i₂ v : ℕ} {c₁ c₂ : Clause ℕ}
    (h₁ : log.clause? i₁ = some c₁) (h₂ : log.clause? i₂ = some c₂) :
    (log.addResolvent i₁ i₂ v c₁ c₂ h₁ h₂).clause? log.next = some (c₁.resolvent c₂ v) :=
  clause?_addResolventAs

/-- Adding a resolvent extends the log. -/
theorem extends_addResolvent {log : LRATLog φ} {i₁ i₂ v : ℕ} {c₁ c₂ : Clause ℕ}
    (h₁ : log.clause? i₁ = some c₁) (h₂ : log.clause? i₂ = some c₂) :
    log.Extends (log.addResolvent i₁ i₂ v c₁ c₂ h₁ h₂) :=
  extends_addResolventAs

/-- **Resolving two clauses of the log**: the resolvent of the clauses numbered `i₁` and `i₂` on
`v`, added under the next number, which is returned with the new log; `none` if a number names no
clause. -/
def resolve (log : LRATLog φ) (i₁ i₂ v : ℕ) : Option (LRATLog φ × ℕ) :=
  match h₁ : log.clause? i₁, h₂ : log.clause? i₂ with
  | some c₁, some c₂ => some (log.addResolvent i₁ i₂ v c₁ c₂ h₁ h₂, log.next)
  | _, _ => none

/-- After resolving, the new number names the resolvent. -/
theorem clause?_resolve {log log' : LRATLog φ} {i₁ i₂ v j : ℕ} {c₁ c₂ : Clause ℕ}
    (h₁ : log.clause? i₁ = some c₁) (h₂ : log.clause? i₂ = some c₂)
    (h : log.resolve i₁ i₂ v = some (log', j)) : log'.clause? j = some (c₁.resolvent c₂ v) := by
  unfold resolve at h
  split at h
  · rename_i c₁' c₂' h₁' h₂'
    rw [h₁] at h₁'
    rw [h₂] at h₂'
    cases h₁'
    cases h₂'
    cases h
    exact clause?_addResolvent _ _
  · simp at h

/-- After resolving, the older numbers name the same clauses. -/
theorem clause?_resolve_of_lt {log log' : LRATLog φ} {i₁ i₂ v j i : ℕ}
    (h : log.resolve i₁ i₂ v = some (log', j)) (hi : i < log.next) :
    log'.clause? i = log.clause? i := by
  unfold resolve at h
  split at h
  · cases h
    simp only [clause?_eq, addResolvent, addResolventAs, addRup, List.find?_cons]
    rw [show (log.next == i) = false by simp; omega]
  · simp at h

/-- Resolving succeeds when both numbers name clauses. -/
theorem isSome_resolve {log : LRATLog φ} {i₁ i₂ v : ℕ} {c₁ c₂ : Clause ℕ}
    (h₁ : log.clause? i₁ = some c₁) (h₂ : log.clause? i₂ = some c₂) :
    log.resolve i₁ i₂ v = some (log.addResolvent i₁ i₂ v c₁ c₂ h₁ h₂, log.next) := by
  unfold resolve
  split
  · rename_i c₁' c₂' h₁' h₂'
    rw [h₁] at h₁'
    rw [h₂] at h₂'
    cases h₁'
    cases h₂'
    rfl
  · rename_i hne
    exact absurd h₂ (hne c₁ c₂ h₁)

/-- **Deleting** the clauses numbered `ids`, with a deletion step. An empty list deletes nothing
and adds no step. The index entries are cleared in place, so deleting a number that names no
clause does not grow the index. -/
def delete (log : LRATLog φ) (ids : List ℕ) : LRATLog φ :=
  if ids.isEmpty then log else
  { steps := .del ids.toArray :: log.steps
    db := log.db.filter fun e => !ids.contains e.1
    next := log.next
    run := fun rest => by
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [log.run]
      simp [checkLRATAux]
    lt_next := fun e he => log.lt_next e (List.mem_filter.1 he).1
    implied := fun σ hσ e he => log.implied σ hσ e (List.mem_filter.1 he).1
    vars_mem := fun e he => log.vars_mem e (List.mem_filter.1 he).1
    index := ids.foldl (fun a i => a.setIfInBounds i none) log.index
    index_eq := fun i => by
      rw [getD_foldl_setIfInBounds_none, log.index_eq, List.find?_filter]
      split
      · rename_i hi
        symm
        rw [Option.map_eq_none_iff, List.find?_eq_none]
        intro e _
        by_cases he : e.1 = i
        · subst he; simp [hi]
        · simp [he]
      · rename_i hi
        congr 1
        refine (List.find?_congr fun e _ => ?_).symm
        by_cases he : e.1 = i
        · subst he; simp [hi]
        · simp [he] }

/-- Deleting clauses keeps the clauses of the numbers not deleted. -/
theorem clause?_delete {log : LRATLog φ} {ids : List ℕ} {i : ℕ} (hi : i ∉ ids) :
    (log.delete ids).clause? i = log.clause? i := by
  unfold delete
  split
  · rfl
  simp only [clause?_eq, List.find?_filter]
  congr 1
  refine List.find?_congr fun e _ => ?_
  by_cases he : e.1 = i
  · subst he
    simp [hi]
  · simp [he]

/-- **Unit propagation along hints on the log's database**, as `propagateHints`, reading the
hinted clauses from the index: the same worker (`Cslib.Logic.PL.CNF.propagateWith`) with another
lookup. -/
def propagate (log : LRATLog φ) : List (Literal ℕ) → List ℕ → Bool :=
  propagateWith log.clause?

theorem propagate_eq (log : LRATLog φ) (t : List (Literal ℕ)) (hs : List ℕ) :
    log.propagate t hs = propagateHints log.db t hs := by
  unfold propagate propagateHints
  congr 1
  funext h
  exact log.clause?_eq h

/-- **Closing the log** at the empty clause, numbered `i`: its steps followed by an empty-clause
step hinting it. -/
def finish (log : LRATLog φ) (i : ℕ) (_h : log.clause? i = some []) : Array LRAT.IntAction :=
  (log.steps.reverse ++ [Std.Tactic.BVDecide.LRAT.Action.addEmpty log.next #[i]]).toArray

/-- **A log closed at the empty clause is accepted by the checker.** -/
theorem checkLRAT_finish {log : LRATLog φ} {i : ℕ} (h : log.clause? i = some []) :
    φ.checkLRAT (log.finish i h) = true := by
  rw [checkLRAT, finish, List.toList_toArray, log.run]
  simp [checkLRATAux, propagateHints_cons, find?_of_clause? h]

end LRATLog

end Cslib.Logic.PL.CNF
