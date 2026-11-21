/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Resolution.LRAT
import CslibFrontier.Foundations.Data.List.Lookup

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
  if i < a.size then a.set! i x
  -- pushing directly at the end, so that the array is updated in place
  else if i = a.size then a.push x
  else (a ++ Array.replicate (i - a.size) none).push x

theorem getD_optSet {α : Type} (a : Array (Option α)) (i j : ℕ) (x : Option α) :
    (optSet a i x).getD j none = if j = i then x else a.getD j none := by
  unfold optSet
  by_cases hi : i < a.size
  · rw [ite_eq_left hi]
    simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds]
    by_cases hj : j = i
    · subst hj; simp [hi]
    · simp [hj, Ne.symm hj]
  rw [ite_eq_right hi]
  by_cases he : i = a.size
  · rw [ite_eq_left he]
    subst he
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
    by_cases hj : j = a.size <;> simp [hj]
  rw [ite_eq_right he]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.size_append,
    Array.size_replicate, Array.getElem?_append, Array.getElem?_replicate]
  by_cases hj : j = i
  · subst hj; simp only [↓reduceIte]; split <;> first | rfl | omega
  · have h' : ¬ j = a.size + (i - a.size) := by omega
    simp only [hj, h', ↓reduceIte]
    by_cases hlt : j < a.size
    · simp [hlt]
    · simp only [hlt, ↓reduceIte, Array.getElem?_eq_none (by omega : a.size ≤ j)]
      split <;> rfl

/-- **An index in chunks**: the entries by number, in arrays of `256`, so that updating a shared
index copies the array of chunks and one chunk rather than every entry. -/
abbrev Chunks (α : Type) := Array (Array (Option α))

/-- The entry `i` of a chunked index, `none` past the end. -/
def chunkGet {α : Type} (a : Chunks α) (i : ℕ) : Option α :=
  (a.getD (i / 256) #[]).getD (i % 256) none

/-- Setting the entry `i` of a chunked index, growing it if needed. -/
def chunkSet {α : Type} (a : Chunks α) (i : ℕ) (x : Option α) : Chunks α :=
  let k := i / 256
  let a := if k < a.size then a else a ++ Array.replicate (k + 1 - a.size) #[]
  a.modify k fun c => optSet c (i % 256) x

theorem chunkGet_empty {α : Type} (j : ℕ) : chunkGet (#[] : Chunks α) j = none := by
  simp [chunkGet]

theorem chunkGet_chunkSet {α : Type} (a : Chunks α) (i j : ℕ) (x : Option α) :
    chunkGet (chunkSet a i x) j = if j = i then x else chunkGet a j := by
  unfold chunkGet chunkSet
  dsimp only
  generalize ha' : (if i / 256 < a.size then a else a ++ Array.replicate (i / 256 + 1 - a.size) #[])
    = a'
  have hgrow : ∀ k, a'.getD k #[] = a.getD k #[] := fun k => by
    rw [← ha']
    split
    · rfl
    · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.getElem?_replicate]
      split
      · rfl
      · split <;> simp [Array.getElem?_eq_none (by omega : a.size ≤ k)]
  have hsize : i / 256 < a'.size := by
    rw [← ha']
    split
    · assumption
    · simp; omega
  have hdecomp : j = i ↔ j / 256 = i / 256 ∧ j % 256 = i % 256 := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h₁, h₂⟩
      rw [← Nat.div_add_mod j 256, ← Nat.div_add_mod i 256, h₁, h₂]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hk : i / 256 = j / 256
  · rw [ite_eq_left hk, ← hk, Array.getElem?_eq_getElem hsize]
    simp only [Option.map_some, Option.getD_some]
    rw [show (a'[i / 256]'hsize) = a'.getD (i / 256) #[] by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsize], hgrow,
      ← Array.getD_eq_getD_getElem?, getD_optSet]
    by_cases hj : j = i
    · subst hj; simp
    · have : ¬ j % 256 = i % 256 := fun h => hj (hdecomp.2 ⟨hk.symm, h⟩)
      simp only [hj, this, ↓reduceIte, Array.getD_eq_getD_getElem?, hk]
  · rw [ite_eq_right hk]
    have hj : ¬ j = i := fun h => hk (by rw [h])
    simp only [hj, ↓reduceIte]
    have := hgrow (j / 256)
    simp only [Array.getD_eq_getD_getElem?] at this
    rw [this]

/-- Clearing the entry `i` of a chunked index, in place: nothing changes if `i` is past the end. -/
def chunkClear {α : Type} (a : Chunks α) (i : ℕ) : Chunks α :=
  a.modify (i / 256) fun c => c.setIfInBounds (i % 256) none

theorem chunkGet_chunkClear {α : Type} (a : Chunks α) (i j : ℕ) :
    chunkGet (chunkClear a i) j = if j = i then none else chunkGet a j := by
  unfold chunkGet chunkClear
  have hdecomp : j = i ↔ j / 256 = i / 256 ∧ j % 256 = i % 256 := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h₁, h₂⟩
      rw [← Nat.div_add_mod j 256, ← Nat.div_add_mod i 256, h₁, h₂]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hk : i / 256 = j / 256
  · rw [ite_eq_left hk, ← hk]
    cases ha : a[i / 256]? with
    | none => split <;> rfl
    | some c =>
      simp only [Option.map_some, Option.getD_some, Array.getElem?_setIfInBounds]
      by_cases hj : j = i
      · subst hj; simp only [↓reduceIte]; split <;> rfl
      · have : ¬ i % 256 = j % 256 := fun h => hj (hdecomp.2 ⟨hk.symm, h.symm⟩)
        simp [hj, this]
  · rw [ite_eq_right hk]
    have hj : ¬ j = i := fun h => hk (by rw [h])
    simp [hj]

/-- Clearing the entries `is` of a chunked index, in place. -/
theorem chunkGet_foldl_chunkClear {α : Type} (is : List ℕ) (a : Chunks α) (j : ℕ) :
    chunkGet (is.foldl chunkClear a) j = if j ∈ is then none else chunkGet a j := by
  induction is generalizing a with
  | nil => simp
  | cons i is ih =>
    rw [List.foldl_cons, ih, chunkGet_chunkClear]
    by_cases h₁ : j ∈ is <;> by_cases h₂ : j = i <;> simp [h₁, h₂]

/-- The chunked index of numbered clauses: the clause of each number, the first one listed. -/
def chunkIndexOf {α : Type} : List (ℕ × α) → Chunks α
  | [] => #[]
  | e :: db => chunkSet (chunkIndexOf db) e.1 (some e.2)

theorem chunkGet_chunkIndexOf {α : Type} : ∀ (db : List (ℕ × α)) (i : ℕ),
    chunkGet (chunkIndexOf db) i = (db.find? (·.1 == i)).map (·.2)
  | [], i => chunkGet_empty i
  | e :: db, i => by
    rw [chunkIndexOf, chunkGet_chunkSet, chunkGet_chunkIndexOf db i, List.find?_cons]
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
  index : Chunks (Clause ℕ)
  /-- The index names the clauses of the database. -/
  index_eq : ∀ i, chunkGet index i = (db.find? (·.1 == i)).map (·.2)
  /-- The next number is beyond the clauses of `φ`. -/
  next_gt : φ.length < next
  /-- The added clauses come newest first, before the clauses of `φ`. -/
  ordered : db.Pairwise fun a b => φ.length < b.1 → b.1 < a.1

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
  index := chunkIndexOf φ.lratDB
  index_eq := chunkGet_chunkIndexOf φ.lratDB
  next_gt := Nat.lt_succ_self _
  ordered := List.pairwise_of_forall_mem_list fun a _ b hb h => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
    have := List.snd_lt_add_of_mem_zipIdx hp
    simp only at h this
    omega

/-- **The clause numbered `i`**, if any, read from the index. -/
def clause? (log : LRATLog φ) (i : ℕ) : Option (Clause ℕ) := chunkGet log.index i

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
  index := chunkSet log.index log.next (some c)
  index_eq i := by
    rw [chunkGet_chunkSet, log.index_eq, List.find?_cons]
    by_cases h : i = log.next
    · subst h; simp
    · simp only [h, ↓reduceIte]
      rw [show (log.next == i) = false by simpa using Ne.symm h]
  next_gt := by have := log.next_gt; omega
  ordered := List.pairwise_cons.2 ⟨fun b hb _ => log.lt_next b hb, log.ordered⟩

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

/-- **Deleting clauses** from the log, given the database `db'` without them, which the caller
may compute faster than by filtering (`Cslib.Logic.PL.CNF.LRATLog.dropRecent`). An empty list
deletes nothing and adds no step. The index entries are cleared in place (`chunkClear`), so
deleting a number that names no clause does not grow the index. -/
def deleteWith (log : LRATLog φ) (ids : List ℕ) (db' : List (ℕ × Clause ℕ))
    (hdb : db' = log.db.filter fun e => !ids.contains e.1) : LRATLog φ :=
  if ids.isEmpty then log else
  { steps := .del ids.toArray :: log.steps
    db := db'
    next := log.next
    run := fun rest => by
      subst hdb
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [log.run]
      simp [checkLRATAux]
    lt_next := fun e he => log.lt_next e (List.mem_filter.1 (hdb ▸ he)).1
    implied := fun σ hσ e he => log.implied σ hσ e (List.mem_filter.1 (hdb ▸ he)).1
    vars_mem := fun e he => log.vars_mem e (List.mem_filter.1 (hdb ▸ he)).1
    index := ids.foldl chunkClear log.index
    index_eq := fun i => by
      subst hdb
      rw [chunkGet_foldl_chunkClear, log.index_eq, List.find?_filter]
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
        · simp [he]
    next_gt := log.next_gt
    ordered := hdb ▸ log.ordered.filter _ }

/-- **Deleting clauses** from the log. -/
def delete (log : LRATLog φ) (ids : List ℕ) : LRATLog φ := log.deleteWith ids _ rfl

/-- Deleting clauses keeps the clauses of the numbers not deleted. -/
theorem clause?_deleteWith {log : LRATLog φ} {ids : List ℕ} {db' : List (ℕ × Clause ℕ)}
    {hdb : db' = log.db.filter fun e => !ids.contains e.1} {i : ℕ} (hi : i ∉ ids) :
    (log.deleteWith ids db' hdb).clause? i = log.clause? i := by
  unfold deleteWith
  split
  · rfl
  subst hdb
  simp only [clause?_eq, List.find?_filter]
  congr 1
  refine List.find?_congr fun e _ => ?_
  by_cases he : e.1 = i
  · subst he
    simp [hi]
  · simp [he]

/-- Deleting clauses keeps the clauses of the numbers not deleted. -/
theorem clause?_delete {log : LRATLog φ} {ids : List ℕ} {i : ℕ} (hi : i ∉ ids) :
    (log.delete ids).clause? i = log.clause? i :=
  clause?_deleteWith hi

/-- The numbers from `n` to below `next` other than `id`: the intermediate resolvents of a conflict
analysis whose learned clause is numbered `id`. -/
def recentIds (n next id : ℕ) : List ℕ := (List.range' n (next - n)).filter (· != id)

/-- The numbers in `recentIds n next id`: from `n` to below `next`, other than `id`. -/
theorem mem_recentIds {n next id i : ℕ} :
    i ∈ recentIds n next id ↔ n ≤ i ∧ i < next ∧ i ≠ id := by
  simp only [recentIds, List.mem_filter, List.mem_range'_1, bne_iff_ne, ne_eq]
  omega

/-- The database without the clauses numbered from `n` up other than `id`, read from the start
only as long as the numbers are at least `n`: the newest clauses come first. -/
def dropRecent (n id : ℕ) : List (ℕ × Clause ℕ) → List (ℕ × Clause ℕ)
  | [] => []
  | e :: rest =>
    if e.1 < n then e :: rest
    else if e.1 = id then e :: dropRecent n id rest
    else dropRecent n id rest

/-- **Deleting the newest clauses by reading only them**: with the added clauses newest first,
before the clauses of `φ`, and `n` beyond those, `dropRecent` filters out `recentIds`. -/
theorem dropRecent_eq {m n next id : ℕ} (hmn : m < n) :
    ∀ {db : List (ℕ × Clause ℕ)}, db.Pairwise (fun a b => m < b.1 → b.1 < a.1) →
      (∀ e ∈ db, e.1 < next) →
      dropRecent n id db = db.filter fun e => !(recentIds n next id).contains e.1
  | [], _, _ => rfl
  | e :: rest, hord, hlt => by
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.1 hord
    have hnot : ∀ i, i < n → i ∉ recentIds n next id := fun i hi h => by
      have := (mem_recentIds.1 h).1
      omega
    unfold dropRecent
    by_cases he : e.1 < n
    · rw [ite_eq_left he, List.filter_cons, ite_eq_left (by simpa using hnot _ he)]
      congr 1
      symm
      refine List.filter_eq_self.2 fun b hb => ?_
      have : b.1 < n := by
        by_cases hb' : m < b.1
        · exact lt_trans (hhead b hb hb') he
        · omega
      simpa using hnot _ this
    · rw [ite_eq_right he]
      have ih := dropRecent_eq (id := id) hmn hrest fun b hb => hlt b (List.mem_cons_of_mem _ hb)
      have hmem : e.1 ∈ recentIds n next id ↔ e.1 ≠ id := by
        have := hlt e List.mem_cons_self
        rw [mem_recentIds]
        omega
      by_cases hid : e.1 = id
      · rw [ite_eq_left hid, List.filter_cons, ite_eq_left (by simpa [hmem] using hid), ih]
      · rw [ite_eq_right hid, List.filter_cons, ite_eq_right (by simpa [hmem] using hid), ih]

/-- **Deleting the intermediate resolvents** of an analysis that started at the number `n`, beyond
the clauses of `φ`, and learned the clause numbered `id`: as `delete`, reading only the newest
clauses of the database. -/
def deleteRecent (log : LRATLog φ) (n id : ℕ) (hn : φ.length < n) : LRATLog φ :=
  log.deleteWith (recentIds n log.next id) (dropRecent n id log.db)
    (dropRecent_eq hn log.ordered log.lt_next)

/-- Deleting the intermediate resolvents keeps the clauses of the other numbers. -/
theorem clause?_deleteRecent {log : LRATLog φ} {n id : ℕ} {hn : φ.length < n} {i : ℕ}
    (hi : i ∉ recentIds n log.next id) : (log.deleteRecent n id hn).clause? i = log.clause? i :=
  clause?_deleteWith hi

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
  rw [log.clause?_eq h, List.lookup_eq_map_find?]
  exact congrArg _ (congrArg (List.find? · _) (funext fun _ => BEq.comm))

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
