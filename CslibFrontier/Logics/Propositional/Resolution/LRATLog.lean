/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Resolution.LRAT
public import CslibFrontier.Foundations.Data.Array.SetGrow

/-! # LRAT certificates built step by step

A solver that learns clauses builds its certificate as it runs. `Cslib.Logic.PL.CNF.LRATLog φ` is a
certificate under construction for `φ`: the steps so far, the numbered clauses they lead to, an
index of them by number, which `Cslib.Logic.PL.CNF.LRATLog.clause?` reads in constant time
instead of searching the database (`Cslib.Logic.PL.CNF.LRATLog.clause?_eq`), and the next unused
number, together with the facts that the checker passes the steps
(`Cslib.Logic.PL.CNF.LRATLog.run`) and that every clause of the database holds in every model of
`φ` (`Cslib.Logic.PL.CNF.LRATLog.implied`).

The log grows by RUP steps (`Cslib.Logic.PL.CNF.LRATLog.addRup`): a clause is added under the next
number with hints along which the checker's unit propagation, from the negation of the clause,
reaches a conflict. A solver that learns clauses by resolution can build those hints without
building the resolvents (`Cslib.Logic.PL.CNF.RupHints`): the hints refuting a clause, after a clause
`R` of the database, refute any clause containing its resolvent with `R`
(`Cslib.Logic.PL.CNF.RupHints.resolve`), since `R` then propagates the literal resolved on. Chaining
this from a conflict clause gives the hints of the clause learned from it, with no step for the
intermediate resolvents. Clauses can be deleted (`Cslib.Logic.PL.CNF.LRATLog.delete`), which clears
their index entries in place but still filters the database list. Closing the log with an
empty-clause step, given hints refuting the empty clause, gives a certificate that the checker
accepts (`Cslib.Logic.PL.CNF.LRATLog.checkLRAT_finish`).

## Main definitions

* `Cslib.Logic.PL.CNF.LRATLog`: a certificate under construction.
* `Cslib.Logic.PL.CNF.LRATLog.init`, `Cslib.Logic.PL.CNF.LRATLog.addRup`,
  `Cslib.Logic.PL.CNF.LRATLog.delete`, `Cslib.Logic.PL.CNF.LRATLog.finish`: starting, adding a RUP
  clause, deleting and closing.
* `Cslib.Logic.PL.CNF.RupHints`: hints refuting every clause containing given literals.

## Main results

* `Cslib.Logic.PL.CNF.LRATLog.checkLRAT_finish`: a closed log is accepted by the checker.
* `Cslib.Logic.PL.CNF.RupHints.resolve`: resolving with a clause of the database extends the hints.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

open Std.Tactic.BVDecide (LRAT.IntAction)

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
  a.modify k fun c => c.setGrow (i % 256) none x

theorem chunkGet_empty {α : Type} (j : ℕ) : chunkGet (#[] : Chunks α) j = none := by
  simp [chunkGet]

private theorem lrat_nat_eq_iff_div_mod_256 (j i : ℕ) :
    j = i ↔ j / 256 = i / 256 ∧ j % 256 = i % 256 := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  rw [← Nat.div_add_mod j 256, ← Nat.div_add_mod i 256, h₁, h₂]

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
  have hdecomp := lrat_nat_eq_iff_div_mod_256 j i
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hk : i / 256 = j / 256
  · rw [ite_eq_left hk, ← hk, Array.getElem?_eq_getElem hsize]
    simp only [Option.map_some, Option.getD_some]
    have ha_get : a'[i / 256]'hsize = a'.getD (i / 256) #[] := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsize]
    rw [ha_get, hgrow, ← Array.getD_eq_getD_getElem?, Array.getD_setGrow]
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
  have hdecomp := lrat_nat_eq_iff_div_mod_256 j i
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

/-! ### Hints built by resolution -/

/-- A hinted clause whose literals other than `l` are false propagates `l`: the shared rule
`Cslib.Logic.PL.CNF.propagateHints_cons_of_forall_ne`, with propagation from `l` succeeding. -/
theorem propagateHints_cons_unit {db : List (ℕ × Clause ℕ)} {t : List (Literal ℕ)} {r : ℕ}
    {hs : List ℕ} {R : Clause ℕ} {l : Literal ℕ} (hR : db.find? (·.1 == r) = some (r, R))
    (hfalse : ∀ y ∈ R, y ≠ l → y.negate ∈ t) (h : propagateHints db (l :: t) hs = true) :
    propagateHints db t (r :: hs) = true :=
  propagateHints_cons_of_forall_ne hR hfalse fun _ _ => h

/-- **Unit propagation along hints succeeds from more literals.** A clause with no open literal
from `t` has none from `t'`, and one with the single open literal `l` from `t` has its other
literals false under `t'`, so the shared rule applies. -/
theorem propagateHints_mono {db : List (ℕ × Clause ℕ)} :
    ∀ {t t' : List (Literal ℕ)} {hs : List ℕ}, (∀ l ∈ t, l ∈ t') →
      propagateHints db t hs = true → propagateHints db t' hs = true
  | _, _, [], _, h => by simp [propagateHints_nil] at h
  | t, t', i :: hs, ht, h => by
    rw [propagateHints_cons] at h
    cases hf : db.find? (·.1 == i) with
    | none => simp [hf] at h
    | some e =>
      simp only [hf] at h
      cases hr : e.2.residual t with
      | empty =>
        have hall := Clause.residual_eq_empty_iff.1 hr
        exact propagateHints_cons_of_forall_ne (l := (0, true)) hf
          (fun m hm _ => ht _ (hall m hm)) fun hl hn => absurd (ht _ (hall _ hl)) hn
      | unit l =>
        obtain ⟨-, -, hothers⟩ := Clause.residual_eq_unit_iff.1 hr
        rw [hr] at h
        exact propagateHints_cons_of_forall_ne hf (fun m hm hne => ht _ (hothers m hm hne))
          fun _ _ => propagateHints_mono (fun x hx => by
            rcases List.mem_cons.1 hx with rfl | hx
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ht x hx)) h
      | other => simp [hr] at h

/-- **Hints refuting the clauses containing `C`**: from the negation of any clause containing the
literals `C`, unit propagation along `hints` in `db` reaches a conflict. -/
def RupHints (db : List (ℕ × Clause ℕ)) (C : Literal ℕ → Prop) (hints : List ℕ) : Prop :=
  ∀ t : List (Literal ℕ), (∀ y, C y → y.negate ∈ t) → propagateHints db t hints = true

namespace RupHints

variable {db : List (ℕ × Clause ℕ)} {C C' : Literal ℕ → Prop} {hints : List ℕ}

/-- A clause of the database hints its own refutation. -/
theorem single {i : ℕ} {c : Clause ℕ} (hc : db.find? (·.1 == i) = some (i, c)) (hC : ∀ y ∈ c, C y) :
    RupHints db C [i] := fun _ ht =>
  propagateHints_cons_of_forall_ne (l := (0, true)) hc (fun m hm _ => ht m (hC m hm))
    fun hl hn => absurd (ht _ (hC _ hl)) hn

/-- Hints refuting the clauses containing `C` refute those containing more. -/
theorem mono (h : RupHints db C hints) (hC : ∀ y, C y → C' y) : RupHints db C' hints :=
  fun t ht => h t fun y hy => ht y (hC y hy)

/-- **Resolving with a clause of the database**: if `C'` contains every literal of the clause `R`
numbered `r` other than `l`, and every literal of `C` other than the negation of `l`, then the hints
refuting `C`, after `r`, refute `C'`: the clause `R` propagates `l`, and then the negation of `C`
holds. -/
theorem resolve (h : RupHints db C hints) {r : ℕ} {R : Clause ℕ} {l : Literal ℕ}
    (hR : db.find? (·.1 == r) = some (r, R)) (hRC : ∀ y ∈ R, y ≠ l → C' y)
    (hC : ∀ y, C y → y = l.negate ∨ C' y) : RupHints db C' (r :: hints) := fun t ht =>
  propagateHints_cons_unit hR (fun y hy hne => ht y (hRC y hy hne)) <| h _ fun y hy => by
    rcases hC y hy with rfl | hy
    · simp [Std.Sat.Literal.negate]
    · exact List.mem_cons_of_mem _ (ht y hy)

/-- Hints refuting the clauses containing `C` refute a clause `D` containing `C` as a RUP step. -/
theorem propagateHints_eq (h : RupHints db C hints) {D : Clause ℕ} (hD : ∀ y, C y → y ∈ D) :
    propagateHints db (D.map Std.Sat.Literal.negate) hints = true :=
  h _ fun y hy => List.mem_map.2 ⟨y, hD y hy, rfl⟩

end RupHints

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

/-- Marking each number of `ids` in `a`: a mark within the array is set when its number is in
`ids`; the array keeps its size. -/
private theorem getD_foldl_setTrue (ids : List ℕ) (a : Array Bool) (i : ℕ) :
    (ids.foldl (fun a j => a.setIfInBounds j true) a).getD i false =
      (a.getD i false || (decide (i < a.size) && ids.contains i)) := by
  induction ids generalizing a with
  | nil => simp
  | cons j ids ih =>
    rw [List.foldl_cons, ih, Array.size_setIfInBounds]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, List.contains_cons]
    by_cases hij : j = i
    · subst hij; by_cases hi : j < a.size <;> simp [hi]
    · simp [hij, show (i == j) = false from beq_false_of_ne (Ne.symm hij)]

private theorem le_foldl_max {ids : List ℕ} {i : ℕ} :
    ∀ m, i ∈ ids ∨ i ≤ m → i ≤ ids.foldl max m := by
  induction ids with
  | nil => intro m h; simpa using h
  | cons j ids ih =>
    intro m h
    refine ih _ ?_
    rcases h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inr (le_max_right _ _)
      · exact .inl h
    · exact .inr (le_max_of_le_left h)

/-- **The numbered clauses `db` without those numbered in `ids`**: the clauses whose number is
not in `ids` (`eraseIds_eq`). The numbers are marked once, in an array reaching the greatest of
them, so that each clause is tested in constant time instead of by searching `ids`. -/
def eraseIds (db : List (ℕ × Clause ℕ)) (ids : List ℕ) : List (ℕ × Clause ℕ) :=
  let marks := ids.foldl (fun a i => a.setIfInBounds i true)
    (Array.replicate (ids.foldl max 0 + 1) false)
  db.filter fun e => !marks.getD e.1 false

theorem eraseIds_eq (db : List (ℕ × Clause ℕ)) (ids : List ℕ) :
    eraseIds db ids = db.filter fun e => !ids.contains e.1 := by
  unfold eraseIds
  refine List.filter_congr fun e _ => ?_
  rw [getD_foldl_setTrue]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, Array.size_replicate]
  by_cases hi : e.1 < ids.foldl max 0 + 1
  · simp [hi]
  · have : e.1 ∉ ids := fun h => hi (Nat.lt_succ_of_le (le_foldl_max 0 (.inl h)))
    simp [hi, this]

/-- **Deleting clauses** from the log. An empty list deletes nothing and adds no step. The index
entries are cleared in place (`chunkClear`), so deleting a number that names no clause does not
grow the index. -/
def delete (log : LRATLog φ) (ids : List ℕ) : LRATLog φ :=
  if ids.isEmpty then log else
  { steps := .del ids.toArray :: log.steps
    db := eraseIds log.db ids
    next := log.next
    run := fun rest => by
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [log.run, eraseIds_eq]
      simp [checkLRATAux]
    lt_next := fun e he => log.lt_next e (List.mem_filter.1 (eraseIds_eq _ _ ▸ he)).1
    implied := fun σ hσ e he => log.implied σ hσ e (List.mem_filter.1 (eraseIds_eq _ _ ▸ he)).1
    vars_mem := fun e he => log.vars_mem e (List.mem_filter.1 (eraseIds_eq _ _ ▸ he)).1
    index := ids.foldl chunkClear log.index
    index_eq := fun i => by
      rw [chunkGet_foldl_chunkClear, log.index_eq, eraseIds_eq, List.find?_filter]
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
    ordered := eraseIds_eq log.db ids ▸ log.ordered.filter _ }

/-- Deleting clauses keeps the clauses of the numbers not deleted. -/
theorem clause?_delete {log : LRATLog φ} {ids : List ℕ} {i : ℕ} (hi : i ∉ ids) :
    (log.delete ids).clause? i = log.clause? i := by
  unfold delete
  split
  · rfl
  · rw [clause?, chunkGet_foldl_chunkClear, ite_eq_right hi, clause?]

/-- **Closing the log** with an empty-clause step, given hints along which unit propagation
reaches a conflict from no assumption. -/
def finish (log : LRATLog φ) (hints : List ℕ) (_h : propagateHints log.db [] hints = true) :
    Array LRAT.IntAction :=
  (log.steps.reverse ++ [Std.Tactic.BVDecide.LRAT.Action.addEmpty log.next hints.toArray]).toArray

/-- **A closed log is accepted by the checker.** -/
theorem checkLRAT_finish {log : LRATLog φ} {hints : List ℕ}
    (h : propagateHints log.db [] hints = true) : φ.checkLRAT (log.finish hints h) = true := by
  rw [checkLRAT, finish, List.toList_toArray, log.run]
  simpa [checkLRATAux] using h

end LRATLog

end Cslib.Logic.PL.CNF
