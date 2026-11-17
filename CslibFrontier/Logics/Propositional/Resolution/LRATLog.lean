/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Resolution.LRAT

/-! # LRAT certificates built by resolution, step by step

A solver that learns clauses builds its certificate as it runs. `Cslib.Logic.PL.CNF.LRATLog φ` is
a certificate under construction for `φ`: the steps so far, the numbered clauses they lead to, and
the next unused number, together with the facts that the checker passes the steps
(`Cslib.Logic.PL.CNF.LRATLog.run`) and that every clause of the database holds in every model of
`φ` (`Cslib.Logic.PL.CNF.LRATLog.implied`).

The log grows by resolution (`Cslib.Logic.PL.CNF.LRATLog.resolve`): the resolvent of two clauses
of the database is added under the next number, as a RUP step hinting the two
(`Cslib.Logic.PL.CNF.propagateHints_resolvent`). A resolvent of any two clauses is a RUP clause of
them, whether or not the variable occurs in them with opposite signs, so every resolution step
keeps the log correct, and a solver that learns clauses by resolution needs no further proof that
its certificate is accepted. Clauses can be deleted
(`Cslib.Logic.PL.CNF.LRATLog.delete`). Once the database contains the empty clause, closing the
log with an empty-clause step hinting it gives a certificate that the checker accepts
(`Cslib.Logic.PL.CNF.LRATLog.checkLRAT_finish`).

## Main definitions

* `Cslib.Logic.PL.CNF.LRATLog`: a certificate under construction.
* `Cslib.Logic.PL.CNF.LRATLog.init`, `Cslib.Logic.PL.CNF.LRATLog.resolve`,
  `Cslib.Logic.PL.CNF.LRATLog.delete`, `Cslib.Logic.PL.CNF.LRATLog.finish`: starting, resolving,
  deleting and closing.

## Main results

* `Cslib.Logic.PL.CNF.LRATLog.checkLRAT_finish`: a closed log is accepted by the checker.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

open Std.Tactic.BVDecide (LRAT.IntAction)

/-- **A certificate under construction** for `φ`: the steps so far, newest first, the numbered
clauses they lead to, and the next unused number. -/
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

/-- The clause numbered `i`, if any. -/
def clause? (log : LRATLog φ) (i : ℕ) : Option (Clause ℕ) :=
  (log.db.find? (·.1 == i)).map (·.2)

theorem find?_of_clause? {log : LRATLog φ} {i : ℕ} {c : Clause ℕ} (h : log.clause? i = some c) :
    log.db.find? (·.1 == i) = some (i, c) := by
  simp only [clause?, Option.map_eq_some_iff] at h
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

/-- Adding the resolvent of the clauses numbered `i₁` and `i₂` on `v`, given those clauses. -/
def addResolvent (log : LRATLog φ) (i₁ i₂ v : ℕ) (c₁ c₂ : Clause ℕ)
    (h₁ : log.clause? i₁ = some c₁) (h₂ : log.clause? i₂ = some c₂) : LRATLog φ where
  steps := .addRup log.next (c₁.resolvent c₂ v).toDIMACS #[i₁, i₂] :: log.steps
  db := (log.next, c₁.resolvent c₂ v) :: log.db
  next := log.next + 1
  run rest := by
    have hprop := propagateHints_resolvent (v := v) (find?_of_clause? h₁) (find?_of_clause? h₂)
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [log.run]
    simp only [checkLRATAux, Clause.ofDIMACS_toDIMACS, hprop, Bool.true_and]
  lt_next e he := by
    rcases List.mem_cons.1 he with rfl | he
    · simp
    · have := log.lt_next e he; omega
  implied σ hσ e he := by
    rcases List.mem_cons.1 he with rfl | he
    · exact Clause.eval_resolvent v (eval_of_clause? h₁ hσ) (eval_of_clause? h₂ hσ)
    · exact log.implied σ hσ e he
  vars_mem e he l hl := by
    rcases List.mem_cons.1 he with rfl | he
    · rcases Clause.mem_resolvent.1 hl with ⟨hl, -⟩ | ⟨hl, -⟩
      · exact log.vars_mem _ (List.mem_of_find?_eq_some (find?_of_clause? h₁)) l hl
      · exact log.vars_mem _ (List.mem_of_find?_eq_some (find?_of_clause? h₂)) l hl
    · exact log.vars_mem e he l hl

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

/-- After adding a resolvent, the new number names it. -/
theorem clause?_addResolvent {log : LRATLog φ} {i₁ i₂ v : ℕ} {c₁ c₂ : Clause ℕ}
    (h₁ : log.clause? i₁ = some c₁) (h₂ : log.clause? i₂ = some c₂) :
    (log.addResolvent i₁ i₂ v c₁ c₂ h₁ h₂).clause? log.next = some (c₁.resolvent c₂ v) := by
  simp [clause?, addResolvent]

/-- Adding a resolvent extends the log. -/
theorem extends_addResolvent {log : LRATLog φ} {i₁ i₂ v : ℕ} {c₁ c₂ : Clause ℕ}
    (h₁ : log.clause? i₁ = some c₁) (h₂ : log.clause? i₂ = some c₂) :
    log.Extends (log.addResolvent i₁ i₂ v c₁ c₂ h₁ h₂) := by
  intro i c h
  have hi := lt_next_of_clause? h
  simp only [clause?, addResolvent, List.find?_cons] at h ⊢
  rw [show (log.next == i) = false by simp; omega]
  exact h

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
    simp [clause?, addResolvent]
  · simp at h

/-- After resolving, the older numbers name the same clauses. -/
theorem clause?_resolve_of_lt {log log' : LRATLog φ} {i₁ i₂ v j i : ℕ}
    (h : log.resolve i₁ i₂ v = some (log', j)) (hi : i < log.next) :
    log'.clause? i = log.clause? i := by
  unfold resolve at h
  split at h
  · cases h
    simp only [clause?, addResolvent, List.find?_cons]
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

/-- **Deleting clauses** from the log. -/
def delete (log : LRATLog φ) (ids : List ℕ) : LRATLog φ where
  steps := .del ids.toArray :: log.steps
  db := log.db.filter fun e => !ids.contains e.1
  next := log.next
  run rest := by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [log.run]
    simp [checkLRATAux]
  lt_next e he := log.lt_next e (List.mem_filter.1 he).1
  implied σ hσ e he := log.implied σ hσ e (List.mem_filter.1 he).1
  vars_mem e he := log.vars_mem e (List.mem_filter.1 he).1

/-- **Closing the log** at the empty clause, numbered `i`: its steps followed by an empty-clause
step hinting it. -/
def finish (log : LRATLog φ) (i : ℕ) (_h : log.clause? i = some []) : Array LRAT.IntAction :=
  (log.steps.reverse ++ [Std.Tactic.BVDecide.LRAT.Action.addEmpty log.next #[i]]).toArray

/-- **A log closed at the empty clause is accepted by the checker.** -/
theorem checkLRAT_finish {log : LRATLog φ} {i : ℕ} (h : log.clause? i = some []) :
    φ.checkLRAT (log.finish i h) = true := by
  rw [checkLRAT, finish, List.toList_toArray, log.run]
  simp [checkLRATAux, propagateHints, find?_of_clause? h]

end LRATLog

end Cslib.Logic.PL.CNF
