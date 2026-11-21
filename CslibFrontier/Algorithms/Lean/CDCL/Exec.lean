/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.System
public import CslibFrontier.Algorithms.Lean.CDCL.Assign
public import CslibFrontier.Logics.Propositional.Resolution.LRATLog
public import CslibFrontier.Algorithms.Lean.DPLL

/-! # The state and moves of the CDCL solver

The state of the executable CDCL solver (`Cslib.Algorithms.Lean.CDCL.solve`), an instance of
abstract DPLL with learning (`Cslib.Algorithms.Lean.CDCL.Step`), with its moves and their
invariant. Finding a conflict or a unit clause is left to the solver, which uses watched literals.

**State.** The solver keeps a trail of decisions and of implied literals carrying the number of
their *reason*, a clause of the log (`Cslib.Algorithms.Lean.CDCL.XEntry`), the numbered clauses of
its database, and an LRAT certificate under construction (`Cslib.Logic.PL.CNF.LRATLog`). Its
invariant (`Cslib.Algorithms.Lean.CDCL.Exec.Inv`) is the invariant of the abstract system together
with:

* every reason contains its literal, and its other literals are false further down the trail
  (`Cslib.Algorithms.Lean.CDCL.Reasons`);
* every clause of the database is in the log under its number;
* no clause of the database is false on the part of the trail below a decision;
* the numbered clauses of the input stay in the database.

**Moves.**

* If a clause is false and the trail has no decision, resolving it with the reasons of the trail,
  newest first, derives the empty clause (`Cslib.Algorithms.Lean.CDCL.refute`); the log, closed at
  that clause, is the certificate (`Cslib.Algorithms.Lean.CDCL.Refutation.cert`).
* If a clause is false and the trail has a decision, *first-UIP analysis*
  (`Cslib.Algorithms.Lean.CDCL.analyze`) resolves it with the reasons of the newest implied
  literals until exactly one of its literals is false at the current level. Its type guarantees an
  asserting clause: the analysed clause always has a literal false at the current level, and at
  the decision only the decision's negation can be one. The solver backjumps, as MiniSat does, to
  the second-highest level of the learned clause: below the newest decision and every level
  below it with no variable of the clause (`Cslib.Algorithms.Lean.CDCL.Exec.jump`, without decision
  levels). It adds the asserting literal with the learned clause as its reason, and learns the
  clause (Backjump and Learn, `Cslib.Algorithms.Lean.CDCL.Exec.afterConflict`). The intermediate
  resolvents of the analysis are then deleted from the log.
* UnitPropagate (`Cslib.Algorithms.Lean.CDCL.Exec.propagate`) and Decide
  (`Cslib.Algorithms.Lean.CDCL.Exec.decide`).
* Restart (`Cslib.Algorithms.Lean.CDCL.Exec.restart`), back to the literals implied below every
  decision.
* Forget (`Cslib.Algorithms.Lean.CDCL.Exec.forget`): deleting clauses other than the reasons of
  the trail from the database and the log, input clauses only if a literal of the root of the
  trail, implied without any decision, satisfies them
  (`Cslib.Algorithms.Lean.CDCL.Exec.forget_inv`). The reasons kept are in the database and entail
  the root (`Cslib.Algorithms.Lean.CDCL.Reasons.eval_of_no_decision`), so under total
  assignments the remaining clauses entail the input clauses, and with them the clauses deleted.
  For partial assignments the guarantee concerns the input only: a partial model of the remaining
  clauses satisfies the input clauses through the root. It is not shown to satisfy the deleted
  clauses.

Every move other than Restart and Forget is a Basic DPLL step, or Backjump followed by Learn, of
the abstract system, and so lowers its rank (`Cslib.Algorithms.Lean.CDCL.rank`); Forget keeps it.
Every learned clause, and every intermediate resolvent of the analysis, enters the certificate as a
RUP step hinting the two clauses it resolves, so the checker accepts the certificate by
construction (`Cslib.Logic.PL.CNF.LRATLog.checkLRAT_finish`).

**Scope.** `Exec` does not choose decisions: the solver with watched literals chooses them
(`Cslib.Algorithms.Lean.CDCL.Activity`).

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.Exec`, `Cslib.Algorithms.Lean.CDCL.Exec.Inv`: the state and its
  invariant.
* `Cslib.Algorithms.Lean.CDCL.analyze`: first-UIP conflict analysis.
* `Cslib.Algorithms.Lean.CDCL.Exec.jump`: the backjump to the second-highest level of the learned
  clause.
* `Cslib.Algorithms.Lean.CDCL.refute`: the certificate when there is no decision.

## Main results

* `Cslib.Algorithms.Lean.CDCL.Exec.afterConflict_spec`,
  `Cslib.Algorithms.Lean.CDCL.Exec.propagate_spec`, `Cslib.Algorithms.Lean.CDCL.Exec.decide_spec`:
  the moves keep the invariant and lower the rank.
* `Cslib.Algorithms.Lean.CDCL.Exec.restart_inv`, `Cslib.Algorithms.Lean.CDCL.Exec.forget_inv`:
  Restart and Forget keep the invariant.

## References

* [R. Nieuwenhuis, A. Oliveras, C. Tinelli, *Solving SAT and SAT Modulo Theories: From an Abstract
  Davis–Putnam–Logemann–Loveland Procedure to DPLL(T)*][NieuwenhuisOliverasTinelli2006], §2.4–2.5
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL Cslib.Logic.PL.CNF

variable {φ : CNF ℕ}

/-- An entry of the solver's trail: a decision, or an implied literal with the number of its
reason clause in the log. -/
inductive XEntry
  /-- A decision. -/
  | decision (l : Literal ℕ)
  /-- An implied literal and the number of its reason. -/
  | implied (l : Literal ℕ) (reason : ℕ)

/-- The entry of the abstract trail. -/
def XEntry.entry : XEntry → Entry
  | .decision l => ⟨l, true⟩
  | .implied l _ => ⟨l, false⟩

@[simp] theorem XEntry.entry_decision (l : Literal ℕ) : (XEntry.decision l).entry = ⟨l, true⟩ :=
  rfl

@[simp] theorem XEntry.entry_implied (l : Literal ℕ) (r : ℕ) :
    (XEntry.implied l r).entry = ⟨l, false⟩ := rfl

/-- The solver's trail, newest first. -/
abbrev XTrail := List XEntry

/-- The abstract trail of the solver's trail. -/
def XTrail.trail (M : XTrail) : Trail := M.map XEntry.entry

@[simp] theorem XTrail.trail_nil : XTrail.trail [] = [] := rfl

@[simp] theorem XTrail.trail_cons (x : XEntry) (M : XTrail) :
    XTrail.trail (x :: M) = x.entry :: XTrail.trail M := rfl

@[simp] theorem XTrail.trail_append (M N : XTrail) :
    XTrail.trail (M ++ N) = XTrail.trail M ++ XTrail.trail N := List.map_append ..

/-- Every implied literal of the trail has a reason clause in the log, containing it, whose other
literals are false further down the trail; decisions have no reason. -/
inductive Reasons (log : LRATLog φ) : XTrail → Prop
  | nil : Reasons log []
  | decision {M : XTrail} (l : Literal ℕ) : Reasons log M → Reasons log (.decision l :: M)
  | implied {M : XTrail} (l : Literal ℕ) (r : ℕ) {R : Clause ℕ} : Reasons log M →
      log.clause? r = some R → l ∈ R →
      (∀ l' ∈ R, l' ≠ l → l'.negate ∈ Trail.lits (XTrail.trail M)) →
      Reasons log (.implied l r :: M)

theorem Reasons.mono {log log' : LRATLog φ} (hext : log.Extends log') {M : XTrail}
    (h : Reasons log M) : Reasons log' M := by
  induction h with
  | nil => exact .nil
  | decision l _ ih => exact .decision l ih
  | implied l r _ hr hl hfalse ih => exact .implied l r ih (hext _ _ hr) hl hfalse

theorem Reasons.tail {log : LRATLog φ} {x : XEntry} {M : XTrail} (h : Reasons log (x :: M)) :
    Reasons log M := by
  cases h <;> assumption

/-- The reason of an implied literal at the head of a trail. -/
theorem Reasons.reason {log : LRATLog φ} {l : Literal ℕ} {r : ℕ} {M : XTrail} {R : Clause ℕ}
    (h : Reasons log (.implied l r :: M)) (hR : log.clause? r = some R) :
    l ∈ R ∧ ∀ l' ∈ R, l' ≠ l → l'.negate ∈ Trail.lits (XTrail.trail M) := by
  cases h with
  | implied _ _ _ hr hl hfalse =>
    rw [hR] at hr
    cases hr
    exact ⟨hl, hfalse⟩

/-- An implied literal at the head of a trail has a reason. -/
theorem Reasons.isSome {log : LRATLog φ} {l : Literal ℕ} {r : ℕ} {M : XTrail}
    (h : Reasons log (.implied l r :: M)) : (log.clause? r).isSome := by
  cases h with
  | implied _ _ _ hr => simp [hr]

theorem Reasons.append_right {log : LRATLog φ} {N M : XTrail} (h : Reasons log (N ++ M)) :
    Reasons log M := by
  induction N with
  | nil => simpa using h
  | cons x N ih => exact ih h.tail

/-- The number of the reason of an entry, if it is implied. -/
def XEntry.reason? : XEntry → Option ℕ
  | .decision _ => none
  | .implied _ r => some r

/-- The numbers of the reasons of a trail, MiniSat's *locked* clauses. -/
def XTrail.reasonIds (M : XTrail) : List ℕ := M.filterMap XEntry.reason?

@[simp] theorem XTrail.reasonIds_nil : XTrail.reasonIds [] = [] := rfl

@[simp] theorem XTrail.reasonIds_decision (l : Literal ℕ) (M : XTrail) :
    XTrail.reasonIds (.decision l :: M) = XTrail.reasonIds M := rfl

@[simp] theorem XTrail.reasonIds_implied (l : Literal ℕ) (r : ℕ) (M : XTrail) :
    XTrail.reasonIds (.implied l r :: M) = r :: XTrail.reasonIds M := rfl

/-- The reasons of a trail are numbers of the log, so below its next number. -/
theorem Reasons.lt_next {log : LRATLog φ} {M : XTrail} (h : Reasons log M) :
    ∀ r ∈ XTrail.reasonIds M, r < log.next := by
  induction h with
  | nil => simp
  | decision l _ ih => simpa using ih
  | implied l r _ hr _ _ ih =>
    intro r' h'
    rcases List.mem_cons.1 (by simpa using h') with rfl | h'
    · exact LRATLog.lt_next_of_clause? hr
    · exact ih r' h'

/-- Deleting clauses other than the reasons keeps the reasons. -/
theorem Reasons.deleteWith {log : LRATLog φ} {ids : List ℕ} {db' : List (ℕ × Clause ℕ)}
    {hdb : db' = log.db.filter fun e => !ids.contains e.1} {M : XTrail} (h : Reasons log M)
    (hids : ∀ r ∈ XTrail.reasonIds M, r ∉ ids) : Reasons (log.deleteWith ids db' hdb) M := by
  induction h with
  | nil => exact .nil
  | decision l _ ih => exact .decision l (ih (by simpa using hids))
  | implied l r _ hr hl hfalse ih =>
    have hr' : r ∉ ids := hids r (by simp)
    exact .implied l r (ih fun r' h' => hids r' (by simp [h']))
      ((LRATLog.clause?_deleteWith hr').trans hr) hl hfalse

/-- Deleting clauses other than the reasons keeps the reasons. -/
theorem Reasons.delete {log : LRATLog φ} {ids : List ℕ} {M : XTrail} (h : Reasons log M)
    (hids : ∀ r ∈ XTrail.reasonIds M, r ∉ ids) : Reasons (log.delete ids) M :=
  h.deleteWith hids

/-- **The resolvent of `c₁` and `c₂` on `v` without repeated literals**: the literals of
`Clause.resolvent`, each once. Conflict analysis then does not accumulate copies of a literal,
and every clause it adds to the certificate is free of repetitions, as LRAT checkers that count
each copy of a literal (such as `lrat-check` of drat-trim) require. -/
def mergeResolvent (c₁ c₂ : Clause ℕ) (v : ℕ) : Clause ℕ := dedupLits (c₁.resolvent c₂ v)

theorem mem_mergeResolvent {c₁ c₂ : Clause ℕ} {v : ℕ} {y : Literal ℕ} :
    y ∈ mergeResolvent c₁ c₂ v ↔ y ∈ c₁.resolvent c₂ v := mem_dedupKey litKey_injective

/-- The resolvent on the variable of `l` of a clause containing the negation of `l` and a clause
containing `l`, as `Clause.resolvent` orders them, without repeated literals. -/
def resolveOn (l : Literal ℕ) (C R : Clause ℕ) : Clause ℕ :=
  if l.2 then mergeResolvent R C l.1 else mergeResolvent C R l.1

theorem mem_resolveOn {l y : Literal ℕ} {C R : Clause ℕ} (h : y ∈ resolveOn l C R) :
    (y ∈ C ∧ y ≠ l.negate) ∨ (y ∈ R ∧ y ≠ l) := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp only [resolveOn, Bool.false_eq_true, ↓reduceIte, mem_mergeResolvent] at h <;>
    rcases Clause.mem_resolvent.1 h with ⟨h, hne⟩ | ⟨h, hne⟩ <;>
    simp_all [Std.Sat.Literal.negate]

/-- Adding to the log the resolvent `D` of the clause numbered `i`, containing the negation of `l`,
and the reason numbered `r` of `l`, computed once by the caller. -/
def resolveLog (log : LRATLog φ) (l : Literal ℕ) (i r : ℕ) (C R : Clause ℕ)
    (hC : log.clause? i = some C) (hR : log.clause? r = some R) (D : Clause ℕ)
    (hD : D = resolveOn l C R) : LRATLog φ :=
  if h : l.2 then
    log.addResolventAs r i l.1 R C hR hC D fun _ => by
      rw [hD, resolveOn, ite_eq_left h, mem_mergeResolvent]
  else
    log.addResolventAs i r l.1 C R hC hR D fun _ => by
      rw [hD, resolveOn, ite_eq_right h, mem_mergeResolvent]

theorem resolveLog_spec {log : LRATLog φ} {l : Literal ℕ} {i r : ℕ} {C R : Clause ℕ}
    (hC : log.clause? i = some C) (hR : log.clause? r = some R) {D : Clause ℕ}
    (hD : D = resolveOn l C R) :
    (resolveLog log l i r C R hC hR D hD).clause? log.next = some D ∧
      log.Extends (resolveLog log l i r C R hC hR D hD) := by
  unfold resolveLog
  split
  · exact ⟨LRATLog.clause?_addResolventAs, LRATLog.extends_addResolventAs⟩
  · exact ⟨LRATLog.clause?_addResolventAs, LRATLog.extends_addResolventAs⟩

/-- The negation is injective. -/
theorem negate_inj {l l' : Literal ℕ} (h : l.negate = l'.negate) : l = l' := by
  obtain ⟨v, b⟩ := l
  obtain ⟨v', b'⟩ := l'
  cases b <;> cases b' <;> simp_all [Std.Sat.Literal.negate]

/-- A refutation in the log: a log in which the number `id` names the empty clause. -/
structure Refutation (φ : CNF ℕ) where
  /-- The log. -/
  log : LRATLog φ
  /-- The number of the empty clause. -/
  id : ℕ
  /-- The number names the empty clause. -/
  clause?_eq : log.clause? id = some []

/-- The certificate of a refutation: its log closed at the empty clause. -/
def Refutation.cert (r : Refutation φ) : Array Std.Tactic.BVDecide.LRAT.IntAction :=
  r.log.finish r.id r.clause?_eq

/-- **Deriving the empty clause from a conflict with no decision**: resolving the clause numbered
`i`, falsified by a trail of implied literals, with their reasons, newest first. -/
def refute : (T : XTrail) → (log : LRATLog φ) → (i : ℕ) → (C : Clause ℕ) →
    log.clause? i = some C → Reasons log T → (∀ x ∈ T, x.entry.decision = false) →
    (∀ y ∈ C, y.negate ∈ Trail.lits (XTrail.trail T)) → Refutation φ
  | [], log, i, C, hC, _, _, hfalse =>
    ⟨log, i, by
      obtain rfl : C = [] := List.eq_nil_iff_forall_not_mem.2 fun y hy => by
        simpa [Trail.lits] using hfalse y hy
      exact hC⟩
  | .implied l r :: T, log, i, C, hC, hreasons, hdec, hfalse =>
    match hR : log.clause? r with
    | some R =>
      have hT := hreasons.tail
      have hRfalse := (hreasons.reason hR).2
      if hmem : l.negate ∈ C then
        -- the number is read and the resolvent computed before the log grows
        let id := log.next
        let D := resolveOn l C R
        let log' := resolveLog log l i r C R hC hR D rfl
        have hspec := resolveLog_spec (l := l) hC hR (D := D) rfl
        refute T log' id D hspec.1 (hT.mono hspec.2)
          (fun x hx => hdec x (List.mem_cons_of_mem _ hx)) fun y hy => by
            rcases mem_resolveOn hy with ⟨hy, hne⟩ | ⟨hy, hne⟩
            · have := hfalse y hy
              simp only [XTrail.trail_cons, XEntry.entry_implied, Trail.lits, List.map_cons,
                List.mem_cons] at this
              rcases this with h | h
              · exact absurd (negate_inj (by simpa [Std.Sat.Literal.negate] using h)) hne
              · exact h
            · exact hRfalse y hy hne
      else
        refute T log i C hC hT (fun x hx => hdec x (List.mem_cons_of_mem _ hx)) fun y hy => by
          have := hfalse y hy
          simp only [XTrail.trail_cons, XEntry.entry_implied, Trail.lits, List.map_cons,
            List.mem_cons] at this
          rcases this with h | h
          · exact absurd (by rw [show y = l.negate from negate_inj (by
              simpa [Std.Sat.Literal.negate] using h)] at hy; exact hy) hmem
          · exact h
    | none => absurd hreasons.isSome (by simp [hR])
  | .decision _ :: _, _, _, _, _, _, hdec, _ => absurd (hdec _ List.mem_cons_self) (by simp)

theorem mem_resolveOn_left {l y : Literal ℕ} {C R : Clause ℕ} (hy : y ∈ C) (hne : y ≠ l.negate) :
    y ∈ resolveOn l C R := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp_all [resolveOn, mem_mergeResolvent, Clause.mem_resolvent,
    Std.Sat.Literal.negate]

theorem lits_append (M N : Trail) : Trail.lits (M ++ N) = Trail.lits M ++ Trail.lits N :=
  List.map_append ..

theorem vars_append (M N : Trail) : Trail.vars (M ++ N) = Trail.vars M ++ Trail.vars N :=
  List.map_append ..

/-- The variables of a clause of the log are variables of `φ`. -/
theorem vars_mem_map_of_clause? {log : LRATLog φ} {i : ℕ} {C : Clause ℕ}
    (hC : log.clause? i = some C) : ∀ v ∈ C.map Prod.fst, v ∈ φ.vars := fun v hv => by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hv
  exact LRATLog.vars_mem_of_clause? hC l hl

/-- A learned clause: a log extending `log₀` in which the number `id` names a clause all of whose
literals but `lit` are false in the trail `M₀`, where `lit` is undefined; its negation is among the
literals `A` above `M₀`. -/
structure Learned (log₀ : LRATLog φ) (A M₀ : Trail) where
  /-- The log. -/
  log : LRATLog φ
  /-- The number of the learned clause. -/
  id : ℕ
  /-- The learned clause. -/
  clause : Clause ℕ
  /-- The asserting literal. -/
  lit : Literal ℕ
  /-- The variables of the clauses met by the analysis: the conflict clause and the resolvents,
  hence the reasons resolved. Branching heuristics bump them. -/
  seen : List ℕ
  /-- The numbers of the clauses met by the analysis: the conflict clause, the resolvents and the
  reasons resolved. Clause activities bump them. -/
  used : List ℕ
  seen_mem : ∀ v ∈ seen, v ∈ φ.vars
  clause?_eq : log.clause? id = some clause
  mem : lit ∈ clause
  false_below : ∀ y ∈ clause, y ≠ lit → y.negate ∈ Trail.lits M₀
  undef : lit.1 ∉ Trail.vars M₀
  above : lit.negate ∈ Trail.lits A
  ext : log₀.Extends log
  /-- The assignment array the analysis was reading when it stopped, returned so that the solver
  can clear it and use it again: it has values only for variables of `A`. -/
  marks : Assign
  marks_none : ∀ v, v ∉ Trail.vars A → marks.value v = none

/-- **First-UIP conflict analysis.** Above the newest decision `d`, with the implied literals `N`
over it and the trail `M₀` below it, the clause numbered `i` is false and has a literal false at
the current level. While it has two different literals false at the current level, it is resolved
with the reason of the newest implied literal whose negation it contains. It stops with a clause
having exactly one literal false at the current level, its first unique implication point, which
is reached at the latest at the decision. The literals of the current level are read from the
assignment `cur`, which agrees with them; passing an implied literal unassigns its variable. -/
def analyze (log₀ : LRATLog φ) (d : Literal ℕ) (M₀ : XTrail) (A : Trail) :
    (N : XTrail) → Trail.lits (XTrail.trail N ++ [⟨d, true⟩]) ⊆ Trail.lits A →
    (cur : Assign) → cur.Agrees (XTrail.trail N ++ [⟨d, true⟩]) →
    (log : LRATLog φ) → log₀.Extends log → (i : ℕ) → (C : Clause ℕ) →
    log.clause? i = some C → Reasons log (N ++ XEntry.decision d :: M₀) →
    (∀ x ∈ N, x.entry.decision = false) →
    (∀ y ∈ C, y.negate ∈ Trail.lits (XTrail.trail (N ++ XEntry.decision d :: M₀))) →
    (∃ y ∈ C, y.negate ∈ Trail.lits (XTrail.trail N ++ [⟨d, true⟩])) →
    (Trail.vars (XTrail.trail (N ++ XEntry.decision d :: M₀))).Nodup →
    Learned log₀ A (XTrail.trail M₀)
  | N, hA, cur, hcurA, log, hext, i, C, hC, hreasons, hdec, hfalse, hcur, hnd =>
    match hys : C.filter (fun y => cur.holds y.negate) with
    | [] => absurd hys (by
        obtain ⟨y, hy, hyc⟩ := hcur
        exact List.ne_nil_of_mem (List.mem_filter.2 ⟨hy, (hcurA.holds_iff _).2 hyc⟩))
    | u :: rest =>
      have hu : u ∈ C ∧ u.negate ∈ Trail.lits (XTrail.trail N ++ [⟨d, true⟩]) := by
        have := List.mem_filter.1 (hys ▸ List.mem_cons_self : u ∈ C.filter _)
        exact ⟨this.1, (hcurA.holds_iff _).1 this.2⟩
      if hall : rest.all (· == u) then
        { log := log, id := i, clause := C, lit := u, seen := C.map Prod.fst, used := [i],
          marks := cur
          marks_none := fun v hv => by
            cases h : cur.value v with
            | none => rfl
            | some b => exact absurd (Trail.mem_vars_of_mem_lits (hA ((hcurA v b).1 h))) hv
          seen_mem := vars_mem_map_of_clause? hC, clause?_eq := hC,
          mem := hu.1,
          false_below := fun y hy hne => by
            have hyT := hfalse y hy
            simp only [XTrail.trail_append, XTrail.trail_cons, lits_append, List.mem_append]
              at hyT
            rcases hyT with h | h
            · refine absurd ?_ hne
              have : y ∈ C.filter (fun y => cur.holds y.negate) :=
                List.mem_filter.2 ⟨hy, (hcurA.holds_iff _).2 (by
                  rw [lits_append]; exact List.mem_append_left _ h)⟩
              rw [hys] at this
              rcases List.mem_cons.1 this with h | h
              · exact h
              · simpa using List.all_eq_true.1 hall y h
            · simp only [Trail.lits, List.map_cons, List.mem_cons] at h
              rcases h with h | h
              · refine absurd ?_ hne
                have : y ∈ C.filter (fun y => cur.holds y.negate) :=
                  List.mem_filter.2 ⟨hy, (hcurA.holds_iff _).2 (by
                    rw [lits_append]; exact List.mem_append_right _ (by simp [Trail.lits, h]))⟩
                rw [hys] at this
                rcases List.mem_cons.1 this with h | h
                · exact h
                · simpa using List.all_eq_true.1 hall y h
              · exact h
          undef := fun hu' => by
            have hv : u.1 ∈ Trail.vars (XTrail.trail N ++ [⟨d, true⟩]) := by
              simpa [Std.Sat.Literal.negate] using Trail.mem_vars_of_mem_lits hu.2
            simp only [XTrail.trail_append, XTrail.trail_cons, XEntry.entry_decision] at hnd
            rw [show XTrail.trail N ++ ⟨d, true⟩ :: XTrail.trail M₀ =
              (XTrail.trail N ++ [⟨d, true⟩]) ++ XTrail.trail M₀ by simp, vars_append] at hnd
            exact List.disjoint_of_nodup_append hnd hv hu'
          above := hA hu.2
          ext := hext }
      else
        match N, hA, hcurA, hreasons, hdec, hfalse, hcur, hnd, hys, hu with
        | [], _, hcurA, _, _, _, _, _, hys, _ => absurd (List.all_eq_true.2 fun y hy => by
            have hy' : y ∈ C.filter _ := hys ▸ List.mem_cons_of_mem _ hy
            have hu' : u ∈ C.filter _ := hys ▸ List.mem_cons_self
            have h₁ := (hcurA.holds_iff _).1 (List.mem_filter.1 hy').2
            have h₂ := (hcurA.holds_iff _).1 (List.mem_filter.1 hu').2
            simp only [Trail.lits, XTrail.trail_nil, List.nil_append, List.map_cons, List.map_nil,
              List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
            simpa using negate_inj (h₁.trans h₂.symm)) hall
        | .decision _ :: _, _, _, _, hdec, _, _, _, _, _ =>
          absurd (hdec _ List.mem_cons_self) (by simp)
        | .implied l r :: N', hA, hcurA, hreasons, hdec, hfalse, hcur, hnd, hys, hu =>
          match hR : log.clause? r with
          | none => absurd hreasons.isSome (by simp [hR])
          | some R =>
            have hT := hreasons.tail
            have hRfalse := (hreasons.reason hR).2
            have hdec' : ∀ x ∈ N', x.entry.decision = false :=
              fun x hx => hdec x (List.mem_cons_of_mem _ hx)
            have hA' : Trail.lits (XTrail.trail N' ++ [⟨d, true⟩]) ⊆ Trail.lits A :=
              fun x hx => hA (by simp only [XTrail.trail_cons, List.cons_append, Trail.lits,
                List.map_cons, List.mem_cons] at hx ⊢; exact .inr hx)
            have hnd' : (Trail.vars (XTrail.trail (N' ++ XEntry.decision d :: M₀))).Nodup := by
              have := hnd
              simp only [List.cons_append, XTrail.trail_cons, Trail.vars, List.map_cons,
                List.nodup_cons] at this
              exact this.2
            -- passing `l` unassigns its variable, which is not further down the level
            have hl : l.1 ∉ Trail.vars (XTrail.trail N' ++ [⟨d, true⟩]) := fun h => by
              have := hnd
              simp only [List.cons_append, XTrail.trail_cons, XTrail.trail_append,
                Trail.vars, List.map_cons, List.map_append, List.nodup_cons, List.mem_append,
                List.mem_cons, not_or] at this
              simp only [Trail.vars, List.map_append, List.map_cons, List.map_nil,
                List.mem_append, List.mem_singleton] at h
              rcases h with h | h
              · exact this.1.1 h
              · exact this.1.2.1 h
            have hcurA' : (cur.unassign [l.1]).Agrees (XTrail.trail N' ++ [⟨d, true⟩]) :=
              Assign.Agrees.drop (N := [⟨l, false⟩]) hcurA fun v hv => by
                rw [show v = l.1 by simpa [Trail.vars] using hv]; exact hl
            -- a literal of `C` false at the current level other than the negation of `l`
            have hz : ∃ z ∈ C, z ≠ l.negate ∧
                z.negate ∈
                  Trail.lits (XTrail.trail (XEntry.implied l r :: N') ++ [⟨d, true⟩]) := by
              obtain ⟨y, hy, hyu⟩ : ∃ y ∈ rest, y ≠ u := by
                by_contra hne
                push Not at hne
                exact hall (List.all_eq_true.2 fun y hy => by simpa using hne y hy)
              have hy' : y ∈ C.filter _ := hys ▸ List.mem_cons_of_mem _ hy
              by_cases hul : u = l.negate
              · exact ⟨y, (List.mem_filter.1 hy').1, hul ▸ hyu,
                  (hcurA.holds_iff _).1 (List.mem_filter.1 hy').2⟩
              · exact ⟨u, hu.1, hul, hu.2⟩
            have hcur' : ∀ z, z ≠ l.negate →
                z.negate ∈ Trail.lits (XTrail.trail (XEntry.implied l r :: N') ++ [⟨d, true⟩]) →
                z.negate ∈ Trail.lits (XTrail.trail N' ++ [⟨d, true⟩]) := fun z hne h => by
              simp only [XTrail.trail_cons, List.cons_append, Trail.lits, List.map_cons,
                List.mem_cons] at h
              rcases h with h | h
              · exact absurd (negate_inj (by simpa [Std.Sat.Literal.negate] using h)) hne
              · exact h
            have hfalse' : ∀ y ∈ C, y ≠ l.negate →
                y.negate ∈ Trail.lits (XTrail.trail (N' ++ XEntry.decision d :: M₀)) :=
              fun y hy hne => by
                have := hfalse y hy
                simp only [List.cons_append, XTrail.trail_cons, Trail.lits, List.map_cons,
                  List.mem_cons] at this
                rcases this with h | h
                · exact absurd (negate_inj (by simpa [Std.Sat.Literal.negate] using h)) hne
                · exact h
            if hmem : l.negate ∈ C then
              -- the number is read and the resolvent computed before the log grows
              let id := log.next
              let D := resolveOn l C R
              let log' := resolveLog log l i r C R hC hR D rfl
              have hspec := resolveLog_spec (l := l) hC hR (D := D) rfl
              let L' := analyze log₀ d M₀ A N' hA' (cur.unassign [l.1]) hcurA' log'
                (hext.trans hspec.2) id D hspec.1 (hT.mono hspec.2) hdec'
                (fun y hy => by
                  rcases mem_resolveOn hy with ⟨hy, hne⟩ | ⟨hy, hne⟩
                  · exact hfalse' y hy hne
                  · exact hRfalse y hy hne)
                (by
                  obtain ⟨z, hz, hne, hzc⟩ := hz
                  exact ⟨z, mem_resolveOn_left hz hne, hcur' z hne hzc⟩)
                hnd'
              { L' with
                seen := C.map Prod.fst ++ L'.seen
                used := i :: r :: L'.used
                seen_mem := fun v hv =>
                  (List.mem_append.1 hv).elim (vars_mem_map_of_clause? hC v) (L'.seen_mem v) }
            else
              analyze log₀ d M₀ A N' hA' (cur.unassign [l.1]) hcurA' log hext i C hC hT hdec'
                (fun y hy => hfalse' y hy fun h => hmem (h ▸ hy))
                (by
                  obtain ⟨z, hz, hne, hzc⟩ := hz
                  exact ⟨z, hz, hcur' z hne hzc⟩)
                hnd'

/-- The root of a trail, in one tail-recursive pass from the newest entry: `acc` is the part below
the oldest decision seen so far, or the whole trail if there is none. -/
def XTrail.rootGo : XTrail → XTrail → XTrail
  | acc, [] => acc
  | acc, x :: M => XTrail.rootGo (if x.entry.decision then M else acc) M

/-- **The root of a trail**: the part below its oldest decision, the literals implied without any
decision. It is found in one tail-recursive pass over the trail. -/
def XTrail.root (M : XTrail) : XTrail := XTrail.rootGo M M

theorem XTrail.rootGo_eq : ∀ (M acc : XTrail),
    XTrail.rootGo acc M = if M.any (·.entry.decision) then XTrail.root M else acc
  | [], _ => rfl
  | x :: M, acc => by
    have h : XTrail.root (x :: M) =
        XTrail.rootGo (if x.entry.decision then M else x :: M) M := rfl
    rw [rootGo, h, XTrail.rootGo_eq M, XTrail.rootGo_eq M]
    by_cases hM : M.any (·.entry.decision) <;> by_cases hx : x.entry.decision <;> simp [hM, hx]

theorem XTrail.root_cons (x : XEntry) (M : XTrail) :
    XTrail.root (x :: M) = if M.any (·.entry.decision) then XTrail.root M
      else if x.entry.decision then M else x :: M := by
  rw [root, rootGo, XTrail.rootGo_eq]

theorem XTrail.root_no_decision : ∀ (M : XTrail), ∀ x ∈ XTrail.root M, x.entry.decision = false
  | [] => by simp [XTrail.root, XTrail.rootGo]
  | x :: M => by
    rw [XTrail.root_cons]
    split
    · exact XTrail.root_no_decision M
    · rename_i hM
      have hM' : ∀ y ∈ M, y.entry.decision = false := fun y hy => by
        simpa using List.any_eq_false.1 (by simpa using hM) y hy
      split
      · exact hM'
      · rename_i hx
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · simpa using hx
        · exact hM' y hy

theorem XTrail.root_suffix : ∀ (M : XTrail), ∃ A, M = A ++ XTrail.root M
  | [] => ⟨[], rfl⟩
  | x :: M => by
    rw [XTrail.root_cons]
    split
    · obtain ⟨A, hA⟩ := XTrail.root_suffix M
      exact ⟨x :: A, by rw [List.cons_append, ← hA]⟩
    · split
      · exact ⟨[x], rfl⟩
      · exact ⟨[], rfl⟩

/-- The root is the whole trail, or the part below a decision. -/
theorem XTrail.root_split : ∀ (M : XTrail), XTrail.root M = M ∨
    ∃ N d, XTrail.trail M = N ++ ⟨d, true⟩ :: XTrail.trail (XTrail.root M)
  | [] => .inl rfl
  | x :: M => by
    rw [XTrail.root_cons]
    split
    · rename_i hM
      rcases XTrail.root_split M with h | ⟨N, d, hN⟩
      · exfalso
        obtain ⟨y, hy, hyd⟩ := List.any_eq_true.1 hM
        have := XTrail.root_no_decision M y (by rw [h]; exact hy)
        simp_all
      · exact .inr ⟨x.entry :: N, d, by rw [XTrail.trail_cons, hN]; rfl⟩
    · split
      · rename_i hx
        cases x with
        | decision l => exact .inr ⟨[], l, rfl⟩
        | implied l r => simp [XEntry.entry] at hx
      · exact .inl rfl

theorem XTrail.root_of_no_decision :
    ∀ M : XTrail, (∀ x ∈ M, x.entry.decision = false) → XTrail.root M = M
  | [], _ => rfl
  | x :: M, h => by
    have hM : M.any (·.entry.decision) = false :=
      List.any_eq_false.2 fun y hy => by simp [h y (List.mem_cons_of_mem _ hy)]
    rw [XTrail.root_cons]
    simp [hM, h x List.mem_cons_self]

theorem XTrail.root_root (M : XTrail) : XTrail.root (XTrail.root M) = XTrail.root M :=
  XTrail.root_of_no_decision _ (XTrail.root_no_decision M)

/-- Below a decision, the root is that of the trail below it. -/
theorem XTrail.root_append_decision (d : Literal ℕ) (K : XTrail) :
    ∀ J : XTrail, XTrail.root (J ++ .decision d :: K) = XTrail.root K
  | [] => by
    rw [List.nil_append, XTrail.root_cons]
    split
    · rfl
    · rename_i hK
      simp only [XEntry.entry, ite_true]
      exact (XTrail.root_of_no_decision K fun y hy => by
        simpa using List.any_eq_false.1 (by simpa using hK) y hy).symm
  | x :: J => by
    rw [List.cons_append, XTrail.root_cons, ite_eq_left_iff.2 fun h => absurd (by simp) h]
    exact XTrail.root_append_decision d K J

/-- The root only grows when an entry is added. -/
theorem XTrail.lits_root_cons {x : XEntry} {M : XTrail} {l : Literal ℕ}
    (h : l ∈ Trail.lits (XTrail.trail (XTrail.root M))) :
    l ∈ Trail.lits (XTrail.trail (XTrail.root (x :: M))) := by
  rw [XTrail.root_cons]
  split
  · exact h
  · rename_i hM
    rw [XTrail.root_of_no_decision M fun y hy => by
      simpa using List.any_eq_false.1 (by simpa using hM) y hy] at h
    split
    · exact h
    · simp only [XTrail.trail_cons, Trail.lits, List.map_cons, List.mem_cons] at h ⊢
      exact .inr h

theorem XTrail.reasonIds_append (M N : XTrail) :
    XTrail.reasonIds (M ++ N) = XTrail.reasonIds M ++ XTrail.reasonIds N :=
  List.filterMap_append

theorem XTrail.mem_reasonIds_root {M : XTrail} {r : ℕ} (h : r ∈ XTrail.reasonIds (XTrail.root M)) :
    r ∈ XTrail.reasonIds M := by
  obtain ⟨A, hA⟩ := XTrail.root_suffix M
  rw [hA, XTrail.reasonIds_append]
  exact List.mem_append_right _ h

/-- **The reasons make the root true in partial models**: on a trail without decisions, every
partial model of numbered clauses containing the reasons makes every literal of the trail true. -/
theorem Reasons.psat_of_no_decision {log : LRATLog φ} {db : List (ℕ × Clause ℕ)}
    (hdb : ∀ e ∈ db, log.clause? e.1 = some e.2) {ρ : ℕ → Option Bool}
    (hρ : ∀ e ∈ db, PSat ρ e.2) {M : XTrail} (h : Reasons log M)
    (hnodec : ∀ x ∈ M, x.entry.decision = false)
    (hR : ∀ r ∈ XTrail.reasonIds M, ∃ R, (r, R) ∈ db) :
    ∀ l ∈ Trail.lits (XTrail.trail M), ρ l.1 = some l.2 := by
  induction h with
  | nil => simp [Trail.lits]
  | decision l _ _ => exact absurd (hnodec _ List.mem_cons_self) (by simp [XEntry.entry])
  | @implied M l r R _ hr hl hfalse ih =>
    have ih' := ih (fun x hx => hnodec x (List.mem_cons_of_mem _ hx))
      (fun r' hr' => hR r' (by simp [hr']))
    intro l' hl'
    simp only [XTrail.trail_cons, XEntry.entry_implied, Trail.lits, List.map_cons,
      List.mem_cons] at hl'
    rcases hl' with rfl | hl'
    · obtain ⟨R', hR'⟩ := hR r (by simp)
      have hRR : R' = R := by have := hdb _ hR'; rw [hr] at this; cases this; rfl
      subst hRR
      obtain ⟨z, hz, hzρ⟩ := hρ _ hR'
      by_contra hne
      have hzl : z ≠ l' := fun h => hne (h ▸ hzρ)
      have := ih' _ (hfalse z hz hzl)
      simp [Std.Sat.Literal.negate, hzρ] at this
    · exact ih' l' hl'

/-- **The reasons entail the root**: on a trail without decisions, in every model of numbered
clauses containing the reasons, every literal holds. The total assignment `σ` is the partial
assignment `fun v => some (σ v)`, so this is `Reasons.psat_of_no_decision`. -/
theorem Reasons.eval_of_no_decision {log : LRATLog φ} {db : List (ℕ × Clause ℕ)}
    (hdb : ∀ e ∈ db, log.clause? e.1 = some e.2) {σ : ℕ → Bool}
    (hσ : ∀ e ∈ db, e.2.eval σ = true) {M : XTrail} (h : Reasons log M)
    (hnodec : ∀ x ∈ M, x.entry.decision = false)
    (hR : ∀ r ∈ XTrail.reasonIds M, ∃ R, (r, R) ∈ db) :
    ∀ l ∈ Trail.lits (XTrail.trail M), Literal.eval σ l = true := fun l hl => by
  have hρ : ∀ e ∈ db, PSat (fun v => some (σ v)) e.2 := fun e he => by
    obtain ⟨z, hz, hzσ⟩ := (Clause.eval_eq_true_iff σ e.2).1 (hσ e he)
    exact ⟨z, hz, by simp [hzσ]⟩
  simpa using Reasons.psat_of_no_decision hdb hρ h hnodec hR l hl

/-! ### The solver state -/

/-- A trail split at its newest decision: the implied literals above it, the decision, and the
trail below it. -/
structure Split where
  /-- The implied literals above the decision. -/
  above : XTrail
  /-- The decision literal. -/
  decision : Literal ℕ
  /-- The trail below the decision. -/
  below : XTrail

/-- The split of a trail at its newest decision, if it has one. -/
def XTrail.split : XTrail → Option Split
  | [] => none
  | .decision l :: M => some ⟨[], l, M⟩
  | .implied l r :: M =>
    (XTrail.split M).map fun s => ⟨.implied l r :: s.above, s.decision, s.below⟩

theorem XTrail.split_eq_none {M : XTrail} (h : XTrail.split M = none) :
    ∀ x ∈ M, x.entry.decision = false := by
  induction M with
  | nil => simp
  | cons x M ih =>
    cases x with
    | decision l => simp [XTrail.split] at h
    | implied l r =>
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · rfl
      · exact ih (by simpa [XTrail.split] using h) y hy

theorem XTrail.split_eq_some {M : XTrail} {s : Split} (h : XTrail.split M = some s) :
    M = s.above ++ .decision s.decision :: s.below ∧ ∀ x ∈ s.above, x.entry.decision = false := by
  induction M generalizing s with
  | nil => simp [XTrail.split] at h
  | cons x M ih =>
    cases x with
    | decision l =>
      simp only [XTrail.split, Option.some.injEq] at h
      subst h
      exact ⟨rfl, by simp⟩
    | implied l r =>
      obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨hM, habove⟩ := ih hs'
      refine ⟨by simp [hM], fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · rfl
      · exact habove y hy

/-- The state of the solver: its trail, the numbered clauses of the database, and the log. -/
structure Exec (φ : CNF ℕ) where
  /-- The trail. -/
  trail : XTrail
  /-- The numbered clauses of the database. -/
  db : List (ℕ × Clause ℕ)
  /-- The log of the certificate. -/
  log : LRATLog φ

/-- The clauses of the database. -/
def Exec.clauses (S : Exec φ) : CNF ℕ := S.db.map Prod.snd

/-- The abstract state of a solver state. -/
def Exec.state (S : Exec φ) : State := .run (XTrail.trail S.trail) S.clauses

/-- **The invariant of the solver**: the abstract invariant, the reasons of the trail, the numbers
of the database in the log, no clause of the database false below a decision, the numbered clauses
of `φ` in the database unless the root satisfies them, and the reasons in the database. -/
structure Exec.Inv (S : Exec φ) : Prop where
  run : RunInv φ φ.vars (XTrail.trail S.trail) S.clauses
  reasons : Reasons S.log S.trail
  db_log : ∀ e ∈ S.db, S.log.clause? e.1 = some e.2
  below : ∀ N d M₀, XTrail.trail S.trail = N ++ ⟨d, true⟩ :: M₀ →
    ∀ c ∈ S.clauses, ¬ Trail.Falsifies M₀ c
  /-- The numbered clauses of `φ` stay in the database, unless a literal of the root of the trail
  satisfies them. -/
  orig : ∀ e ∈ φ.lratDB,
    e ∈ S.db ∨ ∃ l ∈ e.2, l ∈ Trail.lits (XTrail.trail (XTrail.root S.trail))
  /-- The reasons of the trail are clauses of the database. -/
  reasons_db : ∀ r ∈ XTrail.reasonIds S.trail, ∃ R, (r, R) ∈ S.db

/-- The initial state: the empty trail, the clauses of `φ` with their numbers, and the empty log. -/
def Exec.init (φ : CNF ℕ) : Exec φ := ⟨[], φ.lratDB, LRATLog.init φ⟩

/-- In the numbering of `checkLRAT`, each number names its own clause. -/
theorem find?_zipIdx_map {e : ℕ × Clause ℕ} :
    ∀ (φ : CNF ℕ) (n : ℕ), e ∈ (φ.zipIdx n).map (fun p => (p.2 + 1, p.1)) →
      ((φ.zipIdx n).map (fun p => (p.2 + 1, p.1))).find? (·.1 == e.1) = some e
  | [], _, h => by simp at h
  | c :: φ, n, h => by
    simp only [List.zipIdx_cons, List.map_cons, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · simp
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      have := List.le_snd_of_mem_zipIdx hp
      rw [List.find?_cons_of_neg (by simp; omega)]
      exact find?_zipIdx_map φ (n + 1) (List.mem_map.2 ⟨p, hp, rfl⟩)

/-- The clauses of the initial state are those of `φ`. -/
theorem Exec.clauses_init (φ : CNF ℕ) : (Exec.init φ).clauses = φ := by
  simp only [Exec.clauses, Exec.init, lratDB, List.map_map]
  conv_rhs => rw [← List.zipIdx_map_fst 0 φ]
  rfl

theorem Exec.init_inv (φ : CNF ℕ) : (Exec.init φ).Inv := by
  have hclauses : (Exec.init φ).clauses = φ := Exec.clauses_init φ
  refine ⟨?_, .nil, fun e he => ?_, fun N d M₀ h => by simp [Exec.init, XTrail.trail] at h,
    fun e he => .inl he, fun r hr => by simp [Exec.init] at hr⟩
  · rw [hclauses]
    exact (Inv.init fun c hc l hl => CNF.mem_vars.2 ⟨c, hc, l.2, hl⟩ : RunInv _ _ _ _)
  · rw [LRATLog.clause?_eq]
    simp only [Exec.init, LRATLog.init, lratDB] at he ⊢
    rw [find?_zipIdx_map φ 0 he]
    rfl

/-! ### Steps of the solver -/

theorem XTrail.trail_of_split {M : XTrail} {sp : Split} (hsp : XTrail.split M = some sp) :
    XTrail.trail M = XTrail.trail sp.above ++ ⟨sp.decision, true⟩ :: XTrail.trail sp.below := by
  rw [(XTrail.split_eq_some hsp).1]
  simp

theorem Exec.Inv.split_reasons {S : Exec φ} (hS : S.Inv) {sp : Split}
    (hsp : XTrail.split S.trail = some sp) :
    Reasons S.log (sp.above ++ XEntry.decision sp.decision :: sp.below) := by
  rw [← (XTrail.split_eq_some hsp).1]
  exact hS.reasons

theorem Exec.Inv.split_nodup {S : Exec φ} (hS : S.Inv) {sp : Split}
    (hsp : XTrail.split S.trail = some sp) :
    (Trail.vars (XTrail.trail (sp.above ++ XEntry.decision sp.decision :: sp.below))).Nodup := by
  rw [← (XTrail.split_eq_some hsp).1]
  exact hS.run.nodup

/-- The variables of the current level, from the newest decision up, are distinct. -/
theorem Exec.Inv.split_level_nodup {S : Exec φ} (hS : S.Inv) {sp : Split}
    (hsp : XTrail.split S.trail = some sp) :
    (Trail.vars (XTrail.trail sp.above ++ [⟨sp.decision, true⟩])).Nodup := by
  have := hS.split_nodup hsp
  rw [XTrail.trail_append, XTrail.trail_cons, show XTrail.trail sp.above ++
    XEntry.entry (XEntry.decision sp.decision) :: XTrail.trail sp.below =
      (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) ++ XTrail.trail sp.below by simp,
    vars_append] at this
  exact this.of_append_left

theorem XTrail.falsifies_of_split {M : XTrail} {sp : Split} (hsp : XTrail.split M = some sp)
    {c : Clause ℕ} (hconf : Trail.Falsifies (XTrail.trail M) c) :
    Trail.Falsifies (XTrail.trail (sp.above ++ XEntry.decision sp.decision :: sp.below)) c := by
  rw [← (XTrail.split_eq_some hsp).1]
  exact hconf

/-- A clause false on the trail but not below its newest decision has a literal false at the
current level. -/
theorem exists_cur {A B : Trail} {d : Literal ℕ} {c : Clause ℕ}
    (hconf : Trail.Falsifies (A ++ ⟨d, true⟩ :: B) c) (hnb : ¬ Trail.Falsifies B c) :
    ∃ y ∈ c, y.negate ∈ Trail.lits (A ++ [⟨d, true⟩]) := by
  by_contra hne
  push Not at hne
  refine hnb fun y hy => ?_
  have := hconf y hy
  rw [show A ++ ⟨d, true⟩ :: B = (A ++ [⟨d, true⟩]) ++ B by simp, lits_append,
    List.mem_append] at this
  exact this.resolve_left (hne y hy)

theorem Exec.Inv.split_cur {S : Exec φ} (hS : S.Inv) {sp : Split}
    (hsp : XTrail.split S.trail = some sp) {e : ℕ × Clause ℕ} (he : e ∈ S.db)
    (hconf : Trail.Falsifies (XTrail.trail S.trail) e.2) :
    ∃ y ∈ e.2, y.negate ∈ Trail.lits (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) :=
  exists_cur (XTrail.trail_of_split hsp ▸ hconf)
    (hS.below _ _ _ (XTrail.trail_of_split hsp) e.2 (List.mem_map.2 ⟨e, he, rfl⟩))

/-- A clause learned at a conflict, above and below the newest decision of the split `sp`. -/
abbrev Exec.LearnedAt (S : Exec φ) (sp : Split) : Type :=
  Learned S.log (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) (XTrail.trail sp.below)

/-- Walking down the trail for `XTrail.dropLevels`: `acc` holds the entries of the current level
seen so far, newest last, and `hit` whether one of them is marked. At a decision, the level is
dropped if neither it nor its entries are marked, and otherwise kept with everything below; at the
bottom, the entries left are the root level, which is kept. -/
def XTrail.dropLevelsGo (marked : ℕ → Bool) : XTrail → Bool → XTrail → XTrail × XTrail
  | acc, _, [] => ([], acc.reverse)
  | acc, hit, x :: M =>
    match x with
    | .decision d =>
      if hit || marked d.1 then ([], acc.reverse ++ .decision d :: M)
      else
        let r := XTrail.dropLevelsGo marked [] false M
        (acc.reverse ++ .decision d :: r.1, r.2)
    | .implied l i => XTrail.dropLevelsGo marked (.implied l i :: acc) (hit || marked l.1) M

/-- **Dropping the newest levels** of the trail `M` none of whose variables is `marked`: the entries
dropped, and the trail kept. It reads the levels dropped and the first level kept, entry by
entry. -/
def XTrail.dropLevels (marked : ℕ → Bool) (M : XTrail) : XTrail × XTrail :=
  XTrail.dropLevelsGo marked [] false M

theorem XTrail.dropLevelsGo_spec (marked : ℕ → Bool) : ∀ (acc : XTrail) (hit : Bool) (M : XTrail),
    (∀ x ∈ acc, x.entry.decision = false) →
    hit = acc.any (fun x => marked x.entry.lit.1) →
    acc.reverse ++ M = (XTrail.dropLevelsGo marked acc hit M).1 ++
      (XTrail.dropLevelsGo marked acc hit M).2 ∧
    ((XTrail.dropLevelsGo marked acc hit M).1 = [] ∨
      ∃ J d, (XTrail.dropLevelsGo marked acc hit M).1 = J ++ [.decision d]) ∧
    (∀ x ∈ (XTrail.dropLevelsGo marked acc hit M).1, marked x.entry.lit.1 = false) ∧
    ((∀ x ∈ (XTrail.dropLevelsGo marked acc hit M).2, x.entry.decision = false) ∨
      ∃ N d M₀, (XTrail.dropLevelsGo marked acc hit M).2 = N ++ .decision d :: M₀ ∧
        (∀ x ∈ N, x.entry.decision = false) ∧
        (marked d.1 = true ∨ ∃ x ∈ N, marked x.entry.lit.1 = true))
  | acc, hit, [], hacc, _ => by
    refine ⟨by simp [dropLevelsGo], .inl rfl, by simp [dropLevelsGo], .inl ?_⟩
    simpa [dropLevelsGo] using hacc
  | acc, hit, x :: M, hacc, hhit => by
    cases x with
    | decision d =>
      simp only [dropLevelsGo]
      split
      · rename_i hm
        refine ⟨by simp, .inl rfl, by simp, .inr ⟨acc.reverse, d, M, rfl, by simpa using hacc, ?_⟩⟩
        rcases Bool.or_eq_true_iff.1 hm with h | h
        · subst hhit
          obtain ⟨x, hx, hxm⟩ := List.any_eq_true.1 h
          exact .inr ⟨x, List.mem_reverse.2 hx, hxm⟩
        · exact .inl h
      · rename_i hm
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hm
        obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ :=
          XTrail.dropLevelsGo_spec marked [] false M (by simp) (by simp)
        refine ⟨?_, .inr ?_, fun y hy => ?_, ih₄⟩
        · simp only [List.reverse_nil, List.nil_append] at ih₁
          conv_lhs => rw [ih₁]
          simp
        · rcases ih₂ with h | ⟨J, d', h⟩
          · exact ⟨acc.reverse, d, by simp [h]⟩
          · exact ⟨acc.reverse ++ .decision d :: J, d', by simp [h]⟩
        · simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hy
          rcases hy with hy | rfl | hy
          · subst hhit
            have := hm.1
            rw [List.any_eq_false] at this
            simpa using this y hy
          · exact hm.2
          · exact ih₃ y hy
    | implied l i =>
      simp only [dropLevelsGo]
      have := XTrail.dropLevelsGo_spec marked (.implied l i :: acc) (hit || marked l.1) M
        (fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · rfl
          · exact hacc y hy)
        (by subst hhit; simp [XEntry.entry, Bool.or_comm])
      simpa using this

/-- The entries dropped and the trail kept make up the trail; the entries dropped end with a
decision, if any, and none of their variables is marked; and the trail kept is the root, or its
newest level has a marked variable, in an implied entry or in the decision. -/
theorem XTrail.dropLevels_spec (marked : ℕ → Bool) (M : XTrail) :
    M = (XTrail.dropLevels marked M).1 ++ (XTrail.dropLevels marked M).2 ∧
    ((XTrail.dropLevels marked M).1 = [] ∨
      ∃ J d, (XTrail.dropLevels marked M).1 = J ++ [.decision d]) ∧
    (∀ x ∈ (XTrail.dropLevels marked M).1, marked x.entry.lit.1 = false) ∧
    ((∀ x ∈ (XTrail.dropLevels marked M).2, x.entry.decision = false) ∨
      ∃ N d M₀, (XTrail.dropLevels marked M).2 = N ++ .decision d :: M₀ ∧
        (∀ x ∈ N, x.entry.decision = false) ∧
        (marked d.1 = true ∨ ∃ x ∈ N, marked x.entry.lit.1 = true)) := by
  have := XTrail.dropLevelsGo_spec marked [] false M (by simp) (by simp)
  simpa [XTrail.dropLevels] using this

/-- **The backjump of a conflict** at the split `sp`, as MiniSat's: the entries undone, the newest
decision level and the levels below it with no `marked` variable, and the trail kept. With the
variables of the learned clause marked, the trail kept is the trail at the second highest level of
the learned clause (`Cslib.Algorithms.Lean.CDCL.Exec.jump_kept`). The cost is that of reading the
levels undone and the first level kept. -/
def Exec.jump (_S : Exec φ) (sp : Split) (marked : ℕ → Bool) : XTrail × XTrail :=
  let r := XTrail.dropLevels marked sp.below
  (sp.above ++ .decision sp.decision :: r.1, r.2)

/-- The entries undone end with a decision, and the learned clause is asserting on the trail
kept. -/
theorem Exec.jump_spec {S : Exec φ} {sp : Split} (hsp : XTrail.split S.trail = some sp)
    (L : S.LearnedAt sp) {marked : ℕ → Bool}
    (hmarked : ∀ v ∈ L.clause.map Prod.fst, marked v = true) :
    S.trail = (S.jump sp marked).1 ++ (S.jump sp marked).2 ∧
    (∃ J d, (S.jump sp marked).1 = J ++ [.decision d]) ∧
    (∀ y ∈ L.clause, y ≠ L.lit → y.negate ∈ Trail.lits (XTrail.trail (S.jump sp marked).2)) ∧
    L.lit.1 ∉ Trail.vars (XTrail.trail (S.jump sp marked).2) := by
  obtain ⟨h₁, h₂, h₃, -⟩ := XTrail.dropLevels_spec marked sp.below
  simp only [Exec.jump]
  set r := XTrail.dropLevels marked sp.below
  have hbelow : XTrail.trail sp.below = XTrail.trail r.1 ++ XTrail.trail r.2 := by
    conv_lhs => rw [h₁]
    exact XTrail.trail_append _ _
  refine ⟨?_, ?_, fun y hy hne => ?_, fun h => L.undef ?_⟩
  · rw [(XTrail.split_eq_some hsp).1]
    conv_lhs => rw [h₁]
    simp
  · rcases h₂ with h | ⟨J, d, h⟩
    · exact ⟨sp.above, sp.decision, by rw [h]⟩
    · exact ⟨sp.above ++ .decision sp.decision :: J, d, by rw [h]; simp⟩
  · have := L.false_below y hy hne
    rw [hbelow, lits_append, List.mem_append] at this
    refine this.resolve_left fun hU => ?_
    obtain ⟨e, he, hel⟩ := List.mem_map.1 hU
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    have hm := h₃ x hx
    rw [hel] at hm
    have := hmarked y.1 (List.mem_map.2 ⟨y, hy, rfl⟩)
    simp only [Std.Sat.Literal.negate] at hm
    rw [this] at hm
    exact absurd hm (by decide)
  · have hv : Trail.vars (XTrail.trail sp.below) =
        Trail.vars (XTrail.trail r.1) ++ Trail.vars (XTrail.trail r.2) := by
      rw [hbelow, vars_append]
    exact hv ▸ List.mem_append_right _ h

/-- **The target of the backjump**: the trail kept is the root, or its newest level has a marked
variable, in an implied entry or in the decision. With exactly the variables of the learned clause
marked, and none in the levels undone (`Cslib.Algorithms.Lean.CDCL.XTrail.dropLevels_spec`), this
is MiniSat's target: the highest level of the learned clause's literals other than the asserting
one, or the root for a unit clause. -/
theorem Exec.jump_kept {S : Exec φ} (sp : Split) {marked : ℕ → Bool} :
    (∀ x ∈ (S.jump sp marked).2, x.entry.decision = false) ∨
      ∃ N d M₀, (S.jump sp marked).2 = N ++ .decision d :: M₀ ∧
        (∀ x ∈ N, x.entry.decision = false) ∧
        (marked d.1 = true ∨ ∃ x ∈ N, marked x.entry.lit.1 = true) :=
  (XTrail.dropLevels_spec marked sp.below).2.2.2

/-- The state after Backjump and Learn, back to the trail `K` with the asserting literal implied by
the learned clause, the intermediate resolvents deleted from the log. -/
def Exec.afterConflictWith {sp : Split} (S : Exec φ) (L : S.LearnedAt sp) (K : XTrail) : Exec φ :=
  ⟨.implied L.lit L.id :: K, (L.id, L.clause) :: S.db,
    L.log.deleteRecent S.log.next L.id S.log.next_gt⟩

/-- The learned clause of a conflict, and the state after Backjump and Learn: back to the trail
kept by `Exec.jump`, with the asserting literal implied by the learned clause. The intermediate
resolvents of the analysis are deleted from the log. -/
def Exec.afterConflict (S : Exec φ) (sp : Split) (L : S.LearnedAt sp) (marked : ℕ → Bool) :
    Exec φ :=
  S.afterConflictWith L (S.jump sp marked).2

/-- Backjump and Learn keep the invariant and lower the rank. -/
theorem Exec.afterConflict_spec {S : Exec φ} (hS : S.Inv) {e : ℕ × Clause ℕ} (he : e ∈ S.db)
    (hconf : Trail.Falsifies (XTrail.trail S.trail) e.2) {sp : Split}
    (hsp : XTrail.split S.trail = some sp) (L : S.LearnedAt sp) {marked : ℕ → Bool}
    (hmarked : ∀ v ∈ L.clause.map Prod.fst, marked v = true) :
    (S.afterConflict sp L marked).Inv ∧
      rank φ.vars (S.afterConflict sp L marked).state < rank φ.vars S.state := by
  obtain ⟨hUK, ⟨J, d', hJ⟩, hfalseK, hundefK⟩ := Exec.jump_spec hsp L hmarked
  set K := (S.jump sp marked).2
  have hsplitK : XTrail.trail S.trail = XTrail.trail J ++ ⟨d', true⟩ :: XTrail.trail K := by
    conv_lhs => rw [hUK, hJ]
    simp [XTrail.trail_append, XTrail.trail_cons]
  have hsplit := XTrail.trail_of_split hsp
  have hc : e.2 ∈ S.clauses := List.mem_map.2 ⟨e, he, rfl⟩
  have hentails : ∀ σ, CNF.eval σ S.clauses = true → L.clause.eval σ = true :=
    fun σ hσ => L.log.eval_of_clause? L.clause?_eq (by rw [← hS.run.models]; exact hσ)
  have hbj : BasicStep (.run (XTrail.trail S.trail) S.clauses)
      (.run (⟨L.lit, false⟩ :: XTrail.trail K) S.clauses) := by
    -- the asserting literal is over a variable of the current level
    have hocc : L.lit.1 ∈ Trail.vars (XTrail.trail S.trail) := by
      have := Trail.mem_vars_of_mem_lits L.above
      rw [hsplit]
      simp only [Std.Sat.Literal.negate, Trail.vars, List.map_append, List.mem_append,
        List.map_cons, List.mem_cons, List.map_nil, List.not_mem_nil, or_false] at this ⊢
      tauto
    rw [hsplitK] at hconf hocc ⊢
    exact .backjump hc hconf hentails L.mem hfalseK hundefK (.inr hocc)
  have hlearn : Learn (.run (⟨L.lit, false⟩ :: XTrail.trail K) S.clauses)
      (.run (⟨L.lit, false⟩ :: XTrail.trail K) (L.clause :: S.clauses)) :=
    .learn hentails fun l hl => .inr (by
      by_cases hne : l = L.lit
      · subst hne; simp [Trail.vars]
      · have := Trail.mem_vars_of_mem_lits (hfalseK l hl hne)
        simp only [Std.Sat.Literal.negate] at this
        simp only [Trail.vars, List.map_cons, List.mem_cons] at this ⊢
        exact .inr this)
  have hrun₁ := Step.inv (.inl hbj) (show CDCL.Inv φ φ.vars (.run _ _) from hS.run)
  have hrun₂ := Step.inv (.inr (.inl hlearn)) hrun₁
  -- the deleted numbers are new, other than the learned clause's
  have hid : L.id ∉ LRATLog.recentIds S.log.next L.log.next L.id :=
    fun h => (LRATLog.mem_recentIds.1 h).2.2 rfl
  have hold : ∀ i, i < S.log.next → i ∉ LRATLog.recentIds S.log.next L.log.next L.id :=
    fun i hi h => by have := (LRATLog.mem_recentIds.1 h).1; omega
  have hroot : XTrail.root S.trail = XTrail.root K := by
    rw [hUK, hJ, List.append_assoc, List.singleton_append, XTrail.root_append_decision]
  refine ⟨⟨hrun₂, ?_, ?_, ?_, fun e' he' => ?_, fun r hr => ?_⟩, ?_⟩
  rotate_left 3
  · rcases hS.orig e' he' with h | ⟨l, hl, hlr⟩
    · exact .inl (List.mem_cons_of_mem _ h)
    · exact .inr ⟨l, hl, XTrail.lits_root_cons (hroot ▸ hlr)⟩
  · simp only [Exec.afterConflict, Exec.afterConflictWith, XTrail.reasonIds_implied,
      List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨L.clause, List.mem_cons_self⟩
    · obtain ⟨R, hR⟩ := hS.reasons_db r (by
        rw [hUK, XTrail.reasonIds_append]; exact List.mem_append_right _ hr)
      exact ⟨R, List.mem_cons_of_mem _ hR⟩
  rotate_left 1
  · have hbelow : Reasons S.log K := by
      have := hS.reasons
      rw [hUK] at this
      exact this.append_right
    refine .implied L.lit L.id
      ((hbelow.mono L.ext).deleteWith
        (hdb := LRATLog.dropRecent_eq S.log.next_gt L.log.ordered L.log.lt_next)
        fun r hr => hold r (hbelow.lt_next r hr))
      ((LRATLog.clause?_deleteRecent (hn := S.log.next_gt) hid).trans L.clause?_eq) L.mem hfalseK
  · intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact (LRATLog.clause?_deleteRecent (hn := S.log.next_gt) hid).trans L.clause?_eq
    · have hlog := hS.db_log e' he'
      exact (LRATLog.clause?_deleteRecent (hn := S.log.next_gt)
        (hold _ (LRATLog.lt_next_of_clause? hlog))).trans
        (L.ext _ _ hlog)
  · intro N d M₁ hN c hc'
    -- a split of the new trail is below the asserting literal, so a split of the old trail
    obtain ⟨x, N, rfl⟩ : ∃ x N', N = x :: N' := by
      cases N with
      | nil => simp [Exec.afterConflict, Exec.afterConflictWith] at hN
      | cons x N => exact ⟨x, N, rfl⟩
    simp only [Exec.afterConflict, Exec.afterConflictWith, XTrail.trail_cons, List.cons_append,
      List.cons.injEq] at hN
    obtain ⟨-, hN⟩ := hN
    rcases List.mem_cons.1 hc' with rfl | hc'
    · intro hfalse
      apply hundefK
      have := hfalse _ L.mem
      rw [congrArg Trail.vars hN]
      have hv := Trail.mem_vars_of_mem_lits this
      simp only [Trail.vars, Std.Sat.Literal.negate] at hv
      simp only [Trail.vars, List.map_append, List.map_cons, List.mem_append, List.mem_cons]
      exact .inr (.inr hv)
    · exact hS.below (XTrail.trail J ++ ⟨d', true⟩ :: N) d M₁
        (by rw [hsplitK, hN]; simp) c hc'
  · change rank φ.vars (.run (⟨L.lit, false⟩ :: XTrail.trail K) (L.clause :: S.clauses)) <
      rank φ.vars (.run (XTrail.trail S.trail) S.clauses)
    exact (LearnOrForget.rank_eq (.inl hlearn)).trans_lt (hbj.rank_lt hS.run)

/-- A unit clause of the database under the assignment `A`: a numbered clause with every literal but
one false, that literal being unassigned. -/
def findUnit (A : Assign) (db : List (ℕ × Clause ℕ)) : Option ((ℕ × Clause ℕ) × Literal ℕ) :=
  db.findSome? fun e => (e.2.find? fun l =>
    !A.assigned l.1 && e.2.all fun l' => l' == l || A.holds l'.negate).map (e, ·)

theorem findUnit_spec {A : Assign} {M : Trail} (hA : A.Agrees M) {db : List (ℕ × Clause ℕ)}
    {e : ℕ × Clause ℕ} {l : Literal ℕ} (h : findUnit A db = some (e, l)) :
    e ∈ db ∧ l ∈ e.2 ∧ l.1 ∉ Trail.vars M ∧ ∀ l' ∈ e.2, l' ≠ l → l'.negate ∈ Trail.lits M := by
  obtain ⟨e', he', h'⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨l', hl', hel⟩ := Option.map_eq_some_iff.1 h'
  cases hel
  have := List.find?_some hl'
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq] at this
  refine ⟨he', List.mem_of_find?_eq_some hl', fun hv => ?_, fun l' hl' hne => ?_⟩
  · rw [(hA.assigned_iff _).2 hv] at this
    exact absurd this.1 (by decide)
  · exact (hA.holds_iff _).1 ((this.2 l' hl').resolve_left hne)

/-- **UnitPropagate**: add the literal of a unit clause, with that clause as its reason. -/
def Exec.propagate (S : Exec φ) (e : ℕ × Clause ℕ) (l : Literal ℕ) : Exec φ :=
  ⟨.implied l e.1 :: S.trail, S.db, S.log⟩

/-- UnitPropagate with a clause of the database keeps the invariant and lowers the rank. -/
theorem Exec.propagate_spec {S : Exec φ} (hS : S.Inv) {e : ℕ × Clause ℕ} {l : Literal ℕ}
    (he : e ∈ S.db) (hl : l ∈ e.2) (hundef : l.1 ∉ Trail.vars (XTrail.trail S.trail))
    (hfalse : ∀ l' ∈ e.2, l' ≠ l → l'.negate ∈ Trail.lits (XTrail.trail S.trail)) :
    (S.propagate e l).Inv ∧ rank φ.vars (S.propagate e l).state < rank φ.vars S.state := by
  have hc : e.2 ∈ S.clauses := List.mem_map.2 ⟨e, he, rfl⟩
  have hstep : BasicStep (.run (XTrail.trail S.trail) S.clauses)
      (.run (⟨l, false⟩ :: XTrail.trail S.trail) S.clauses) :=
    .unitPropagate hc hl hfalse hundef
  refine ⟨⟨Step.inv (.inl hstep) (show CDCL.Inv φ φ.vars (.run _ _) from hS.run),
    .implied l e.1 hS.reasons (hS.db_log e he) hl hfalse, hS.db_log, ?_,
    fun e' he' => (hS.orig e' he').imp id fun ⟨l', hl', hr⟩ => ⟨l', hl', XTrail.lits_root_cons hr⟩,
    fun r hr => by
      simp only [Exec.propagate, XTrail.reasonIds_implied, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨e.2, he⟩
      · exact hS.reasons_db r hr⟩,
    hstep.rank_lt hS.run⟩
  intro N d M₁ hN c hc'
  cases N with
  | nil => simp [Exec.propagate] at hN
  | cons x N =>
    simp only [Exec.propagate, XTrail.trail_cons, List.cons_append, List.cons.injEq] at hN
    exact hS.below N d M₁ hN.2 c hc'

/-- **Decide**: add the literal of the variable `x` with polarity `b` as a decision. -/
def Exec.decide (S : Exec φ) (x : ℕ) (b : Bool) : Exec φ :=
  ⟨.decision (x, b) :: S.trail, S.db, S.log⟩

theorem Exec.decide_spec {S : Exec φ} (hS : S.Inv)
    (hnoconf : ∀ c ∈ S.clauses, ¬ Trail.Falsifies (XTrail.trail S.trail) c) {x : ℕ}
    (hx : x ∈ S.clauses.vars) (hundef : x ∉ Trail.vars (XTrail.trail S.trail)) (b : Bool) :
    (S.decide x b).Inv ∧ rank φ.vars (S.decide x b).state < rank φ.vars S.state := by
  have hstep : BasicStep (.run (XTrail.trail S.trail) S.clauses)
      (.run (⟨(x, b), true⟩ :: XTrail.trail S.trail) S.clauses) :=
    .decide (l := (x, b)) hundef hx
  refine ⟨⟨Step.inv (.inl hstep) (show CDCL.Inv φ φ.vars (.run _ _) from hS.run),
    .decision _ hS.reasons, hS.db_log, ?_,
    fun e' he' => (hS.orig e' he').imp id fun ⟨l', hl', hr⟩ => ⟨l', hl', XTrail.lits_root_cons hr⟩,
    fun r hr => hS.reasons_db r hr⟩, hstep.rank_lt hS.run⟩
  intro N d M₁ hN c hc'
  cases N with
  | nil =>
    simp only [Exec.decide, XTrail.trail_cons, List.nil_append, List.cons.injEq] at hN
    rw [← hN.2]
    exact hnoconf c hc'
  | cons y N =>
    simp only [Exec.decide, XTrail.trail_cons, List.cons_append, List.cons.injEq] at hN
    exact hS.below N d M₁ hN.2 c hc'


/-! ### Restarts -/

/-- **Restart**: going back to the root of the trail, keeping the database and the log. -/
def Exec.restart (S : Exec φ) : Exec φ := ⟨XTrail.root S.trail, S.db, S.log⟩

/-- Restart keeps the invariant. -/
theorem Exec.restart_inv {S : Exec φ} (hS : S.Inv) : S.restart.Inv := by
  obtain ⟨A, hA⟩ := XTrail.root_suffix S.trail
  have hrun := hS.run
  have hreasons := hS.reasons
  rw [hA] at hrun hreasons
  rw [XTrail.trail_append] at hrun
  have hnodup := hrun.nodup
  rw [vars_append] at hnodup
  refine ⟨⟨hrun.models, hrun.pmodels, hnodup.of_append_right, fun x hx => hrun.subset x
    (by rw [vars_append]; exact List.mem_append_right _ hx), hrun.db_vars,
    Trail.entailed_append hrun.entailed⟩, hreasons.append_right, hS.db_log, ?_,
    fun e' he' => by
      change e' ∈ S.db ∨
        ∃ l ∈ e'.2, l ∈ Trail.lits (XTrail.trail (XTrail.root (XTrail.root S.trail)))
      rw [XTrail.root_root]; exact hS.orig e' he',
    fun r hr => hS.reasons_db r (XTrail.mem_reasonIds_root hr)⟩
  intro N d M₀ hN
  have hd : (⟨d, true⟩ : Entry) ∈ XTrail.trail (XTrail.root S.trail) := by
    change _ ∈ XTrail.trail S.restart.trail
    rw [hN]; simp
  obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hd
  have := XTrail.root_no_decision S.trail x hx
  rw [hxe] at this
  exact absurd this (by simp)

/-! ### Forgetting clauses -/

/-- The numbers of the clauses of `φ` are at most its length. -/
theorem le_length_of_mem_lratDB {e : ℕ × Clause ℕ} (he : e ∈ φ.lratDB) : e.1 ≤ φ.length := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
  have := List.snd_lt_add_of_mem_zipIdx hp
  simp only at this ⊢
  omega

/-- Every clause of `φ` has a number. -/
theorem exists_mem_lratDB {c : Clause ℕ} (hc : c ∈ φ) : ∃ e ∈ φ.lratDB, e.2 = c := by
  rw [← List.zipIdx_map_fst 0 φ] at hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  exact ⟨(p.2 + 1, p.1), List.mem_map.2 ⟨p, hp, rfl⟩, rfl⟩

/-- **Forget**: deleting the clauses numbered `ids` from the database and the log. -/
def Exec.forget (S : Exec φ) (ids : List ℕ) : Exec φ :=
  ⟨S.trail, S.db.filter fun e => !ids.contains e.1, S.log.delete ids⟩

/-- **Forgetting clauses** keeps the invariant, if they are not reasons of the trail, and the
clauses of `φ` among them are satisfied by the root of the trail. The reasons kept entail the root
(`Cslib.Algorithms.Lean.CDCL.Reasons.eval_of_no_decision`), so the remaining clauses still have the
models of `φ`, and their partial models, through the root, satisfy `φ`. This does not show that
each removed clause is partially entailed by the remaining ones, the side condition of the abstract
`Forget` rule; the invariant does not need it. -/
theorem Exec.forget_inv {S : Exec φ} (hS : S.Inv) {ids : List ℕ}
    (horig : ∀ e ∈ S.db, e ∈ φ.lratDB → e.1 ∈ ids →
      ∃ l ∈ e.2, l ∈ Trail.lits (XTrail.trail (XTrail.root S.trail)))
    (hreasons : ∀ r ∈ XTrail.reasonIds S.trail, r ∉ ids) :
    (S.forget ids).Inv := by
  have hmem : ∀ e ∈ (S.forget ids).db, e ∈ S.db ∧ e.1 ∉ ids := fun e he => by
    have := List.mem_filter.1 he
    exact ⟨this.1, by simpa using this.2⟩
  have hmem' : ∀ e ∈ S.db, e.1 ∉ ids → e ∈ (S.forget ids).db := fun e he hid =>
    List.mem_filter.2 ⟨he, by simpa using hid⟩
  have hsub : ∀ c ∈ (S.forget ids).clauses, c ∈ S.clauses := fun c hc => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    exact List.mem_map.2 ⟨e, (hmem e he).1, rfl⟩
  have hkeep : ∀ e ∈ φ.lratDB, e ∈ (S.forget ids).db ∨
      ∃ l ∈ e.2, l ∈ Trail.lits (XTrail.trail (XTrail.root S.trail)) := fun e he => by
    rcases hS.orig e he with h | h
    · by_cases hid : e.1 ∈ ids
      · exact .inr (horig e h he hid)
      · exact .inl (hmem' e h hid)
    · exact .inr h
  have hreasons_db : ∀ r ∈ XTrail.reasonIds S.trail, ∃ R, (r, R) ∈ (S.forget ids).db :=
    fun r hr => by
      obtain ⟨R, hR⟩ := hS.reasons_db r hr
      exact ⟨R, hmem' _ hR (hreasons r hr)⟩
  have hrun := hS.run
  refine ⟨⟨fun σ => ?_, fun ρ hρ c hc => ?_, hrun.nodup, hrun.subset,
    fun c hc => hrun.db_vars c (hsub c hc), hrun.entailed⟩, hS.reasons.delete hreasons,
    fun e he => ?_, fun N d M₀ hN c hc => hS.below N d M₀ hN c (hsub c hc), hkeep, hreasons_db⟩
  · apply Bool.eq_iff_iff.2
    rw [CNF.eval_eq_true_iff, CNF.eval_eq_true_iff]
    refine ⟨fun h c hc => ?_, fun h c hc => ?_⟩
    · -- the root holds, so the clauses of `φ` it satisfies do too
      have hroot : ∀ l ∈ Trail.lits (XTrail.trail (XTrail.root S.trail)),
          Literal.eval σ l = true := by
        obtain ⟨A, hA⟩ := XTrail.root_suffix S.trail
        have hR := hS.reasons
        rw [hA] at hR
        exact Reasons.eval_of_no_decision (db := (S.forget ids).db)
          (fun e he => hS.db_log e (hmem e he).1)
          (fun e he => h e.2 (List.mem_map.2 ⟨e, he, rfl⟩)) hR.append_right
          (XTrail.root_no_decision _)
          (fun r hr => hreasons_db r (XTrail.mem_reasonIds_root hr))
      obtain ⟨e, he, rfl⟩ := exists_mem_lratDB hc
      rcases hkeep e he with h' | ⟨l, hl, hlr⟩
      · exact h e.2 (List.mem_map.2 ⟨e, h', rfl⟩)
      · exact (Clause.eval_eq_true_iff σ e.2).2
          ⟨l, hl, (Literal.eval_eq_true_iff σ l).1 (hroot l hlr)⟩
    · have hall := (CNF.eval_eq_true_iff σ S.clauses).1
        (by rw [hrun.models]; exact (CNF.eval_eq_true_iff σ φ).2 h)
      exact hall c (hsub c hc)
  · -- a partial model of the remaining clauses makes the root true, so it satisfies the
    -- clauses of `φ` that the root satisfies
    have hroot : ∀ l ∈ Trail.lits (XTrail.trail (XTrail.root S.trail)), ρ l.1 = some l.2 := by
      obtain ⟨A, hA⟩ := XTrail.root_suffix S.trail
      have hR := hS.reasons
      rw [hA] at hR
      exact Reasons.psat_of_no_decision (db := (S.forget ids).db)
        (fun e he => hS.db_log e (hmem e he).1)
        (fun e he => hρ e.2 (List.mem_map.2 ⟨e, he, rfl⟩)) hR.append_right
        (XTrail.root_no_decision _)
        (fun r hr => hreasons_db r (XTrail.mem_reasonIds_root hr))
    obtain ⟨e, he, rfl⟩ := exists_mem_lratDB hc
    rcases hkeep e he with h' | ⟨l, hl, hlr⟩
    · exact hρ e.2 (List.mem_map.2 ⟨e, h', rfl⟩)
    · exact ⟨l, hl, hroot l hlr⟩
  · obtain ⟨he, hid⟩ := hmem e he
    exact (LRATLog.clause?_delete hid).trans (hS.db_log e he)

/-- Forgetting leaves the trail, hence the rank, unchanged. -/
theorem Exec.rank_forget (S : Exec φ) (ids : List ℕ) :
    rank φ.vars (S.forget ids).state = rank φ.vars S.state := rfl

end Cslib.Algorithms.Lean.CDCL
