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
  newest first, derives the empty clause (`Cslib.Algorithms.Lean.CDCL.refute`). The resolvents are
  not built: the variables met are marked, and the certificate is the log closed by one
  empty-clause step hinting the reasons resolved, oldest first, and the conflict clause
  (`Cslib.Algorithms.Lean.CDCL.Refutation.cert`).
* If a clause is false and the trail has a decision, *first-UIP analysis*
  (`Cslib.Algorithms.Lean.CDCL.analyze`) resolves it with the reasons of the newest implied
  literals until exactly one of its literals is false at the current level. As in MiniSat, the
  resolvents are not built: the variables met are marked in an array, the literals below the
  current level are collected, and the marked variables of the current level not yet passed are
  counted (`Cslib.Algorithms.Lean.CDCL.Marks`). The invariant of the analysis guarantees an
  asserting clause: the count is never zero, and at the decision only the decision's variable can
  be counted. It also guarantees the hints of the learned clause, the reasons resolved, oldest
  first, and then the conflict clause: they refute the clause that the marks describe
  (`Cslib.Logic.PL.CNF.RupHints`), which is the resolvent so far. The solver backjumps, as MiniSat
  does, to the second-highest level of the learned clause: below the newest decision and every
  level below it with no variable of the clause (`Cslib.Algorithms.Lean.CDCL.Exec.jump`, without
  decision levels). It adds the asserting literal with the learned clause as its reason, and learns
  the clause, adding it to the log as one RUP step (Backjump and Learn,
  `Cslib.Algorithms.Lean.CDCL.Exec.afterConflict`).
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
Every learned clause enters the certificate as one RUP step whose hints are proved to propagate to
a conflict, so the checker accepts the certificate by construction, with no check at run time
(`Cslib.Logic.PL.CNF.LRATLog.checkLRAT_finish`).

**Scope.** `Exec` does not choose decisions: the solver with watched literals chooses them
(`Cslib.Algorithms.Lean.CDCL.Activity`).

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.Exec`, `Cslib.Algorithms.Lean.CDCL.Exec.Inv`: the state and its
  invariant.
* `Cslib.Algorithms.Lean.CDCL.analyze`: first-UIP conflict analysis, with its marks
  `Cslib.Algorithms.Lean.CDCL.Marks`, and the learned clause `Cslib.Algorithms.Lean.CDCL.Learned`.
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
theorem Reasons.delete {log : LRATLog φ} {ids : List ℕ} {M : XTrail} (h : Reasons log M)
    (hids : ∀ r ∈ XTrail.reasonIds M, r ∉ ids) : Reasons (log.delete ids) M := by
  induction h with
  | nil => exact .nil
  | decision l _ ih => exact .decision l (ih (by simpa using hids))
  | implied l r _ hr hl hfalse ih =>
    have hr' : r ∉ ids := hids r (by simp)
    exact .implied l r (ih fun r' h' => hids r' (by simp [h']))
      ((LRATLog.clause?_delete hr').trans hr) hl hfalse

/-- The negation is injective. -/
theorem negate_inj {l l' : Literal ℕ} (h : l.negate = l'.negate) : l = l' := by
  obtain ⟨v, b⟩ := l
  obtain ⟨v', b'⟩ := l'
  cases b <;> cases b' <;> simp_all [Std.Sat.Literal.negate]

private theorem negate_eq_iff {y l : Literal ℕ} : y.negate = l ↔ y = l.negate :=
  ⟨fun h => by subst h; simp, fun h => by subst h; simp⟩

theorem lits_append (M N : Trail) : Trail.lits (M ++ N) = Trail.lits M ++ Trail.lits N :=
  List.map_append ..

theorem vars_append (M N : Trail) : Trail.vars (M ++ N) = Trail.vars M ++ Trail.vars N :=
  List.map_append ..

theorem mem_lits_cons {e : Entry} {M : Trail} {y : Literal ℕ} :
    y ∈ Trail.lits (e :: M) ↔ y = e.lit ∨ y ∈ Trail.lits M := by
  simp [Trail.lits]

/-- On a trail assigning each variable once, a literal is determined by its variable. -/
theorem eq_of_mem_lits {M : Trail} (hM : (Trail.vars M).Nodup) {a b : Literal ℕ}
    (ha : a ∈ Trail.lits M) (hb : b ∈ Trail.lits M) (h : a.1 = b.1) : a = b := by
  induction M with
  | nil => simp [Trail.lits] at ha
  | cons e M ih =>
    simp only [Trail.vars, List.map_cons, List.nodup_cons] at hM
    rw [mem_lits_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd (by rw [show e.var = b.1 from h]; exact Trail.mem_vars_of_mem_lits hb) hM.1
    · exact absurd (by rw [show e.var = a.1 from h.symm]; exact Trail.mem_vars_of_mem_lits ha) hM.1
    · exact ih hM.2 ha hb

/-! ### Conflict analysis with marks -/

/-- **The state of conflict analysis**, as MiniSat keeps it: the array of the variables `seen`, the
literals `out` of the analysed clause false below the current level, the number `path` of seen
variables of the current level not yet passed, and the variables seen, newest first. -/
structure Marks where
  /-- The variables seen, as an array. -/
  seen : Assign
  /-- The literals of the analysed clause false below the current level. -/
  out : Clause ℕ
  /-- The seen variables of the current level not yet passed. -/
  path : ℕ
  /-- The variables seen, newest first. -/
  vars : List ℕ

/-- Nothing seen. -/
def Marks.empty : Marks := ⟨⟨#[]⟩, [], 0, []⟩

/-- **The analysed clause** of the state `m`, with the entries `Cur` of the current level still to
pass: the literals of `out`, and the negations of the literals of `Cur` whose variables are seen.
It is never built; the hints of the learned clause refute it (`Cslib.Logic.PL.CNF.RupHints`). -/
def Marks.clause (m : Marks) (Cur : Trail) (y : Literal ℕ) : Prop :=
  y ∈ m.out ∨ (m.seen.assigned y.1 = true ∧ y.negate ∈ Trail.lits Cur)

/-- **Adding the literals of a clause** to the analysis: each literal on a variable not yet seen is
seen; it counts on the path if its negation is on the current level, whose literals `cur` holds,
and goes to `out` otherwise. -/
def Marks.absorb (cur : Assign) : Marks → Clause ℕ → Marks
  | m, [] => m
  | m, y :: R =>
    if m.seen.assigned y.1 then Marks.absorb cur m R
    else if cur.holds y.negate then
      Marks.absorb cur ⟨m.seen.set y.1 (some true), m.out, m.path + 1, y.1 :: m.vars⟩ R
    else Marks.absorb cur ⟨m.seen.set y.1 (some true), y :: m.out, m.path, y.1 :: m.vars⟩ R

/-- The invariant of the analysis, with the entries `Cur` of the current level still to pass, the
trail `M₀` below it, and the variables `V` of the formula: the literals of `out` are false below the
current level, and are those of the seen variables there; `path` counts the seen variables of
`Cur`; and `vars` lists the seen variables, of `V`. -/
structure Marks.Inv (m : Marks) (Cur M₀ : Trail) (V : List ℕ) : Prop where
  out_below : ∀ y ∈ m.out, y.negate ∈ Trail.lits M₀
  out_seen : ∀ y ∈ m.out, m.seen.assigned y.1 = true
  below_out : ∀ y, y.negate ∈ Trail.lits M₀ → m.seen.assigned y.1 = true → y ∈ m.out
  path_eq : m.path = Cur.countP fun e => m.seen.assigned e.lit.1
  seen_iff : ∀ v, m.seen.assigned v = true ↔ v ∈ m.vars
  vars_mem : ∀ v ∈ m.vars, v ∈ V

theorem Marks.inv_empty (Cur M₀ : Trail) (V : List ℕ) : Marks.empty.Inv Cur M₀ V where
  out_below := by simp [Marks.empty]
  out_seen := by simp [Marks.empty]
  below_out _ _ h := by simp [Marks.empty, Assign.assigned, Assign.value] at h
  path_eq := by
    simp [Marks.empty, Assign.assigned, Assign.value]
  seen_iff _ := by simp [Marks.empty, Assign.assigned, Assign.value]
  vars_mem := by simp [Marks.empty]

/-- Seeing the variable `v` adds one to the count of the seen variables of a trail assigning each
variable once, if it is one of its variables. -/
private theorem countP_set_seen {s : Assign} {v : ℕ} (hv : s.assigned v = false) :
    ∀ {Cur : Trail}, (Trail.vars Cur).Nodup →
      (Cur.countP fun e => (s.set v (some true)).assigned e.lit.1) =
        (Cur.countP fun e => s.assigned e.lit.1) + if v ∈ Trail.vars Cur then 1 else 0
  | [], _ => by simp [Trail.vars]
  | e :: Cur, hnd => by
    simp only [Trail.vars, List.map_cons, List.nodup_cons] at hnd
    rw [List.countP_cons, List.countP_cons, countP_set_seen hv hnd.2, Assign.assigned_set]
    by_cases he : e.lit.1 = v
    · subst he
      have h₁ : e.lit.1 ∈ Trail.vars (e :: Cur) := List.mem_cons_self
      have h₂ : e.lit.1 ∉ Trail.vars Cur := hnd.1
      simp only [h₁, h₂, hv, ↓reduceIte, Option.isSome_some, Bool.false_eq_true]
    · have : (v ∈ Trail.vars (e :: Cur)) ↔ v ∈ Trail.vars Cur := by
        simp [Trail.vars, Ne.symm he]
      simp only [he, ↓reduceIte, this]
      omega

theorem Marks.Inv.clause_of_seen {m : Marks} {Cur M₀ : Trail} {V : List ℕ} (hm : m.Inv Cur M₀ V)
    {y : Literal ℕ} (hs : m.seen.assigned y.1 = true)
    (hy : y.negate ∈ Trail.lits Cur ∨ y.negate ∈ Trail.lits M₀) : m.clause Cur y :=
  hy.elim (fun h => .inr ⟨hs, h⟩) fun h => .inl (hm.below_out y h hs)

/-- **Adding a clause** keeps the invariant, if the literals of the clause on variables not yet
seen are false on the current level or below; every variable of the clause is seen afterwards,
and nothing seen or in `out` is lost. -/
theorem Marks.absorb_spec {cur : Assign} {Cur M₀ : Trail} {V : List ℕ} (hcur : cur.Agrees Cur)
    (hnd : (Trail.vars (Cur ++ M₀)).Nodup) :
    ∀ (m : Marks) (R : Clause ℕ), m.Inv Cur M₀ V → (∀ y ∈ R, y.1 ∈ V) →
      (∀ y ∈ R, m.seen.assigned y.1 = false →
        y.negate ∈ Trail.lits Cur ∨ y.negate ∈ Trail.lits M₀) →
      (m.absorb cur R).Inv Cur M₀ V ∧ (∀ y ∈ R, (m.absorb cur R).seen.assigned y.1 = true) ∧
      (∀ v, m.seen.assigned v = true → (m.absorb cur R).seen.assigned v = true) ∧
      (∀ y ∈ m.out, y ∈ (m.absorb cur R).out)
  | m, [], hm, _, _ => ⟨hm, by simp, fun _ h => h, fun _ h => h⟩
  | m, y :: R, hm, hV, hR => by
    rw [vars_append] at hnd
    have hdisj := List.disjoint_of_nodup_append hnd
    have hndM : (Trail.vars M₀).Nodup := hnd.of_append_right
    have hndC : (Trail.vars Cur).Nodup := hnd.of_append_left
    rw [← vars_append] at hnd
    have hV' : ∀ z ∈ R, z.1 ∈ V := fun z hz => hV z (List.mem_cons_of_mem _ hz)
    simp only [Marks.absorb]
    split
    · rename_i hs
      obtain ⟨h₁, h₂, h₃, h₄⟩ := Marks.absorb_spec hcur hnd m R hm hV'
        fun z hz => hR z (List.mem_cons_of_mem _ hz)
      refine ⟨h₁, fun z hz => ?_, h₃, h₄⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact h₃ _ hs
      · exact h₂ z hz
    · rename_i hs
      have hs' : m.seen.assigned y.1 = false := by simpa using hs
      have hy := hR y List.mem_cons_self hs'
      -- seeing `y.1` keeps what was seen
      have hmono : ∀ v, m.seen.assigned v = true → (m.seen.set y.1 (some true)).assigned v = true :=
        fun v hv => by rw [Assign.assigned_set]; split <;> simp [hv]
      have hR' : ∀ z ∈ R, (m.seen.set y.1 (some true)).assigned z.1 = false →
          z.negate ∈ Trail.lits Cur ∨ z.negate ∈ Trail.lits M₀ := fun z hz hz' => by
        refine hR z (List.mem_cons_of_mem _ hz) ?_
        cases h : m.seen.assigned z.1
        · rfl
        · rw [hmono _ h] at hz'; exact hz'
      have hseen_iff : ∀ v, (m.seen.set y.1 (some true)).assigned v = true ↔ v ∈ y.1 :: m.vars :=
        fun v => by
          rw [Assign.assigned_set, List.mem_cons, ← hm.seen_iff]
          by_cases hv : v = y.1 <;> simp [hv]
      have hvars : ∀ v ∈ y.1 :: m.vars, v ∈ V := fun v hv => by
        rcases List.mem_cons.1 hv with rfl | hv
        · exact hV y List.mem_cons_self
        · exact hm.vars_mem v hv
      have hfin : ∀ (m' : Marks), m'.seen = m.seen.set y.1 (some true) →
          (∀ z ∈ m.out, z ∈ m'.out) → m'.Inv Cur M₀ V →
          (m'.absorb cur R).Inv Cur M₀ V ∧
            (∀ z ∈ y :: R, (m'.absorb cur R).seen.assigned z.1 = true) ∧
            (∀ v, m.seen.assigned v = true → (m'.absorb cur R).seen.assigned v = true) ∧
            (∀ z ∈ m.out, z ∈ (m'.absorb cur R).out) := fun m' hseen hout hm' => by
        obtain ⟨h₁, h₂, h₃, h₄⟩ := Marks.absorb_spec hcur hnd m' R hm' hV' (hseen ▸ hR')
        refine ⟨h₁, fun z hz => ?_, fun v hv => h₃ v (hseen ▸ hmono v hv),
          fun z hz => h₄ z (hout z hz)⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact h₃ _ (by rw [hseen, Assign.assigned_set]; simp)
        · exact h₂ z hz
      split
      · rename_i hc
        have hyc : y.negate ∈ Trail.lits Cur := (hcur.holds_iff _).1 hc
        have hyv : y.1 ∈ Trail.vars Cur := by
          simpa [Std.Sat.Literal.negate] using Trail.mem_vars_of_mem_lits hyc
        refine hfin _ rfl (fun z hz => hz) ⟨hm.out_below, fun z hz => hmono _ (hm.out_seen z hz),
          fun z hz hzs => ?_, ?_, hseen_iff, hvars⟩
        · rw [Assign.assigned_set] at hzs
          split at hzs
          · rename_i hzy
            have : z.1 ∈ Trail.vars M₀ := by
              simpa [Std.Sat.Literal.negate] using Trail.mem_vars_of_mem_lits hz
            exact absurd (hzy ▸ this) (hdisj hyv)
          · exact hm.below_out z hz hzs
        · simp only
          rw [countP_set_seen hs' hndC, ← hm.path_eq, ite_eq_left hyv]
      · rename_i hc
        have hyM : y.negate ∈ Trail.lits M₀ :=
          hy.resolve_left fun h => hc ((hcur.holds_iff _).2 h)
        have hyv : y.1 ∉ Trail.vars Cur := fun h => hdisj h (by
          simpa [Std.Sat.Literal.negate] using Trail.mem_vars_of_mem_lits hyM)
        refine hfin _ rfl (fun z hz => List.mem_cons_of_mem _ hz) ⟨fun z hz => ?_,
          fun z hz => ?_, fun z hz hzs => ?_, ?_, hseen_iff, hvars⟩
        · rcases List.mem_cons.1 hz with rfl | hz
          · exact hyM
          · exact hm.out_below z hz
        · rcases List.mem_cons.1 hz with rfl | hz
          · simp [Assign.assigned_set]
          · exact hmono _ (hm.out_seen z hz)
        · rw [Assign.assigned_set] at hzs
          split at hzs
          · rename_i hzy
            have : z.negate = y.negate := eq_of_mem_lits hndM hz hyM (by
              simpa [Std.Sat.Literal.negate] using hzy)
            rw [negate_inj this]
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hm.below_out z hz hzs)
        · simp only
          rw [countP_set_seen hs' hndC, ← hm.path_eq, ite_eq_right hyv]
          rfl

/-- Passing an entry of the current level: if its variable is not seen, nothing changes. -/
theorem Marks.Inv.pass {m : Marks} {e : Entry} {Cur M₀ : Trail} {V : List ℕ}
    (hm : m.Inv (e :: Cur) M₀ V) (he : m.seen.assigned e.lit.1 = false) : m.Inv Cur M₀ V :=
  { hm with
    path_eq := by rw [hm.path_eq, List.countP_cons, he]; rfl }

/-- Passing an entry of the current level whose variable is seen takes one off the path. -/
theorem Marks.Inv.resolve {m : Marks} {e : Entry} {Cur M₀ : Trail} {V : List ℕ}
    (hm : m.Inv (e :: Cur) M₀ V) (he : m.seen.assigned e.lit.1 = true) :
    (⟨m.seen, m.out, m.path - 1, m.vars⟩ : Marks).Inv Cur M₀ V :=
  { hm with
    path_eq := by
      have := hm.path_eq
      rw [List.countP_cons, he] at this
      simp only [↓reduceIte] at this
      simp only
      omega }

/-- A learned clause: a clause all of whose literals but `lit` are false in the trail `M₀`, where
`lit` is undefined, and whose negation is among the literals `A` above `M₀`, with hints along which
unit propagation in the log refutes it. Adding it to the log
(`Cslib.Algorithms.Lean.CDCL.Learned.log`) is one RUP step. -/
structure Learned (log : LRATLog φ) (A M₀ : Trail) where
  /-- The learned clause. -/
  clause : Clause ℕ
  /-- The asserting literal. -/
  lit : Literal ℕ
  /-- The hints of the RUP step: the reasons resolved, oldest first, and the conflict clause. -/
  hints : List ℕ
  /-- The variables met by the analysis: those of the conflict clause and of the reasons resolved.
  Branching heuristics bump them. -/
  seen : List ℕ
  /-- The numbers of the clauses met by the analysis: the conflict clause and the reasons resolved.
  Clause activities bump them. -/
  used : List ℕ
  seen_mem : ∀ v ∈ seen, v ∈ φ.vars
  rup : propagateHints log.db (clause.map Std.Sat.Literal.negate) hints = true
  vars_mem : ∀ l ∈ clause, l.1 ∈ φ.vars
  mem : lit ∈ clause
  false_below : ∀ y ∈ clause, y ≠ lit → y.negate ∈ Trail.lits M₀
  undef : lit.1 ∉ Trail.vars M₀
  above : lit.negate ∈ Trail.lits A
  /-- The assignment array the analysis was reading when it stopped, returned so that the solver
  can clear it and use it again: it has values only for variables of `A`. -/
  marks : Assign
  marks_none : ∀ v, v ∉ Trail.vars A → marks.value v = none

namespace Learned

variable {log₀ : LRATLog φ} {A M₀ : Trail}

/-- The log with the learned clause added, as one RUP step. -/
def log (L : Learned log₀ A M₀) : LRATLog φ := log₀.addRup L.clause L.hints L.rup L.vars_mem

/-- The number of the learned clause in `L.log`. -/
def id (_L : Learned log₀ A M₀) : ℕ := log₀.next

theorem clause?_eq (L : Learned log₀ A M₀) : L.log.clause? L.id = some L.clause :=
  LRATLog.clause?_addRup

theorem ext (L : Learned log₀ A M₀) : log₀.Extends L.log := LRATLog.extends_addRup

end Learned

/-- **The learned clause at the first unique implication point** `l`, the entry of the current
level `⟨l, b⟩ :: Cur` whose variable is the only one seen there: the negation of `l` and the
literals `out`. -/
def Marks.learned (log : LRATLog φ) {A M₀ Cur : Trail} (m : Marks) (l : Literal ℕ) (b : Bool)
    (hm : m.Inv (⟨l, b⟩ :: Cur) M₀ φ.vars) (hl : m.seen.assigned l.1 = true) (hp : m.path = 1)
    (hints : List ℕ) (hh : RupHints log.db (m.clause (⟨l, b⟩ :: Cur)) hints)
    (hlA : l ∈ Trail.lits A) (hlM : l.1 ∉ Trail.vars M₀) (cur : Assign)
    (hcur : ∀ v, v ∉ Trail.vars A → cur.value v = none) : Learned log A M₀ where
  clause := l.negate :: m.out
  lit := l.negate
  hints := hints
  seen := m.vars
  used := hints
  seen_mem := hm.vars_mem
  rup := hh.propagateHints_eq fun y hy => by
    rcases hy with hy | ⟨hs, hy⟩
    · exact List.mem_cons_of_mem _ hy
    rcases mem_lits_cons.1 hy with hy | hy
    · exact negate_eq_iff.1 hy ▸ List.mem_cons_self
    -- `l` is the only seen variable of the level
    have h0 : (Cur.countP fun e => m.seen.assigned e.lit.1) = 0 := by
      have := hm.path_eq
      rw [List.countP_cons, hl] at this
      simp only [↓reduceIte] at this
      omega
    obtain ⟨e, he, hey⟩ := List.mem_map.1 hy
    have := List.countP_eq_zero.1 h0 e he
    rw [hey] at this
    exact absurd hs (by simpa [Std.Sat.Literal.negate] using this)
  vars_mem y hy := by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hm.vars_mem _ ((hm.seen_iff _).1 hl)
    · exact hm.vars_mem _ ((hm.seen_iff _).1 (hm.out_seen y hy))
  mem := List.mem_cons_self
  false_below y hy hne := hm.out_below y ((List.mem_cons.1 hy).resolve_left hne)
  undef := by simpa [Std.Sat.Literal.negate] using hlM
  above := by simpa using hlA
  marks := cur
  marks_none := hcur

/-- The trail split at a decision, the current level first. -/
theorem trail_level (N M₀ : XTrail) (d : Literal ℕ) :
    XTrail.trail (N ++ XEntry.decision d :: M₀) =
      (XTrail.trail N ++ [⟨d, true⟩]) ++ XTrail.trail M₀ := by
  simp

/-- An assignment agreeing with the current level has values only on the literals above. -/
private theorem value_eq_none_of_agrees {cur : Assign} {Cur A : Trail} (h : cur.Agrees Cur)
    (hA : Trail.lits Cur ⊆ Trail.lits A) : ∀ v, v ∉ Trail.vars A → cur.value v = none :=
  fun v hv => by
    cases hc : cur.value v with
    | none => rfl
    | some b => exact absurd (Trail.mem_vars_of_mem_lits (hA ((h v b).1 hc))) hv

/-- **First-UIP conflict analysis**, as MiniSat's: above the newest decision `d`, with the implied
literals `N` over it still to pass and the trail `M₀` below it, the state `m` marks the analysed
clause, which the hints refute. At an entry whose variable is seen, the analysis stops if it is the
only seen variable left on the level, its first unique implication point, and otherwise adds its
reason, whose number it prepends to the hints; entries whose variables are not seen are passed. The
literals of the current level are read from the assignment `cur`, which agrees with them; passing
an implied literal unassigns its variable. -/
def analyzeGo (log : LRATLog φ) (d : Literal ℕ) (M₀ : XTrail) (A : Trail) :
    (N : XTrail) → Trail.lits (XTrail.trail N ++ [⟨d, true⟩]) ⊆ Trail.lits A →
    (cur : Assign) → cur.Agrees (XTrail.trail N ++ [⟨d, true⟩]) →
    (m : Marks) → m.Inv (XTrail.trail N ++ [⟨d, true⟩]) (XTrail.trail M₀) φ.vars → 1 ≤ m.path →
    (hints : List ℕ) → RupHints log.db (m.clause (XTrail.trail N ++ [⟨d, true⟩])) hints →
    Reasons log (N ++ XEntry.decision d :: M₀) → (∀ x ∈ N, x.entry.decision = false) →
    (Trail.vars (XTrail.trail (N ++ XEntry.decision d :: M₀))).Nodup →
    Learned log A (XTrail.trail M₀)
  | [], hA, cur, hcurA, m, hm, hpath, hints, hh, _, _, hnd =>
    -- at the decision, the path has only its variable
    have hd : m.seen.assigned d.1 = true := by
      have := hm.path_eq
      by_contra h
      simp only [XTrail.trail_nil, List.nil_append, List.countP_singleton] at this
      simp only [Bool.not_eq_true] at h
      rw [h] at this
      simp at this
      omega
    have hp : m.path = 1 := by
      have := hm.path_eq
      simp only [XTrail.trail_nil, List.nil_append, List.countP_singleton, hd] at this
      simpa using this
    m.learned log d true hm hd hp hints hh (hA (by simp [Trail.lits]))
      (fun h => by
        simp only [List.nil_append, XTrail.trail_cons, XEntry.entry_decision, Trail.vars,
          List.map_cons, List.nodup_cons] at hnd
        exact hnd.1 h)
      cur (by exact value_eq_none_of_agrees hcurA hA)
  | .decision _ :: _, _, _, _, _, _, _, _, _, _, hdec, _ =>
    absurd (hdec _ List.mem_cons_self) (by simp)
  | .implied l r :: N', hA, cur, hcurA, m, hm, hpath, hints, hh, hreasons, hdec, hnd =>
    have hA' : Trail.lits (XTrail.trail N' ++ [⟨d, true⟩]) ⊆ Trail.lits A :=
      fun x hx => hA (mem_lits_cons.2 (.inr hx))
    have hdec' : ∀ x ∈ N', x.entry.decision = false :=
      fun x hx => hdec x (List.mem_cons_of_mem _ hx)
    have hnd' : (Trail.vars (XTrail.trail (N' ++ XEntry.decision d :: M₀))).Nodup := by
      have := hnd
      simp only [List.cons_append, XTrail.trail_cons, Trail.vars, List.map_cons,
        List.nodup_cons] at this
      exact this.2
    -- passing `l` unassigns its variable, which is not further down the trail
    have hl₀ : l.1 ∉ Trail.vars (XTrail.trail (N' ++ XEntry.decision d :: M₀)) := by
      have := hnd
      simp only [List.cons_append, XTrail.trail_cons, Trail.vars, List.map_cons,
        List.nodup_cons] at this
      exact this.1
    have hl : l.1 ∉ Trail.vars (XTrail.trail N' ++ [⟨d, true⟩]) := fun h =>
      hl₀ (by rw [trail_level, vars_append]; exact List.mem_append_left _ h)
    have hlM : l.1 ∉ Trail.vars (XTrail.trail M₀) := fun h =>
      hl₀ (by rw [trail_level, vars_append]; exact List.mem_append_right _ h)
    have hcurA' : (cur.unassign [l.1]).Agrees (XTrail.trail N' ++ [⟨d, true⟩]) :=
      Assign.Agrees.drop (N := [⟨l, false⟩]) hcurA fun v hv => by
        rw [show v = l.1 by simpa [Trail.vars] using hv]; exact hl
    if hs : m.seen.assigned l.1 = true then
      if hp : m.path = 1 then
        m.learned log l false hm hs hp hints hh (hA (mem_lits_cons.2 (.inl rfl))) hlM
          cur (by exact value_eq_none_of_agrees hcurA hA)
      else
        match hR : log.clause? r with
        | none => absurd hreasons.isSome (by simp [hR])
        | some R =>
          have hRfalse := (hreasons.reason hR).2
          have hm₀ := hm.resolve (e := ⟨l, false⟩) hs
          have hspec := Marks.absorb_spec hcurA' (by rw [← trail_level]; exact hnd')
            ⟨m.seen, m.out, m.path - 1, m.vars⟩ R hm₀ (LRATLog.vars_mem_of_clause? hR)
            fun y hy hys => by
              have hne : y ≠ l := fun h => by simp_all
              have : y.negate ∈ Trail.lits (XTrail.trail (N' ++ XEntry.decision d :: M₀)) :=
                hRfalse y hy hne
              rw [trail_level, lits_append, List.mem_append] at this
              exact this
          analyzeGo log d M₀ A N' hA' (cur.unassign [l.1]) hcurA'
            (Marks.absorb (cur.unassign [l.1]) ⟨m.seen, m.out, m.path - 1, m.vars⟩ R) hspec.1
            (by
              rw [hspec.1.path_eq]
              calc 1 ≤ m.path - 1 := by omega
                _ = _ := hm₀.path_eq
                _ ≤ _ := List.countP_mono_left fun e _ he => hspec.2.2.1 _ he)
            (r :: hints)
            (hh.resolve (LRATLog.find?_of_clause? hR)
              (fun y hy hne => hspec.1.clause_of_seen (hspec.2.1 y hy) (by
                have : y.negate ∈ Trail.lits (XTrail.trail (N' ++ XEntry.decision d :: M₀)) :=
                  hRfalse y hy hne
                rw [trail_level, lits_append, List.mem_append] at this
                exact this))
              fun y hy => by
                rcases hy with hy | ⟨hys, hy⟩
                · exact .inr (.inl (hspec.2.2.2 y hy))
                rcases mem_lits_cons.1 hy with hy | hy
                · exact .inl (negate_eq_iff.1 hy)
                · exact .inr (.inr ⟨hspec.2.2.1 _ hys, hy⟩))
            hreasons.tail hdec' hnd'
    else
      analyzeGo log d M₀ A N' hA' (cur.unassign [l.1]) hcurA' m
        (hm.pass (e := ⟨l, false⟩) (by simpa using hs)) hpath hints
        (hh.mono fun y hy => by
          rcases hy with hy | ⟨hys, hy⟩
          · exact .inl hy
          rcases mem_lits_cons.1 hy with hy | hy
          · refine absurd ?_ hs
            obtain rfl := negate_eq_iff.1 hy
            simpa [Std.Sat.Literal.negate] using hys
          · exact .inr ⟨hys, hy⟩)
        hreasons.tail hdec' hnd'

/-- **First-UIP conflict analysis.** Above the newest decision `d`, with the implied literals `N`
over it and the trail `M₀` below it, the clause numbered `i` is false and has a literal false at
the current level. Its literals are marked (`Cslib.Algorithms.Lean.CDCL.Marks.absorb`), and the
analysis walks down the level, adding the reasons of the entries whose variables are seen, until
one seen variable is left on the level, its first unique implication point, which is reached at
the latest at the decision. The learned clause is never false at the current level elsewhere, and
the hints, the reasons added, oldest first, and then the clause `i`, refute it by unit
propagation. -/
def analyze (log : LRATLog φ) (d : Literal ℕ) (M₀ : XTrail) (A : Trail) (N : XTrail)
    (hA : Trail.lits (XTrail.trail N ++ [⟨d, true⟩]) ⊆ Trail.lits A) (cur : Assign)
    (hcurA : cur.Agrees (XTrail.trail N ++ [⟨d, true⟩])) (i : ℕ) (C : Clause ℕ)
    (hC : log.clause? i = some C) (hreasons : Reasons log (N ++ XEntry.decision d :: M₀))
    (hdec : ∀ x ∈ N, x.entry.decision = false)
    (hfalse : ∀ y ∈ C, y.negate ∈ Trail.lits (XTrail.trail (N ++ XEntry.decision d :: M₀)))
    (hcur : ∃ y ∈ C, y.negate ∈ Trail.lits (XTrail.trail N ++ [⟨d, true⟩]))
    (hnd : (Trail.vars (XTrail.trail (N ++ XEntry.decision d :: M₀))).Nodup) :
    Learned log A (XTrail.trail M₀) :=
  have hfalse' : ∀ y ∈ C, y.negate ∈ Trail.lits (XTrail.trail N ++ [⟨d, true⟩]) ∨
      y.negate ∈ Trail.lits (XTrail.trail M₀) := fun y hy => by
    have := hfalse y hy
    rw [trail_level, lits_append, List.mem_append] at this
    exact this
  have hspec := Marks.absorb_spec hcurA (by rw [← trail_level]; exact hnd) Marks.empty C
    (Marks.inv_empty _ _ _) (LRATLog.vars_mem_of_clause? hC) fun y hy _ => hfalse' y hy
  analyzeGo log d M₀ A N hA cur hcurA (Marks.empty.absorb cur C) hspec.1
    (by
      obtain ⟨y, hy, hyc⟩ := hcur
      rw [hspec.1.path_eq]
      obtain ⟨e, he, hey⟩ := List.mem_map.1 hyc
      refine List.countP_pos_iff.2 ⟨e, he, ?_⟩
      have := hspec.2.1 y hy
      rw [show e.lit.1 = y.1 by rw [hey]; rfl]
      exact this)
    [i] (RupHints.single (LRATLog.find?_of_clause? hC) fun y hy =>
      hspec.1.clause_of_seen (hspec.2.1 y hy) (hfalse' y hy))
    hreasons hdec hnd

/-- A refutation in the log: hints along which unit propagation in the log reaches a conflict from
no assumption. -/
structure Refutation (φ : CNF ℕ) where
  /-- The log. -/
  log : LRATLog φ
  /-- The hints of the empty-clause step. -/
  hints : List ℕ
  rup : propagateHints log.db [] hints = true

/-- The certificate of a refutation: its log closed with an empty-clause step. -/
def Refutation.cert (r : Refutation φ) : Array Std.Tactic.BVDecide.LRAT.IntAction :=
  r.log.finish r.hints r.rup

/-- The hints refuting a conflict with no decision, the trail `T` still to pass: at an implied
literal whose variable is seen, its reason is hinted, first, and its variables are seen. -/
def refuteGo (log : LRATLog φ) : (T : XTrail) → (seen : Assign) → (hints : List ℕ) →
    RupHints log.db (fun y => seen.assigned y.1 = true ∧ y.negate ∈ Trail.lits (XTrail.trail T))
      hints →
    Reasons log T → (∀ x ∈ T, x.entry.decision = false) → Refutation φ
  | [], _, hints, h, _, _ => ⟨log, hints, h [] fun y hy => by simp [Trail.lits] at hy⟩
  | .implied l r :: T, seen, hints, h, hreasons, hdec =>
    if hl : seen.assigned l.1 = true then
      match hR : log.clause? r with
      | some R =>
        refuteGo log T (seen.mark (R.map Prod.fst)) (r :: hints)
          (h.resolve (LRATLog.find?_of_clause? hR)
            (fun y hy hne => ⟨(Assign.assigned_mark _ _ _).2 (.inl (List.mem_map.2 ⟨y, hy, rfl⟩)),
              (hreasons.reason hR).2 y hy hne⟩)
            fun y ⟨hs, hy⟩ => by
              rcases mem_lits_cons.1 hy with hy | hy
              · exact .inl (negate_eq_iff.1 hy)
              · exact .inr ⟨(Assign.assigned_mark _ _ _).2 (.inr hs), hy⟩)
          hreasons.tail fun x hx => hdec x (List.mem_cons_of_mem _ hx)
      | none => absurd hreasons.isSome (by simp [hR])
    else
      refuteGo log T seen hints
        (h.mono fun y ⟨hs, hy⟩ => by
          rcases mem_lits_cons.1 hy with hy | hy
          · refine absurd ?_ hl
            obtain rfl := negate_eq_iff.1 hy
            simpa [Std.Sat.Literal.negate] using hs
          · exact ⟨hs, hy⟩)
        hreasons.tail fun x hx => hdec x (List.mem_cons_of_mem _ hx)
  | .decision _ :: _, _, _, _, _, hdec => absurd (hdec _ List.mem_cons_self) (by simp)

/-- **Refuting a conflict with no decision**: the clause numbered `i`, falsified by a trail of
implied literals, is hinted last, after the reasons of the entries of the trail whose variables
it or a reason hinted contains, oldest first. -/
def refute (T : XTrail) (log : LRATLog φ) (i : ℕ) (C : Clause ℕ) (hC : log.clause? i = some C)
    (hreasons : Reasons log T) (hdec : ∀ x ∈ T, x.entry.decision = false)
    (hfalse : ∀ y ∈ C, y.negate ∈ Trail.lits (XTrail.trail T)) : Refutation φ :=
  refuteGo log T (Assign.marks (C.map Prod.fst)) [i]
    (RupHints.single (LRATLog.find?_of_clause? hC) fun y hy =>
      ⟨(Assign.assigned_marks _ _).2 (List.mem_map.2 ⟨y, hy, rfl⟩), hfalse y hy⟩)
    hreasons hdec

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
the learned clause, which is added to the log. -/
def Exec.afterConflictWith {sp : Split} (S : Exec φ) (L : S.LearnedAt sp) (K : XTrail) : Exec φ :=
  ⟨.implied L.lit L.id :: K, (L.id, L.clause) :: S.db, L.log⟩

/-- The learned clause of a conflict, and the state after Backjump and Learn: back to the trail
kept by `Exec.jump`, with the asserting literal implied by the learned clause, which is added to
the log as one RUP step. -/
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
    exact .implied L.lit L.id (hbelow.mono L.ext) L.clause?_eq L.mem hfalseK
  · intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact L.clause?_eq
    · exact L.ext _ _ (hS.db_log e' he')
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
  ⟨S.trail, CNF.LRATLog.eraseIds S.db ids, S.log.delete ids⟩

/-- The database after Forget: the clauses whose number is not deleted. -/
theorem Exec.mem_forget_db {S : Exec φ} {ids : List ℕ} {e : ℕ × Clause ℕ} :
    e ∈ (S.forget ids).db ↔ e ∈ S.db ∧ e.1 ∉ ids := by
  change e ∈ CNF.LRATLog.eraseIds S.db ids ↔ _
  simp [CNF.LRATLog.eraseIds_eq]

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
  have hmem : ∀ e ∈ (S.forget ids).db, e ∈ S.db ∧ e.1 ∉ ids := fun e he =>
    Exec.mem_forget_db.1 he
  have hmem' : ∀ e ∈ S.db, e.1 ∉ ids → e ∈ (S.forget ids).db := fun e he hid =>
    Exec.mem_forget_db.2 ⟨he, hid⟩
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
