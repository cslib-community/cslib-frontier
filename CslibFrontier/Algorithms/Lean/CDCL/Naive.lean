/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.System
public import CslibFrontier.Logics.Propositional.Resolution.LRATLog
public import CslibFrontier.Algorithms.Lean.DPLL

/-! # A naive CDCL solver with LRAT certificates

An executable instance of abstract DPLL with learning (`Cslib.Algorithms.Lean.CDCL.Step`), which
returns a model or an LRAT certificate (`Cslib.Algorithms.Lean.CDCL.solve`).

**State.** The solver keeps a trail of decisions and of implied literals carrying the number of
their *reason*, a clause of the log (`Cslib.Algorithms.Lean.CDCL.XEntry`), the numbered clauses of
its database, and an LRAT certificate under construction (`Cslib.Logic.PL.CNF.LRATLog`). Its
invariant (`Cslib.Algorithms.Lean.CDCL.Exec.Inv`) is the invariant of the abstract system together
with:

* every reason contains its literal, and its other literals are false further down the trail
  (`Cslib.Algorithms.Lean.CDCL.Reasons`);
* every clause of the database is in the log under its number;
* no clause of the database is false on the part of the trail below a decision.

**Moves** (`Cslib.Algorithms.Lean.CDCL.loop`):

* If a clause is false and the trail has no decision, resolving it with the reasons of the trail,
  newest first, derives the empty clause (`Cslib.Algorithms.Lean.CDCL.refute`); the log, closed at
  that clause, is the certificate (`Cslib.Algorithms.Lean.CDCL.Refutation.cert`).
* If a clause is false and the trail has a decision, *first-UIP analysis*
  (`Cslib.Algorithms.Lean.CDCL.analyze`) resolves it with the reasons of the newest implied
  literals until exactly one of its literals is false at the current level. Its type guarantees an
  asserting clause: the analysed clause always has a literal false at the current level, and at
  the decision only the decision's negation can be one. The solver backjumps below the newest
  decision, adds the asserting literal with the learned clause as its reason, and learns the
  clause (Backjump and Learn).
* Otherwise it propagates a unit clause (UnitPropagate) if there is one, decides the first
  variable of the database not yet assigned, `true` first (Decide), or returns the trail as a
  model.

Every move is a Basic DPLL step, or Backjump followed by Learn, of the abstract system, and so
lowers its rank (`Cslib.Algorithms.Lean.CDCL.rank`); recursion is structural on a bound on the
rank, which provably never runs out, and the kernel can run the solver. Every learned clause, and
every intermediate resolvent of the analysis, enters the certificate as a RUP step hinting the two
clauses it resolves, so the checker accepts the certificate by construction
(`Cslib.Logic.PL.CNF.LRATLog.checkLRAT_finish`).

**Scope.** This is the naive milestone of the MiniSat port: clauses are scanned in full instead of
watched, decisions follow a fixed order, Backjump returns to just below the newest decision
rather than to the second-highest level of the learned clause, intermediate resolvents are never
deleted, and there are no restarts. These are later milestones.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.analyze`: first-UIP conflict analysis.
* `Cslib.Algorithms.Lean.CDCL.loop`, `Cslib.Algorithms.Lean.CDCL.solve`: the solver.

## Main results

* `Cslib.Algorithms.Lean.CDCL.solve_sat`, `Cslib.Algorithms.Lean.CDCL.solve_unsat`: both answers are
  correct.
* `Cslib.Algorithms.Lean.CDCL.isSat_solve_iff`: the solver decides satisfiability.

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

/-- The resolvent on the variable of `l` of a clause containing the negation of `l` and a clause
containing `l`, as `Clause.resolvent` orders them. -/
def resolveOn (l : Literal ℕ) (C R : Clause ℕ) : Clause ℕ :=
  if l.2 then R.resolvent C l.1 else C.resolvent R l.1

theorem mem_resolveOn {l y : Literal ℕ} {C R : Clause ℕ} (h : y ∈ resolveOn l C R) :
    (y ∈ C ∧ y ≠ l.negate) ∨ (y ∈ R ∧ y ≠ l) := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp only [resolveOn, Bool.false_eq_true, ↓reduceIte] at h <;>
    rcases Clause.mem_resolvent.1 h with ⟨h, hne⟩ | ⟨h, hne⟩ <;>
    simp_all [Std.Sat.Literal.negate]

/-- Adding to the log the resolvent of the clause numbered `i`, containing the negation of `l`, and
the reason numbered `r` of `l`. -/
def resolveLog (log : LRATLog φ) (l : Literal ℕ) (i r : ℕ) (C R : Clause ℕ)
    (hC : log.clause? i = some C) (hR : log.clause? r = some R) : LRATLog φ :=
  if l.2 then log.addResolvent r i l.1 R C hR hC else log.addResolvent i r l.1 C R hC hR

theorem resolveLog_spec {log : LRATLog φ} {l : Literal ℕ} {i r : ℕ} {C R : Clause ℕ}
    (hC : log.clause? i = some C) (hR : log.clause? r = some R) :
    (resolveLog log l i r C R hC hR).clause? log.next = some (resolveOn l C R) ∧
      log.Extends (resolveLog log l i r C R hC hR) := by
  cases hl : l.2
  · simp only [resolveLog, resolveOn, hl, Bool.false_eq_true, ↓reduceIte]
    exact ⟨LRATLog.clause?_addResolvent hC hR, LRATLog.extends_addResolvent hC hR⟩
  · simp only [resolveLog, resolveOn, hl, ↓reduceIte]
    exact ⟨LRATLog.clause?_addResolvent hR hC, LRATLog.extends_addResolvent hR hC⟩

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
        let log' := resolveLog log l i r C R hC hR
        have hspec := resolveLog_spec (l := l) hC hR
        refute T log' log.next (resolveOn l C R) hspec.1 (hT.mono hspec.2)
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
  cases b <;> simp_all [resolveOn, Clause.mem_resolvent, Std.Sat.Literal.negate]

theorem lits_append (M N : Trail) : Trail.lits (M ++ N) = Trail.lits M ++ Trail.lits N :=
  List.map_append ..

theorem vars_append (M N : Trail) : Trail.vars (M ++ N) = Trail.vars M ++ Trail.vars N :=
  List.map_append ..

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
  clause?_eq : log.clause? id = some clause
  mem : lit ∈ clause
  false_below : ∀ y ∈ clause, y ≠ lit → y.negate ∈ Trail.lits M₀
  undef : lit.1 ∉ Trail.vars M₀
  above : lit.negate ∈ Trail.lits A
  ext : log₀.Extends log

/-- **First-UIP conflict analysis.** Above the newest decision `d`, with the implied literals `N`
over it and the trail `M₀` below it, the clause numbered `i` is false and has a literal false at
the current level. While it has two different literals false at the current level, it is resolved
with the reason of the newest implied literal whose negation it contains. It stops with a clause
having exactly one literal false at the current level, its first unique implication point, which
is reached at the latest at the decision. -/
def analyze (log₀ : LRATLog φ) (d : Literal ℕ) (M₀ : XTrail) (A : Trail) :
    (N : XTrail) → Trail.lits (XTrail.trail N ++ [⟨d, true⟩]) ⊆ Trail.lits A →
    (log : LRATLog φ) → log₀.Extends log → (i : ℕ) → (C : Clause ℕ) →
    log.clause? i = some C → Reasons log (N ++ XEntry.decision d :: M₀) →
    (∀ x ∈ N, x.entry.decision = false) →
    (∀ y ∈ C, y.negate ∈ Trail.lits (XTrail.trail (N ++ XEntry.decision d :: M₀))) →
    (∃ y ∈ C, y.negate ∈ Trail.lits (XTrail.trail N ++ [⟨d, true⟩])) →
    (Trail.vars (XTrail.trail (N ++ XEntry.decision d :: M₀))).Nodup →
    Learned log₀ A (XTrail.trail M₀)
  | N, hA, log, hext, i, C, hC, hreasons, hdec, hfalse, hcur, hnd =>
    match hys : C.filter (fun y => (Trail.lits (XTrail.trail N ++ [⟨d, true⟩])).contains
        y.negate) with
    | [] => absurd hys (by
        obtain ⟨y, hy, hyc⟩ := hcur
        exact List.ne_nil_of_mem (List.mem_filter.2 ⟨hy, by simpa using hyc⟩))
    | u :: rest =>
      have hu : u ∈ C ∧ u.negate ∈ Trail.lits (XTrail.trail N ++ [⟨d, true⟩]) := by
        have := List.mem_filter.1 (hys ▸ List.mem_cons_self : u ∈ C.filter _)
        exact ⟨this.1, by simpa using this.2⟩
      if hall : rest.all (· == u) then
        { log := log, id := i, clause := C, lit := u, clause?_eq := hC, mem := hu.1,
          false_below := fun y hy hne => by
            have hyT := hfalse y hy
            simp only [XTrail.trail_append, XTrail.trail_cons, lits_append, List.mem_append]
              at hyT
            rcases hyT with h | h
            · refine absurd ?_ hne
              have : y ∈ C.filter (fun y => (Trail.lits (XTrail.trail N ++ [⟨d, true⟩])).contains
                  y.negate) := List.mem_filter.2 ⟨hy, List.contains_iff_mem.2 (by
                rw [lits_append]; exact List.mem_append_left _ h)⟩
              rw [hys] at this
              rcases List.mem_cons.1 this with h | h
              · exact h
              · simpa using List.all_eq_true.1 hall y h
            · simp only [Trail.lits, List.map_cons, List.mem_cons] at h
              rcases h with h | h
              · refine absurd ?_ hne
                have : y ∈ C.filter (fun y => (Trail.lits (XTrail.trail N ++ [⟨d, true⟩])).contains
                  y.negate) := List.mem_filter.2 ⟨hy, List.contains_iff_mem.2 (by
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
        match N, hA, hreasons, hdec, hfalse, hcur, hnd, hys, hu with
        | [], _, _, _, _, _, _, hys, _ => absurd (List.all_eq_true.2 fun y hy => by
            have hy' : y ∈ C.filter _ := hys ▸ List.mem_cons_of_mem _ hy
            have hu' : u ∈ C.filter _ := hys ▸ List.mem_cons_self
            have h₁ := (List.mem_filter.1 hy').2
            have h₂ := (List.mem_filter.1 hu').2
            simp only [Trail.lits, XTrail.trail_nil, List.nil_append, List.map_cons, List.map_nil,
              List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false,
              decide_eq_true_eq] at h₁ h₂
            simpa using negate_inj (h₁.trans h₂.symm)) hall
        | .decision _ :: _, _, _, hdec, _, _, _, _, _ =>
          absurd (hdec _ List.mem_cons_self) (by simp)
        | .implied l r :: N', hA, hreasons, hdec, hfalse, hcur, hnd, hys, hu =>
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
              · exact ⟨y, (List.mem_filter.1 hy').1, hul ▸ hyu, by
                  simpa using (List.mem_filter.1 hy').2⟩
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
              let log' := resolveLog log l i r C R hC hR
              have hspec := resolveLog_spec (l := l) hC hR
              analyze log₀ d M₀ A N' hA' log' (hext.trans hspec.2) log.next (resolveOn l C R)
                hspec.1 (hT.mono hspec.2) hdec'
                (fun y hy => by
                  rcases mem_resolveOn hy with ⟨hy, hne⟩ | ⟨hy, hne⟩
                  · exact hfalse' y hy hne
                  · exact hRfalse y hy hne)
                (by
                  obtain ⟨z, hz, hne, hzc⟩ := hz
                  exact ⟨z, mem_resolveOn_left hz hne, hcur' z hne hzc⟩)
                hnd'
            else
              analyze log₀ d M₀ A N' hA' log hext i C hC hT hdec'
                (fun y hy => hfalse' y hy fun h => hmem (h ▸ hy))
                (by
                  obtain ⟨z, hz, hne, hzc⟩ := hz
                  exact ⟨z, hz, hcur' z hne hzc⟩)
                hnd'

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
of the database in the log, and no clause of the database false below a decision. -/
structure Exec.Inv (S : Exec φ) : Prop where
  run : RunInv φ φ.vars (XTrail.trail S.trail) S.clauses
  reasons : Reasons S.log S.trail
  db_log : ∀ e ∈ S.db, S.log.clause? e.1 = some e.2
  below : ∀ N d M₀, XTrail.trail S.trail = N ++ ⟨d, true⟩ :: M₀ →
    ∀ c ∈ S.clauses, ¬ Trail.Falsifies M₀ c

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

theorem Exec.init_inv (φ : CNF ℕ) : (Exec.init φ).Inv := by
  have hclauses : (Exec.init φ).clauses = φ := by
    simp only [Exec.clauses, Exec.init, lratDB, List.map_map]
    conv_rhs => rw [← List.zipIdx_map_fst 0 φ]
    rfl
  refine ⟨?_, .nil, fun e he => ?_, fun N d M₀ h => by simp [Exec.init, XTrail.trail] at h⟩
  · rw [hclauses]
    exact (Inv.init fun c hc l hl => CNF.mem_vars.2 ⟨c, hc, l.2, hl⟩ : RunInv _ _ _ _)
  · simp only [LRATLog.clause?, Exec.init, LRATLog.init, lratDB] at he ⊢
    rw [find?_zipIdx_map φ 0 he]
    rfl

/-! ### Steps of the solver -/

/-- A solver state with the invariant and a smaller rank than `S`. -/
abbrev Exec.Next (S : Exec φ) :=
  {S' : Exec φ // S'.Inv ∧ rank φ.vars S'.state < rank φ.vars S.state}

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

/-- The learned clause of a conflict, and the state after Backjump and Learn. -/
def Exec.afterConflict (S : Exec φ) (sp : Split) (L : S.LearnedAt sp) :
    Exec φ :=
  ⟨.implied L.lit L.id :: sp.below, (L.id, L.clause) :: S.db, L.log⟩

/-- Backjump and Learn keep the invariant and lower the rank. -/
theorem Exec.afterConflict_spec {S : Exec φ} (hS : S.Inv) {e : ℕ × Clause ℕ} (he : e ∈ S.db)
    (hconf : Trail.Falsifies (XTrail.trail S.trail) e.2) {sp : Split}
    (hsp : XTrail.split S.trail = some sp) (L : S.LearnedAt sp) :
    (S.afterConflict sp L).Inv ∧
      rank φ.vars (S.afterConflict sp L).state < rank φ.vars S.state := by
  have hsplit := XTrail.trail_of_split hsp
  have hc : e.2 ∈ S.clauses := List.mem_map.2 ⟨e, he, rfl⟩
  have hentails : ∀ σ, CNF.eval σ S.clauses = true → L.clause.eval σ = true :=
    fun σ hσ => L.log.eval_of_clause? L.clause?_eq (by rw [← hS.run.models]; exact hσ)
  have hbj : BasicStep (.run (XTrail.trail S.trail) S.clauses)
      (.run (⟨L.lit, false⟩ :: XTrail.trail sp.below) S.clauses) := by
    -- the asserting literal is over a variable of the current level
    have hocc : L.lit.1 ∈ Trail.vars
        (XTrail.trail sp.above ++ ⟨sp.decision, true⟩ :: XTrail.trail sp.below) := by
      have := Trail.mem_vars_of_mem_lits L.above
      simp only [Std.Sat.Literal.negate, Trail.vars, List.map_append, List.mem_append,
        List.map_cons, List.mem_cons, List.map_nil, List.not_mem_nil, or_false] at this ⊢
      tauto
    rw [hsplit]
    exact .backjump hc (hsplit ▸ hconf) hentails L.mem L.false_below L.undef (.inr hocc)
  have hlearn : Learn (.run (⟨L.lit, false⟩ :: XTrail.trail sp.below) S.clauses)
      (.run (⟨L.lit, false⟩ :: XTrail.trail sp.below) (L.clause :: S.clauses)) :=
    .learn hentails fun l hl => .inr (by
      by_cases hne : l = L.lit
      · subst hne; simp [Trail.vars]
      · have := Trail.mem_vars_of_mem_lits (L.false_below l hl hne)
        simp only [Std.Sat.Literal.negate] at this
        simp only [Trail.vars, List.map_cons, List.mem_cons] at this ⊢
        exact .inr this)
  have hrun₁ := Step.inv (.inl hbj) (show CDCL.Inv φ φ.vars (.run _ _) from hS.run)
  have hrun₂ := Step.inv (.inr (.inl hlearn)) hrun₁
  refine ⟨⟨hrun₂, ?_, ?_, ?_⟩, ?_⟩
  · exact .implied L.lit L.id ((hS.split_reasons hsp).append_right.tail.mono L.ext)
      L.clause?_eq L.mem L.false_below
  · intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact L.clause?_eq
    · exact L.ext _ _ (hS.db_log e' he')
  · intro N d M₁ hN c hc'
    -- a split of the new trail is below the asserting literal, so a split of the old trail
    obtain ⟨x, N, rfl⟩ : ∃ x N', N = x :: N' := by
      cases N with
      | nil => simp [Exec.afterConflict] at hN
      | cons x N => exact ⟨x, N, rfl⟩
    simp only [Exec.afterConflict, XTrail.trail_cons, List.cons_append, List.cons.injEq] at hN
    obtain ⟨-, hN⟩ := hN
    rcases List.mem_cons.1 hc' with rfl | hc'
    · intro hfalse
      apply L.undef
      have := hfalse _ L.mem
      rw [congrArg Trail.vars hN]
      have hv := Trail.mem_vars_of_mem_lits this
      simp only [Trail.vars, Std.Sat.Literal.negate] at hv
      simp only [Trail.vars, List.map_append, List.map_cons, List.mem_append, List.mem_cons]
      exact .inr (.inr hv)
    · exact hS.below (XTrail.trail sp.above ++ ⟨sp.decision, true⟩ :: N) d M₁
        (by rw [hsplit, hN]; simp) c hc'
  · change rank φ.vars (.run (⟨L.lit, false⟩ :: XTrail.trail sp.below) (L.clause :: S.clauses)) <
      rank φ.vars (.run (XTrail.trail S.trail) S.clauses)
    exact (LearnOrForget.rank_eq (.inl hlearn)).trans_lt (hbj.rank_lt hS.run)

/-- **Conflict, analysis, Backjump and Learn**: with the clause `e` of the database false and the
trail split at its newest decision, learn the first-UIP clause and go back below the decision,
adding its asserting literal with the learned clause as reason. -/
def Exec.backjump (S : Exec φ) (hS : S.Inv) (e : ℕ × Clause ℕ) (he : e ∈ S.db)
    (hconf : Trail.Falsifies (XTrail.trail S.trail) e.2) (sp : Split)
    (hsp : XTrail.split S.trail = some sp) : S.Next :=
  let L := analyze S.log sp.decision sp.below (XTrail.trail sp.above ++ [⟨sp.decision, true⟩])
    sp.above (fun _ h => h) S.log (LRATLog.Extends.refl _) e.1 e.2
    (hS.db_log e he) (hS.split_reasons hsp) (XTrail.split_eq_some hsp).2
    (XTrail.falsifies_of_split hsp hconf) (hS.split_cur hsp he hconf) (hS.split_nodup hsp)
  ⟨S.afterConflict sp L, Exec.afterConflict_spec hS he hconf hsp L⟩

/-- A unit clause of the database: a numbered clause with every literal but one false on the trail,
that literal being undefined. -/
def findUnit (M : Trail) (db : List (ℕ × Clause ℕ)) : Option ((ℕ × Clause ℕ) × Literal ℕ) :=
  db.findSome? fun e => (e.2.find? fun l =>
    decide (l.1 ∉ Trail.vars M ∧ ∀ l' ∈ e.2, l' ≠ l → l'.negate ∈ Trail.lits M)).map (e, ·)

theorem findUnit_spec {M : Trail} {db : List (ℕ × Clause ℕ)} {e : ℕ × Clause ℕ} {l : Literal ℕ}
    (h : findUnit M db = some (e, l)) :
    e ∈ db ∧ l ∈ e.2 ∧ l.1 ∉ Trail.vars M ∧ ∀ l' ∈ e.2, l' ≠ l → l'.negate ∈ Trail.lits M := by
  obtain ⟨e', he', h'⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨l', hl', hel⟩ := Option.map_eq_some_iff.1 h'
  cases hel
  have := List.find?_some hl'
  simp only [decide_eq_true_eq] at this
  exact ⟨he', List.mem_of_find?_eq_some hl', this⟩

/-- **UnitPropagate**: add the literal of a unit clause, with that clause as its reason. -/
def Exec.propagate (S : Exec φ) (e : ℕ × Clause ℕ) (l : Literal ℕ) : Exec φ :=
  ⟨.implied l e.1 :: S.trail, S.db, S.log⟩

/-- UnitPropagate with a clause of the database keeps the invariant and lowers the rank. -/
theorem Exec.propagate_spec' {S : Exec φ} (hS : S.Inv) {e : ℕ × Clause ℕ} {l : Literal ℕ}
    (he : e ∈ S.db) (hl : l ∈ e.2) (hundef : l.1 ∉ Trail.vars (XTrail.trail S.trail))
    (hfalse : ∀ l' ∈ e.2, l' ≠ l → l'.negate ∈ Trail.lits (XTrail.trail S.trail)) :
    (S.propagate e l).Inv ∧ rank φ.vars (S.propagate e l).state < rank φ.vars S.state := by
  have hc : e.2 ∈ S.clauses := List.mem_map.2 ⟨e, he, rfl⟩
  have hstep : BasicStep (.run (XTrail.trail S.trail) S.clauses)
      (.run (⟨l, false⟩ :: XTrail.trail S.trail) S.clauses) :=
    .unitPropagate hc hl hfalse hundef
  refine ⟨⟨Step.inv (.inl hstep) (show CDCL.Inv φ φ.vars (.run _ _) from hS.run),
    .implied l e.1 hS.reasons (hS.db_log e he) hl hfalse, hS.db_log, ?_⟩,
    hstep.rank_lt hS.run⟩
  intro N d M₁ hN c hc'
  cases N with
  | nil => simp [Exec.propagate] at hN
  | cons x N =>
    simp only [Exec.propagate, XTrail.trail_cons, List.cons_append, List.cons.injEq] at hN
    exact hS.below N d M₁ hN.2 c hc'

theorem Exec.propagate_spec {S : Exec φ} (hS : S.Inv) {e : ℕ × Clause ℕ} {l : Literal ℕ}
    (h : findUnit (XTrail.trail S.trail) S.db = some (e, l)) :
    (S.propagate e l).Inv ∧ rank φ.vars (S.propagate e l).state < rank φ.vars S.state := by
  obtain ⟨he, hl, hundef, hfalse⟩ := findUnit_spec h
  exact Exec.propagate_spec' hS he hl hundef hfalse

/-- **Decide**: add the variable `x` as a decision, `true` first. -/
def Exec.decide (S : Exec φ) (x : ℕ) : Exec φ :=
  ⟨.decision (x, true) :: S.trail, S.db, S.log⟩

theorem Exec.decide_spec {S : Exec φ} (hS : S.Inv)
    (hnoconf : ∀ c ∈ S.clauses, ¬ Trail.Falsifies (XTrail.trail S.trail) c) {x : ℕ}
    (hx : x ∈ S.clauses.vars) (hundef : x ∉ Trail.vars (XTrail.trail S.trail)) :
    (S.decide x).Inv ∧ rank φ.vars (S.decide x).state < rank φ.vars S.state := by
  have hstep : BasicStep (.run (XTrail.trail S.trail) S.clauses)
      (.run (⟨(x, true), true⟩ :: XTrail.trail S.trail) S.clauses) :=
    .decide (l := (x, true)) hundef hx
  refine ⟨⟨Step.inv (.inl hstep) (show CDCL.Inv φ φ.vars (.run _ _) from hS.run),
    .decision _ hS.reasons, hS.db_log, ?_⟩, hstep.rank_lt hS.run⟩
  intro N d M₁ hN c hc'
  cases N with
  | nil =>
    simp only [Exec.decide, XTrail.trail_cons, List.nil_append, List.cons.injEq] at hN
    rw [← hN.2]
    exact hnoconf c hc'
  | cons y N =>
    simp only [Exec.decide, XTrail.trail_cons, List.cons_append, List.cons.injEq] at hN
    exact hS.below N d M₁ hN.2 c hc'

theorem Exec.Inv.rank_pos {S : Exec φ} (hS : S.Inv) : 0 < rank φ.vars S.state := by
  have := hS.run.measure_le
  simp only [Exec.state, rank]
  omega

/-! ### The solver -/

/-- The answer of the solver, with its correctness: a model, or an LRAT certificate accepted by
the checker. -/
inductive Answer (φ : CNF ℕ) : Type
  /-- A model. -/
  | sat (σ : ℕ → Bool) (h : φ.eval σ = true)
  /-- An accepted certificate. -/
  | unsat (cert : Array Std.Tactic.BVDecide.LRAT.IntAction) (h : φ.checkLRAT cert = true)

/-- **The CDCL loop.** With a false clause and no decision, derive the empty clause and return the
certificate; with a false clause, analyze, backjump and learn; otherwise propagate a unit clause,
or decide the first unassigned variable, or return the trail as a model when every variable is
assigned. Every move lowers the rank, so `fuel` never runs out. -/
def loop (φ : CNF ℕ) : (fuel : ℕ) → (S : Exec φ) → S.Inv → rank φ.vars S.state ≤ fuel → Answer φ
  | 0, _, hS, hfuel => absurd hfuel (by have := hS.rank_pos; omega)
  | fuel + 1, S, hS, hfuel =>
    match hconf : S.db.find? (fun e => decide (Trail.Falsifies (XTrail.trail S.trail) e.2)) with
    | some e =>
      have he : e ∈ S.db := List.mem_of_find?_eq_some hconf
      have hce : Trail.Falsifies (XTrail.trail S.trail) e.2 := by
        have := List.find?_some hconf
        simpa only [decide_eq_true_eq] using this
      match hsp : XTrail.split S.trail with
      | none =>
        let r := refute S.trail S.log e.1 e.2 (hS.db_log e he) hS.reasons
          (XTrail.split_eq_none hsp) hce
        .unsat r.cert (LRATLog.checkLRAT_finish r.clause?_eq)
      | some sp =>
        let S' := S.backjump hS e he hce sp hsp
        loop φ fuel S'.1 S'.2.1 (by have := S'.2.2; omega)
    | none =>
      have hnoconf : ∀ c ∈ S.clauses, ¬ Trail.Falsifies (XTrail.trail S.trail) c := by
        intro c hc hfalse
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
        exact List.find?_eq_none.1 hconf e he (decide_eq_true hfalse)
      match hu : findUnit (XTrail.trail S.trail) S.db with
      | some (e, l) =>
        have hspec := Exec.propagate_spec hS hu
        loop φ fuel (S.propagate e l) hspec.1 (by have := hspec.2; omega)
      | none =>
        match hx : S.clauses.vars.find? (fun x => !(Trail.vars (XTrail.trail S.trail)).contains x)
        with
        | some x =>
          have hspec := Exec.decide_spec hS hnoconf (List.mem_of_find?_eq_some hx)
            (by simpa using List.find?_some hx)
          loop φ fuel (S.decide x) hspec.1 (by have := hspec.2; omega)
        | none =>
          .sat (Trail.assignment (XTrail.trail S.trail)) (hS.run.eval_model hnoconf fun x hxV => by
            simpa using List.find?_eq_none.1 hx x hxV)

/-- **The CDCL solver**: a model, or an LRAT certificate of unsatisfiability. -/
def solve (φ : CNF ℕ) : DPLL.Result :=
  match loop φ (rank φ.vars (Exec.init φ).state) (Exec.init φ) (Exec.init_inv φ) le_rfl with
  | .sat σ _ => .sat σ
  | .unsat cert _ => .unsat cert

/-- **The models returned by the solver are models.** -/
theorem solve_sat {φ : CNF ℕ} {σ : ℕ → Bool} (h : solve φ = .sat σ) : φ.eval σ = true := by
  unfold solve at h
  split at h
  · rename_i hσ _
    cases h
    exact hσ
  · cases h

/-- **The certificates returned by the solver are accepted by the LRAT checker.** -/
theorem solve_unsat {φ : CNF ℕ} {cert : Array Std.Tactic.BVDecide.LRAT.IntAction}
    (h : solve φ = .unsat cert) : φ.checkLRAT cert = true := by
  unfold solve at h
  split at h
  · cases h
  · rename_i hcert _
    cases h
    exact hcert

/-- **The solver decides satisfiability.** -/
theorem isSat_solve_iff (φ : CNF ℕ) : (solve φ).isSat = true ↔ φ.Satisfiable :=
  DPLL.Result.isSat_iff (fun _ => solve_sat) (fun _ => solve_unsat)

end Cslib.Algorithms.Lean.CDCL
