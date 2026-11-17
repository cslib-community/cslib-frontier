/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The abstract CDCL transition system

Following Nieuwenhuis, Oliveras and Tinelli [NieuwenhuisOliverasTinelli2006], conflict-driven
clause learning is a transition system on states made of a *trail* and a clause database. The
trail (`Cslib.Algorithms.Lean.CDCL.Trail`) lists the literals assigned so far, newest first, each
marked as a *decision* or as *implied*; its *level* is its number of decisions. The rules
(`Cslib.Algorithms.Lean.CDCL.Step`) are:

* **UnitPropagate**: if a clause of the database has every literal but `l` false and `l` is
  undefined, add `l` as implied.
* **Decide**: add an undefined literal over a variable of `V` as a decision.
* **Backjump**: if a clause of the database is false, and a clause `C` that holds in every model
  of the database has every literal but `l` false on the trail below some decision, with `l`
  undefined there, go back below that decision and add `l` as implied. With `learn` the step also
  adds `C` to the database (**Learn**).

**Fail** is not a step: it is the final state with a false clause and no decision. Forget and
Restart are not included.

The invariant `Cslib.Algorithms.Lean.CDCL.Inv` says that the database has the models of `φ`, that
the trail assigns each variable of `V` at most once, that the database only uses variables of `V`,
and that every implied literal holds in every model of `φ` that satisfies the older literals. Every
step keeps it (`Cslib.Algorithms.Lean.CDCL.Step.inv`). Then:

* a state with no false clause that assigns every variable of `V` gives a model of `φ`
  (`Cslib.Algorithms.Lean.CDCL.Inv.eval_model`);
* a state with a false clause and no decision shows that `φ` is unsatisfiable
  (`Cslib.Algorithms.Lean.CDCL.Inv.not_satisfiable`);
* in any other state some step applies: Decide if a variable is undefined, and Backjump with the
  negation of the decisions if a clause is false
  (`Cslib.Algorithms.Lean.CDCL.Inv.exists_step`);
* there is no infinite run (`Cslib.Algorithms.Lean.CDCL.wellFounded_step`). Each step strictly
  increases the measure `Cslib.Algorithms.Lean.CDCL.Trail.measure`, which weighs a literal at
  level `k` by `(N + 1) ^ (N - k)` for `N` variables: Backjump trades the literals above the
  level it returns to for one literal at that level, which weighs more than all of them together.
  The measure is at most `N * (N + 1) ^ N`.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.Step`: the transition system.
* `Cslib.Algorithms.Lean.CDCL.Inv`: its invariant.

## Main results

* `Cslib.Algorithms.Lean.CDCL.Step.inv`: steps keep the invariant.
* `Cslib.Algorithms.Lean.CDCL.Inv.eval_model`, `Cslib.Algorithms.Lean.CDCL.Inv.not_satisfiable`,
  `Cslib.Algorithms.Lean.CDCL.Inv.exists_step`, `Cslib.Algorithms.Lean.CDCL.Inv.final`: final
  states are models or refutations.
* `Cslib.Algorithms.Lean.CDCL.wellFounded_step`: every run terminates.

## References

* [R. Nieuwenhuis, A. Oliveras, C. Tinelli, *Solving SAT and SAT Modulo Theories: From an Abstract
  Davis–Putnam–Logemann–Loveland Procedure to DPLL(T)*][NieuwenhuisOliverasTinelli2006]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL

/-- A trail: the assigned literals, newest first, each marked `true` if it is a decision. -/
abbrev Trail := List (Literal ℕ × Bool)

namespace Trail

/-- The literals of a trail. -/
def lits (M : Trail) : List (Literal ℕ) := M.map Prod.fst

/-- The variable of a trail entry. -/
abbrev entryVar (e : Literal ℕ × Bool) : ℕ := e.1.1

/-- The variables of a trail. -/
def vars (M : Trail) : List ℕ := M.map entryVar

/-- A trail falsifies a clause if it contains the negation of every literal of the clause. -/
abbrev Falsifies (M : Trail) (c : Clause ℕ) : Prop := ∀ l ∈ c, (l.1, !l.2) ∈ Trail.lits M

/-- The level of a trail: its number of decisions. -/
def level (M : Trail) : ℕ := (M.filter (·.2)).length

/-- An assignment satisfies a trail if it makes every literal of the trail true. -/
def Sat (σ : ℕ → Bool) (M : Trail) : Prop := ∀ l ∈ Trail.lits M, Literal.eval σ l = true

/-- Every implied literal of the trail holds in every model of `φ` satisfying the older
literals. -/
inductive Entailed (φ : CNF ℕ) : Trail → Prop
  | nil : Entailed φ []
  | decision {M : Trail} (l : Literal ℕ) : Entailed φ M → Entailed φ ((l, true) :: M)
  | implied {M : Trail} (l : Literal ℕ) : Entailed φ M →
      (∀ σ, φ.eval σ = true → Sat σ M → Literal.eval σ l = true) → Entailed φ ((l, false) :: M)

/-- The total assignment of a trail: a variable is true if the trail makes it true. -/
def assignment (M : Trail) (x : ℕ) : Bool := decide ((x, true) ∈ Trail.lits M)

end Trail

/-- A state: a trail and a clause database. -/
structure State where
  /-- The trail. -/
  trail : Trail
  /-- The clause database. -/
  db : CNF ℕ

/-- **The CDCL transition system** over the variables `V`. -/
inductive Step (V : List ℕ) : State → State → Prop
  /-- UnitPropagate: a clause with every literal but `l` false makes `l` implied. -/
  | unitPropagate {M : Trail} {F : CNF ℕ} {c : Clause ℕ} {l : Literal ℕ} (hc : c ∈ F) (hl : l ∈ c)
      (hfalse : ∀ l' ∈ c, l' ≠ l → (l'.1, !l'.2) ∈ Trail.lits M) (hundef : l.1 ∉ Trail.vars M)
      (hv : l.1 ∈ V) : Step V ⟨M, F⟩ ⟨(l, false) :: M, F⟩
  /-- Decide: an undefined literal over a variable of `V` becomes a decision. -/
  | decide {M : Trail} {F : CNF ℕ} {l : Literal ℕ} (hundef : l.1 ∉ Trail.vars M) (hv : l.1 ∈ V) :
      Step V ⟨M, F⟩ ⟨(l, true) :: M, F⟩
  /-- Backjump, and with `learn` also Learn: going back below a decision and adding the literal
  that a clause `C` of the consequences of the database implies there. -/
  | backjump {N M₀ : Trail} {F : CNF ℕ} {d : Literal ℕ} {c C : Clause ℕ} {l : Literal ℕ}
      (learn : Bool) (hc : c ∈ F) (hconf : (Trail.Falsifies (N ++ (d, true) :: M₀)) c)
      (hC : ∀ σ, F.eval σ = true → C.eval σ = true) (hl : l ∈ C)
      (hfalse : ∀ l' ∈ C, l' ≠ l → (l'.1, !l'.2) ∈ Trail.lits M₀) (hundef : l.1 ∉ Trail.vars M₀)
      (hCV : ∀ l' ∈ C, l'.1 ∈ V) :
      Step V ⟨N ++ (d, true) :: M₀, F⟩ ⟨(l, false) :: M₀, if learn then C :: F else F⟩

/-- **The invariant** of the system for the formula `φ` over the variables `V`. -/
structure Inv (φ : CNF ℕ) (V : List ℕ) (S : State) : Prop where
  /-- The database has the models of `φ`. -/
  models : ∀ σ, S.db.eval σ = φ.eval σ
  /-- The trail assigns each variable at most once. -/
  nodup : (Trail.vars S.trail).Nodup
  /-- The trail assigns variables of `V`. -/
  subset : ∀ x ∈ Trail.vars S.trail, x ∈ V
  /-- The database uses variables of `V`. -/
  db_vars : ∀ c ∈ S.db, ∀ l ∈ c, l.1 ∈ V
  /-- Every implied literal follows from `φ` and the older literals. -/
  entailed : (Trail.Entailed φ S.trail)

namespace Trail

theorem mem_lits_iff {M : Trail} {l : Literal ℕ} : l ∈ Trail.lits M ↔ ∃ b, (l, b) ∈ M := by
  simp [lits]

theorem mem_vars_of_mem_lits {M : Trail} {l : Literal ℕ} (h : l ∈ Trail.lits M) :
    l.1 ∈ Trail.vars M := by
  obtain ⟨b, hb⟩ := mem_lits_iff.1 h
  exact List.mem_map.2 ⟨_, hb, rfl⟩

/-- A trail assigning each variable once does not contain a literal and its negation. -/
theorem not_mem_neg {M : Trail} (hM : (Trail.vars M).Nodup) {l : Literal ℕ}
    (h : l ∈ Trail.lits M) :
    (l.1, !l.2) ∉ Trail.lits M := by
  induction M with
  | nil => simp [lits] at h
  | cons e M ih =>
    simp only [vars, List.map_cons, List.nodup_cons] at hM
    simp only [lits, List.map_cons, List.mem_cons] at h ⊢
    rintro (heq | hmem)
    · rcases h with rfl | h
      · obtain ⟨⟨v, b⟩, _⟩ := e; cases b <;> simp at heq
      · exact hM.1 (by simpa [vars, entryVar, ← heq] using mem_vars_of_mem_lits h)
    · rcases h with rfl | h
      · exact hM.1 (by simpa [vars] using mem_vars_of_mem_lits hmem)
      · exact ih hM.2 h hmem

theorem entailed_append {φ : CNF ℕ} {N M : Trail} (h : Trail.Entailed φ (N ++ M)) :
    Trail.Entailed φ M := by
  induction N with
  | nil => simpa using h
  | cons e N ih => cases h <;> exact ih ‹_›

/-- A model of `φ` that satisfies the decisions of an entailed trail satisfies the trail. -/
theorem sat_of_entailed {φ : CNF ℕ} {M : Trail} (h : Trail.Entailed φ M) {σ : ℕ → Bool}
    (hσ : φ.eval σ = true) (hdec : ∀ l, (l, true) ∈ M → Literal.eval σ l = true) : Sat σ M := by
  induction h with
  | nil => simp [Sat, lits]
  | decision l _ ih =>
    intro l' hl'
    simp only [lits, List.map_cons, List.mem_cons] at hl'
    rcases hl' with rfl | hl'
    · exact hdec _ List.mem_cons_self
    · exact ih (fun l hl => hdec l (List.mem_cons_of_mem _ hl)) l' hl'
  | implied l _ himp ih =>
    have hM := ih fun l hl => hdec l (List.mem_cons_of_mem _ hl)
    intro l' hl'
    simp only [lits, List.map_cons, List.mem_cons] at hl'
    rcases hl' with rfl | hl'
    · exact himp σ hσ hM
    · exact hM l' hl'

end Trail

/-- The initial state, with the empty trail and the clauses of `φ`, satisfies the invariant. -/
theorem Inv.init {φ : CNF ℕ} {V : List ℕ} (hV : ∀ c ∈ φ, ∀ l ∈ c, l.1 ∈ V) : Inv φ V ⟨[], φ⟩ :=
  ⟨fun _ => rfl, by simp [Trail.vars], by simp [Trail.vars], hV, .nil⟩

/-! ### Steps keep the invariant -/

/-- **Steps keep the invariant.** -/
theorem Step.inv {φ : CNF ℕ} {V : List ℕ} {S S' : State} (hstep : Step V S S') (h : Inv φ V S) :
    Inv φ V S' := by
  cases hstep with
  | @unitPropagate M F c l hc hl hfalse hundef hv =>
    refine ⟨h.models, ?_, ?_, h.db_vars, ?_⟩
    · simp only [Trail.vars, List.map_cons, List.nodup_cons]; exact ⟨hundef, h.nodup⟩
    · intro x hx
      simp only [Trail.vars, List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hv
      · exact h.subset x hx
    · refine .implied l h.entailed fun σ hσ hM => ?_
      have hcσ : c.eval σ = true := (CNF.eval_eq_true_iff σ F).1 (by rw [h.models]; exact hσ) c hc
      obtain ⟨l', hl', hl'σ⟩ := (Clause.eval_eq_true_iff σ c).1 hcσ
      by_cases hne : l' = l
      · subst hne; simpa [Literal.eval] using hl'σ
      · have := hM _ (hfalse l' hl' hne)
        obtain ⟨v, b⟩ := l'
        simp only [Literal.eval, beq_iff_eq] at this hl'σ
        simp_all
  | @decide M F l hundef hv =>
    refine ⟨h.models, ?_, ?_, h.db_vars, .decision l h.entailed⟩
    · simp only [Trail.vars, List.map_cons, List.nodup_cons]; exact ⟨hundef, h.nodup⟩
    · intro x hx
      simp only [Trail.vars, List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hv
      · exact h.subset x hx
  | @backjump N M₀ F d c C l learn hc hconf hC hl hfalse hundef hCV =>
    have hnodup : (Trail.vars M₀).Nodup := by
      have := h.nodup
      simp only [Trail.vars, List.map_append, List.map_cons] at this
      exact (List.nodup_cons.1 (List.nodup_append.1 this).2.1).2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro σ
      cases learn
      · exact h.models σ
      · change CNF.eval σ (C :: F) = φ.eval σ
        rw [CNF.eval_cons, ← h.models]
        cases hF : CNF.eval σ F
        · simp
        · simp [hC σ hF]
    · simp only [Trail.vars, List.map_cons, List.nodup_cons]; exact ⟨hundef, hnodup⟩
    · intro x hx
      simp only [Trail.vars, List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hCV l hl
      · exact h.subset x (by simp [Trail.vars, Trail.entryVar] at hx ⊢; tauto)
    · intro c' hc' l' hl'
      cases learn
      · exact h.db_vars c' hc' l' hl'
      · simp only [ite_true, List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact hCV l' hl'
        · exact h.db_vars c' hc' l' hl'
    · refine .implied l (Trail.entailed_append (N := N ++ [(d, true)])
        (by simpa using h.entailed)) fun σ hσ hM => ?_
      have hFσ : F.eval σ = true := by rw [h.models]; exact hσ
      obtain ⟨l', hl', hl'σ⟩ := (Clause.eval_eq_true_iff σ C).1 (hC σ hFσ)
      by_cases hne : l' = l
      · subst hne; simpa [Literal.eval] using hl'σ
      · have := hM _ (hfalse l' hl' hne)
        obtain ⟨v, b⟩ := l'
        simp only [Literal.eval, beq_iff_eq] at this hl'σ
        simp_all

/-! ### Final states -/

/-- **A state with no false clause that assigns every variable gives a model.** -/
theorem Inv.eval_model {φ : CNF ℕ} {V : List ℕ} {S : State} (h : Inv φ V S)
    (hnoconf : ∀ c ∈ S.db, ¬ Trail.Falsifies S.trail c)
    (htotal : ∀ x ∈ V, x ∈ Trail.vars S.trail) :
    φ.eval (Trail.assignment S.trail) = true := by
  rw [← h.models, CNF.eval_eq_true_iff]
  intro c hc
  have : ∃ l ∈ c, (l.1, !l.2) ∉ Trail.lits S.trail := by
    by_contra hne
    push Not at hne
    exact hnoconf c hc hne
  obtain ⟨l, hl, hopen⟩ := this
  -- `l` is assigned, and not falsely, so the trail contains it
  have hdef := htotal l.1 (h.db_vars c hc l hl)
  obtain ⟨⟨l', b⟩, hmem, hl'⟩ := List.mem_map.1 hdef
  have hl'lits : l' ∈ Trail.lits S.trail := Trail.mem_lits_iff.2 ⟨b, hmem⟩
  have hll' : l' = l := by
    obtain ⟨v, s⟩ := l
    obtain ⟨v', s'⟩ := l'
    simp only at hl'
    subst hl'
    cases s <;> cases s' <;> simp_all
  subst hll'
  refine (Clause.eval_eq_true_iff _ c).2 ⟨l', hl, ?_⟩
  obtain ⟨v, s⟩ := l'
  have := Trail.not_mem_neg h.nodup hl'lits
  cases s <;> simp_all [Trail.assignment]

/-- **A false clause with no decision shows that `φ` is unsatisfiable.** -/
theorem Inv.not_satisfiable {φ : CNF ℕ} {V : List ℕ} {S : State} (h : Inv φ V S) {c : Clause ℕ}
    (hc : c ∈ S.db) (hconf : Trail.Falsifies S.trail c) (hnodec : ∀ l, (l, true) ∉ S.trail) :
    ¬ φ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  have hM := Trail.sat_of_entailed h.entailed hσ fun l hl => absurd hl (hnodec l)
  have hcσ : c.eval σ = true := (CNF.eval_eq_true_iff σ _).1 (by rw [h.models]; exact hσ) c hc
  obtain ⟨l, hl, hlσ⟩ := (Clause.eval_eq_true_iff σ c).1 hcσ
  have := hM _ (hconf l hl)
  simp [Literal.eval, hlσ] at this

/-- The negation of the decisions of a trail. -/
def Trail.decisionClause (M : Trail) : Clause ℕ :=
  (M.filter (·.2)).map fun ⟨⟨v, b⟩, _⟩ => (v, !b)

/-- A trail with a decision splits at its newest decision. -/
theorem Trail.exists_split {M : Trail} {l : Literal ℕ} (h : (l, true) ∈ M) :
    ∃ N d M₀, M = N ++ (d, true) :: M₀ ∧ ∀ e ∈ N, e.2 = false := by
  induction M with
  | nil => simp at h
  | cons e M ih =>
    obtain ⟨l', b⟩ := e
    cases b
    · obtain ⟨N, d, M₀, rfl, hN⟩ := ih (by simpa using h)
      exact ⟨(l', false) :: N, d, M₀, rfl, by simpa using hN⟩
    · exact ⟨[], l', M, rfl, by simp⟩

/-- **In any other state some step applies**: Decide if a variable of `V` is unassigned, and
Backjump with the negation of the decisions if a clause is false. -/
theorem Inv.exists_step {φ : CNF ℕ} {V : List ℕ} {S : State} (h : Inv φ V S)
    (hfinal : ¬ ((∀ c ∈ S.db, ¬ Trail.Falsifies S.trail c) ∧ ∀ x ∈ V, x ∈ Trail.vars S.trail))
    (hfail : ¬ ∃ c ∈ S.db, Trail.Falsifies S.trail c ∧ ∀ l, (l, true) ∉ S.trail) :
    ∃ S', Step V S S' := by
  obtain ⟨M, F⟩ := S
  by_cases hconf : ∃ c ∈ F, Trail.Falsifies M c
  · obtain ⟨c, hc, hcM⟩ := hconf
    obtain ⟨l, hl⟩ : ∃ l, (l, true) ∈ M := by
      by_contra hne
      push Not at hne
      exact hfail ⟨c, hc, hcM, hne⟩
    obtain ⟨N, d, M₀, rfl, hN⟩ := Trail.exists_split hl
    have hinv := h
    have hnodup := h.nodup
    simp only [Trail.vars, List.map_append, List.map_cons] at hnodup
    obtain ⟨-, hdM₀, -⟩ := List.nodup_append.1 hnodup
    refine ⟨_, Step.backjump (C := (d.1, !d.2) :: Trail.decisionClause M₀) (l := (d.1, !d.2))
      false hc
      hcM ?_ List.mem_cons_self ?_ ?_ ?_⟩
    · -- the decisions cannot all hold in a model
      intro σ hFσ
      have hσ : φ.eval σ = true := by rw [← h.models]; exact hFσ
      by_contra hfalse
      simp only [Bool.not_eq_true, Clause.eval, List.any_eq_false, Literal.eval,
        beq_eq_false_iff_ne, ne_eq, List.mem_cons, forall_eq_or_imp] at hfalse
      have hsat := Trail.sat_of_entailed h.entailed hσ (σ := σ) fun l hl => by
        simp only [List.mem_append, List.mem_cons] at hl
        rcases hl with hl | hl | hl
        · exact absurd (hN _ hl) (by simp)
        · cases hl; simp only [Literal.eval, beq_iff_eq]; cases h' : σ d.1 <;> simp_all
        · have := hfalse.2 (l.1, !l.2) (List.mem_map.2 ⟨(l, true), List.mem_filter.2 ⟨hl, rfl⟩,
            rfl⟩)
          simp only [Literal.eval, beq_iff_eq]; cases h' : σ l.1 <;> simp_all
      obtain ⟨l', hl', hl'σ⟩ := (Clause.eval_eq_true_iff σ c).1
        ((CNF.eval_eq_true_iff σ F).1 hFσ c hc)
      have := hsat _ (hcM l' hl')
      simp [Literal.eval, hl'σ] at this
    · intro l' hl' hne
      simp only [List.mem_cons] at hl'
      rcases hl' with rfl | hl'
      · exact absurd rfl hne
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hl'
        simp only [Bool.not_not]
        exact List.mem_map.2 ⟨e, (List.mem_filter.1 he).1, rfl⟩
    · exact (List.nodup_cons.1 hdM₀).1
    · intro l' hl'
      simp only [List.mem_cons] at hl'
      rcases hl' with rfl | hl'
      · exact h.subset _ (by simp [Trail.vars])
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hl'
        exact h.subset _ (by simp only [Trail.vars, List.map_append, List.map_cons,
          List.mem_append, List.mem_cons]; exact .inr (.inr (List.mem_map.2
            ⟨e, (List.mem_filter.1 he).1, rfl⟩)))
  · push Not at hconf
    have : ∃ x ∈ V, x ∉ Trail.vars M := by
      by_contra hne
      push Not at hne
      exact hfinal ⟨hconf, hne⟩
    obtain ⟨x, hx, hxM⟩ := this
    exact ⟨_, Step.decide (l := (x, true)) hxM hx⟩

/-- **Final states decide satisfiability**: if no step applies, the trail is a model of `φ` or
`φ` is unsatisfiable. -/
theorem Inv.final {φ : CNF ℕ} {V : List ℕ} {S : State} (h : Inv φ V S)
    (hfinal : ∀ S', ¬ Step V S S') :
    φ.eval (Trail.assignment S.trail) = true ∨ ¬ φ.Satisfiable := by
  by_contra hne
  push Not at hne
  refine (h.exists_step ?_ ?_).elim fun S' hS' => hfinal S' hS'
  · rintro ⟨hnoconf, htotal⟩
    exact absurd (h.eval_model hnoconf htotal) (by simp [hne.1])
  · rintro ⟨c, hc, hconf, hnodec⟩
    exact h.not_satisfiable hc hconf hnodec hne.2

/-! ### Termination -/

/-- The measure of a trail over `N` variables: a literal at level `k` weighs `(N + 1) ^ (N - k)`. -/
def Trail.measure (N : ℕ) : Trail → ℕ
  | [] => 0
  | e :: M => measure N M + (N + 1) ^ (N - (Trail.level M + if e.2 then 1 else 0))

theorem Trail.level_cons (e : Literal ℕ × Bool) (M : Trail) :
    level (e :: M) = Trail.level M + if e.2 then 1 else 0 := by
  obtain ⟨l, b⟩ := e
  cases b <;> simp [level]

theorem Trail.level_le_length (M : Trail) : Trail.level M ≤ M.length :=
  List.length_filter_le _ _

theorem Trail.level_le_level_append (N M : Trail) : Trail.level M ≤ (Trail.level (N ++ M)) := by
  simp only [level, List.filter_append, List.length_append]
  omega

/-- The literals above a trail weigh at most `(N + 1) ^ (N - level)` each. -/
theorem Trail.measure_append_le (n : ℕ) (N M : Trail) :
    measure n (N ++ M) ≤ measure n M + N.length * (n + 1) ^ (n - Trail.level M) := by
  induction N with
  | nil => simp
  | cons e N ih =>
    simp only [List.cons_append, measure, List.length_cons]
    have hlev := level_le_level_append N M
    have : (n + 1) ^ (n - (Trail.level (N ++ M) + if e.2 then 1 else 0)) ≤
        (n + 1) ^ (n - Trail.level M) :=
      Nat.pow_le_pow_right (by omega) (by split <;> omega)
    nlinarith

theorem Trail.measure_le (n : ℕ) (M : Trail) : measure n M ≤ M.length * (n + 1) ^ n := by
  induction M with
  | nil => simp [measure]
  | cons e M ih =>
    simp only [measure, List.length_cons]
    have : (n + 1) ^ (n - (Trail.level M + if e.2 then 1 else 0)) ≤ (n + 1) ^ n :=
      Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith

/-- The length of a trail is at most the number of variables it may use. -/
theorem Inv.length_le {φ : CNF ℕ} {V : List ℕ} {S : State} (h : Inv φ V S) :
    S.trail.length ≤ V.dedup.length := by
  have := List.Nodup.length_le_of_subset h.nodup fun x hx => List.mem_dedup.2 (h.subset x hx)
  simpa [Trail.vars] using this

/-- **Every step strictly increases the measure.** -/
theorem Step.measure_lt {φ : CNF ℕ} {V : List ℕ} {S S' : State} (hstep : Step V S S')
    (h : Inv φ V S) :
    (Trail.measure V.dedup.length S.trail) < (Trail.measure V.dedup.length S'.trail) := by
  have hlen' := (hstep.inv h).length_le
  cases hstep with
  | unitPropagate | decide =>
    simp only [Trail.measure]
    exact Nat.lt_add_of_pos_right (Nat.pow_pos (by omega))
  | @backjump N M₀ F d c C l learn hc hconf hC hl hfalse hundef hCV =>
    have hlen := h.length_le
    set n := V.dedup.length
    simp only [List.length_append, List.length_cons] at hlen
    have hle := Trail.measure_append_le n N ((d, true) :: M₀)
    simp only [Trail.measure, Trail.level_cons, ite_true, Bool.false_eq_true, ite_false,
      Nat.add_zero] at hle ⊢
    have hlev := Trail.level_le_length M₀
    -- one literal at level `L` outweighs the literals above it
    have hpow :
        (n + 1) ^ (n - Trail.level M₀) = (n + 1) * (n + 1) ^ (n - (Trail.level M₀ + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    have : (N.length + 1) * (n + 1) ^ (n - (Trail.level M₀ + 1)) <
        (n + 1) * (n + 1) ^ (n - (Trail.level M₀ + 1)) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    nlinarith

/-- **There is no infinite run**: the converse of the step relation, on states satisfying the
invariant, is well founded. -/
theorem wellFounded_step (φ : CNF ℕ) (V : List ℕ) :
    WellFounded fun S' S => Inv φ V S ∧ Step V S S' := by
  set n := V.dedup.length
  refine Subrelation.wf (r := InvImage (· < ·) fun S : State =>
    n * (n + 1) ^ n + 1 - (Trail.measure n S.trail)) ?_ (InvImage.wf _ wellFounded_lt)
  intro S' S ⟨h, hstep⟩
  have hlt : Trail.measure n S.trail < Trail.measure n S'.trail := hstep.measure_lt h
  have hle := Trail.measure_le n S'.trail
  have hlen := (hstep.inv h).length_le
  have : (Trail.measure n S'.trail) ≤ n * (n + 1) ^ n :=
    hle.trans (Nat.mul_le_mul_right _ hlen)
  simp only [InvImage]
  omega

end Cslib.Algorithms.Lean.CDCL
