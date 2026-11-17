/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF
import Mathlib.Tactic.Linarith

/-! # Abstract DPLL with learning

Nieuwenhuis, Oliveras and Tinelli [NieuwenhuisOliverasTinelli2006, §2] describe DPLL and conflict
driven clause learning as transition systems. A state (`Cslib.Algorithms.Lean.CDCL.State`) is
either the distinguished `fail` state or a trail `M` with a clause database `F`. The trail
(`Cslib.Algorithms.Lean.CDCL.Trail`) is the sequence of assigned literals, kept here newest first,
each marked as a decision or not (`Cslib.Algorithms.Lean.CDCL.Entry`). The rules over the variables
`V` are:

* the *Basic DPLL* rules (`Cslib.Algorithms.Lean.CDCL.BasicStep`, their Definition 2.4):
  * **UnitPropagate**: if a clause of `F` has every literal but `l` false and `l` is undefined,
    add `l`;
  * **Decide**: add an undefined literal over a variable of `V` as a decision;
  * **Fail**: if a clause of `F` is false and `M` has no decision, go to `fail`;
  * **Backjump**: if a clause of `F` is false, `M = N ++ dᵈ :: M₀`, and a clause `C` entailed by
    `F` has every literal but `l` false in `M₀`, with `l` undefined in `M₀`, go to `l :: M₀`;
* **Learn** (`Cslib.Algorithms.Lean.CDCL.Learn`, their Definition 2.5): add a clause entailed by `F`
  over variables of `V`.

The invariant `Cslib.Algorithms.Lean.CDCL.Inv` is their Lemma 2.7: the database has the models of
`φ`, the trail assigns each variable of `V` at most once, and every implied literal holds in every
model of `φ` satisfying the older literals; in `fail`, `φ` is unsatisfiable. Every step keeps it
(`Cslib.Algorithms.Lean.CDCL.Step.inv`). Their results then hold:

* **Lemma 2.8**: in a state with a false clause, Fail or Backjump applies, the latter with the
  negation of the decisions (`Cslib.Algorithms.Lean.CDCL.RunInv.exists_basicStep`).
* **Theorem 2.10**: there is no infinite run of Basic DPLL steps from the initial state
  (`Cslib.Algorithms.Lean.CDCL.wellFounded_basicStep`). With `N` variables, a literal at level `k`
  weighs `(N + 1) ^ (N - k)`, and every step increases the weight of the trail, which is at most
  `N * (N + 1) ^ N` (`Cslib.Algorithms.Lean.CDCL.Trail.measure`); this replaces their
  lexicographic order on the numbers of literals per level with a single number.
* **Theorem 2.11**: every run with Learn is finite if it has no infinite stretch of Learn steps,
  stated as the well-foundedness of "Learn steps, then a Basic DPLL step"
  (`Cslib.Algorithms.Lean.CDCL.wellFounded_learn_basicStep`).
* **Theorem 2.12**: a reachable state that is final for Basic DPLL is `fail` exactly when `φ` is
  unsatisfiable, and otherwise its trail is a model of `φ`
  (`Cslib.Algorithms.Lean.CDCL.final_of_reachable`).

**Adaptations.** The Forget rule and restarts are not included. The variables are a list `V`
containing those of `φ`, rather than the atoms occurring in the current database; the headline
statements take `V = φ.vars`. A literal is decided over a variable of `V`, where the source asks
that it occur in the database; their Lemma 2.7(1) makes these the same variables. Locators refer to
the authors' manuscript, printed pp. 5–15.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.BasicStep`, `Cslib.Algorithms.Lean.CDCL.Learn`,
  `Cslib.Algorithms.Lean.CDCL.Step`: the transition systems.
* `Cslib.Algorithms.Lean.CDCL.Inv`: the invariant.

## Main results

* `Cslib.Algorithms.Lean.CDCL.Step.inv`: steps keep the invariant (Lemma 2.7).
* `Cslib.Algorithms.Lean.CDCL.RunInv.exists_basicStep`: progress (Lemma 2.8).
* `Cslib.Algorithms.Lean.CDCL.wellFounded_basicStep`,
  `Cslib.Algorithms.Lean.CDCL.wellFounded_learn_basicStep`: termination (Theorems 2.10, 2.11).
* `Cslib.Algorithms.Lean.CDCL.final_of_reachable`: final states decide satisfiability
  (Theorem 2.12).

## References

* [R. Nieuwenhuis, A. Oliveras, C. Tinelli, *Solving SAT and SAT Modulo Theories: From an Abstract
  Davis–Putnam–Logemann–Loveland Procedure to DPLL(T)*][NieuwenhuisOliverasTinelli2006], §2.2–2.5
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL

/-- An entry of a trail: a literal and whether it is a decision. -/
structure Entry where
  /-- The literal. -/
  lit : Literal ℕ
  /-- Whether the literal is a decision. -/
  decision : Bool
deriving DecidableEq

/-- The variable of an entry. -/
abbrev Entry.var (e : Entry) : ℕ := e.lit.1

/-- A trail: the assigned literals, newest first. -/
abbrev Trail := List Entry

namespace Trail

/-- The literals of a trail. -/
def lits (M : Trail) : List (Literal ℕ) := M.map Entry.lit

/-- The variables of a trail. -/
def vars (M : Trail) : List ℕ := M.map Entry.var

/-- A trail falsifies a clause if it contains the negation of every literal of the clause. -/
abbrev Falsifies (M : Trail) (c : Clause ℕ) : Prop := ∀ l ∈ c, l.negate ∈ lits M

/-- The level of a trail: its number of decisions. -/
def level (M : Trail) : ℕ := (M.filter Entry.decision).length

/-- An assignment satisfies a trail if it makes every literal of the trail true. -/
def Sat (σ : ℕ → Bool) (M : Trail) : Prop := ∀ l ∈ lits M, Literal.eval σ l = true

/-- Every implied literal of the trail holds in every model of `φ` satisfying the older
literals. -/
inductive Entailed (φ : CNF ℕ) : Trail → Prop
  | nil : Entailed φ []
  | decision {M : Trail} (l : Literal ℕ) : Entailed φ M → Entailed φ (⟨l, true⟩ :: M)
  | implied {M : Trail} (l : Literal ℕ) : Entailed φ M →
      (∀ σ, φ.eval σ = true → Sat σ M → Literal.eval σ l = true) →
      Entailed φ (⟨l, false⟩ :: M)

/-- The total assignment of a trail: a variable is true if the trail makes it true. -/
def assignment (M : Trail) (x : ℕ) : Bool := decide ((x, true) ∈ lits M)

/-- The negation of the decisions of a trail. -/
def decisionClause (M : Trail) : Clause ℕ :=
  (M.filter Entry.decision).map fun e => e.lit.negate

end Trail

/-- A state: the distinguished failure state, or a trail and a clause database. -/
inductive State
  /-- The failure state. -/
  | fail
  /-- A trail and a clause database. -/
  | run (trail : Trail) (db : CNF ℕ)

/-- **The Basic DPLL rules** over the variables `V` [NieuwenhuisOliverasTinelli2006, Definition
2.4]. -/
inductive BasicStep (V : List ℕ) : State → State → Prop
  /-- UnitPropagate: a clause with every literal but `l` false makes `l` implied. -/
  | unitPropagate {M : Trail} {F : CNF ℕ} {c : Clause ℕ} {l : Literal ℕ} (hc : c ∈ F) (hl : l ∈ c)
      (hfalse : ∀ l' ∈ c, l' ≠ l → l'.negate ∈ Trail.lits M) (hundef : l.1 ∉ Trail.vars M)
      (hv : l.1 ∈ V) : BasicStep V (.run M F) (.run (⟨l, false⟩ :: M) F)
  /-- Decide: an undefined literal over a variable of `V` becomes a decision. -/
  | decide {M : Trail} {F : CNF ℕ} {l : Literal ℕ} (hundef : l.1 ∉ Trail.vars M) (hv : l.1 ∈ V) :
      BasicStep V (.run M F) (.run (⟨l, true⟩ :: M) F)
  /-- Fail: a false clause and no decision. -/
  | fail {M : Trail} {F : CNF ℕ} {c : Clause ℕ} (hc : c ∈ F) (hconf : Trail.Falsifies M c)
      (hnodec : ∀ e ∈ M, e.decision = false) : BasicStep V (.run M F) .fail
  /-- Backjump: going back below a decision and adding the literal that an entailed clause `C`
  implies there. -/
  | backjump {N M₀ : Trail} {F : CNF ℕ} {d : Literal ℕ} {c C : Clause ℕ} {l : Literal ℕ}
      (hc : c ∈ F) (hconf : Trail.Falsifies (N ++ ⟨d, true⟩ :: M₀) c)
      (hC : ∀ σ, F.eval σ = true → C.eval σ = true) (hl : l ∈ C)
      (hfalse : ∀ l' ∈ C, l' ≠ l → l'.negate ∈ Trail.lits M₀) (hundef : l.1 ∉ Trail.vars M₀)
      (hCV : ∀ l' ∈ C, l'.1 ∈ V) :
      BasicStep V (.run (N ++ ⟨d, true⟩ :: M₀) F) (.run (⟨l, false⟩ :: M₀) F)

/-- **Learn** [NieuwenhuisOliverasTinelli2006, Definition 2.5]: adding a clause entailed by the
database, over variables of `V`. -/
inductive Learn (V : List ℕ) : State → State → Prop
  | learn {M : Trail} {F : CNF ℕ} {C : Clause ℕ} (hC : ∀ σ, F.eval σ = true → C.eval σ = true)
      (hCV : ∀ l ∈ C, l.1 ∈ V) : Learn V (.run M F) (.run M (C :: F))

/-- **DPLL with learning**: a Basic DPLL step or a Learn step. -/
def Step (V : List ℕ) (S S' : State) : Prop := BasicStep V S S' ∨ Learn V S S'

/-- The invariant of a running state [NieuwenhuisOliverasTinelli2006, Lemma 2.7]. -/
structure RunInv (φ : CNF ℕ) (V : List ℕ) (M : Trail) (F : CNF ℕ) : Prop where
  /-- The database has the models of `φ`. -/
  models : ∀ σ, F.eval σ = φ.eval σ
  /-- The trail assigns each variable at most once. -/
  nodup : (Trail.vars M).Nodup
  /-- The trail assigns variables of `V`. -/
  subset : ∀ x ∈ Trail.vars M, x ∈ V
  /-- The database uses variables of `V`. -/
  db_vars : ∀ c ∈ F, ∀ l ∈ c, l.1 ∈ V
  /-- Every implied literal follows from `φ` and the older literals. -/
  entailed : Trail.Entailed φ M

/-- **The invariant** for the formula `φ` over the variables `V`: in a running state
`Cslib.Algorithms.Lean.CDCL.RunInv`, and in `fail`, `φ` is unsatisfiable. -/
def Inv (φ : CNF ℕ) (V : List ℕ) : State → Prop
  | .fail => ¬ φ.Satisfiable
  | .run M F => RunInv φ V M F

namespace Trail

theorem mem_vars_of_mem_lits {M : Trail} {l : Literal ℕ} (h : l ∈ lits M) : l.1 ∈ vars M := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
  exact List.mem_map.2 ⟨e, he, rfl⟩

/-- A trail assigning each variable once does not contain a literal and its negation. -/
theorem negate_not_mem {M : Trail} (hM : (vars M).Nodup) {l : Literal ℕ} (h : l ∈ lits M) :
    l.negate ∉ lits M := by
  induction M with
  | nil => simp [lits] at h
  | cons e M ih =>
    simp only [vars, List.map_cons, List.nodup_cons] at hM
    simp only [lits, List.map_cons, List.mem_cons] at h ⊢
    rintro (heq | hmem)
    · rcases h with rfl | h
      · obtain ⟨⟨v, b⟩, _⟩ := e
        cases b <;> simp [Std.Sat.Literal.negate] at heq
      · exact hM.1 (by simpa [vars, Entry.var, ← heq, Std.Sat.Literal.negate] using
          mem_vars_of_mem_lits h)
    · rcases h with rfl | h
      · exact hM.1 (by simpa [vars, Entry.var, Std.Sat.Literal.negate] using
          mem_vars_of_mem_lits hmem)
      · exact ih hM.2 h hmem

theorem entailed_append {φ : CNF ℕ} {N M : Trail} (h : Entailed φ (N ++ M)) : Entailed φ M := by
  induction N with
  | nil => simpa using h
  | cons e N ih => cases h <;> exact ih ‹_›

/-- A model of `φ` that satisfies the decisions of an entailed trail satisfies the trail. -/
theorem sat_of_entailed {φ : CNF ℕ} {M : Trail} (h : Entailed φ M) {σ : ℕ → Bool}
    (hσ : φ.eval σ = true) (hdec : ∀ l, (⟨l, true⟩ : Entry) ∈ M → Literal.eval σ l = true) :
    Sat σ M := by
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

/-- A clause that holds, with every literal but `l` false, forces `l`. -/
theorem eval_of_forall_ne {σ : ℕ → Bool} {c : Clause ℕ} {l : Literal ℕ} {M : Trail}
    (hc : c.eval σ = true) (hM : Sat σ M) (hfalse : ∀ l' ∈ c, l' ≠ l → l'.negate ∈ lits M) :
    Literal.eval σ l = true := by
  obtain ⟨l', hl', hl'σ⟩ := (Clause.eval_eq_true_iff σ c).1 hc
  by_cases hne : l' = l
  · subst hne; simpa [Literal.eval] using hl'σ
  · have := hM _ (hfalse l' hl' hne)
    rw [Literal.eval_negate] at this
    simp [Literal.eval, hl'σ] at this

end Trail

/-- The initial state, with the empty trail and the clauses of `φ`, satisfies the invariant. -/
theorem Inv.init {φ : CNF ℕ} {V : List ℕ} (hV : ∀ c ∈ φ, ∀ l ∈ c, l.1 ∈ V) :
    Inv φ V (.run [] φ) :=
  ⟨fun _ => rfl, by simp [Trail.vars], by simp [Trail.vars], hV, .nil⟩

/-! ### Steps keep the invariant -/

/-- Adding a literal over an unassigned variable of `V` keeps the trail's variables distinct and
in `V`. -/
theorem RunInv.push {φ : CNF ℕ} {V : List ℕ} {M : Trail} {F : CNF ℕ} (h : RunInv φ V M F)
    {l : Literal ℕ} (b : Bool) (hundef : l.1 ∉ Trail.vars M) (hv : l.1 ∈ V) :
    (Trail.vars (⟨l, b⟩ :: M)).Nodup ∧ ∀ x ∈ Trail.vars (⟨l, b⟩ :: M), x ∈ V := by
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [Trail.vars, List.map_cons, List.nodup_cons]
    exact ⟨hundef, h.nodup⟩
  · simp only [Trail.vars, List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hv
    · exact h.subset x hx

/-- **Steps keep the invariant** [NieuwenhuisOliverasTinelli2006, Lemma 2.7]. -/
theorem Step.inv {φ : CNF ℕ} {V : List ℕ} {S S' : State} (hstep : Step V S S') (h : Inv φ V S) :
    Inv φ V S' := by
  rcases hstep with hstep | hstep
  · cases hstep with
    | @unitPropagate M F c l hc hl hfalse hundef hv =>
      obtain ⟨hnd, hsub⟩ := RunInv.push h false hundef hv
      refine ⟨h.models, hnd, hsub, h.db_vars, .implied l h.entailed fun σ hσ hM => ?_⟩
      exact Trail.eval_of_forall_ne
        ((CNF.eval_eq_true_iff σ F).1 (by rw [h.models]; exact hσ) c hc) hM hfalse
    | @decide M F l hundef hv =>
      obtain ⟨hnd, hsub⟩ := RunInv.push h true hundef hv
      exact ⟨h.models, hnd, hsub, h.db_vars, .decision l h.entailed⟩
    | @fail M F c hc hconf hnodec =>
      rintro ⟨σ, hσ⟩
      have hM := Trail.sat_of_entailed h.entailed hσ fun l hl => by simpa using hnodec _ hl
      obtain ⟨l, hl, hlσ⟩ := (Clause.eval_eq_true_iff σ c).1
        ((CNF.eval_eq_true_iff σ F).1 (by rw [h.models]; exact hσ) c hc)
      have := hM _ (hconf l hl)
      rw [Literal.eval_negate] at this
      simp [Literal.eval, hlσ] at this
    | @backjump N M₀ F d c C l hc hconf hC hl hfalse hundef hCV =>
      have hnodup : (Trail.vars M₀).Nodup := by
        have := h.nodup
        simp only [Trail.vars, List.map_append, List.map_cons] at this
        exact (List.nodup_cons.1 (List.nodup_append.1 this).2.1).2
      refine ⟨h.models, ?_, ?_, h.db_vars, ?_⟩
      · simp only [Trail.vars, List.map_cons, List.nodup_cons]
        exact ⟨hundef, hnodup⟩
      · intro x hx
        simp only [Trail.vars, List.map_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hCV l hl
        · exact h.subset x (by simp [Trail.vars] at hx ⊢; tauto)
      · refine .implied l (Trail.entailed_append (N := N ++ [⟨d, true⟩])
          (by simpa using h.entailed)) fun σ hσ hM => ?_
        exact Trail.eval_of_forall_ne (hC σ (by rw [h.models]; exact hσ)) hM hfalse
  · cases hstep with
    | @learn M F C hC hCV =>
      refine ⟨fun σ => ?_, h.nodup, h.subset, ?_, h.entailed⟩
      · rw [CNF.eval_cons, ← h.models]
        cases hF : CNF.eval σ F
        · simp
        · simp [hC σ hF]
      · intro c hc l hl
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hCV l hl
        · exact h.db_vars c hc l hl

/-! ### Final states -/

/-- A running state with no false clause that assigns every variable gives a model. -/
theorem RunInv.eval_model {φ : CNF ℕ} {V : List ℕ} {M : Trail} {F : CNF ℕ} (h : RunInv φ V M F)
    (hnoconf : ∀ c ∈ F, ¬ Trail.Falsifies M c) (htotal : ∀ x ∈ V, x ∈ Trail.vars M) :
    φ.eval (Trail.assignment M) = true := by
  rw [← h.models, CNF.eval_eq_true_iff]
  intro c hc
  have : ∃ l ∈ c, l.negate ∉ Trail.lits M := by
    by_contra hne
    push Not at hne
    exact hnoconf c hc hne
  obtain ⟨l, hl, hopen⟩ := this
  -- `l` is assigned, and not falsely, so the trail contains it
  obtain ⟨e, hmem, hl'⟩ := List.mem_map.1 (htotal l.1 (h.db_vars c hc l hl))
  have helits : e.lit ∈ Trail.lits M := List.mem_map.2 ⟨e, hmem, rfl⟩
  have hel : e.lit = l := by
    obtain ⟨⟨v', s'⟩, b⟩ := e
    obtain ⟨v, s⟩ := l
    simp only [Entry.var] at hl'
    subst hl'
    cases s <;> cases s' <;> simp_all [Std.Sat.Literal.negate]
  rw [hel] at helits
  refine (Clause.eval_eq_true_iff _ c).2 ⟨l, hl, ?_⟩
  obtain ⟨v, s⟩ := l
  have := Trail.negate_not_mem h.nodup helits
  cases s <;> simp_all [Trail.assignment, Std.Sat.Literal.negate]

/-- A trail with a decision splits at its newest decision. -/
theorem Trail.exists_split {M : Trail} (h : ∃ e ∈ M, e.decision = true) :
    ∃ N d M₀, M = N ++ ⟨d, true⟩ :: M₀ ∧ ∀ e ∈ N, e.decision = false := by
  induction M with
  | nil => simp at h
  | cons e M ih =>
    obtain ⟨l', b⟩ := e
    cases b
    · obtain ⟨N, d, M₀, rfl, hN⟩ := ih (by simpa using h)
      exact ⟨⟨l', false⟩ :: N, d, M₀, rfl, by simpa using hN⟩
    · exact ⟨[], l', M, rfl, by simp⟩

/-- **Progress** [NieuwenhuisOliverasTinelli2006, Lemma 2.8, and the Decide case of Lemma 2.9]:
in a running state with a false clause, Fail applies if the trail has no decision and Backjump with
the negation of the decisions otherwise; with no false clause, Decide applies if a variable of `V`
is unassigned. -/
theorem RunInv.exists_basicStep {φ : CNF ℕ} {V : List ℕ} {M : Trail} {F : CNF ℕ}
    (h : RunInv φ V M F)
    (hfinal : ¬ ((∀ c ∈ F, ¬ Trail.Falsifies M c) ∧ ∀ x ∈ V, x ∈ Trail.vars M)) :
    ∃ S', BasicStep V (.run M F) S' := by
  by_cases hconf : ∃ c ∈ F, Trail.Falsifies M c
  · obtain ⟨c, hc, hcM⟩ := hconf
    by_cases hdec : ∃ e ∈ M, e.decision = true
    · obtain ⟨N, d, M₀, rfl, hN⟩ := Trail.exists_split hdec
      have hnodup := h.nodup
      simp only [Trail.vars, List.map_append, List.map_cons] at hnodup
      obtain ⟨-, hdM₀, -⟩ := List.nodup_append.1 hnodup
      refine ⟨_, BasicStep.backjump (C := d.negate :: Trail.decisionClause M₀) (l := d.negate)
        hc hcM ?_ List.mem_cons_self ?_ ?_ ?_⟩
      · -- the decisions cannot all hold in a model
        intro σ hFσ
        have hσ : φ.eval σ = true := by rw [← h.models]; exact hFσ
        by_contra hfalse
        simp only [Bool.not_eq_true, Clause.eval, List.any_eq_false, List.mem_cons,
          forall_eq_or_imp] at hfalse
        have hsat := Trail.sat_of_entailed h.entailed hσ (σ := σ) fun l hl => by
          simp only [List.mem_append, List.mem_cons] at hl
          rcases hl with hl | hl | hl
          · exact absurd (hN _ hl) (by simp)
          · cases hl
            have := hfalse.1
            rw [Literal.eval_negate] at this
            simpa using this
          · have := hfalse.2 _ (List.mem_map.2 ⟨⟨l, true⟩, List.mem_filter.2 ⟨hl, rfl⟩, rfl⟩)
            rw [Literal.eval_negate] at this
            simpa using this
        obtain ⟨l', hl', hl'σ⟩ := (Clause.eval_eq_true_iff σ c).1
          ((CNF.eval_eq_true_iff σ F).1 hFσ c hc)
        have := hsat _ (hcM l' hl')
        rw [Literal.eval_negate] at this
        simp [Literal.eval, hl'σ] at this
      · intro l' hl' hne
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact absurd rfl hne
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hl'
          simp only [Std.Sat.Literal.negate, Bool.not_not]
          exact List.mem_map.2 ⟨e, (List.mem_filter.1 he).1, rfl⟩
      · exact (List.nodup_cons.1 hdM₀).1
      · intro l' hl'
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact h.subset _ (by simp [Trail.vars, Std.Sat.Literal.negate])
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hl'
          exact h.subset _ (by simp only [Trail.vars, List.map_append, List.map_cons,
            List.mem_append, List.mem_cons]; exact .inr (.inr (List.mem_map.2
              ⟨e, (List.mem_filter.1 he).1, rfl⟩)))
    · push Not at hdec
      exact ⟨_, BasicStep.fail hc hcM fun e he => by simpa using hdec e he⟩
  · push Not at hconf
    have : ∃ x ∈ V, x ∉ Trail.vars M := by
      by_contra hne
      push Not at hne
      exact hfinal ⟨hconf, hne⟩
    obtain ⟨x, hx, hxM⟩ := this
    exact ⟨_, BasicStep.decide (l := (x, true)) hxM hx⟩

/-- A state that satisfies the invariant and is final for Basic DPLL is `fail` exactly when `φ` is
unsatisfiable, and otherwise its trail is a model of `φ`. -/
theorem Inv.final {φ : CNF ℕ} {V : List ℕ} {S : State} (h : Inv φ V S)
    (hfinal : ∀ S', ¬ BasicStep V S S') :
    (S = .fail ↔ ¬ φ.Satisfiable) ∧ ∀ M F, S = .run M F → φ.eval (Trail.assignment M) = true := by
  cases S with
  | fail => exact ⟨⟨fun _ => h, fun _ => rfl⟩, fun _ _ h => absurd h (by simp)⟩
  | run M F =>
    have hmodel : φ.eval (Trail.assignment M) = true := by
      by_contra hne
      obtain ⟨S', hS'⟩ := RunInv.exists_basicStep h fun ⟨hnoconf, htotal⟩ =>
        hne (h.eval_model hnoconf htotal)
      exact hfinal S' hS'
    refine ⟨⟨fun hS => absurd hS (by simp), fun hns => absurd ⟨_, hmodel⟩ hns⟩, ?_⟩
    rintro M' F' hS
    cases hS
    exact hmodel

/-- The states reachable from the initial state satisfy the invariant. -/
theorem inv_of_reachable {φ : CNF ℕ} {S : State}
    (h : Relation.ReflTransGen (Step φ.vars) (.run [] φ) S) : Inv φ φ.vars S := by
  induction h with
  | refl => exact Inv.init fun c hc l hl => CNF.mem_vars.2 ⟨c, hc, l.2, hl⟩
  | tail _ hstep ih => exact hstep.inv ih

/-- **Final states decide satisfiability** [NieuwenhuisOliverasTinelli2006, Theorem 2.12]: a state
reachable from the initial state by DPLL with learning and final for Basic DPLL is `fail` exactly
when `φ` is unsatisfiable, and otherwise its trail is a model of `φ`. -/
theorem final_of_reachable {φ : CNF ℕ} {S : State}
    (h : Relation.ReflTransGen (Step φ.vars) (.run [] φ) S)
    (hfinal : ∀ S', ¬ BasicStep φ.vars S S') :
    (S = .fail ↔ ¬ φ.Satisfiable) ∧ ∀ M F, S = .run M F → φ.eval (Trail.assignment M) = true :=
  (inv_of_reachable h).final hfinal

/-! ### Termination -/

/-- The measure of a trail over `N` variables: a literal at level `k` weighs `(N + 1) ^ (N - k)`. -/
def Trail.measure (N : ℕ) : Trail → ℕ
  | [] => 0
  | e :: M => measure N M + (N + 1) ^ (N - (level M + if e.decision then 1 else 0))

theorem Trail.level_cons (e : Entry) (M : Trail) :
    level (e :: M) = level M + if e.decision then 1 else 0 := by
  obtain ⟨l, b⟩ := e
  cases b <;> simp [level]

theorem Trail.level_le_length (M : Trail) : level M ≤ M.length :=
  List.length_filter_le _ _

theorem Trail.level_le_level_append (N M : Trail) : level M ≤ level (N ++ M) := by
  simp only [level, List.filter_append, List.length_append]
  omega

theorem Trail.measure_lt_cons (n : ℕ) (e : Entry) (M : Trail) :
    measure n M < measure n (e :: M) := by
  simp only [measure]
  exact Nat.lt_add_of_pos_right (Nat.pow_pos (Nat.succ_pos n))

/-- The literals above a trail weigh at most `(N + 1) ^ (N - level)` each. -/
theorem Trail.measure_append_le (n : ℕ) (N M : Trail) :
    measure n (N ++ M) ≤ measure n M + N.length * (n + 1) ^ (n - level M) := by
  induction N with
  | nil => simp
  | cons e N ih =>
    simp only [List.cons_append, measure, List.length_cons]
    have hlev := level_le_level_append N M
    have : (n + 1) ^ (n - (level (N ++ M) + if e.decision then 1 else 0)) ≤
        (n + 1) ^ (n - level M) :=
      Nat.pow_le_pow_right (by omega) (by split <;> omega)
    nlinarith

theorem Trail.measure_le (n : ℕ) (M : Trail) : measure n M ≤ M.length * (n + 1) ^ n := by
  simpa [measure, level] using measure_append_le n M []

/-- The length of a trail is at most the number of variables it may use. -/
theorem RunInv.length_le {φ : CNF ℕ} {V : List ℕ} {M : Trail} {F : CNF ℕ} (h : RunInv φ V M F) :
    M.length ≤ V.dedup.length := by
  have := List.Nodup.length_le_of_subset h.nodup fun x hx => List.mem_dedup.2 (h.subset x hx)
  simpa [Trail.vars] using this

/-- The measure of a trail satisfying the invariant is at most `N * (N + 1) ^ N`. -/
theorem RunInv.measure_le {φ : CNF ℕ} {V : List ℕ} {M : Trail} {F : CNF ℕ} (h : RunInv φ V M F) :
    Trail.measure V.dedup.length M ≤
      V.dedup.length * (V.dedup.length + 1) ^ V.dedup.length :=
  (Trail.measure_le _ M).trans (Nat.mul_le_mul_right _ h.length_le)

/-- The rank of a state over the variables `V`: `0` for `fail`, and otherwise one more than the
room left below the bound on the measure. Every Basic DPLL step lowers it. -/
def rank (V : List ℕ) : State → ℕ
  | .fail => 0
  | .run M _ =>
    V.dedup.length * (V.dedup.length + 1) ^ V.dedup.length + 1 - Trail.measure V.dedup.length M

/-- **Every Basic DPLL step lowers the rank.** -/
theorem BasicStep.rank_lt {φ : CNF ℕ} {V : List ℕ} {S S' : State} (hstep : BasicStep V S S')
    (h : Inv φ V S) : rank V S' < rank V S := by
  have h' := Step.inv (.inl hstep) h
  cases hstep with
  | fail =>
    have := RunInv.measure_le (show RunInv _ _ _ _ from h)
    simp only [rank]
    omega
  | @unitPropagate M F c l _ _ _ _ _ =>
    have hle := RunInv.measure_le (show RunInv _ _ _ _ from h')
    have := Trail.measure_lt_cons V.dedup.length ⟨l, false⟩ M
    simp only [rank]
    omega
  | @decide M F l _ _ =>
    have hle := RunInv.measure_le (show RunInv _ _ _ _ from h')
    have := Trail.measure_lt_cons V.dedup.length ⟨l, true⟩ M
    simp only [rank]
    omega
  | @backjump N M₀ F d c C l hc hconf hC hl hfalse hundef hCV =>
    have hlen := (show RunInv _ _ _ _ from h).length_le
    have hle' := RunInv.measure_le (show RunInv _ _ _ _ from h')
    set n := V.dedup.length with hn
    simp only [List.length_append, List.length_cons] at hlen
    have hle := Trail.measure_append_le n N (⟨d, true⟩ :: M₀)
    simp only [Trail.measure, Trail.level_cons, ite_true, Bool.false_eq_true, ite_false,
      Nat.add_zero] at hle hle' ⊢
    have hlev := Trail.level_le_length M₀
    -- one literal at level `L` outweighs the literals above it
    have hpow :
        (n + 1) ^ (n - Trail.level M₀) = (n + 1) * (n + 1) ^ (n - (Trail.level M₀ + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    have : (N.length + 1) * (n + 1) ^ (n - (Trail.level M₀ + 1)) <
        (n + 1) * (n + 1) ^ (n - (Trail.level M₀ + 1)) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega))
    have hlt : Trail.measure n (N ++ ⟨d, true⟩ :: M₀) <
        Trail.measure n M₀ + (n + 1) ^ (n - Trail.level M₀) := by
      nlinarith
    have heq : Trail.measure n (⟨l, false⟩ :: M₀) =
        Trail.measure n M₀ + (n + 1) ^ (n - Trail.level M₀) := by
      simp [Trail.measure]
    simp only [rank]
    rw [← hn]
    omega

/-- **Termination of Basic DPLL** [NieuwenhuisOliverasTinelli2006, Theorem 2.10]: there is no
infinite run of Basic DPLL steps from the initial state. -/
theorem wellFounded_basicStep (φ : CNF ℕ) :
    WellFounded fun S' S =>
      Relation.ReflTransGen (Step φ.vars) (.run [] φ) S ∧ BasicStep φ.vars S S' :=
  Subrelation.wf (r := InvImage (· < ·) (rank φ.vars))
    (fun ⟨hreach, hstep⟩ => hstep.rank_lt (inv_of_reachable hreach)) (InvImage.wf _ wellFounded_lt)

/-- Learn steps keep the trail, hence the rank. -/
theorem Learn.rank_eq {V : List ℕ} {S S' : State} (h : Learn V S S') : rank V S' = rank V S := by
  cases h
  rfl

/-- Learn steps from a reachable state reach states of the same rank. -/
theorem reachable_rank_of_learn {φ : CNF ℕ} {S S₁ : State}
    (hreach : Relation.ReflTransGen (Step φ.vars) (.run [] φ) S)
    (hl : Relation.ReflTransGen (Learn φ.vars) S S₁) :
    Relation.ReflTransGen (Step φ.vars) (.run [] φ) S₁ ∧ rank φ.vars S₁ = rank φ.vars S := by
  induction hl with
  | refl => exact ⟨hreach, rfl⟩
  | tail _ hl ih => exact ⟨ih.1.tail (.inr hl), hl.rank_eq.trans ih.2⟩

/-- **Termination of DPLL with learning** [NieuwenhuisOliverasTinelli2006, Theorem 2.11]: a run in
which no stretch of Learn steps is infinite is finite. Equivalently, there is no infinite sequence
of moves from the initial state, each a finite run of Learn steps followed by a Basic DPLL step. -/
theorem wellFounded_learn_basicStep (φ : CNF ℕ) :
    WellFounded fun S' S => Relation.ReflTransGen (Step φ.vars) (.run [] φ) S ∧
      ∃ S₁, Relation.ReflTransGen (Learn φ.vars) S S₁ ∧ BasicStep φ.vars S₁ S' := by
  refine Subrelation.wf (r := InvImage (· < ·) (rank φ.vars)) ?_ (InvImage.wf _ wellFounded_lt)
  rintro S' S ⟨hreach, S₁, hlearn, hstep⟩
  obtain ⟨hreach₁, hrank⟩ := reachable_rank_of_learn hreach hlearn
  have := hstep.rank_lt (inv_of_reachable hreach₁)
  simp only [InvImage]
  omega

end Cslib.Algorithms.Lean.CDCL
