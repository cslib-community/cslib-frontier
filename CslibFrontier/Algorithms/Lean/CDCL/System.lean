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
each marked as a decision or not (`Cslib.Algorithms.Lean.CDCL.Entry`). The rules are:

* the *Basic DPLL* rules (`Cslib.Algorithms.Lean.CDCL.BasicStep`, their Definition 2.4):
  * **UnitPropagate**: if a clause of `F` has every literal but `l` false and `l` is undefined,
    add `l`;
  * **Decide**: add an undefined literal over a variable occurring in `F` as a decision;
  * **Fail**: if a clause of `F` is false and `M` has no decision, go to `fail`;
  * **Backjump**: if a clause of `F` is false, `M = N ++ dᵈ :: M₀`, and a clause `C` entailed by
    `F` has every literal but `l` false in `M₀`, with `l` undefined in `M₀` and occurring in `F`
    or `M`, go to `l :: M₀`;
* **Learn** (`Cslib.Algorithms.Lean.CDCL.Learn`, their Definition 2.5): add a clause entailed by
  `F` whose variables occur in `F` or `M`;
* **Forget** (`Cslib.Algorithms.Lean.CDCL.Forget`, their Definition 2.5): remove a clause entailed
  by the rest of `F`.

**Entailment.** The source (§2.1) works with partial assignments: a set of literals is a model of a
clause set if it contains a literal of every clause, and `F` entails `C` if every such model of `F`
contains a literal of `C` (`Cslib.Algorithms.Lean.CDCL.PEntails`). Forget uses this entailment,
which the partial-model conclusion of Theorem 2.12 needs: entailment by total assignments would let
Forget remove the tautology `b ∨ ¬b` from `a, b ∨ ¬b`, ending at the trail `a`, which has no
literal of `b ∨ ¬b`. Backjump and Learn use entailment by total assignments. The §2.1 entailment
implies it (`Cslib.Algorithms.Lean.CDCL.PEntails.eval`), so every step of the source is a step
here, and the results below hold for at least the source's runs.

DPLL with learning (`Cslib.Algorithms.Lean.CDCL.Step`) is the union of the three. The invariant
`Cslib.Algorithms.Lean.CDCL.Inv` is their Lemma 2.7, over a list `V` of variables containing those
of the input formula `φ`: the database has the models of `φ`, its partial models are partial
models of `φ`, and it uses variables of `V`, the trail assigns each variable of `V` at most once,
and every implied literal holds in every model of `φ` satisfying the older literals; in `fail`, `φ`
is unsatisfiable. Every step keeps it
(`Cslib.Algorithms.Lean.CDCL.Step.inv`). Their results then hold, from the initial state with the
empty trail and `F = φ`, taking `V` to be the variables of `φ`:

* **Lemma 2.8**: in a state with a false clause, Fail applies if there is no decision, and
  otherwise Backjump applies (`Cslib.Algorithms.Lean.CDCL.RunInv.fail_or_backjump`).
* **Theorem 2.10**: there is no infinite run of Basic DPLL steps
  (`Cslib.Algorithms.Lean.CDCL.wellFounded_basicStep`). With `N` variables, a literal at level `k`
  weighs `(N + 1) ^ (N - k)`, and every step increases the weight of the trail, which is at most
  `N * (N + 1) ^ N` (`Cslib.Algorithms.Lean.CDCL.Trail.measure`); this replaces their
  lexicographic order on the numbers of literals per level with a single number.
* **Theorem 2.11**: every run of DPLL with learning without an infinite stretch of Learn and Forget
  steps is finite, stated as the well-foundedness of "Learn and Forget steps, then a Basic DPLL
  step" (`Cslib.Algorithms.Lean.CDCL.wellFounded_learnOrForget_basicStep`).
* **Theorem 2.12**: a reachable state that is final for Basic DPLL is `fail` exactly when `φ` is
  unsatisfiable, and otherwise its trail is a model of `φ` in the sense of §2.1, containing a
  literal of every clause (`Cslib.Algorithms.Lean.CDCL.final_of_reachable`). The invariant keeps
  every partial model of the database a partial model of `φ`, and Forget's side condition is what
  preserves this.

**Representations.** Clause sets are lists, so Learn prepends a clause and Forget removes one
occurrence. The trail is kept newest first. Locators refer to the authors' manuscript, printed
pp. 5–16.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.BasicStep`, `Cslib.Algorithms.Lean.CDCL.Learn`,
  `Cslib.Algorithms.Lean.CDCL.Forget`, `Cslib.Algorithms.Lean.CDCL.Step`: the transition systems.
* `Cslib.Algorithms.Lean.CDCL.Inv`: the invariant.

## Main results

* `Cslib.Algorithms.Lean.CDCL.Step.inv`: steps keep the invariant (Lemma 2.7).
* `Cslib.Algorithms.Lean.CDCL.RunInv.fail_or_backjump`: Fail or Backjump applies (Lemma 2.8).
* `Cslib.Algorithms.Lean.CDCL.wellFounded_basicStep`,
  `Cslib.Algorithms.Lean.CDCL.wellFounded_learnOrForget_basicStep`: termination (Theorems 2.10,
  2.11).
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

/-- A partial assignment satisfies a clause if it makes one of its literals true
[NieuwenhuisOliverasTinelli2006, §2.1]: the variable of the literal is assigned, with its
polarity. -/
def PSat (ρ : ℕ → Option Bool) (c : Clause ℕ) : Prop := ∃ l ∈ c, ρ l.1 = some l.2

/-- A partial assignment is a model of a clause set if it satisfies every clause. -/
def PModels (ρ : ℕ → Option Bool) (F : CNF ℕ) : Prop := ∀ c ∈ F, PSat ρ c

/-- **Entailment** [NieuwenhuisOliverasTinelli2006, §2.1]: every partial model of `F` satisfies
`C`. It implies entailment by total assignments (`Cslib.Algorithms.Lean.CDCL.PEntails.eval`), but
not conversely: the tautology `b ∨ ¬b` holds under every total assignment, while the partial
model `{a}` of the clause `a` does not satisfy it. -/
def PEntails (F : CNF ℕ) (C : Clause ℕ) : Prop := ∀ ρ, PModels ρ F → PSat ρ C

/-- Entailment by partial assignments implies entailment by total ones. -/
theorem PEntails.eval {F : CNF ℕ} {C : Clause ℕ} (h : PEntails F C) (σ : ℕ → Bool)
    (hσ : F.eval σ = true) : C.eval σ = true := by
  obtain ⟨l, hl, hlσ⟩ := h (fun x => some (σ x)) fun c hc => by
    obtain ⟨l, hl, hlσ⟩ := (Clause.eval_eq_true_iff σ c).1 ((CNF.eval_eq_true_iff σ F).1 hσ c hc)
    exact ⟨l, hl, by simp [hlσ]⟩
  exact (Clause.eval_eq_true_iff σ C).2 ⟨l, hl, by simpa using hlσ⟩

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

/-- The partial assignment of a trail: a variable is true or false if the trail makes it so, and
unassigned otherwise. -/
def partialAssignment (M : Trail) (x : ℕ) : Option Bool :=
  if (x, true) ∈ lits M then some true else if (x, false) ∈ lits M then some false else none

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

/-- **The Basic DPLL rules** [NieuwenhuisOliverasTinelli2006, Definition 2.4]. -/
inductive BasicStep : State → State → Prop
  /-- UnitPropagate: a clause with every literal but `l` false makes `l` implied. -/
  | unitPropagate {M : Trail} {F : CNF ℕ} {c : Clause ℕ} {l : Literal ℕ} (hc : c ∈ F) (hl : l ∈ c)
      (hfalse : ∀ l' ∈ c, l' ≠ l → l'.negate ∈ Trail.lits M) (hundef : l.1 ∉ Trail.vars M) :
      BasicStep (.run M F) (.run (⟨l, false⟩ :: M) F)
  /-- Decide: an undefined literal over a variable occurring in the database becomes a
  decision. -/
  | decide {M : Trail} {F : CNF ℕ} {l : Literal ℕ} (hundef : l.1 ∉ Trail.vars M)
      (hv : l.1 ∈ F.vars) : BasicStep (.run M F) (.run (⟨l, true⟩ :: M) F)
  /-- Fail: a false clause and no decision. -/
  | fail {M : Trail} {F : CNF ℕ} {c : Clause ℕ} (hc : c ∈ F) (hconf : Trail.Falsifies M c)
      (hnodec : ∀ e ∈ M, e.decision = false) : BasicStep (.run M F) .fail
  /-- Backjump: going back below a decision and adding the literal that an entailed clause `C`
  implies there. -/
  | backjump {N M₀ : Trail} {F : CNF ℕ} {d : Literal ℕ} {c C : Clause ℕ} {l : Literal ℕ}
      (hc : c ∈ F) (hconf : Trail.Falsifies (N ++ ⟨d, true⟩ :: M₀) c)
      (hC : ∀ σ, F.eval σ = true → C.eval σ = true) (hl : l ∈ C)
      (hfalse : ∀ l' ∈ C, l' ≠ l → l'.negate ∈ Trail.lits M₀) (hundef : l.1 ∉ Trail.vars M₀)
      (hocc : l.1 ∈ F.vars ∨ l.1 ∈ Trail.vars (N ++ ⟨d, true⟩ :: M₀)) :
      BasicStep (.run (N ++ ⟨d, true⟩ :: M₀) F) (.run (⟨l, false⟩ :: M₀) F)

/-- **Learn** [NieuwenhuisOliverasTinelli2006, Definition 2.5]: adding a clause entailed by the
database, whose variables occur in the database or the trail. -/
inductive Learn : State → State → Prop
  | learn {M : Trail} {F : CNF ℕ} {C : Clause ℕ} (hC : ∀ σ, F.eval σ = true → C.eval σ = true)
      (hCV : ∀ l ∈ C, l.1 ∈ F.vars ∨ l.1 ∈ Trail.vars M) : Learn (.run M F) (.run M (C :: F))

/-- **Forget** [NieuwenhuisOliverasTinelli2006, Definition 2.5]: removing a clause entailed by the
rest of the database, in the sense of §2.1 (`Cslib.Algorithms.Lean.CDCL.PEntails`). -/
inductive Forget : State → State → Prop
  | forget {M : Trail} {F₁ F₂ : CNF ℕ} {C : Clause ℕ} (hC : PEntails (F₁ ++ F₂) C) :
      Forget (.run M (F₁ ++ C :: F₂)) (.run M (F₁ ++ F₂))

/-- **DPLL with learning** [NieuwenhuisOliverasTinelli2006, Definition 2.5]: a Basic DPLL step, a
Learn step or a Forget step. -/
def Step (S S' : State) : Prop := BasicStep S S' ∨ Learn S S' ∨ Forget S S'

/-- The invariant of a running state [NieuwenhuisOliverasTinelli2006, Lemma 2.7]. -/
structure RunInv (φ : CNF ℕ) (V : List ℕ) (M : Trail) (F : CNF ℕ) : Prop where
  /-- The database has the models of `φ`. -/
  models : ∀ σ, F.eval σ = φ.eval σ
  /-- Every partial model of the database is a partial model of `φ`. -/
  pmodels : ∀ ρ, PModels ρ F → PModels ρ φ
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
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact hdec _ List.mem_cons_self
    · exact ih (fun l hl => hdec l (List.mem_cons_of_mem _ hl)) l' hl'
  | implied l _ himp ih =>
    have hM := ih fun l hl => hdec l (List.mem_cons_of_mem _ hl)
    intro l' hl'
    rcases List.mem_cons.1 hl' with rfl | hl'
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
  ⟨fun _ => rfl, fun _ h => h, by simp [Trail.vars], by simp [Trail.vars], hV, .nil⟩

/-! ### Steps keep the invariant -/

/-- Adding a literal over an unassigned variable of `V` keeps the trail's variables distinct and
in `V`. -/
theorem RunInv.push {φ : CNF ℕ} {V : List ℕ} {M : Trail} {F : CNF ℕ} (h : RunInv φ V M F)
    {l : Literal ℕ} (b : Bool) (hundef : l.1 ∉ Trail.vars M) (hv : l.1 ∈ V) :
    (Trail.vars (⟨l, b⟩ :: M)).Nodup ∧ ∀ x ∈ Trail.vars (⟨l, b⟩ :: M), x ∈ V := by
  refine ⟨List.nodup_cons.2 ⟨hundef, h.nodup⟩, fun x hx => ?_⟩
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hv
  · exact h.subset x hx

/-- A variable occurring in the database or on the trail lies in `V`. -/
private theorem RunInv.mem_of_occurs {φ : CNF ℕ} {V : List ℕ} {M : Trail} {F : CNF ℕ}
    (h : RunInv φ V M F) {x : ℕ} (hx : x ∈ F.vars ∨ x ∈ Trail.vars M) : x ∈ V := by
  rcases hx with hx | hx
  · obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.1 hx
    exact h.db_vars c hc (_, b) hb
  · exact h.subset _ hx

/-- **Steps keep the invariant** [NieuwenhuisOliverasTinelli2006, Lemma 2.7]. -/
theorem Step.inv {φ : CNF ℕ} {V : List ℕ} {S S' : State} (hstep : Step S S') (h : Inv φ V S) :
    Inv φ V S' := by
  rcases hstep with hstep | hstep | hstep
  · cases hstep with
    | @unitPropagate M F c l hc hl hfalse hundef =>
      obtain ⟨hnd, hsub⟩ := RunInv.push h false hundef (h.db_vars c hc l hl)
      exact ⟨h.models, h.pmodels, hnd, hsub, h.db_vars, .implied l h.entailed fun σ hσ hM =>
        Trail.eval_of_forall_ne ((CNF.eval_eq_true_iff σ F).1 (h.models σ ▸ hσ) c hc) hM hfalse⟩
    | @decide M F l hundef hv =>
      obtain ⟨hnd, hsub⟩ := RunInv.push h true hundef (h.mem_of_occurs (.inl hv))
      exact ⟨h.models, h.pmodels, hnd, hsub, h.db_vars, .decision l h.entailed⟩
    | @fail M F c hc hconf hnodec =>
      rintro ⟨σ, hσ⟩
      have hM := Trail.sat_of_entailed h.entailed hσ fun l hl => by simpa using hnodec _ hl
      obtain ⟨l, hl, hlσ⟩ := (Clause.eval_eq_true_iff σ c).1
        ((CNF.eval_eq_true_iff σ F).1 (h.models σ ▸ hσ) c hc)
      have := hM _ (hconf l hl)
      rw [Literal.eval_negate] at this
      simp [Literal.eval, hlσ] at this
    | @backjump N M₀ F d c C l hc hconf hC hl hfalse hundef hocc =>
      have hnodup : (Trail.vars M₀).Nodup := by
        have := h.nodup
        simp only [Trail.vars, List.map_append, List.map_cons] at this
        exact (List.nodup_cons.1 (List.nodup_append.1 this).2.1).2
      refine ⟨h.models, h.pmodels, List.nodup_cons.2 ⟨hundef, hnodup⟩, fun x hx => ?_,
        h.db_vars, .implied l (Trail.entailed_append (N := N ++ [⟨d, true⟩])
          (by simpa using h.entailed)) fun σ hσ hM =>
          Trail.eval_of_forall_ne (hC σ (h.models σ ▸ hσ)) hM hfalse⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.mem_of_occurs hocc
      · exact h.subset x (by simp [Trail.vars] at hx ⊢; tauto)
  · cases hstep with
    | @learn M F C hC hCV =>
      refine ⟨fun σ => ?_, fun ρ hρ => h.pmodels ρ fun c hc => hρ c (List.mem_cons_of_mem _ hc),
        h.nodup, h.subset, fun c hc l hl => (List.mem_cons.1 hc).elim
          (fun hEq => h.mem_of_occurs (hCV l (hEq ▸ hl))) (h.db_vars c · l hl), h.entailed⟩
      rw [CNF.eval_cons, ← h.models]
      cases hF : CNF.eval σ F <;> simp [hC σ, hF]
  · cases hstep with
    | @forget M F₁ F₂ C hC =>
      refine ⟨fun σ => ?_, fun ρ hρ => h.pmodels ρ fun c hc => ?_, h.nodup, h.subset,
        fun c hc => h.db_vars c (by simp at hc ⊢; tauto), h.entailed⟩
      · rw [← h.models]
        have := hC.eval σ
        simp only [CNF.eval_append, CNF.eval_cons, Bool.and_eq_true] at this ⊢
        cases h₁ : CNF.eval σ F₁ <;> cases h₂ : CNF.eval σ F₂ <;> simp_all
      · rcases (by simpa using hc : c ∈ F₁ ∨ c = C ∨ c ∈ F₂) with hc | rfl | hc
        · exact hρ c (List.mem_append_left _ hc)
        · exact hC ρ hρ
        · exact hρ c (List.mem_append_right _ hc)

/-! ### Final states -/

/-- With each variable assigned once, the partial assignment of a trail makes a literal true
exactly when the literal is on the trail. -/
theorem Trail.partialAssignment_eq_some_iff {M : Trail} (hM : (Trail.vars M).Nodup)
    (l : Literal ℕ) : Trail.partialAssignment M l.1 = some l.2 ↔ l ∈ Trail.lits M := by
  obtain ⟨v, b⟩ := l
  cases b
  · have := fun h : (v, false) ∈ Trail.lits M => Trail.negate_not_mem hM h
    by_cases ht : (v, true) ∈ Trail.lits M <;> by_cases hf : (v, false) ∈ Trail.lits M <;>
      simp_all [Trail.partialAssignment, Std.Sat.Literal.negate]
  · by_cases ht : (v, true) ∈ Trail.lits M <;> simp [Trail.partialAssignment, ht]

/-- A trail that falsifies no clause of `F` and assigns every variable of `F` has a literal of
every clause of `F`. -/
theorem Trail.exists_mem_lits {M : Trail} {F : CNF ℕ} (hnoconf : ∀ c ∈ F, ¬ Trail.Falsifies M c)
    (htotal : ∀ x ∈ F.vars, x ∈ Trail.vars M) : ∀ c ∈ F, ∃ l ∈ c, l ∈ Trail.lits M := by
  intro c hc
  obtain ⟨l, hl, hopen⟩ : ∃ l ∈ c, l.negate ∉ Trail.lits M := by
    by_contra! hne
    exact hnoconf c hc hne
  -- `l` is assigned, and not falsely, so the trail contains it
  obtain ⟨e, hmem, hl'⟩ := List.mem_map.1 (htotal l.1 (CNF.mem_vars.2 ⟨c, hc, l.2, hl⟩))
  have helits : e.lit ∈ Trail.lits M := List.mem_map.2 ⟨e, hmem, rfl⟩
  have hel : e.lit = l := by
    obtain ⟨⟨v', s'⟩, b⟩ := e
    obtain ⟨v, s⟩ := l
    simp only [Entry.var] at hl'
    subst hl'
    cases s <;> cases s' <;> simp_all [Std.Sat.Literal.negate]
  exact ⟨l, hl, hel ▸ helits⟩

/-- **The trail is a model** [NieuwenhuisOliverasTinelli2006, §2.1]: in a running state with no
false clause that assigns every variable, every clause of `φ` has a literal on the trail. -/
theorem RunInv.trail_model {φ : CNF ℕ} {V : List ℕ} {M : Trail} {F : CNF ℕ} (h : RunInv φ V M F)
    (hnoconf : ∀ c ∈ F, ¬ Trail.Falsifies M c) (htotal : ∀ x ∈ F.vars, x ∈ Trail.vars M) :
    ∀ c ∈ φ, ∃ l ∈ c, l ∈ Trail.lits M := by
  intro c hc
  obtain ⟨l, hl, hlM⟩ := h.pmodels (Trail.partialAssignment M) (fun c hc => by
    obtain ⟨l, hl, hlM⟩ := Trail.exists_mem_lits hnoconf htotal c hc
    exact ⟨l, hl, (Trail.partialAssignment_eq_some_iff h.nodup l).2 hlM⟩) c hc
  exact ⟨l, hl, (Trail.partialAssignment_eq_some_iff h.nodup l).1 hlM⟩

/-- A running state with no false clause that assigns every variable gives a total model: the
assignment making the trail's literals true. -/
theorem RunInv.eval_model {φ : CNF ℕ} {V : List ℕ} {M : Trail} {F : CNF ℕ} (h : RunInv φ V M F)
    (hnoconf : ∀ c ∈ F, ¬ Trail.Falsifies M c) (htotal : ∀ x ∈ F.vars, x ∈ Trail.vars M) :
    φ.eval (Trail.assignment M) = true := by
  rw [CNF.eval_eq_true_iff]
  intro c hc
  obtain ⟨l, hl, hlM⟩ := h.trail_model hnoconf htotal c hc
  refine (Clause.eval_eq_true_iff _ c).2 ⟨l, hl, ?_⟩
  obtain ⟨v, s⟩ := l
  have := Trail.negate_not_mem h.nodup hlM
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

/-- Backjump with the negation of the decisions: below the newest decision `d`, a false clause
lets Backjump add the negation of `d`. -/
theorem RunInv.backjump_decisions {φ : CNF ℕ} {V : List ℕ} {N M₀ : Trail} {F : CNF ℕ}
    {d : Literal ℕ} (h : RunInv φ V (N ++ ⟨d, true⟩ :: M₀) F)
    (hN : ∀ e ∈ N, e.decision = false) {c : Clause ℕ} (hc : c ∈ F)
    (hcM : Trail.Falsifies (N ++ ⟨d, true⟩ :: M₀) c) :
    BasicStep (.run (N ++ ⟨d, true⟩ :: M₀) F) (.run (⟨d.negate, false⟩ :: M₀) F) := by
  have hnodup := h.nodup
  simp only [Trail.vars, List.map_append, List.map_cons] at hnodup
  obtain ⟨-, hdM₀, -⟩ := List.nodup_append.1 hnodup
  refine BasicStep.backjump (C := d.negate :: Trail.decisionClause M₀) (l := d.negate)
    hc hcM ?_ List.mem_cons_self ?_ ?_ (.inr (by simp [Trail.vars, Std.Sat.Literal.negate]))
  · -- the decisions cannot all hold in a model
    intro σ hFσ
    by_contra hfalse
    simp only [Bool.not_eq_true, Clause.eval, List.any_eq_false, List.mem_cons,
      forall_eq_or_imp] at hfalse
    have hsat := Trail.sat_of_entailed h.entailed (h.models σ ▸ hFσ) (σ := σ) fun l hl => by
      rcases (by simpa using hl : _ ∨ _ = _ ∨ _) with hl | ⟨rfl, -⟩ | hl
      · exact absurd (hN _ hl) (by simp)
      · simpa [Literal.eval_negate] using hfalse.1
      · simpa [Literal.eval_negate] using
          hfalse.2 _ (List.mem_map.2 ⟨⟨l, true⟩, List.mem_filter.2 ⟨hl, rfl⟩, rfl⟩)
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

/-- **Fail or Backjump applies** [NieuwenhuisOliverasTinelli2006, Lemma 2.8]: in a running state
with a false clause, Fail applies if the trail has no decision, and otherwise Backjump applies,
going below the newest decision `d` and adding its negation. -/
theorem RunInv.fail_or_backjump {φ : CNF ℕ} {V : List ℕ} {M : Trail} {F : CNF ℕ}
    (h : RunInv φ V M F) {c : Clause ℕ} (hc : c ∈ F) (hcM : Trail.Falsifies M c) :
    BasicStep (.run M F) .fail ∨ ∃ N d M₀, M = N ++ ⟨d, true⟩ :: M₀ ∧
      BasicStep (.run M F) (.run (⟨d.negate, false⟩ :: M₀) F) := by
  by_cases hdec : ∃ e ∈ M, e.decision = true
  · obtain ⟨N, d, M₀, rfl, hN⟩ := Trail.exists_split hdec
    exact .inr ⟨N, d, M₀, rfl, h.backjump_decisions hN hc hcM⟩
  · push Not at hdec
    exact .inl (BasicStep.fail hc hcM fun e he => by simpa using hdec e he)

/-- **Progress**: a running state from which no Basic DPLL step applies has no false clause and
assigns every variable occurring in the database (the first two parts of
[NieuwenhuisOliverasTinelli2006, Lemma 2.9]): otherwise Fail or Backjump applies by
`Cslib.Algorithms.Lean.CDCL.RunInv.fail_or_backjump`, or Decide applies. -/
theorem RunInv.exists_basicStep {φ : CNF ℕ} {V : List ℕ} {M : Trail} {F : CNF ℕ}
    (h : RunInv φ V M F)
    (hfinal : ¬ ((∀ c ∈ F, ¬ Trail.Falsifies M c) ∧ ∀ x ∈ F.vars, x ∈ Trail.vars M)) :
    ∃ S', BasicStep (.run M F) S' := by
  by_cases hconf : ∃ c ∈ F, Trail.Falsifies M c
  · obtain ⟨c, hc, hcM⟩ := hconf
    rcases h.fail_or_backjump hc hcM with hfail | ⟨N, d, M₀, -, hbj⟩
    · exact ⟨_, hfail⟩
    · exact ⟨_, hbj⟩
  · push Not at hconf
    obtain ⟨x, hx, hxM⟩ : ∃ x ∈ F.vars, x ∉ Trail.vars M := by
      by_contra! hne
      exact hfinal ⟨hconf, hne⟩
    exact ⟨_, BasicStep.decide (l := (x, true)) hxM hx⟩

/-- A state that satisfies the invariant and is final for Basic DPLL is `fail` exactly when `φ` is
unsatisfiable, and otherwise its trail is a model of `φ`: every clause of `φ` has a literal on the
trail, so the total assignment making the trail's literals true is a model too. -/
theorem Inv.final {φ : CNF ℕ} {V : List ℕ} {S : State} (h : Inv φ V S)
    (hfinal : ∀ S', ¬ BasicStep S S') :
    (S = .fail ↔ ¬ φ.Satisfiable) ∧ ∀ M F, S = .run M F →
      (∀ c ∈ φ, ∃ l ∈ c, l ∈ Trail.lits M) ∧ φ.eval (Trail.assignment M) = true := by
  cases S with
  | fail => exact ⟨⟨fun _ => h, fun _ => rfl⟩, fun _ _ h => absurd h (by simp)⟩
  | run M F =>
    have hdone : (∀ c ∈ F, ¬ Trail.Falsifies M c) ∧ ∀ x ∈ F.vars, x ∈ Trail.vars M := by
      by_contra hne
      obtain ⟨S', hS'⟩ := RunInv.exists_basicStep h hne
      exact hfinal S' hS'
    have hmodel := h.eval_model hdone.1 hdone.2
    refine ⟨⟨fun hS => absurd hS (by simp), fun hns => absurd ⟨_, hmodel⟩ hns⟩, ?_⟩
    rintro M' F' hS
    cases hS
    exact ⟨h.trail_model hdone.1 hdone.2, hmodel⟩

/-- The states reachable from the initial state satisfy the invariant. -/
theorem inv_of_reachable {φ : CNF ℕ} {S : State}
    (h : Relation.ReflTransGen Step (.run [] φ) S) : Inv φ φ.vars S := by
  induction h with
  | refl => exact Inv.init fun c hc l hl => CNF.mem_vars.2 ⟨c, hc, l.2, hl⟩
  | tail _ hstep ih => exact hstep.inv ih

/-- **Final states decide satisfiability** [NieuwenhuisOliverasTinelli2006, Theorem 2.12]: a state
reachable from the initial state by DPLL with learning and final for Basic DPLL is `fail` exactly
when `φ` is unsatisfiable, and otherwise its trail is a model of `φ` in the sense of §2.1: every
clause of `φ` has a literal on the trail. The total assignment making the trail's literals true is
then a model as well. -/
theorem final_of_reachable {φ : CNF ℕ} {S : State}
    (h : Relation.ReflTransGen Step (.run [] φ) S)
    (hfinal : ∀ S', ¬ BasicStep S S') :
    (S = .fail ↔ ¬ φ.Satisfiable) ∧ ∀ M F, S = .run M F →
      (∀ c ∈ φ, ∃ l ∈ c, l ∈ Trail.lits M) ∧ φ.eval (Trail.assignment M) = true :=
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
theorem BasicStep.rank_lt {φ : CNF ℕ} {V : List ℕ} {S S' : State} (hstep : BasicStep S S')
    (h : Inv φ V S) : rank V S' < rank V S := by
  have h' := Step.inv (.inl hstep) h
  cases hstep with
  | fail =>
    have := RunInv.measure_le (show RunInv _ _ _ _ from h)
    simp only [rank]; omega
  | @unitPropagate M F c l _ _ _ _ =>
    have := RunInv.measure_le (show RunInv _ _ _ _ from h')
    have := Trail.measure_lt_cons V.dedup.length ⟨l, false⟩ M
    simp only [rank]; omega
  | @decide M F l _ _ =>
    have := RunInv.measure_le (show RunInv _ _ _ _ from h')
    have := Trail.measure_lt_cons V.dedup.length ⟨l, true⟩ M
    simp only [rank]; omega
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
    have hpow : (n + 1) ^ (n - Trail.level M₀) =
        (n + 1) * (n + 1) ^ (n - (Trail.level M₀ + 1)) := by
      rw [← pow_succ']
      exact congrArg ((n + 1) ^ ·) (by omega)
    have : (N.length + 1) * (n + 1) ^ (n - (Trail.level M₀ + 1)) <
        (n + 1) * (n + 1) ^ (n - (Trail.level M₀ + 1)) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega))
    have hlt : Trail.measure n (N ++ ⟨d, true⟩ :: M₀) <
        Trail.measure n M₀ + (n + 1) ^ (n - Trail.level M₀) := by
      nlinarith
    simp only [rank, ← hn, Trail.measure, Bool.false_eq_true, ite_false, Nat.add_zero]
    omega

/-- **Termination of Basic DPLL** [NieuwenhuisOliverasTinelli2006, Theorem 2.10]: there is no
infinite run of Basic DPLL steps from the initial state. -/
theorem wellFounded_basicStep (φ : CNF ℕ) :
    WellFounded fun S' S =>
      Relation.ReflTransGen Step (.run [] φ) S ∧ BasicStep S S' :=
  Subrelation.wf (r := InvImage (· < ·) (rank φ.vars))
    (fun ⟨hreach, hstep⟩ => hstep.rank_lt (inv_of_reachable hreach)) (InvImage.wf _ wellFounded_lt)

/-- A Learn or Forget step. -/
def LearnOrForget (S S' : State) : Prop := Learn S S' ∨ Forget S S'

/-- Learn and Forget steps keep the trail, hence the rank. -/
theorem LearnOrForget.rank_eq {V : List ℕ} {S S' : State} (h : LearnOrForget S S') :
    rank V S' = rank V S := by
  rcases h with h | h <;> cases h <;> rfl

/-- Learn and Forget steps from a reachable state reach states of the same rank. -/
theorem reachable_rank_of_learnOrForget {φ : CNF ℕ} {S S₁ : State}
    (hreach : Relation.ReflTransGen Step (.run [] φ) S)
    (hl : Relation.ReflTransGen LearnOrForget S S₁) :
    Relation.ReflTransGen Step (.run [] φ) S₁ ∧ rank φ.vars S₁ = rank φ.vars S := by
  induction hl with
  | refl => exact ⟨hreach, rfl⟩
  | tail _ hl ih =>
    exact ⟨ih.1.tail (hl.elim (fun h => .inr (.inl h)) fun h => .inr (.inr h)),
      hl.rank_eq.trans ih.2⟩

/-- **Termination of DPLL with learning** [NieuwenhuisOliverasTinelli2006, Theorem 2.11]: a run
from the initial state in which no stretch of Learn and Forget steps is infinite is finite. It is
stated as: there is no infinite sequence of moves from the initial state, each a finite run of
Learn and Forget steps followed by a Basic DPLL step. -/
theorem wellFounded_learnOrForget_basicStep (φ : CNF ℕ) :
    WellFounded fun S' S => Relation.ReflTransGen Step (.run [] φ) S ∧
      ∃ S₁, Relation.ReflTransGen LearnOrForget S S₁ ∧ BasicStep S₁ S' := by
  refine Subrelation.wf (r := InvImage (· < ·) (rank φ.vars)) ?_ (InvImage.wf _ wellFounded_lt)
  rintro S' S ⟨hreach, S₁, hlearn, hstep⟩
  obtain ⟨hreach₁, hrank⟩ := reachable_rank_of_learnOrForget hreach hlearn
  have := hstep.rank_lt (inv_of_reachable hreach₁)
  simp only [InvImage]
  omega

end Cslib.Algorithms.Lean.CDCL
