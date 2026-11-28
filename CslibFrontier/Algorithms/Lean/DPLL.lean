/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Resolution.LRAT
public import CslibFrontier.Logics.Propositional.CNF.LRATRat
public import CslibFrontier.Logics.Propositional.CNF.UnitPropagation
public import CslibFrontier.Foundations.Data.List.EraseDups

/-! # A DPLL solver with LRAT certificates

The procedure of Davis, Logemann and Loveland [DavisLogemannLoveland1962, pp. 394–395] decides
satisfiability of a formula in conjunctive normal form by splitting on variables and propagating
unit clauses. This is a variant: it keeps the splitting and the unit rule, but not the pure-literal
rule, and it does not rewrite the formula as the search assigns variables. Here a partial assignment
is a list `π` of literals assumed true, and the search (`Cslib.Algorithms.Lean.DPLL.search`) returns
one of two outcomes (`Cslib.Algorithms.Lean.DPLL.Outcome`):

* a model of the formula, with a proof that it is one; or
* a tree-like resolution derivation (`Cslib.Logic.PL.CNF.Derivation`) of a clause that `π`
  falsifies.

If `π` falsifies a clause of the formula, that clause is the derivation. If `π` satisfies every
clause, it gives the model. Otherwise the search branches on a variable that `π` leaves open: the
variable of a *unit* clause, one with a single literal not falsified by `π`, trying that literal
first, or else the next open variable, trying `true` first. Trying the literal of a unit clause
first is unit propagation, since the other branch falsifies the unit clause at once. The search
keeps the open variables in a list without repetitions (`Cslib.Algorithms.Lean.DPLL.OpenVars`), so
it never branches on a variable already assigned (`Cslib.Algorithms.Lean.DPLL.OpenVars.fresh`). When
both branches return derivations and both clauses contain the branch variable, their resolvent on it
is falsified by `π`; when one does not, that clause is already falsified by `π`. Recursion is
structural on a bound on the number of open variables, which provably never runs out, so the search
always ends with an outcome; there is no `partial`. The kernel can run it, so `decide` evaluates the
solver on small formulas.

From the empty partial assignment, a derivation is a refutation, which compiles to an LRAT
certificate (`Cslib.Logic.PL.CNF.Derivation.toLRAT`). `Cslib.Algorithms.Lean.DPLL.solve` returns a
model or a certificate. Models are models (`Cslib.Algorithms.Lean.DPLL.solve_sat`), certificates
are accepted by `Cslib.Logic.PL.CNF.checkLRAT` (`Cslib.Algorithms.Lean.DPLL.solve_unsat`), and so
the solver answers `sat` exactly on satisfiable formulas
(`Cslib.Algorithms.Lean.DPLL.isSat_solve_iff`). As a corollary, every unsatisfiable formula has a
certificate that the checker accepts (`Cslib.Algorithms.Lean.DPLL.exists_checkLRAT_iff`).

This solver learns no clauses: a certificate has one step per resolution of the search tree, which
can be exponentially longer than what clause learning needs.

## Main definitions

* `Cslib.Algorithms.Lean.DPLL.search`: the search from a partial assignment.
* `Cslib.Algorithms.Lean.DPLL.solve`: a model or an LRAT certificate.

## Main results

* `Cslib.Algorithms.Lean.DPLL.solve_sat`, `Cslib.Algorithms.Lean.DPLL.solve_unsat`: both answers
  are correct.
* `Cslib.Algorithms.Lean.DPLL.Result.isSat_iff`: an answer whose model satisfies the formula and
  whose certificate the LRAT checker accepts decides satisfiability.
* `Cslib.Algorithms.Lean.DPLL.isSat_solve_iff`: the solver decides satisfiability.
* `Cslib.Algorithms.Lean.DPLL.OpenVars.fresh`: the search branches only on unassigned variables.
* `Cslib.Algorithms.Lean.DPLL.exists_checkLRAT_iff`: the checker is complete.
* `Cslib.Algorithms.Lean.DPLL.exists_checkLRATRat_iff`: so is the checker with RAT steps.

## References

* [M. Davis, G. Logemann, D. Loveland, *A machine program for
  theorem-proving*][DavisLogemannLoveland1962]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.DPLL

open Cslib.Logic.PL Cslib.Logic.PL.CNF
open Std.Tactic.BVDecide (LRAT.IntAction)

/-! ### Partial assignments -/

/-- A partial assignment, as a list of literals assumed true, falsifies a clause if it contains the
negation of every literal of the clause. -/
def Falsifies (π : List (Literal ℕ)) (c : Clause ℕ) : Bool :=
  c.all fun l => π.contains l.negate

/-- A literal holds under a partial assignment if the assignment contains it and not its
negation. -/
def Holds (π : List (Literal ℕ)) (l : Literal ℕ) : Bool :=
  π.contains l && !π.contains l.negate

/-- The total assignment of a partial assignment: a variable is true if it is assumed true. -/
def assignment (π : List (Literal ℕ)) (x : ℕ) : Bool :=
  π.contains (x, true)

theorem falsifies_iff {π : List (Literal ℕ)} {c : Clause ℕ} :
    Falsifies π c = true ↔ ∀ l ∈ c, l.negate ∈ π := by
  simp [Falsifies]

/-- A literal that holds under a partial assignment holds under its total assignment. -/
theorem eval_assignment_of_holds {π : List (Literal ℕ)} {l : Literal ℕ}
    (h : Holds π l = true) : Literal.eval (assignment π) l = true := by
  obtain ⟨v, b⟩ := l
  simp only [Holds, Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at h
  cases b <;> simp_all [assignment, Literal.eval, Std.Sat.Literal.negate]

/-- If every clause has a literal that holds, the total assignment is a model. -/
theorem eval_assignment {φ : CNF ℕ} {π : List (Literal ℕ)}
    (h : φ.all (fun c => c.any (Holds π)) = true) : φ.eval (assignment π) = true := by
  rw [CNF.eval_eq_true_iff]
  intro c hc
  obtain ⟨l, hl, hhl⟩ := List.any_eq_true.1 (List.all_eq_true.1 h c hc)
  exact List.any_eq_true.2 ⟨l, hl, eval_assignment_of_holds hhl⟩

/-- If a partial assignment falsifies no clause and assigns every variable, every clause has a
literal that holds. -/
theorem all_any_holds {φ : CNF ℕ} {π : List (Literal ℕ)}
    (hnone : φ.find? (Falsifies π) = none)
    (hassigned : ∀ x ∈ φ.vars, (x, true) ∈ π ∨ (x, false) ∈ π) :
    φ.all (fun c => c.any (Holds π)) = true := by
  refine List.all_eq_true.2 fun c hc => ?_
  have hnf : Falsifies π c = false := by
    simpa using List.find?_eq_none.1 hnone c hc
  obtain ⟨l, hl, hopen⟩ : ∃ l ∈ c, l.negate ∉ π := by
    by_contra hne
    push Not at hne
    simp [falsifies_iff.2 hne] at hnf
  refine List.any_eq_true.2 ⟨l, hl, ?_⟩
  have hv := hassigned l.1 (CNF.mem_vars.2 ⟨c, hc, l.2, hl⟩)
  obtain ⟨v, b⟩ := l
  cases b <;> simp_all [Holds, Std.Sat.Literal.negate]

/-! ### The search -/

/-- The outcome of the search from a partial assignment `π`: a model, or a tree-like derivation
of a clause that `π` falsifies. -/
inductive Outcome (φ : CNF ℕ) (π : List (Literal ℕ)) : Type
  /-- A model of the formula. -/
  | sat (σ : ℕ → Bool) (h : φ.eval σ = true)
  /-- A derivation of a clause that `π` falsifies. -/
  | unsat (c : Clause ℕ) (d : φ.Derivation c) (h : ∀ l ∈ c, l.negate ∈ π)

/-- The literal of a clause that has exactly one literal not falsified by `π`, if that literal is
not already assumed. -/
def unitLiteral? (φ : CNF ℕ) (π : List (Literal ℕ)) : Option (Literal ℕ) :=
  φ.findSome? fun c =>
    match Clause.unit? (c.filter fun l => !π.contains l.negate) with
    | some l => if π.contains l then none else some l
    | none => none

/-- The literal to branch on: the literal of a unit clause if its variable is open, and otherwise
the first open variable, `true` first. -/
def branchLiteral (φ : CNF ℕ) (π : List (Literal ℕ)) (x : ℕ) (xs : List ℕ) :
    {l : Literal ℕ // l.1 ∈ x :: xs} :=
  match unitLiteral? φ π with
  | some l => if h : l.1 ∈ x :: xs then ⟨l, h⟩ else ⟨(x, true), List.mem_cons_self⟩
  | none => ⟨(x, true), List.mem_cons_self⟩

/-- Combining the outcomes of the two branches on `v`, both derivations: the resolvent of their
clauses on `v`, which `π` falsifies. -/
def resolveBranches {φ : CNF ℕ} {π : List (Literal ℕ)} (v : ℕ) :
    (b : Bool) → {c₁ c₂ : Clause ℕ} → φ.Derivation c₁ → (v, !b) ∈ c₁ →
      (∀ l ∈ c₁, l.negate ∈ (v, b) :: π) → φ.Derivation c₂ → (v, b) ∈ c₂ →
      (∀ l ∈ c₂, l.negate ∈ (v, !b) :: π) → Outcome φ π
  | true, c₁, c₂, d₁, hc₁, h₁, d₂, hc₂, h₂ =>
    .unsat (c₂.resolvent c₁ v) (.resolvent v d₂ d₁ hc₂ hc₁) fun l hl => by
      rcases Clause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact Literal.negate_mem_of_mem_cons (h₂ l hl) hne
      · exact Literal.negate_mem_of_mem_cons (h₁ l hl) hne
  | false, c₁, c₂, d₁, hc₁, h₁, d₂, hc₂, h₂ =>
    .unsat (c₁.resolvent c₂ v) (.resolvent v d₁ d₂ hc₁ hc₂) fun l hl => by
      rcases Clause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact Literal.negate_mem_of_mem_cons (h₁ l hl) hne
      · exact Literal.negate_mem_of_mem_cons (h₂ l hl) hne

/-- The open variables of a partial assignment: a list without repetitions of variables that `π`
does not assign, containing every variable of the formula that `π` does not assign. -/
structure OpenVars (φ : CNF ℕ) (π : List (Literal ℕ)) (vs : List ℕ) : Prop where
  /-- Every variable of the formula is open or assigned. -/
  covers : ∀ x ∈ φ.vars, x ∈ vs ∨ (x, true) ∈ π ∨ (x, false) ∈ π
  /-- No open variable is assigned. -/
  unassigned : ∀ x ∈ vs, (x, true) ∉ π ∧ (x, false) ∉ π
  /-- No open variable is listed twice. -/
  nodup : vs.Nodup

/-- Assigning an open variable removes it from the open variables. -/
theorem OpenVars.erase {φ : CNF ℕ} {π : List (Literal ℕ)} {vs : List ℕ}
    (h : OpenVars φ π vs) (v : ℕ) (b : Bool) : OpenVars φ ((v, b) :: π) (vs.erase v) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, h.nodup.erase v⟩
  · by_cases hxv : x = v
    · subst hxv
      cases b <;> simp
    · rcases h.covers x hx with h | h
      · exact .inl ((List.mem_erase_of_ne hxv).2 h)
      · simp_all
  · obtain ⟨hxv, hx⟩ := (h.nodup.mem_erase_iff).1 hx
    simpa [hxv] using h.unassigned x hx

/-- **The variable the search branches on is not yet assigned.** -/
theorem OpenVars.fresh {φ : CNF ℕ} {π : List (Literal ℕ)} {x : ℕ} {xs : List ℕ}
    (h : OpenVars φ π (x :: xs)) {v : ℕ} {b : Bool} (hl : (branchLiteral φ π x xs).val = (v, b)) :
    (v, true) ∉ π ∧ (v, false) ∉ π := by
  have := (branchLiteral φ π x xs).2
  rw [hl] at this
  exact h.unassigned v this

/-- **The DPLL search** from the partial assignment `π`, with the open variables `vs` and at most
`fuel` of them. -/
def search (φ : CNF ℕ) : (fuel : ℕ) → (π : List (Literal ℕ)) → (vs : List ℕ) →
    OpenVars φ π vs → vs.length ≤ fuel → Outcome φ π
  | fuel, π, vs, hvs, hfuel =>
    match hfind : φ.find? (Falsifies π) with
    | some c => .unsat c (.mem (List.mem_of_find?_eq_some hfind))
        (falsifies_iff.1 (List.find?_some hfind))
    | none =>
      if hsat : φ.all (fun c => c.any (Holds π)) = true then
        .sat (assignment π) (eval_assignment hsat)
      else
        match vs, fuel, hvs, hfuel with
        | [], _, hvs, _ => absurd (all_any_holds hfind fun x hx => (hvs.covers x hx).resolve_left
            List.not_mem_nil) hsat
        | _ :: _, 0, _, hfuel => absurd hfuel (by simp)
        | x :: xs, fuel + 1, hvs, hfuel =>
          match branchLiteral φ π x xs with
          | ⟨(v, b), hv⟩ =>
            have hlen : ((x :: xs).erase v).length ≤ fuel := by
              rw [List.length_erase_of_mem hv]
              simp only [List.length_cons] at hfuel ⊢
              omega
            match search φ fuel ((v, b) :: π) ((x :: xs).erase v) (hvs.erase v b) hlen with
            | .sat σ h => .sat σ h
            | .unsat c₁ d₁ h₁ =>
              if hc₁ : (v, !b) ∈ c₁ then
                match search φ fuel ((v, !b) :: π) ((x :: xs).erase v) (hvs.erase v !b) hlen with
                | .sat σ h => .sat σ h
                | .unsat c₂ d₂ h₂ =>
                  if hc₂ : (v, b) ∈ c₂ then
                    resolveBranches v b d₁ hc₁ h₁ d₂ hc₂ (by simpa using h₂)
                  else .unsat c₂ d₂ fun l hl =>
                    Literal.negate_mem_of_mem_cons (h₂ l hl)
                      (by rintro rfl; exact hc₂ (by simpa using hl))
              else .unsat c₁ d₁ fun l hl =>
                Literal.negate_mem_of_mem_cons (h₁ l hl) (by rintro rfl; exact hc₁ hl)

/-- The search from the empty partial assignment, with the variables of the formula open, in the
order of their first occurrences. -/
def dpll (φ : CNF ℕ) : Outcome φ [] :=
  search φ φ.vars.eraseDups.length [] φ.vars.eraseDups
    ⟨fun _ hx => .inl (List.mem_eraseDups.2 hx), by simp, List.nodup_eraseDups _⟩ le_rfl

/-! ### The solver -/

/-- The answer of the solver: a model, or an LRAT certificate of unsatisfiability. -/
inductive Result : Type
  /-- A model. -/
  | sat (σ : ℕ → Bool)
  /-- An LRAT certificate of unsatisfiability. -/
  | unsat (cert : Array LRAT.IntAction)

/-- Whether the answer is a model. -/
def Result.isSat : Result → Bool
  | .sat _ => true
  | .unsat _ => false

/-- **A sound answer decides satisfiability**: if a model in the answer satisfies `φ` and a
certificate in it is accepted by the LRAT checker on `φ`, the answer is a model exactly when `φ` is
satisfiable. -/
theorem Result.isSat_iff {φ : CNF ℕ} {r : Result}
    (hsat : ∀ σ, r = .sat σ → φ.eval σ = true)
    (hunsat : ∀ cert, r = .unsat cert → φ.checkLRAT cert = true) :
    r.isSat = true ↔ φ.Satisfiable := by
  cases r with
  | sat σ => exact ⟨fun _ => ⟨σ, hsat σ rfl⟩, fun _ => rfl⟩
  | unsat cert =>
    exact ⟨fun h => absurd h Bool.false_ne_true,
      fun h => absurd h (not_satisfiable_of_checkLRAT (hunsat cert rfl))⟩

/-- A derivation of a clause falsified by the empty partial assignment derives the empty
clause. -/
def refutationOf {φ : CNF ℕ} : (c : Clause ℕ) → φ.Derivation c →
    (∀ l ∈ c, l.negate ∈ ([] : List (Literal ℕ))) → φ.Derivation []
  | [], d, _ => d
  | l :: _, _, h => absurd (h l List.mem_cons_self) List.not_mem_nil

/-- **The DPLL solver**: a model, or the LRAT certificate of the refutation found by the search. -/
def solve (φ : CNF ℕ) : Result :=
  match dpll φ with
  | .sat σ _ => .sat σ
  | .unsat c d h => .unsat (refutationOf c d h).toLRAT

/-- **The models returned by the solver are models.** -/
theorem solve_sat {φ : CNF ℕ} {σ : ℕ → Bool} (h : solve φ = .sat σ) : φ.eval σ = true := by
  unfold solve at h
  split at h
  · rename_i hσ _
    cases h
    exact hσ
  · cases h

/-- **The certificates returned by the solver are accepted by the LRAT checker.** -/
theorem solve_unsat {φ : CNF ℕ} {cert : Array LRAT.IntAction} (h : solve φ = .unsat cert) :
    φ.checkLRAT cert = true := by
  unfold solve at h
  split at h
  · cases h
  · rename_i c d hc _
    cases h
    exact (refutationOf c d hc).checkLRAT_toLRAT

/-- **The solver decides satisfiability.** -/
theorem isSat_solve_iff (φ : CNF ℕ) : (solve φ).isSat = true ↔ φ.Satisfiable :=
  Result.isSat_iff (fun _ => solve_sat) (fun _ => solve_unsat)

/-- **The LRAT checker is complete**: a formula has a certificate that the checker accepts exactly
when it is unsatisfiable. -/
theorem exists_checkLRAT_iff (φ : CNF ℕ) :
    (∃ cert, φ.checkLRAT cert = true) ↔ ¬ φ.Satisfiable := by
  refine ⟨fun ⟨_, h⟩ => not_satisfiable_of_checkLRAT h, fun h => ?_⟩
  cases hs : solve φ with
  | sat σ => exact absurd ⟨σ, solve_sat hs⟩ h
  | unsat cert => exact ⟨cert, solve_unsat hs⟩

/-- **The LRAT checker with RAT steps is complete**: a formula has a certificate that it accepts
exactly when it is unsatisfiable. -/
theorem exists_checkLRATRat_iff (φ : CNF ℕ) :
    (∃ cert, φ.checkLRATRat cert = true) ↔ ¬ φ.Satisfiable :=
  ⟨fun ⟨_, h⟩ => not_satisfiable_of_checkLRATRat h, fun h =>
    let ⟨cert, hc⟩ := (exists_checkLRAT_iff φ).2 h
    ⟨cert, checkLRATRat_of_checkLRAT hc⟩⟩

end Cslib.Algorithms.Lean.DPLL
