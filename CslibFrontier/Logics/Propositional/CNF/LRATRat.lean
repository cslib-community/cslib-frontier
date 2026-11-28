/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT
public import CslibFrontier.Logics.Propositional.CNF.Tautology
import CslibFrontier.Foundations.Data.List.Lookup

/-! # RAT steps in LRAT certificates

`Cslib.Logic.PL.CNF.checkLRAT` checks the RUP fragment of LRAT: it rejects RAT additions. The
LRAT format of [Cruz-Filipe et al.][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017] also adds
clauses with the *RAT* property. A clause `C` whose first literal is `p` has it with respect to a
formula `F` when, for every clause `D` of `F` containing `¬p`, the resolvent `C ∨ (D \ {¬p})`
follows from `F` by unit propagation, or is a tautology. Adding such a clause does not preserve
the models of `F`, only its satisfiability: a model of `F` falsifying `C` becomes a model of
`F ∧ C` once `p` is made true. Solvers emit RAT steps for bounded variable addition, as CaDiCaL's
`--factor` does, and extended resolution.

`Cslib.Logic.PL.CNF.checkLRATRat` checks certificates with RAT steps too. A RAT step
`.addRat id c _ rup rat` carries RUP hints `rup` and RAT hints `rat`, pairs `(i, hs)` of a clause
number and a hint list. It is accepted (`Cslib.Logic.PL.CNF.ratWith`) when the RUP hints refute
the negation of `c`, or else when every clause `d` numbered `i` that contains `¬p` has a
tautological resolvent with `c` or a resolvent refuted by unit propagation along `rup` followed
by the hints that `rat` gives to `i`. This is Algorithm `check_RAT` of the paper (Section 4),
with the following differences, each of which only accepts more certificates:

* the pivot is the first literal of the clause, as the paper's format requires (Section 3); the
  step's `pivot` field, which Lean core's parser sets to that literal, is not read;
* the RAT hints may come in any order, and hints naming clauses without `¬p` are ignored; the
  paper's format lists the negative hints in increasing order (Section 3);
* the RUP hints are propagated again in each resolvent check, rather than once before them, so a
  clause of the RUP part that is not yet unit does not reject the step.

As in the paper's algorithm, a candidate with a tautological resolvent needs no RAT hint, and a
RAT step with no candidate needs no hints at all: Lean core's parser reads a clause with no hints
as such a step, which is how CaDiCaL writes the definition clauses of `--factor`. Drat-trim's
`lrat-check` rejects those steps, since it does not check that no candidate exists.

The checker numbers clauses as `checkLRAT` does, and reads a clause number as its first entry in
the database, the clause a later one with the same number shadows being gone. Accepted
certificates refute their formula (`Cslib.Logic.PL.CNF.not_satisfiable_of_checkLRATRat`), and it
accepts every certificate `checkLRAT` accepts (`Cslib.Logic.PL.CNF.checkLRATRat_of_checkLRAT`), so
it is also complete (`Cslib.Algorithms.Lean.DPLL.exists_checkLRATRat_iff`). The RAT check is
written for any clause lookup and any test over the stored clauses, so that the kernel checker
`Cslib.Logic.PL.CNF.checkLRATKernel` and the array checker `Cslib.Logic.PL.CNF.checkLRATFast`
run the same check on their own databases.

## Main definitions

* `Cslib.Logic.PL.CNF.ratWith`: the RAT check of a step.
* `Cslib.Logic.PL.CNF.checkLRATRat`: the checker.

## Main results

* `Cslib.Logic.PL.CNF.exists_eval_of_ratWith`: a RAT step keeps a database satisfiable.
* `Cslib.Logic.PL.CNF.not_satisfiable_of_checkLRATRat`: a formula with an accepted certificate is
  unsatisfiable.
* `Cslib.Logic.PL.CNF.checkLRATRat_of_checkLRAT`: the checker accepts what `checkLRAT` accepts.

## References

* [L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt, Jr., M. Kaufmann and P. Schneider-Kamp,
  *Efficient Certified RAT Verification*][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Std.Tactic.BVDecide (LRAT.IntAction)

namespace CNF

/-- **The RAT check** of the clause `c`, whose pivot is its first literal `p`, with the RUP hints
`rup` and the RAT hints `rat`, reading clauses with `lookup`; `all f` tells whether `f n d` holds
for every clause `d` that `lookup` gives the number `n`. Either unit propagation along `rup`
refutes the negation of `c`, or every clause `d` containing `¬p` has a resolvent
`c ∨ (d \ {¬p})` that is a tautology or whose negation unit propagation refutes along `rup`
followed by the hints `rat` gives to the number of `d`. -/
def ratWith (lookup : ℕ → Option (Clause ℕ)) (all : (ℕ → Clause ℕ → Bool) → Bool) :
    Clause ℕ → List ℕ → List (ℕ × List ℕ) → Bool
  | [], _, _ => false
  | p :: ps, rup, rat =>
    propagateWith lookup ((p :: ps).map Std.Sat.Literal.negate) rup ||
      all fun n d =>
        !d.contains (Std.Sat.Literal.negate p) ||
          let r := (p :: ps) ++ d.filter (· != Std.Sat.Literal.negate p)
          isTautClause r ||
            propagateWith lookup (r.map Std.Sat.Literal.negate) (rup ++ (rat.lookup n).getD [])

/-- The RAT check reads the stored clauses only through what `all` tells about them. -/
theorem ratWith_congr {lookup : ℕ → Option (Clause ℕ)} {all all' : (ℕ → Clause ℕ → Bool) → Bool}
    (h : ∀ f, all f = true ↔ ∀ n d, lookup n = some d → f n d = true)
    (h' : ∀ f, all' f = true ↔ ∀ n d, lookup n = some d → f n d = true)
    (c : Clause ℕ) (rup : List ℕ) (rat : List (ℕ × List ℕ)) :
    ratWith lookup all c rup rat = ratWith lookup all' c rup rat := by
  rw [show all = all' from funext fun f => Bool.eq_iff_iff.2 ((h f).trans (h' f).symm)]

/-- The negations of the literals of a false clause are true. -/
private theorem eval_of_mem_map_negate {σ : ℕ → Bool} {r : Clause ℕ} (hr : r.eval σ = false)
    {l : Literal ℕ} (hl : l ∈ r.map Std.Sat.Literal.negate) : Literal.eval σ l = true := by
  obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
  simp only [Clause.eval, List.any_eq_false] at hr
  rw [Literal.eval_negate, Bool.eq_false_iff.2 (hr l₀ hl₀)]
  rfl

/-- **A RAT step keeps a database satisfiable**: if the RAT check of `c` succeeds and `σ`
satisfies every clause that `lookup` returns, some assignment satisfies them and `c`. It is `σ`
if `σ` satisfies `c`, and otherwise `σ` with the pivot made true. -/
theorem exists_eval_of_ratWith {lookup : ℕ → Option (Clause ℕ)}
    {all : (ℕ → Clause ℕ → Bool) → Bool}
    (hall : ∀ f, all f = true → ∀ n d, lookup n = some d → f n d = true)
    {c : Clause ℕ} {rup : List ℕ} {rat : List (ℕ × List ℕ)}
    (h : ratWith lookup all c rup rat = true)
    {σ : ℕ → Bool} (hσ : ∀ n d, lookup n = some d → d.eval σ = true) :
    ∃ τ : ℕ → Bool, (∀ n d, lookup n = some d → d.eval τ = true) ∧ c.eval τ = true := by
  obtain _ | ⟨p, ps⟩ := c
  · simp [ratWith] at h
  by_cases hc : Clause.eval σ (p :: ps) = true
  · exact ⟨σ, hσ, hc⟩
  rw [Bool.not_eq_true] at hc
  simp only [ratWith, Bool.or_eq_true] at h
  rcases h with h | h
  · exact (false_of_propagateWith hσ (fun _ => eval_of_mem_map_negate hc) h).elim
  -- the assignment `σ` with the pivot made true
  let τ := Function.update σ p.1 p.2
  -- a literal other than `¬p` true under `σ` is true under `τ`
  have hτ {l : Literal ℕ} (hl : l ≠ Std.Sat.Literal.negate p) (hσl : Literal.eval σ l = true) :
      Literal.eval τ l = true := by
    obtain ⟨v, b⟩ := l
    obtain ⟨w, a⟩ := p
    by_cases hv : v = w
    · subst hv
      have hb : b = a := by
        cases a <;> cases b <;> simp_all [Std.Sat.Literal.negate]
      simp [τ, Literal.eval, hb]
    · simpa [τ, Literal.eval, Function.update_of_ne hv] using hσl
  refine ⟨τ, fun n d hd => ?_, by simp [τ, Clause.eval_cons, Literal.eval]⟩
  -- some literal of `d` other than `¬p` is true under `σ`
  suffices ∃ l ∈ d, l ≠ Std.Sat.Literal.negate p ∧ Literal.eval σ l = true by
    obtain ⟨l, hl, hne, hσl⟩ := this
    exact List.any_eq_true.2 ⟨l, hl, hτ hne hσl⟩
  have hf := hall _ h n d hd
  by_cases hp : Std.Sat.Literal.negate p ∈ d
  · simp only [List.contains_eq_mem, hp, decide_true, Bool.not_true, Bool.false_or,
      Bool.or_eq_true] at hf
    by_contra hno
    push Not at hno
    -- the resolvent is false under `σ`
    have hr : Clause.eval σ ((p :: ps) ++ d.filter (· != Std.Sat.Literal.negate p)) = false := by
      simp only [Clause.eval, List.any_eq_false] at hc ⊢
      intro l hl
      rcases List.mem_append.1 hl with hl | hl
      · exact hc l hl
      · obtain ⟨hld, hlp⟩ := List.mem_filter.1 hl
        simpa using hno l hld (by simpa using hlp)
    rcases hf with hf | hf
    · have ht := eval_eq_true_of_isTautClause hf σ
      rw [hr] at ht
      exact Bool.false_ne_true ht
    · exact false_of_propagateWith hσ (fun _ => eval_of_mem_map_negate hr) hf
  · obtain ⟨l, hl, hσl⟩ := List.any_eq_true.1 (hσ n d hd)
    exact ⟨l, hl, fun h => hp (h ▸ hl), hσl⟩

/-! ### The checker -/

/-- Whether `f n d` holds for each clause `d` of the database `db` that its number `n` looks up,
as `ratWith` reads the clauses: a clause shadowed by an earlier one with the same number is not
read. -/
def allLookup (db : List (ℕ × Clause ℕ)) (f : ℕ → Clause ℕ → Bool) : Bool :=
  db.all fun e => (db.lookup e.1).all (f e.1)

/-- `allLookup` tests every clause that a number looks up. -/
theorem allLookup_eq_true {db : List (ℕ × Clause ℕ)} {f : ℕ → Clause ℕ → Bool} :
    allLookup db f = true ↔ ∀ n d, db.lookup n = some d → f n d = true := by
  refine ⟨fun h n d hd => ?_, fun h => List.all_eq_true.2 fun e _ => ?_⟩
  · obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.1 hd
    simpa [hd] using List.all_eq_true.1 h (n, d) (by simp [hl])
  · cases hl : db.lookup e.1 with
    | none => rfl
    | some d => simpa using h _ _ hl

/-- The RAT hints of a step as lists. -/
def ratHintList (rat : Array (ℕ × Array ℕ)) : List (ℕ × List ℕ) :=
  rat.toList.map fun h => (h.1, h.2.toList)

/-- The checker with RAT steps on a database of numbered clauses. -/
def checkLRATRatAux : List (ℕ × Clause ℕ) → List LRAT.IntAction → Bool
  | _, [] => false
  | db, .addEmpty _ hints :: _ => propagateHints db [] hints.toList
  | db, .addRup id c hints :: rest =>
    propagateHints db ((Clause.ofDIMACS c.toList).map Std.Sat.Literal.negate) hints.toList &&
      checkLRATRatAux ((id, Clause.ofDIMACS c.toList) :: db) rest
  | db, .addRat id c _ rup rat :: rest =>
    ratWith (db.lookup ·) (allLookup db) (Clause.ofDIMACS c.toList) rup.toList
        (ratHintList rat) &&
      checkLRATRatAux ((id, Clause.ofDIMACS c.toList) :: db) rest
  | db, .del ids :: rest => checkLRATRatAux (db.filter fun e => !ids.toList.contains e.1) rest

/-- **The LRAT checker with RAT steps**: the clauses of `φ` are numbered from `1`, and the
certificate must reach an empty-clause step through RUP steps, RAT steps (`CNF.ratWith`) and
deletions. -/
def checkLRATRat (φ : CNF ℕ) (cert : Array LRAT.IntAction) : Bool :=
  checkLRATRatAux φ.lratDB cert.toList

/-! ### Soundness and completeness -/

/-- Adding a clause that holds keeps every clause of a database true. -/
private theorem eval_lookup_cons {db : List (ℕ × Clause ℕ)} {σ : ℕ → Bool}
    (hdb : ∀ n d, db.lookup n = some d → d.eval σ = true) {id : ℕ} {c : Clause ℕ}
    (hc : c.eval σ = true) : ∀ n d, ((id, c) :: db).lookup n = some d → d.eval σ = true := by
  intro n d hd
  rw [List.lookup_cons_eq_ite] at hd
  split_ifs at hd
  · exact Option.some.inj hd ▸ hc
  · exact hdb n d hd

/-- If the checker accepts on a database, no assignment satisfies the clauses it looks up. -/
theorem false_of_checkLRATRatAux {db : List (ℕ × Clause ℕ)} {cert : List LRAT.IntAction}
    (h : checkLRATRatAux db cert = true) {σ : ℕ → Bool}
    (hdb : ∀ n d, db.lookup n = some d → d.eval σ = true) : False := by
  fun_induction checkLRATRatAux db cert generalizing σ with
  | case1 => simp at h -- no actions
  | case2 db => exact false_of_propagateWith hdb (trail := []) (by simp) h -- addEmpty
  | case3 db id c hints rest ih => -- addRup
    rw [Bool.and_eq_true] at h
    have hc : (Clause.ofDIMACS c.toList).eval σ = true := by
      by_contra hne
      exact false_of_propagateWith hdb
        (fun _ => eval_of_mem_map_negate (Bool.not_eq_true _ ▸ hne)) h.1
    exact ih h.2 (eval_lookup_cons hdb hc)
  | case4 db id c _ rup rat rest ih => -- addRat
    rw [Bool.and_eq_true] at h
    obtain ⟨τ, hτ, hc⟩ := exists_eval_of_ratWith (fun _ => allLookup_eq_true.1) h.1 hdb
    exact ih h.2 (eval_lookup_cons hτ hc)
  | case5 db ids rest ih => -- del
    refine ih h fun n d hd => hdb n d ?_
    rw [List.lookup_filter_not_contains] at hd
    split_ifs at hd
    exact hd

/-- **A formula with a certificate accepted by the checker with RAT steps is unsatisfiable.** -/
theorem not_satisfiable_of_checkLRATRat {φ : CNF ℕ} {cert : Array LRAT.IntAction}
    (h : φ.checkLRATRat cert = true) : ¬ φ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  refine false_of_checkLRATRatAux (σ := σ) h fun n d hd => ?_
  obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.1 hd
  have he : (n, d) ∈ φ.zipIdx.map fun e => (e.2 + 1, e.1) := by
    rw [← lratDB, hl]
    simp
  obtain ⟨p, hp, hpe⟩ := List.mem_map.1 he
  obtain rfl : p.1 = d := (Prod.mk.inj hpe).2
  exact (CNF.eval_eq_true_iff σ φ).1 hσ _
    (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp))

/-- The checker with RAT steps accepts on a database whatever `checkLRATAux` accepts. -/
theorem checkLRATRatAux_of_checkLRATAux {db : List (ℕ × Clause ℕ)} {cert : List LRAT.IntAction}
    (h : checkLRATAux db cert = true) : checkLRATRatAux db cert = true := by
  fun_induction checkLRATAux db cert with
  | case1 | case4 => simp at h -- no actions, addRat
  | case2 => simpa [checkLRATRatAux] using h -- addEmpty
  | case3 db id c hints rest ih => -- addRup
    simp only [Bool.and_eq_true] at h
    simp only [checkLRATRatAux, Bool.and_eq_true]
    exact ⟨h.1, ih h.2⟩
  | case5 db ids rest ih => simpa [checkLRATRatAux] using ih h -- del

/-- **The checker with RAT steps accepts every certificate `checkLRAT` accepts.** -/
theorem checkLRATRat_of_checkLRAT {φ : CNF ℕ} {cert : Array LRAT.IntAction}
    (h : φ.checkLRAT cert = true) : φ.checkLRATRat cert = true :=
  checkLRATRatAux_of_checkLRATAux h

end CNF

end Cslib.Logic.PL
