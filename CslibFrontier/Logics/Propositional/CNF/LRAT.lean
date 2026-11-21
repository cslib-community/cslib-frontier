/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF
public import Std.Tactic.BVDecide.LRAT.Actions
import CslibFrontier.Foundations.Data.List.Lookup

/-! # A kernel-reducible LRAT checker

An LRAT certificate [Cruz-Filipe et al.][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017] refutes a
formula in conjunctive normal form by a sequence of steps, each adding a clause, adding the empty
clause, or deleting clauses. Every clause has a number: the clauses of the formula are numbered
`1, 2, …` in order, and every added clause carries its own number. An added clause comes with
*hints*, a list of numbers of clauses. Starting from the negation of the added clause, the hinted
clauses are visited in order. Each must have all but one of its literals false, and then the
remaining literal becomes true, except the last, which must have all its literals false. So the
added clause follows from the hinted clauses by unit propagation: it is a *RUP* clause.

`Cslib.Logic.PL.CNF.checkLRAT φ cert` checks a certificate in the format of Lean core's
`Std.Tactic.BVDecide.LRAT.IntAction`: literals are nonzero integers in DIMACS style, so the
variable `v` of `φ : CNF ℕ` is written `v + 1`, and is negated by negating the integer. It accepts
RUP steps, empty-clause steps and deletions, and rejects RAT steps. It is written with structural
recursion on lists, so the kernel can evaluate it and `decide` proves that it accepts a given
certificate. Lean core's `Std.Tactic.BVDecide.LRAT.check` checks the same format, but the kernel
cannot evaluate it, and it is only proved sound, not complete.

A clause added by a RUP step holds under every assignment satisfying the clauses so far, so an
accepted certificate shows that the formula has no model
(`Cslib.Logic.PL.CNF.not_satisfiable_of_checkLRAT`).

## Main definitions

* `Cslib.Logic.PL.Clause.ofDIMACS`: a clause from DIMACS integers.
* `Cslib.Logic.PL.CNF.propagateHints`: unit propagation along hints.
* `Cslib.Logic.PL.CNF.checkLRAT`: the checker.

## Main results

* `Cslib.Logic.PL.CNF.not_satisfiable_of_checkLRAT`: a formula with an accepted certificate is
  unsatisfiable.

## References

* [L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt, Jr., M. Kaufmann and P. Schneider-Kamp,
  *Efficient Certified RAT Verification*][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Std.Tactic.BVDecide (LRAT.IntAction)

/-- The literal named by a DIMACS integer: `v + 1` is the variable `v` and `-(v + 1)` its
negation; `0` names nothing. -/
def Literal.ofDIMACS (i : Int) : Option (Literal ℕ) :=
  if 0 < i then some (i.natAbs - 1, true)
  else if i < 0 then some (i.natAbs - 1, false)
  else none

/-- The clause named by a list of DIMACS integers. -/
def Clause.ofDIMACS (c : List Int) : Clause ℕ :=
  c.filterMap Literal.ofDIMACS

/-- Unit propagation along hints, from the literals `trail` assumed true, reading the hinted
clauses with `lookup`. Each hinted clause must have every literal but one false under `trail`, and
that literal is added to `trail`; the run succeeds when a hinted clause has every literal false. A
literal repeated in a clause counts once. The checker reads clauses from a list of numbered
clauses (`Cslib.Logic.PL.CNF.propagateHints`); a solver can read them from an index. -/
def CNF.propagateWith (lookup : ℕ → Option (Clause ℕ)) : List (Literal ℕ) → List ℕ → Bool
  | _, [] => false
  | trail, h :: hs =>
    match lookup h with
    | none => false
    | some c =>
      match c.filter (fun l => !trail.contains (Std.Sat.Literal.negate l)) with
      | [] => true
      | l :: ls => if ls.all (· == l) then propagateWith lookup (l :: trail) hs else false

/-- **Unit propagation along hints** in a database of numbered clauses
(`Cslib.Logic.PL.CNF.propagateWith`), looking up the first clause of each number (`List.lookup`). -/
def CNF.propagateHints (db : List (ℕ × Clause ℕ)) : List (Literal ℕ) → List ℕ → Bool :=
  propagateWith (fun h => db.lookup h)

theorem CNF.propagateHints_nil (db : List (ℕ × Clause ℕ)) (t : List (Literal ℕ)) :
    propagateHints db t [] = false := rfl

/-- One step of unit propagation along hints in a database. -/
theorem CNF.propagateHints_cons (db : List (ℕ × Clause ℕ)) (t : List (Literal ℕ)) (h : ℕ)
    (hs : List ℕ) :
    propagateHints db t (h :: hs) =
      match db.find? (·.1 == h) with
      | none => false
      | some e =>
        match e.2.filter (fun l => !t.contains (Std.Sat.Literal.negate l)) with
        | [] => true
        | l :: ls => if ls.all (· == l) then propagateHints db (l :: t) hs else false := by
  have hk : (fun e : ℕ × Clause ℕ => h == e.1) = (·.1 == h) := funext fun _ => BEq.comm
  simp only [propagateHints, propagateWith, List.lookup_eq_map_find?, hk]
  cases db.find? (·.1 == h) <;> rfl

/-- The checker on a database of numbered clauses. -/
def CNF.checkLRATAux : List (ℕ × Clause ℕ) → List LRAT.IntAction → Bool
  | _, [] => false
  | db, .addEmpty _ hints :: _ => propagateHints db [] hints.toList
  | db, .addRup id c hints :: rest =>
    propagateHints db ((Clause.ofDIMACS c.toList).map Std.Sat.Literal.negate) hints.toList &&
      checkLRATAux ((id, Clause.ofDIMACS c.toList) :: db) rest
  | _, .addRat .. :: _ => false
  | db, .del ids :: rest => checkLRATAux (db.filter fun e => !ids.toList.contains e.1) rest

/-- The numbered clauses the checker starts from: clause `i` of `φ` has the number `i + 1`. -/
def CNF.lratDB (φ : CNF ℕ) : List (ℕ × Clause ℕ) :=
  φ.zipIdx.map fun e => (e.2 + 1, e.1)

/-- **The LRAT checker**: the clauses of `φ` are numbered from `1`, and the certificate must reach
an empty-clause step through RUP steps and deletions. -/
def CNF.checkLRAT (φ : CNF ℕ) (cert : Array LRAT.IntAction) : Bool :=
  checkLRATAux φ.lratDB cert.toList

/-- Unit propagation along hints reads the starting literals only through membership. -/
theorem CNF.propagateWith_congr (lookup : ℕ → Option (Clause ℕ)) :
    ∀ {t t' : List (Literal ℕ)}, (∀ l, l ∈ t ↔ l ∈ t') → ∀ hs : List ℕ,
      propagateWith lookup t hs = propagateWith lookup t' hs
  | _, _, _, [] => rfl
  | t, t', h, x :: hs => by
    have hf : (fun l => !t.contains (Std.Sat.Literal.negate l)) =
        fun l => !t'.contains (Std.Sat.Literal.negate l) := by
      funext l
      have : t.contains (Std.Sat.Literal.negate l) = true ↔
          t'.contains (Std.Sat.Literal.negate l) = true := by
        rw [List.contains_iff_mem, List.contains_iff_mem, h]
      rw [Bool.eq_iff_iff.2 this]
    simp only [propagateWith, hf]
    split
    · rfl
    · split
      · rfl
      · rename_i l ls _
        split
        · exact CNF.propagateWith_congr lookup (fun y => by simp [h]) hs
        · rfl

/-- Unit propagation along hints reads the starting literals only through membership. -/
theorem CNF.propagateHints_congr (db : List (ℕ × Clause ℕ)) {t t' : List (Literal ℕ)}
    (h : ∀ l, l ∈ t ↔ l ∈ t') (hs : List ℕ) : propagateHints db t hs = propagateHints db t' hs :=
  CNF.propagateWith_congr _ h hs

/-! ### Soundness -/

/-- If unit propagation along hints succeeds, no assignment satisfying every clause the lookup
returns makes the starting literals true. -/
theorem CNF.false_of_propagateWith {lookup : ℕ → Option (Clause ℕ)} {σ : ℕ → Bool}
    (hlookup : ∀ h c, lookup h = some c → c.eval σ = true) {trail : List (Literal ℕ)}
    (htrail : ∀ l ∈ trail, Literal.eval σ l = true) {hs : List ℕ}
    (h : propagateWith lookup trail hs = true) : False := by
  induction hs generalizing trail with
  | nil => simp [propagateWith] at h
  | cons x hs ih =>
    simp only [propagateWith] at h
    split at h
    · simp at h
    · rename_i c hc
      obtain ⟨l', hl', hl'σ⟩ := (Clause.eval_eq_true_iff σ c).1 (hlookup x c hc)
      -- a literal of the clause that holds is not falsified by the trail
      have hl'e : Literal.eval σ l' = true := by simp [Literal.eval, hl'σ]
      have hkeep : l' ∈ c.filter (fun l => !trail.contains (Std.Sat.Literal.negate l)) := by
        refine List.mem_filter.2 ⟨hl', ?_⟩
        cases hm : trail.contains (Std.Sat.Literal.negate l')
        · rfl
        · have := htrail _ (by simpa using hm)
          simp [hl'e] at this
      split at h
      · rename_i hnil
        rw [hnil] at hkeep
        simp at hkeep
      · rename_i l ls hone
        split at h
        · rename_i hall
          -- the literal that holds is the repeated one
          have hl'l : l' = l := by
            rw [hone, List.mem_cons] at hkeep
            rcases hkeep with rfl | hmem
            · rfl
            · simpa using List.all_eq_true.1 hall l' hmem
          subst hl'l
          refine ih (trail := l' :: trail) ?_ h
          intro l hl
          rcases List.mem_cons.1 hl with rfl | hl
          · exact hl'e
          · exact htrail l hl
        · simp at h

/-- If unit propagation along hints succeeds, no assignment satisfies the database and makes the
starting literals true. -/
theorem CNF.false_of_propagateHints {db : List (ℕ × Clause ℕ)} {σ : ℕ → Bool}
    (hdb : ∀ e ∈ db, e.2.eval σ = true) {trail : List (Literal ℕ)}
    (htrail : ∀ l ∈ trail, Literal.eval σ l = true) {hs : List ℕ}
    (h : propagateHints db trail hs = true) : False :=
  CNF.false_of_propagateWith (fun k c hc => by
    obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.1 hc
    exact hdb (k, c) (by simp [hl])) htrail h

/-- **A RUP clause holds**: if unit propagation along hints from its negation succeeds, every
assignment satisfying the database satisfies it. -/
theorem CNF.eval_of_propagateHints {db : List (ℕ × Clause ℕ)} {σ : ℕ → Bool}
    (hdb : ∀ e ∈ db, e.2.eval σ = true) {c : Clause ℕ} {hs : List ℕ}
    (h : propagateHints db (c.map Std.Sat.Literal.negate) hs = true) : c.eval σ = true := by
  by_contra hne
  refine false_of_propagateHints hdb ?_ h
  intro l hl
  obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
  have := (Clause.eval_eq_true_iff σ _).not.1 hne
  simp only [not_exists, not_and] at this
  rw [Literal.eval_negate]
  simpa [Literal.eval] using this l₀ hl₀

/-- If the checker accepts on a database, no assignment satisfies the database. -/
theorem CNF.false_of_checkLRATAux {σ : ℕ → Bool} {db : List (ℕ × Clause ℕ)}
    (hdb : ∀ e ∈ db, e.2.eval σ = true) {cert : List LRAT.IntAction}
    (h : checkLRATAux db cert = true) : False := by
  induction cert generalizing db with
  | nil => simp [checkLRATAux] at h
  | cons a cert ih =>
    cases a with
    | addEmpty id hints =>
      exact false_of_propagateHints hdb (trail := []) (by simp) h
    | addRup id c hints =>
      simp only [checkLRATAux, Bool.and_eq_true] at h
      refine ih (db := (id, Clause.ofDIMACS c.toList) :: db) ?_ h.2
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact eval_of_propagateHints hdb h.1
      · exact hdb e he
    | addRat id c pivot rupHints ratHints => simp [checkLRATAux] at h
    | del ids =>
      simp only [checkLRATAux] at h
      exact ih (fun e he => hdb e (List.mem_filter.1 he).1) h

/-- **A formula with an accepted LRAT certificate is unsatisfiable.** -/
theorem CNF.not_satisfiable_of_checkLRAT {φ : CNF ℕ} {cert : Array LRAT.IntAction}
    (h : φ.checkLRAT cert = true) : ¬ φ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  refine false_of_checkLRATAux (σ := σ) ?_ h
  intro e he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (show e ∈ φ.zipIdx.map fun e => (e.2 + 1, e.1) from he)
  exact (CNF.eval_eq_true_iff σ φ).1 hσ _
    (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp))

end Cslib.Logic.PL
