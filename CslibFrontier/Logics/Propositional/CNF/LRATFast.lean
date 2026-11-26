/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.Array.SetGrow

/-! # An array-based LRAT checker

`Cslib.Logic.PL.CNF.checkLRAT` is the reference LRAT checker: it is written for the kernel, with
lists and structural recursion, so looking up a hinted clause and testing whether a literal is
false each search a list. The hints of an LRAT certificate
[Cruz-Filipe et al.][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017] let a checker visit only the
clauses they name; `Cslib.Logic.PL.CNF.checkLRATFast` checks the same certificates with arrays:

* the clause database is an `Array (Option (Clause ℕ))` indexed by clause number, grown as
  needed; adding a clause writes it at its number, and deleting a clause writes `none`;
* the literals assumed true during a step are marked in an `Array Bool` indexed by literal, the
  literal `(v, b)` at `2 * v + 1` if `b` and at `2 * v` otherwise. At the end of each step the
  literals that step marked are unmarked, so every step starts from an empty assignment.

The assignment is indexed by literal rather than by variable because the reference checker's
trail is a list of literals, which holds both polarities of a variable when the added clause
contains both: such a variable makes both of its literals false. An array of `Option Bool`
indexed by variable cannot express that state, an array of marks indexed by literal can.

It accepts the fragment `checkLRAT` accepts: RUP additions, empty-clause steps and deletions.
RAT additions, which the general LRAT format allows, are rejected unless an accepted empty-clause
step comes first.

The checker agrees with `checkLRAT` on every formula and certificate
(`Cslib.Logic.PL.CNF.checkLRATFast_eq_checkLRAT`), so it is sound
(`Cslib.Logic.PL.CNF.not_satisfiable_of_checkLRATFast`). It is also complete: rewriting
`Cslib.Algorithms.Lean.DPLL.exists_checkLRAT_iff` with `checkLRATFast_eq_checkLRAT` shows that a
formula has a certificate this checker accepts exactly when it is unsatisfiable.

It is the checker for compiled and interpreted code. The kernel's `Array` wraps a list, so the
kernel cannot evaluate it efficiently: for kernel reduction, `decide` uses
`Cslib.Logic.PL.CNF.checkLRATKernel`, which checks the same certificates with a binary trie and a
bitmask. Each wins in its own setting. Measured on one machine with the two checkers alternating
in one process (2026-11; [#7225](https://github.com/cslib-community/cslib-frontier/issues/7225),
milestone 4):

* compiled, `checkLRATKernel` takes 6.0 to 6.5 times as long on the CDCL solver's certificates for
  SATLIB's `uuf100` to `uuf250` (on 583226 steps, 22.4 s against 3.4 s), 4.8 to 6.1 times as long
  on CaDiCaL's for PHP(7, 6) to PHP(9, 8) and for `uuf175` to `uuf250` (on 233006 steps, 5.4 s
  against 0.9 s), and 2 to 7 times as long on the trimmed certificates of `lrat_tauto`'s benchmark
  families. Almost half of its time is `Nat.testBit` on the bitmask, which is a multi-word number
  once there are more than about 30 variables;
* interpreted, as in `lrat_tauto`'s check of its trimmed certificate, `checkLRATKernel` takes 1.8 to
  4 times as long on those families;
* in the kernel (`decide +kernel`), `checkLRATFast` took 62.8 s on `lrat_tauto`'s certificate for
  the chain of 80 implications, against 0.67 s for `checkLRATKernel` and 6.8 s for `checkLRAT`, and
  exceeded 14 GB of memory on those for `dist 5`, `iff 5`, `php 4` and `php 5`, which
  `checkLRATKernel` checks in 0.9 to 8.4 s.

The arrays are updated in place when uniquely referenced, so that a step costs about the total
length of its clause and its hinted clauses. That speed is an engineering property, measured, not
a theorem here; the instruction bound on the library's word RAM is
[#6611](https://github.com/cslib-community/cslib-frontier/issues/6611). Clause numbers and
variables index the arrays directly, so a certificate that adds a clause with a very large number,
or mentions a very large variable, allocates an array of that length.

## Main definitions

* `Cslib.Logic.PL.CNF.checkLRATFast`: the array-based checker.

## Main results

* `Cslib.Logic.PL.CNF.checkLRATFast_eq_checkLRAT`: it agrees with `checkLRAT`.
* `Cslib.Logic.PL.CNF.not_satisfiable_of_checkLRATFast`: it is sound.

## References

* [L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt, Jr., M. Kaufmann and P. Schneider-Kamp,
  *Efficient Certified RAT Verification*][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017]
-/

public section

namespace Cslib.Logic.PL

open Std.Tactic.BVDecide (LRAT.IntAction)

namespace CNF

/-! ### Clause databases -/

/-- The database of clauses indexed by number, holding the clauses of an association list; an
earlier entry shadows a later one with the same number. -/
private def dbOfList (l : List (ℕ × Clause ℕ)) : Array (Option (Clause ℕ)) :=
  l.foldr (fun e db => Array.setGrow db e.1 none (some e.2)) #[]

private theorem getD_dbOfList (l : List (ℕ × Clause ℕ)) (n : ℕ) :
    (dbOfList l).getD n none = l.lookup n := by
  induction l with
  | nil => simp [dbOfList]
  | cons e l ih =>
    simp only [dbOfList, List.foldr_cons] at ih ⊢
    rw [Array.getD_setGrow, ih, List.lookup_cons_eq_ite]

/-- Delete the clauses with the given numbers. -/
private def deleteAll (db : Array (Option (Clause ℕ))) (ids : List ℕ) :
    Array (Option (Clause ℕ)) :=
  ids.foldl (fun db i => db.setIfInBounds i none) db

private theorem getD_deleteAll (db : Array (Option (Clause ℕ))) (ids : List ℕ) (n : ℕ) :
    (deleteAll db ids).getD n none = if ids.contains n then none else db.getD n none := by
  induction ids generalizing db with
  | nil => simp [deleteAll]
  | cons i ids ih =>
    simp only [deleteAll, List.foldl_cons] at ih ⊢
    rw [ih, Array.getD_setIfInBounds_self]
    by_cases h : n = i <;> simp [h]

/-! ### Assignments -/

/-- The index of a literal in an assignment. -/
private def litIdx (l : Literal ℕ) : ℕ := 2 * l.1 + l.2.toNat

private theorem litIdx_inj {l l' : Literal ℕ} : litIdx l = litIdx l' ↔ l = l' := by
  rcases l with ⟨v, b⟩
  rcases l' with ⟨v', b'⟩
  cases b <;> cases b' <;> simp [litIdx] <;> omega

/-- Whether a literal is marked true. -/
private def isTrue (asg : Array Bool) (l : Literal ℕ) : Bool := asg.getD (litIdx l) false

/-- Mark the literal true. -/
private def assign (asg : Array Bool) (l : Literal ℕ) : Array Bool :=
  Array.setGrow asg (litIdx l) false true

/-- Mark the literals true. -/
private def assignAll (asg : Array Bool) (ls : List (Literal ℕ)) : Array Bool :=
  ls.foldl assign asg

/-- Unmark the literals. -/
private def unassign (asg : Array Bool) (ls : List (Literal ℕ)) : Array Bool :=
  ls.foldl (fun a l => a.setIfInBounds (litIdx l) false) asg

private theorem isTrue_assign (asg : Array Bool) (l l' : Literal ℕ) :
    isTrue (assign asg l) l' = (l' == l || isTrue asg l') := by
  simp only [isTrue, assign, Array.getD_setGrow, litIdx_inj]
  by_cases h : l' = l <;> simp [h]

private theorem isTrue_assignAll (asg : Array Bool) (ls : List (Literal ℕ)) (l' : Literal ℕ) :
    isTrue (assignAll asg ls) l' = (isTrue asg l' || ls.contains l') := by
  induction ls generalizing asg with
  | nil => simp [assignAll]
  | cons l ls ih =>
    simp only [assignAll, List.foldl_cons] at ih ⊢
    rw [ih, isTrue_assign, List.contains_cons]
    cases l' == l <;> cases isTrue asg l' <;> simp

private theorem isTrue_unassign (asg : Array Bool) (ls : List (Literal ℕ)) (l' : Literal ℕ) :
    isTrue (unassign asg ls) l' = (isTrue asg l' && !ls.contains l') := by
  induction ls generalizing asg with
  | nil => simp [unassign]
  | cons l ls ih =>
    simp only [unassign, List.foldl_cons] at ih ⊢
    rw [ih, List.contains_cons]
    simp only [isTrue, Array.getD_setIfInBounds_self, litIdx_inj]
    rcases eq_or_ne l' l with rfl | h
    · simp
    · simp [h, beq_eq_false_iff_ne.mpr h]

/-! ### The checker -/

/-- Unit propagation along hints, as `CNF.propagateHints`: the literals of `trail` are the ones
marked in `asg`. Returns the verdict and the assignment with the literals of the final trail
unmarked. -/
private def propagateFast (db : Array (Option (Clause ℕ))) :
    Array Bool → List (Literal ℕ) → List ℕ → Bool × Array Bool
  | asg, trail, [] => (false, unassign asg trail)
  | asg, trail, h :: hs =>
    match db.getD h none with
    | none => (false, unassign asg trail)
    | some c =>
      match c.filter (fun l => !isTrue asg (Std.Sat.Literal.negate l)) with
      | [] => (true, unassign asg trail)
      | l :: ls =>
        if ls.all (· == l) then propagateFast db (assign asg l) (l :: trail) hs
        else (false, unassign asg trail)

/-- The checker on a clause database and an assignment with no literal marked. -/
private def checkLRATFastAux :
    Array (Option (Clause ℕ)) → Array Bool → List LRAT.IntAction → Bool
  | _, _, [] => false
  | db, asg, .addEmpty _ hints :: _ => (propagateFast db asg [] hints.toList).1
  | db, asg, .addRup id c hints :: rest =>
    let cl := Clause.ofDIMACS c.toList
    let neg := cl.map Std.Sat.Literal.negate
    let r := propagateFast db (assignAll asg neg) neg hints.toList
    r.1 && checkLRATFastAux (Array.setGrow db id none (some cl)) r.2 rest
  | _, _, .addRat .. :: _ => false
  | db, asg, .del ids :: rest => checkLRATFastAux (deleteAll db ids.toList) asg rest

/-- **The array-based LRAT checker**: it accepts exactly the certificates that
`CNF.checkLRAT` accepts (`CNF.checkLRATFast_eq_checkLRAT`), with the clauses of `φ` numbered from
`1`. Clauses are looked up in an array indexed by number, and literals in an array of marks
indexed by literal, reset after each step. It is for compiled and interpreted code, where it is
about 2 to 7 times as fast as `CNF.checkLRATKernel`; in the kernel, use `CNF.checkLRATKernel`. -/
def checkLRATFast (φ : CNF ℕ) (cert : Array LRAT.IntAction) : Bool :=
  checkLRATFastAux (dbOfList (φ.zipIdx.map fun e => (e.2 + 1, e.1))) #[] cert.toList

/-! ### Agreement with the reference checker -/

private theorem propagateFast_eq {db : Array (Option (Clause ℕ))} {L : List (ℕ × Clause ℕ)}
    (hdb : ∀ n, db.getD n none = L.lookup n) (hs : List ℕ) :
    ∀ (asg : Array Bool) (trail : List (Literal ℕ)), (∀ l, isTrue asg l = trail.contains l) →
      (propagateFast db asg trail hs).1 = propagateHints L trail hs ∧
        ∀ l, isTrue (propagateFast db asg trail hs).2 l = false := by
  have hreset (asg : Array Bool) (trail : List (Literal ℕ))
      (hasg : ∀ l, isTrue asg l = trail.contains l) (l : Literal ℕ) :
      isTrue (unassign asg trail) l = false := by
    rw [isTrue_unassign, hasg]
    cases trail.contains l <;> rfl
  induction hs with
  | nil => exact fun asg trail hasg => ⟨rfl, hreset asg trail hasg⟩
  | cons h hs ih =>
    intro asg trail hasg
    have hfind : db.getD h none = (L.find? (·.1 == h)).map (·.2) := by
      rw [hdb, List.lookup_eq_map_find?]
      congr 2 with e
      simp [eq_comm]
    rw [propagateHints_cons]
    simp only [propagateFast, hfind]
    cases L.find? (·.1 == h) with
    | none => exact ⟨rfl, hreset asg trail hasg⟩
    | some e =>
      simp only [Option.map_some, hasg, Clause.residual]
      cases e.2.filter (fun l => !trail.contains (Std.Sat.Literal.negate l)) with
      | nil => exact ⟨rfl, hreset asg trail hasg⟩
      | cons l ls =>
        dsimp only
        split_ifs with hall
        · exact ih _ _ fun l' => by rw [isTrue_assign, hasg, List.contains_cons]
        · exact ⟨rfl, hreset asg trail hasg⟩

private theorem checkLRATFastAux_eq {db : Array (Option (Clause ℕ))} {L : List (ℕ × Clause ℕ)}
    (hdb : ∀ n, db.getD n none = L.lookup n) {asg : Array Bool}
    (hasg : ∀ l, isTrue asg l = false) (cert : List LRAT.IntAction) :
    checkLRATFastAux db asg cert = checkLRATAux L cert := by
  fun_induction checkLRATFastAux db asg cert generalizing L with
  | case1 | case4 => rfl -- no actions, addRat
  | case2 db asg => exact (propagateFast_eq hdb _ asg [] (by simp [hasg])).1 -- addEmpty
  | case3 db asg id c hints rest cl neg r ih => -- addRup
    have hp := propagateFast_eq hdb hints.toList (assignAll asg neg) neg
      (fun l => by rw [isTrue_assignAll, hasg, Bool.false_or])
    exact congrArg₂ (· && ·) hp.1
      (ih (fun n => by rw [Array.getD_setGrow, hdb, List.lookup_cons_eq_ite]) hp.2)
  | case5 db asg ids rest ih => -- del
    exact ih (fun n => by rw [getD_deleteAll, hdb, List.lookup_filter_not_contains]) hasg

/-- **The array-based checker agrees with the reference checker** on every formula and
certificate. -/
theorem checkLRATFast_eq_checkLRAT (φ : CNF ℕ) (cert : Array LRAT.IntAction) :
    checkLRATFast φ cert = checkLRAT φ cert :=
  checkLRATFastAux_eq (getD_dbOfList _) (fun _ => by simp [isTrue]) cert.toList

/-- **A formula with a certificate accepted by the array-based checker is unsatisfiable.** -/
theorem not_satisfiable_of_checkLRATFast {φ : CNF ℕ} {cert : Array LRAT.IntAction}
    (h : φ.checkLRATFast cert = true) : ¬ φ.Satisfiable :=
  not_satisfiable_of_checkLRAT ((checkLRATFast_eq_checkLRAT φ cert) ▸ h)

end CNF

end Cslib.Logic.PL
