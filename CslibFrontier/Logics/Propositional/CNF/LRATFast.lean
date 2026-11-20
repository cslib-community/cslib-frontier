/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT
import CslibFrontier.Foundations.Data.List.Lookup

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
formula has a certificate this checker accepts exactly when it is unsatisfiable. The kernel cannot
evaluate it efficiently, and `decide` keeps using `checkLRAT`.

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

/-! ### Arrays as finite maps -/

/-- Write `x` at index `i`, first padding the array with `d` up to `i` if it is too short. -/
private def setGrow {α : Type} (a : Array α) (i : ℕ) (d x : α) : Array α :=
  if i < a.size then a.setIfInBounds i x else (a ++ Array.replicate (i - a.size) d).push x

private theorem getD_setGrow {α : Type} (a : Array α) (i j : ℕ) (d x : α) :
    (setGrow a i d x).getD j d = if j = i then x else a.getD j d := by
  unfold setGrow
  simp only [Array.getD_eq_getD_getElem?]
  split
  · rename_i hi
    by_cases hj : j = i
    · subst hj
      simp [hi]
    · simp [Ne.symm hj, hj]
  · rename_i hi
    have hs : a.size + (i - a.size) = i := by omega
    rw [Array.getElem?_push, Array.size_append, Array.size_replicate, hs]
    by_cases hj : j = i
    · simp [hj]
    · simp only [hj, ↓reduceIte, Array.getElem?_append]
      split
      · rfl
      · rw [Array.getElem?_replicate, Array.getElem?_eq_none (by omega)]
        split <;> rfl

private theorem getD_setIfInBounds_self {α : Type} (a : Array α) (i j : ℕ) (d : α) :
    (a.setIfInBounds i d).getD j d = if j = i then d else a.getD j d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split <;> split <;> simp_all

/-! ### Clause databases -/

/-- The database of clauses indexed by number, holding the clauses of an association list; an
earlier entry shadows a later one with the same number. -/
private def dbOfList (l : List (ℕ × Clause ℕ)) : Array (Option (Clause ℕ)) :=
  l.foldr (fun e db => setGrow db e.1 none (some e.2)) #[]

private theorem lookup_cons_ite (n k : ℕ) (c : Clause ℕ) (l : List (ℕ × Clause ℕ)) :
    ((k, c) :: l).lookup n = if n = k then some c else l.lookup n := by
  by_cases h : n = k
  · subst h
    simp
  · simp [List.lookup_cons, h, beq_eq_false_iff_ne.mpr h]

private theorem getD_dbOfList (l : List (ℕ × Clause ℕ)) (n : ℕ) :
    (dbOfList l).getD n none = l.lookup n := by
  induction l with
  | nil => simp [dbOfList]
  | cons e l ih =>
    simp only [dbOfList, List.foldr_cons] at ih ⊢
    rw [getD_setGrow, ih, lookup_cons_ite]

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
    rw [ih, getD_setIfInBounds_self]
    by_cases h : n = i <;> simp [h]

private theorem lookup_filter_not_contains (l : List (ℕ × Clause ℕ)) (ids : List ℕ) (n : ℕ) :
    (l.filter fun e => !ids.contains e.1).lookup n =
      if ids.contains n then none else l.lookup n := by
  induction l with
  | nil => simp
  | cons e l ih =>
    rcases e with ⟨k, c⟩
    by_cases hk : k ∈ ids
    · rw [List.filter_cons_of_neg (by simpa using hk), ih, lookup_cons_ite]
      by_cases h : n = k
      · subst h
        simp [hk]
      · simp [h]
    · rw [List.filter_cons_of_pos (by simpa using hk), lookup_cons_ite, lookup_cons_ite, ih]
      by_cases h : n = k
      · subst h
        simp [hk]
      · simp [h]

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
  setGrow asg (litIdx l) false true

/-- Mark the literals true. -/
private def assignAll (asg : Array Bool) (ls : List (Literal ℕ)) : Array Bool :=
  ls.foldl assign asg

/-- Unmark the literals. -/
private def unassign (asg : Array Bool) (ls : List (Literal ℕ)) : Array Bool :=
  ls.foldl (fun a l => a.setIfInBounds (litIdx l) false) asg

private theorem isTrue_assign (asg : Array Bool) (l l' : Literal ℕ) :
    isTrue (assign asg l) l' = (l' == l || isTrue asg l') := by
  simp only [isTrue, assign, getD_setGrow, litIdx_inj]
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
    simp only [isTrue, getD_setIfInBounds_self, litIdx_inj]
    by_cases h : l' = l
    · simp [h]
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
    r.1 && checkLRATFastAux (setGrow db id none (some cl)) r.2 rest
  | _, _, .addRat .. :: _ => false
  | db, asg, .del ids :: rest => checkLRATFastAux (deleteAll db ids.toList) asg rest

/-- **The array-based LRAT checker**: it accepts exactly the certificates that
`CNF.checkLRAT` accepts (`CNF.checkLRATFast_eq_checkLRAT`), with the clauses of `φ` numbered from
`1`. Clauses are looked up in an array indexed by number, and literals in an array of marks
indexed by literal, reset after each step. -/
def checkLRATFast (φ : CNF ℕ) (cert : Array LRAT.IntAction) : Bool :=
  checkLRATFastAux (dbOfList (φ.zipIdx.map fun e => (e.2 + 1, e.1))) #[] cert.toList

/-! ### Agreement with the reference checker -/

private theorem propagateFast_eq {db : Array (Option (Clause ℕ))} {L : List (ℕ × Clause ℕ)}
    (hdb : ∀ n, db.getD n none = L.lookup n) (hs : List ℕ) :
    ∀ (asg : Array Bool) (trail : List (Literal ℕ)), (∀ l, isTrue asg l = trail.contains l) →
      (propagateFast db asg trail hs).1 = propagateHints L trail hs ∧
        ∀ l, isTrue (propagateFast db asg trail hs).2 l = false := by
  have hreset : ∀ (asg : Array Bool) (trail : List (Literal ℕ)),
      (∀ l, isTrue asg l = trail.contains l) → ∀ l, isTrue (unassign asg trail) l = false := by
    intro asg trail hasg l
    rw [isTrue_unassign, hasg]
    cases trail.contains l <;> rfl
  induction hs with
  | nil => intro asg trail hasg; exact ⟨rfl, hreset asg trail hasg⟩
  | cons h hs ih =>
    intro asg trail hasg
    have hfind : db.getD h none = (L.find? (·.1 == h)).map (·.2) := by
      rw [hdb, List.lookup_eq_map_find?]
      congr 2
      funext e
      exact Bool.eq_iff_iff.2 (by simp only [beq_iff_eq]; exact eq_comm)
    have hfilter (c : Clause ℕ) : c.filter (fun l => !isTrue asg (Std.Sat.Literal.negate l)) =
        c.filter (fun l => !trail.contains (Std.Sat.Literal.negate l)) := by
      simp only [hasg]
    simp only [propagateFast, propagateHints, hfind]
    cases L.find? (·.1 == h) with
    | none => exact ⟨rfl, hreset asg trail hasg⟩
    | some e =>
      simp only [Option.map_some, hfilter]
      cases e.2.filter (fun l => !trail.contains (Std.Sat.Literal.negate l)) with
      | nil => exact ⟨rfl, hreset asg trail hasg⟩
      | cons l ls =>
        by_cases hall : ls.all (· == l)
        · simp only [hall, ite_true]
          refine ih _ _ fun l' => ?_
          rw [isTrue_assign, hasg, List.contains_cons]
        · simp only [hall]
          exact ⟨rfl, hreset asg trail hasg⟩

private theorem checkLRATFastAux_eq {db : Array (Option (Clause ℕ))} {L : List (ℕ × Clause ℕ)}
    (hdb : ∀ n, db.getD n none = L.lookup n) {asg : Array Bool}
    (hasg : ∀ l, isTrue asg l = false) (cert : List LRAT.IntAction) :
    checkLRATFastAux db asg cert = checkLRATAux L cert := by
  induction cert generalizing db L asg with
  | nil => rfl
  | cons a cert ih =>
    cases a with
    | addEmpty id hints =>
      exact (propagateFast_eq hdb _ asg [] (by simp [hasg])).1
    | addRup id c hints =>
      have hp := propagateFast_eq hdb hints.toList
        (assignAll asg ((Clause.ofDIMACS c.toList).map Std.Sat.Literal.negate))
        ((Clause.ofDIMACS c.toList).map Std.Sat.Literal.negate)
        (fun l => by rw [isTrue_assignAll, hasg, Bool.false_or])
      simp only [checkLRATFastAux, checkLRATAux, hp.1]
      congr 1
      refine ih (fun n => ?_) hp.2
      rw [getD_setGrow, hdb, lookup_cons_ite]
    | addRat => rfl
    | del ids =>
      simp only [checkLRATFastAux, checkLRATAux]
      refine ih (fun n => ?_) hasg
      rw [getD_deleteAll, hdb, lookup_filter_not_contains]

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
