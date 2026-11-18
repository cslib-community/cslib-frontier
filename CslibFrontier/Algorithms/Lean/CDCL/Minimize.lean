/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.Exec

/-! # Minimizing learned clauses

MiniSat's minimization of learned clauses. In its recursive mode (`ccmin_mode = 2`, Sörensson and
Biere), a literal `y` of a learned clause, false below the backjump point, is *redundant* when the
literal `¬y` of the trail is implied and every other literal of its reason is either in the learned
clause or, recursively, redundant (`Cslib.Algorithms.Lean.CDCL.derived`). In its basic mode
(`ccmin_mode = 1`, MiniSat 1.13), the recursion goes only into the literals implied without any
decision, which MiniSat's test of level `0` admits. Removing every redundant literal
gives a clause that follows from the rest by unit propagation: assuming its negation, the reasons
of the redundant literals, oldest first, propagate the negations of the removed literals, and then
the learned clause is false.

That is exactly a RUP step of LRAT. So the minimized clause enters the certificate as one RUP step
hinting those reasons and then the learned clause (`Cslib.Logic.PL.CNF.LRATLog.addRup`), and its
correctness needs no proof about the search for redundant literals: the solver runs the checker's
unit propagation on the hints (`Cslib.Logic.PL.CNF.LRATLog.propagate`), and keeps the minimized
clause only if it succeeds, and the learned clause otherwise
(`Cslib.Algorithms.Lean.CDCL.Learned.minimize`). What is certified is the checked candidate:
`Learned.minimize` accepts any trail, with no proof that its reasons are those of the learned
clause, so nothing here proves that the check succeeds; when it fails, the answer is still
correct, with the unminimized clause. The minimized clause is a subset of the learned one
containing its asserting literal once, at its head, so it is again a learned clause.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.derived`: whether a literal of the trail follows from the learned
  clause's other literals.
* `Cslib.Algorithms.Lean.CDCL.Learned.minimize`: the minimized learned clause.

## References

* [N. Sörensson, A. Biere, *Minimizing Learned Clauses*][SorenssonBiere2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL Cslib.Logic.PL.CNF

variable {φ : CNF ℕ}

/-- A bound on the variables of a trail: one past the greatest. -/
def XTrail.varBound (T : XTrail) : ℕ := T.foldl (fun m x => max m (x.entry.lit.1 + 1)) 0

/-- The number of the reason of each implied variable of the trail `T`, indexed by variable, for
the variables below `n`. -/
def XTrail.reasons (T : XTrail) (n : ℕ) : Array (Option ℕ) :=
  T.foldl (fun a x => match x with
    | .implied l r => a.setIfInBounds l.1 (some r)
    | .decision _ => a) (Array.replicate n none)

/-- **Whether the literal of the trail on `v` is derived** from the literals of the learned clause,
whose variables are marked by `inC`: its reason, looked up in `log` through `reason`, has every
other literal either on a variable of the learned clause or, on a variable where `deep` allows the
recursion, derived. Decisions and literals without a reason are not derived. The results are
memoized in `memo`; `fuel` bounds the depth of the search, and running out of it counts as not
derived. -/
def derived (log : LRATLog φ) (reason : Array (Option ℕ)) (inC : Array Bool) (deep : ℕ → Bool) :
    (fuel : ℕ) → (memo : Array (Option Bool)) → (v : ℕ) → Bool × Array (Option Bool)
  | 0, memo, _ => (false, memo)
  | fuel + 1, memo, v =>
    match memo.getD v none with
    | some b => (b, memo)
    | none =>
      match (reason.getD v none).bind log.clause? with
      | none => (false, memo.setIfInBounds v (some false))
      | some R =>
        let r := R.foldl (fun (acc : Bool × Array (Option Bool)) z =>
          if !acc.1 then acc
          else if z.1 == v || inC.getD z.1 false then acc
          else if deep z.1 then derived log reason inC deep fuel acc.2 z.1
          else (false, acc.2)) (true, memo)
        (r.1, r.2.setIfInBounds v (some r.1))

/-- The literals of the clause `C`, other than `lit`, whose negations are derived, and the
memoized search. -/
def redundant (log : LRATLog φ) (reason : Array (Option ℕ)) (inC : Array Bool) (deep : ℕ → Bool)
    (fuel : ℕ) (lit : Literal ℕ) (C : Clause ℕ) (memo : Array (Option Bool)) :
    List (Literal ℕ) × Array (Option Bool) :=
  C.foldl (fun (acc : List (Literal ℕ) × Array (Option Bool)) y =>
    if y == lit then acc
    else
      let r := derived log reason inC deep fuel acc.2 y.1
      (if r.1 then y :: acc.1 else acc.1, r.2)) ([], memo)

/-- The reasons of the derived literals of the trail `T`, oldest first: the hints that propagate
them. -/
def derivedHints (T : XTrail) (memo : Array (Option Bool)) : List ℕ :=
  T.reverse.filterMap fun x => match x with
    | .implied l r => if memo.getD l.1 none == some true then some r else none
    | .decision _ => none

/-- **The redundant literals** of the learned clause `C` with the asserting literal `lit`, whose
false literals are on the trail `T`, and the memoized search: recursively if `recursive`, and
otherwise following only the reasons of the literals implied at the root. -/
def minimizeRedundant (log : LRATLog φ) (T : XTrail) (C : Clause ℕ) (lit : Literal ℕ)
    (recursive : Bool) : List (Literal ℕ) × Array (Option Bool) :=
  let n := max T.varBound (C.foldl (fun m y => max m (y.1 + 1)) 0)
  let reason := T.reasons n
  let inC := C.foldl (fun a y => a.setIfInBounds y.1 true) (Array.replicate n false)
  let deep : ℕ → Bool :=
    if recursive then fun _ => true
    else
      let root := Assign.ofTrail (XTrail.trail (XTrail.root T))
      fun v => root.assigned v
  redundant log reason inC deep (T.length + 1) lit C (Array.replicate n none)

variable {log₀ : LRATLog φ} {A M₀ : Trail}

/-- **Minimizing a learned clause**, whose false literals are on the trail `T`, recursively if
`recursive` (MiniSat's `ccmin_mode = 2`) and otherwise in the basic way (`ccmin_mode = 1`): the
learned clause without its redundant literals, added to the log as a RUP step hinting the reasons
of the derived literals and then the learned clause. The learned clause is kept if nothing is
redundant, or if the RUP check fails. -/
def Learned.minimize (L : Learned log₀ A M₀) (T : XTrail) (recursive : Bool := true) :
    Learned log₀ A M₀ :=
  let C := dedupLits L.clause
  let r := minimizeRedundant L.log T C L.lit recursive
  if r.1.isEmpty then L
  else
    let D := L.lit :: C.filter fun y => y != L.lit && !r.1.contains y
    let hints := derivedHints T r.2 ++ [L.id]
    have hsub : ∀ y ∈ D, y ∈ L.clause := fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact L.mem
      · exact (mem_dedupKey litKey_injective).1 (List.mem_filter.1 hy).1
    if hprop : L.log.propagate (D.map Std.Sat.Literal.negate) hints = true then
      { log := L.log.addRup D hints (L.log.propagate_eq _ _ ▸ hprop) fun l hl =>
          LRATLog.vars_mem_of_clause? L.clause?_eq l (hsub l hl)
        id := L.log.next
        clause := D
        lit := L.lit
        seen := L.seen
        used := L.used
        seen_mem := L.seen_mem
        marks := L.marks
        marks_none := L.marks_none
        clause?_eq := LRATLog.clause?_addRup
        mem := List.mem_cons_self
        false_below := fun y hy hne => L.false_below y (hsub y hy) hne
        undef := L.undef
        above := L.above
        ext := L.ext.trans LRATLog.extends_addRup }
    else L

end Cslib.Algorithms.Lean.CDCL
