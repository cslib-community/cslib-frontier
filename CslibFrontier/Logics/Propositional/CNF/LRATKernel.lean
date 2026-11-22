/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT
public import CslibFrontier.Algorithms.WordRAM.ClauseCode
import CslibFrontier.Foundations.Data.List.Lookup

/-! # An LRAT checker for kernel reduction

`Cslib.Logic.PL.CNF.checkLRAT` is the reference LRAT checker
[Cruz-Filipe et al.][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017]. The kernel can evaluate it,
but it keeps its clause database and its trail of true literals in lists: looking up a hinted
clause searches the list of all clauses, and testing whether a literal is false searches the
trail. `Cslib.Logic.PL.CNF.checkLRATKernel` checks the same certificates with data the kernel
reduces quickly:

* the clause database is a binary trie keyed by the bits of the clause number, least significant
  bit first (`Cslib.Logic.PL.CNF.ClauseTrie`), so that looking up, adding and deleting a clause
  take a number of reduction steps proportional to the number's bit length;
* the trail of a step is a bitmask, a natural number with the literal `(v, b)` at bit `2 v + b`,
  its word code (`Cslib.Algorithms.WordRAM.ClauseCode.litCode`). Testing a literal is
  `Nat.testBit`, a shift right and a conjunction, and setting it is a disjunction with a shifted
  `1`. The kernel evaluates these operations on numerals with GMP. Each step starts again from
  `0`, so no literal is ever unset.

The checker uses structural recursion only, and no `Array`. Looking up and deleting recurse on
the trie. Adding a clause may build the path to its number, so it recurses on a bound on the
number's bit length instead: the number itself.

As in `checkLRATFast`, the trail is indexed by literal rather than by variable: the reference
checker's trail holds both polarities of a variable when the added clause contains both, which
makes both literals false.

It accepts the fragment `checkLRAT` accepts: RUP additions, empty-clause steps and deletions.
It agrees with `checkLRAT` on every formula and certificate
(`Cslib.Logic.PL.CNF.checkLRATKernel_eq_checkLRAT`). Rewriting with that equation,
`Cslib.Logic.PL.CNF.not_satisfiable_of_checkLRAT` and
`Cslib.Algorithms.Lean.DPLL.exists_checkLRAT_iff` give its soundness and completeness.

## Main definitions

* `Cslib.Logic.PL.CNF.ClauseTrie`: the clause database.
* `Cslib.Logic.PL.CNF.checkLRATKernel`: the checker.

## Main results

* `Cslib.Logic.PL.CNF.ClauseTrie.get_insert`: reading the trie after adding or deleting a clause.
* `Cslib.Logic.PL.CNF.checkLRATKernel_eq_checkLRAT`: the checker agrees with `checkLRAT`.

## References

* [L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt, Jr., M. Kaufmann and P. Schneider-Kamp,
  *Efficient Certified RAT Verification*][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Std.Tactic.BVDecide (LRAT.IntAction)
open Cslib.Algorithms.WordRAM.ClauseCode (litCode)

namespace CNF

/-! ### The clause database -/

/-- **A clause database as a binary trie** keyed by clause number. The number `0` is stored at the
root; a positive number `n` is stored in the subtrie `zero` if it is even and `one` if it is odd,
under the key `n / 2`. So a number is found by reading its bits from the least significant one.
An absent subtrie is a `leaf`. -/
inductive ClauseTrie where
  /-- The empty trie. -/
  | leaf
  /-- The clause numbered `0`, if any, and the subtries of the even and odd positive numbers. -/
  | node (val : Option (Clause ℕ)) (zero one : ClauseTrie)

namespace ClauseTrie

/-- The clause stored under the number `0`. -/
def val : ClauseTrie → Option (Clause ℕ)
  | leaf => none
  | node v _ _ => v

/-- The subtrie of the even positive numbers. -/
def zero : ClauseTrie → ClauseTrie
  | leaf => leaf
  | node _ z _ => z

/-- The subtrie of the odd numbers. -/
def one : ClauseTrie → ClauseTrie
  | leaf => leaf
  | node _ _ o => o

/-- The clause stored under the number `n`. -/
def get : ClauseTrie → ℕ → Option (Clause ℕ)
  | leaf, _ => none
  | node v z o, n => if n = 0 then v else if n % 2 = 0 then z.get (n / 2) else o.get (n / 2)

private theorem get_node (v : Option (Clause ℕ)) (z o : ClauseTrie) (n : ℕ) :
    (node v z o).get n = if n = 0 then v else if n % 2 = 0 then z.get (n / 2)
      else o.get (n / 2) := rfl

/-- Reading a trie by the first bit of the number, whether or not the trie is a `leaf`. -/
private theorem get_eq (t : ClauseTrie) (n : ℕ) :
    t.get n = if n = 0 then t.val else if n % 2 = 0 then t.zero.get (n / 2)
      else t.one.get (n / 2) := by
  cases t
  · simp only [val, zero, one]
    split_ifs <;> rfl
  · rfl

/-- Store `x` under the number `n`, which has at most `fuel` bits. The recursion is on `fuel`,
since the path to `n` may not exist yet. -/
def setAux (x : Option (Clause ℕ)) : ℕ → ClauseTrie → ℕ → ClauseTrie
  | 0, t, n => if n = 0 then node x t.zero t.one else t
  | fuel + 1, t, n =>
    if n = 0 then node x t.zero t.one
    else if n % 2 = 0 then node t.val (setAux x fuel t.zero (n / 2)) t.one
    else node t.val t.zero (setAux x fuel t.one (n / 2))
termination_by structural fuel => fuel

/-- Store `x` under the number `n`: `some c` adds the clause `c`, and `none` deletes it. -/
def insert (t : ClauseTrie) (n : ℕ) (x : Option (Clause ℕ)) : ClauseTrie := setAux x n t n

private theorem get_setAux (x : Option (Clause ℕ)) :
    ∀ (fuel : ℕ) (t : ClauseTrie) (n m : ℕ), n ≤ fuel →
      (setAux x fuel t n).get m = if m = n then x else t.get m := by
  intro fuel
  induction fuel with
  | zero =>
    intro t n m hn
    obtain rfl : n = 0 := by omega
    simp only [setAux, ↓reduceIte, get_node, get_eq t m]
    split_ifs <;> rfl
  | succ fuel ih =>
    intro t n m hn
    rw [get_eq t m]
    by_cases h0 : n = 0
    · subst h0
      simp only [setAux, ↓reduceIte, get_node]
      split_ifs <;> rfl
    · have hf : n / 2 ≤ fuel := by omega
      by_cases h2 : n % 2 = 0
      · simp only [setAux, h0, h2, ↓reduceIte, get_node, ih _ _ _ hf]
        split_ifs <;> first | rfl | (exfalso; omega)
      · simp only [setAux, h0, h2, ↓reduceIte, get_node, ih _ _ _ hf]
        split_ifs <;> first | rfl | (exfalso; omega)

/-- **Reading a trie after storing `x` under `n`.** -/
theorem get_insert (t : ClauseTrie) (n : ℕ) (x : Option (Clause ℕ)) (m : ℕ) :
    (t.insert n x).get m = if m = n then x else t.get m :=
  get_setAux x n t n m le_rfl

/-- The trie of an association list of numbered clauses; an earlier entry shadows a later one with
the same number, as in `List.lookup`. -/
def ofList (l : List (ℕ × Clause ℕ)) : ClauseTrie :=
  l.foldr (fun e t => t.insert e.1 (some e.2)) leaf

private theorem get_ofList (l : List (ℕ × Clause ℕ)) (n : ℕ) : (ofList l).get n = l.lookup n := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [ofList, List.foldr_cons] at ih ⊢
    rw [get_insert, ih, List.lookup_cons_eq_ite]

/-- Delete the clauses with the given numbers. -/
def eraseAll (t : ClauseTrie) (ids : List ℕ) : ClauseTrie :=
  ids.foldl (fun t i => t.insert i none) t

private theorem get_eraseAll (t : ClauseTrie) (ids : List ℕ) (n : ℕ) :
    (t.eraseAll ids).get n = if ids.contains n then none else t.get n := by
  induction ids generalizing t with
  | nil => simp [eraseAll]
  | cons i ids ih =>
    simp only [eraseAll, List.foldl_cons] at ih ⊢
    rw [ih, get_insert]
    by_cases h : n = i <;> simp [h]

end ClauseTrie

/-! ### Trails as bitmasks -/

/-- The bitmask with the literals of `ls` set, at their word codes. -/
def litMask (ls : List (Literal ℕ)) : ℕ :=
  ls.foldl (fun m l => m ||| 1 <<< litCode l) 0

private theorem testBit_or_litCode (m : ℕ) (l l' : Literal ℕ) :
    (m ||| 1 <<< litCode l).testBit (litCode l') = (m.testBit (litCode l') || decide (l' = l)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
  congr 1
  exact decide_eq_decide.2 ((Cslib.Algorithms.WordRAM.ClauseCode.litCodeBy_injective
    (f := (id : ℕ → ℕ)) Function.injective_id).eq_iff.trans eq_comm)

private theorem testBit_litMask (ls : List (Literal ℕ)) (l : Literal ℕ) :
    (litMask ls).testBit (litCode l) = decide (l ∈ ls) := by
  suffices ∀ m, (ls.foldl (fun m l => m ||| 1 <<< litCode l) m).testBit (litCode l) =
      (m.testBit (litCode l) || decide (l ∈ ls)) by
    rw [litMask, this, Nat.zero_testBit, Bool.false_or]
  induction ls with
  | nil => simp
  | cons l' ls ih =>
    intro m
    rw [List.foldl_cons, ih, testBit_or_litCode]
    by_cases h : l = l' <;> simp [h]

/-- **The residual of a clause** under the literals set in the bitmask `mask`, as
`Cslib.Logic.PL.Clause.residual` under a trail. -/
def residualMask (c : Clause ℕ) (mask : ℕ) : Clause.Residual :=
  match c.filter (fun l => !mask.testBit (litCode (Std.Sat.Literal.negate l))) with
  | [] => .empty
  | l :: ls => if ls.all (· == l) then .unit l else .other

private theorem residualMask_eq {mask : ℕ} {t : List (Literal ℕ)}
    (h : ∀ l, mask.testBit (litCode l) = decide (l ∈ t)) (c : Clause ℕ) :
    residualMask c mask = c.residual t := by
  unfold residualMask Clause.residual
  congr 2
  funext l
  simp [h]

/-- Unit propagation along hints, as `Cslib.Logic.PL.CNF.propagateHints`, reading the hinted
clauses from a trie and keeping the trail in a bitmask. -/
def propagateKernel (db : ClauseTrie) : ℕ → List ℕ → Bool
  | _, [] => false
  | mask, h :: hs =>
    match db.get h with
    | none => false
    | some c =>
      match residualMask c mask with
      | .empty => true
      | .unit l => propagateKernel db (mask ||| 1 <<< litCode l) hs
      | .other => false

private theorem propagateKernel_eq (db : ClauseTrie) (hs : List ℕ) :
    ∀ {mask : ℕ} {t : List (Literal ℕ)}, (∀ l, mask.testBit (litCode l) = decide (l ∈ t)) →
      propagateKernel db mask hs = propagateWith db.get t hs := by
  induction hs with
  | nil => intro _ _ _; rfl
  | cons h hs ih =>
    intro mask t hmask
    simp only [propagateKernel, propagateWith, residualMask_eq hmask]
    cases db.get h with
    | none => rfl
    | some c =>
      dsimp only
      cases c.residual t with
      | empty => rfl
      | unit l =>
        refine ih fun l' => ?_
        rw [testBit_or_litCode, hmask]
        by_cases h : l' = l <;> simp [h]
      | other => rfl

/-- The checker on a clause database. -/
def checkLRATKernelAux : ClauseTrie → List LRAT.IntAction → Bool
  | _, [] => false
  | db, .addEmpty _ hints :: _ => propagateKernel db 0 hints.toList
  | db, .addRup id c hints :: rest =>
    propagateKernel db (litMask ((Clause.ofDIMACS c.toList).map Std.Sat.Literal.negate))
        hints.toList &&
      checkLRATKernelAux (db.insert id (some (Clause.ofDIMACS c.toList))) rest
  | _, .addRat .. :: _ => false
  | db, .del ids :: rest => checkLRATKernelAux (db.eraseAll ids.toList) rest

/-- **The LRAT checker for kernel reduction**: it accepts exactly the certificates that
`CNF.checkLRAT` accepts (`CNF.checkLRATKernel_eq_checkLRAT`), with the clauses of `φ` numbered from
`1`. Clauses are looked up in a binary trie keyed by number, and the literals assumed true in a
step are the bits set in a natural number. -/
def checkLRATKernel (φ : CNF ℕ) (cert : Array LRAT.IntAction) : Bool :=
  checkLRATKernelAux (ClauseTrie.ofList φ.lratDB) cert.toList

/-! ### Agreement with the reference checker -/

private theorem checkLRATKernelAux_eq {db : ClauseTrie} {L : List (ℕ × Clause ℕ)}
    (hdb : ∀ n, db.get n = L.lookup n) (cert : List LRAT.IntAction) :
    checkLRATKernelAux db cert = checkLRATAux L cert := by
  induction cert generalizing db L with
  | nil => rfl
  | cons a cert ih =>
    have hp (t : List (Literal ℕ)) (hs : List ℕ) :
        propagateWith db.get t hs = propagateHints L t hs := by
      rw [show db.get = fun n => L.lookup n from funext hdb]
      rfl
    cases a with
    | addEmpty id hints =>
      simp only [checkLRATKernelAux, checkLRATAux, ← hp]
      exact propagateKernel_eq db _ (by simp)
    | addRup id c hints =>
      simp only [checkLRATKernelAux, checkLRATAux, ← hp,
        propagateKernel_eq db _ (testBit_litMask _)]
      congr 1
      exact ih fun n => by rw [ClauseTrie.get_insert, hdb, List.lookup_cons_eq_ite]
    | addRat => rfl
    | del ids =>
      simp only [checkLRATKernelAux, checkLRATAux]
      exact ih fun n => by
        rw [ClauseTrie.get_eraseAll, hdb, List.lookup_filter_not_contains]

/-- **The kernel checker agrees with the reference checker** on every formula and certificate. -/
theorem checkLRATKernel_eq_checkLRAT (φ : CNF ℕ) (cert : Array LRAT.IntAction) :
    checkLRATKernel φ cert = checkLRAT φ cert :=
  checkLRATKernelAux_eq (ClauseTrie.get_ofList _) cert.toList

end CNF

end Cslib.Logic.PL
