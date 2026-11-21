/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.System

/-! # Phase saving for the CDCL solver

MiniSat's choice of polarity for a decision (with `phase_saving = 2`). Every variable has a saved
*phase*, initially `false`, so a fresh variable is decided negative, as MiniSat's default polarity
does. When a backjump unassigns variables, each one's phase becomes the value it had on the trail
(`Phases.save`), and a later decision on it takes that value again (`Phases.get`). The solver thus
returns to the part of the search space it left, keeping the assignments of the subproblems it
had solved.

The polarity of a decision does not affect correctness.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.Phases`: the saved phases.
* `Cslib.Algorithms.Lean.CDCL.Phases.save`: saving the phases of the literals undone by a
  backjump.

## Main results

* `Cslib.Algorithms.Lean.CDCL.Phases.get_save_of_mem`,
  `Cslib.Algorithms.Lean.CDCL.Phases.get_save_of_not_mem`: on a trail assigning each variable
  once, each undone variable reads back the value it had, and every other variable keeps its
  phase.

**Storage.** The phases are an array indexed by variable; setting a variable past its end grows it.
`WExec.init` gives it `varSlots φ` slots, one more than the largest variable of the formula and
none for a formula without variables, so `solveCompact`, which renames the variables to
`0, …, k - 1` first, keeps it at `k` slots.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL

/-- **Saved phases**: a polarity for each variable, by index; variables past the end have the
phase `false`. -/
structure Phases where
  /-- The saved polarity of each variable. -/
  saved : Array Bool

/-- The initial phases of the variables below `n`: all `false`. -/
def Phases.init (n : ℕ) : Phases := ⟨Array.replicate n false⟩

/-- The phase of the variable `v`: the polarity of its next decision. -/
def Phases.get (P : Phases) (v : ℕ) : Bool := P.saved.getD v false

/-- Setting the phase of `v` to `b`, growing the array with `false` if `v` is past its end. -/
def Phases.set (P : Phases) (v : ℕ) (b : Bool) : Phases :=
  let a := if v < P.saved.size then P.saved
    else P.saved ++ Array.replicate (v + 1 - P.saved.size) false
  ⟨a.setIfInBounds v b⟩

/-- **Saving** the phases of the literals of `M`, which a backjump undoes: each variable takes the
value it had. -/
def Phases.save (P : Phases) (M : Trail) : Phases :=
  (Trail.lits M).foldl (fun P l => P.set l.1 l.2) P

/-- Setting a phase changes that variable only. -/
theorem Phases.get_set (P : Phases) (v : ℕ) (b : Bool) (w : ℕ) :
    (P.set v b).get w = if v = w then b else P.get w := by
  unfold Phases.set Phases.get
  simp only [Array.getD_eq_getD_getElem?]
  have hsize : v < (if v < P.saved.size then P.saved
      else P.saved ++ Array.replicate (v + 1 - P.saved.size) false).size := by
    split <;> simp_all; omega
  by_cases hvw : v = w
  · subst hvw
    simp [hsize]
  · simp only [Array.getElem?_setIfInBounds, hvw, ite_false]
    split
    · rfl
    · rename_i hlt
      rw [Array.getElem?_append]
      split
      · rfl
      · rename_i hw
        rw [Array.getElem?_replicate, Array.getElem?_eq_none (by omega : P.saved.size ≤ w)]
        split <;> rfl

private theorem Phases.get_foldl_set_of_not_mem (L : List (Literal ℕ)) (P : Phases) {v : ℕ}
    (hv : v ∉ L.map Prod.fst) : (L.foldl (fun P l => P.set l.1 l.2) P).get v = P.get v := by
  induction L generalizing P with
  | nil => rfl
  | cons l L ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hv
    simp only [List.foldl_cons]
    rw [ih _ hv.2, Phases.get_set, ite_eq_right_iff.2 fun h => absurd h.symm hv.1]

private theorem Phases.get_foldl_set_of_mem (L : List (Literal ℕ)) (P : Phases)
    (hL : (L.map Prod.fst).Nodup) {l : Literal ℕ} (hl : l ∈ L) :
    (L.foldl (fun P l => P.set l.1 l.2) P).get l.1 = l.2 := by
  induction L generalizing P with
  | nil => simp at hl
  | cons l' L ih =>
    simp only [List.map_cons, List.nodup_cons] at hL
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hl with rfl | hl
    · rw [Phases.get_foldl_set_of_not_mem _ _ hL.1, Phases.get_set,
        ite_eq_left_iff.2 fun h => absurd rfl h]
    · exact ih _ hL.2 hl

/-- **Saved phases are the undone values**: on a trail assigning each variable once, saving its
literals gives each of their variables the value it had. -/
theorem Phases.get_save_of_mem (P : Phases) {M : Trail} (hM : (Trail.vars M).Nodup)
    {l : Literal ℕ} (hl : l ∈ Trail.lits M) : (P.save M).get l.1 = l.2 :=
  Phases.get_foldl_set_of_mem _ P
    (by simpa [Trail.lits, Trail.vars, List.map_map, Function.comp_def] using hM) hl

/-- **Other phases are kept**: saving the literals of a trail leaves the phase of every other
variable unchanged. -/
theorem Phases.get_save_of_not_mem (P : Phases) {M : Trail} {v : ℕ} (hv : v ∉ Trail.vars M) :
    (P.save M).get v = P.get v :=
  Phases.get_foldl_set_of_not_mem _ P
    (by simpa [Trail.lits, Trail.vars, List.map_map, Function.comp_def] using hv)

end Cslib.Algorithms.Lean.CDCL
