/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.System

/-! # Assignments indexed by variable

The value of each variable on the trail, in an array indexed by variable, as MiniSat's `assigns`:
whether a literal is true, or a variable assigned, is read in constant time instead of by a scan
of the trail. `Assign.Agrees A M` says that the array `A` holds exactly the literals of the trail
`M`. It survives assigning a new variable (`Assign.Agrees.cons`), and undoing the newest literals
of a trail, over variables not on the rest (`Assign.Agrees.drop`), as Backjump does; any trail
without repeated variables has an array agreeing with it (`Assign.agrees_ofTrail`).

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.Assign`: the value of each variable, if any.
* `Cslib.Algorithms.Lean.CDCL.Assign.holds`, `Cslib.Algorithms.Lean.CDCL.Assign.falsifies`: whether
  a literal is true, and whether a clause is false.
* `Cslib.Algorithms.Lean.CDCL.Assign.Agrees`: the array holds the literals of a trail.

## Main results

* `Cslib.Algorithms.Lean.CDCL.Assign.Agrees.holds_iff`,
  `Cslib.Algorithms.Lean.CDCL.Assign.Agrees.assigned_iff`: a literal holds when it is on the trail,
  and a variable is assigned when it is a variable of the trail.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL

/-- **An assignment indexed by variable**: the value of each variable, if it has one. -/
structure Assign where
  /-- The values, indexed by variable. -/
  vals : Array (Option Bool)

namespace Assign

/-- The value of the variable `v`, `none` past the end of the array. -/
def value (A : Assign) (v : ℕ) : Option Bool := A.vals.getD v none

/-- **Whether the literal `l` is true.** -/
def holds (A : Assign) (l : Literal ℕ) : Bool := A.value l.1 == some l.2

/-- **Whether the variable `v` is assigned.** -/
def assigned (A : Assign) (v : ℕ) : Bool := (A.value v).isSome

/-- Setting the value of `v` to `x`, growing the array if needed. -/
def set (A : Assign) (v : ℕ) (x : Option Bool) : Assign :=
  if v < A.vals.size then ⟨A.vals.set! v x⟩
  else ⟨(A.vals ++ Array.replicate (v - A.vals.size) none).push x⟩

/-- Assigning the literal `l`. -/
def assign (A : Assign) (l : Literal ℕ) : Assign := A.set l.1 (some l.2)

/-- Unassigning the variable `v`: an update within the array, which is left as it is if `v` is past
its end, since `v` then has no value. -/
def clear (A : Assign) (v : ℕ) : Assign := ⟨A.vals.setIfInBounds v none⟩

/-- Unassigning the variables `vs`. It never grows the array. -/
def unassign (A : Assign) (vs : List ℕ) : Assign := vs.foldl (fun A v => A.clear v) A

/-- Assigning the literals of a trail on top of `A`, oldest first so that the newest occurrence of
a variable wins, with a left fold, which uses constant stack. -/
def assignTrail (A : Assign) (M : Trail) : Assign := M.reverse.foldl (fun A e => A.assign e.lit) A

theorem assignTrail_cons (A : Assign) (e : Entry) (M : Trail) :
    A.assignTrail (e :: M) = (A.assignTrail M).assign e.lit := by
  simp [assignTrail, List.foldl_append]

/-- The assignment of the literals of a trail. -/
def ofTrail (M : Trail) : Assign := assignTrail ⟨#[]⟩ M

theorem ofTrail_nil : ofTrail [] = ⟨#[]⟩ := rfl

theorem ofTrail_cons (e : Entry) (M : Trail) : ofTrail (e :: M) = (ofTrail M).assign e.lit :=
  assignTrail_cons _ e M

theorem value_set (A : Assign) (v w : ℕ) (x : Option Bool) :
    (A.set v x).value w = if w = v then x else A.value w := by
  unfold set value
  split
  · rename_i hv
    simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds]
    by_cases hw : w = v
    · subst hw; simp [hv]
    · simp [hw, Ne.symm hw]
  · rename_i hv
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.size_append,
      Array.size_replicate, Array.getElem?_append, Array.getElem?_replicate]
    by_cases hw : w = v
    · subst hw; simp only [↓reduceIte]; split <;> first | rfl | omega
    · have : ¬ w = A.vals.size + (v - A.vals.size) := by omega
      simp only [hw, this, ↓reduceIte]
      by_cases hlt : w < A.vals.size
      · simp [hlt]
      · simp only [hlt, ↓reduceIte, Array.getElem?_eq_none (by omega : A.vals.size ≤ w)]
        split <;> rfl

theorem value_clear (A : Assign) (v w : ℕ) :
    (A.clear v).value w = if w = v then none else A.value w := by
  unfold clear value
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hw : w = v
  · subst hw; simp only [↓reduceIte]; split <;> rfl
  · simp [hw, Ne.symm hw]

theorem size_clear (A : Assign) (v : ℕ) : (A.clear v).vals.size = A.vals.size := by
  simp [clear]

theorem value_unassign (A : Assign) (vs : List ℕ) (w : ℕ) :
    (A.unassign vs).value w = if w ∈ vs then none else A.value w := by
  induction vs generalizing A with
  | nil => simp [unassign]
  | cons v vs ih =>
    change ((A.clear v).unassign vs).value w = _
    rw [ih, value_clear]
    by_cases h₁ : w ∈ vs <;> by_cases h₂ : w = v <;> simp [h₁, h₂]

/-- **Unassigning never grows the array.** -/
theorem size_unassign (A : Assign) (vs : List ℕ) : (A.unassign vs).vals.size = A.vals.size := by
  induction vs generalizing A with
  | nil => rfl
  | cons v vs ih =>
    change ((A.clear v).unassign vs).vals.size = _
    rw [ih, size_clear]

/-- **The array agrees with the trail** `M`: the variable `v` has the value `b` exactly when the
literal `(v, b)` is on `M`. -/
def Agrees (A : Assign) (M : Trail) : Prop := ∀ v b, A.value v = some b ↔ (v, b) ∈ Trail.lits M

variable {A : Assign} {M : Trail}

/-- **A literal holds exactly when it is on the trail.** -/
theorem Agrees.holds_iff (h : A.Agrees M) (l : Literal ℕ) :
    A.holds l = true ↔ l ∈ Trail.lits M := by
  simp only [holds, beq_iff_eq]
  exact h l.1 l.2

/-- **A variable is assigned exactly when it is a variable of the trail.** -/
theorem Agrees.assigned_iff (h : A.Agrees M) (v : ℕ) :
    A.assigned v = true ↔ v ∈ Trail.vars M := by
  simp only [assigned, Option.isSome_iff_exists]
  constructor
  · rintro ⟨b, hb⟩
    exact Trail.mem_vars_of_mem_lits ((h v b).1 hb)
  · intro hv
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
    exact ⟨e.lit.2, (h _ _).2 (List.mem_map.2 ⟨e, he, rfl⟩)⟩

theorem Agrees.not_assigned (h : A.Agrees M) {v : ℕ} (hv : v ∉ Trail.vars M) :
    A.assigned v = false := by
  rw [← Bool.not_eq_true, h.assigned_iff]; exact hv

theorem agrees_nil : (⟨#[]⟩ : Assign).Agrees [] := fun v b => by simp [value, Trail.lits]

/-- **Assigning a literal of an unassigned variable** keeps the agreement. -/
theorem Agrees.cons (h : A.Agrees M) {l : Literal ℕ} (hl : l.1 ∉ Trail.vars M) (d : Bool) :
    (A.assign l).Agrees (⟨l, d⟩ :: M) := by
  intro v b
  simp only [assign, value_set, Trail.lits, List.map_cons, List.mem_cons]
  change _ ↔ _ ∨ (v, b) ∈ Trail.lits M
  split
  · rename_i hv
    subst hv
    have : (l.1, b) ∉ Trail.lits M := fun h' => hl (Trail.mem_vars_of_mem_lits (l := (l.1, b)) h')
    obtain ⟨x, c⟩ := l
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at this ⊢
    constructor
    · rintro rfl; exact .inl rfl
    · rintro (rfl | h')
      · rfl
      · exact absurd h' this
  · rename_i hv
    rw [h v b]
    constructor
    · exact .inr
    · rintro (rfl | h')
      · exact absurd rfl hv
      · exact h'

/-- **Undoing the newest literals `N`** of a trail, over variables not on the rest `M₀`, by
unassigning their variables, keeps the agreement with the rest. -/
theorem Agrees.drop {N M₀ : Trail} (h : A.Agrees (N ++ M₀))
    (hdisj : ∀ v ∈ Trail.vars N, v ∉ Trail.vars M₀) : (A.unassign (Trail.vars N)).Agrees M₀ := by
  intro v b
  rw [value_unassign]
  have hlits : Trail.lits (N ++ M₀) = Trail.lits N ++ Trail.lits M₀ := List.map_append
  split
  · rename_i hv
    simp only [reduceCtorEq, false_iff]
    intro hm
    exact hdisj v hv (Trail.mem_vars_of_mem_lits hm)
  · rename_i hv
    rw [h v b, hlits, List.mem_append]
    constructor
    · rintro (h' | h')
      · exact absurd (Trail.mem_vars_of_mem_lits h') hv
      · exact h'
    · exact .inr

/-- **Whether the clause `c` is false**: every literal is false. -/
def falsifies (A : Assign) (c : Clause ℕ) : Bool := c.all fun l => A.holds l.negate

theorem Agrees.falsifies_iff (h : A.Agrees M) (c : Clause ℕ) :
    A.falsifies c = true ↔ Trail.Falsifies M c := by
  simp only [falsifies, List.all_eq_true, h.holds_iff]

/-- **Assigning a trail** without repeated variables on top of an empty array, one with no value
anywhere, gives an array agreeing with the trail. -/
theorem agrees_assignTrail {A : Assign} (hA : ∀ v, A.value v = none) :
    ∀ M : Trail, (Trail.vars M).Nodup → (A.assignTrail M).Agrees M
  | [], _ => fun v b => by simp [assignTrail, hA, Trail.lits]
  | e :: M, hnd => by
    simp only [Trail.vars, List.map_cons, List.nodup_cons] at hnd
    rw [assignTrail_cons]
    exact (agrees_assignTrail hA M hnd.2).cons hnd.1 e.decision

/-- Unassigning every variable that has a value leaves no value. -/
theorem value_unassign_eq_none {A : Assign} {vs : List ℕ} (h : ∀ v, v ∉ vs → A.value v = none)
    (v : ℕ) : (A.unassign vs).value v = none := by
  rw [value_unassign]
  split
  · rfl
  · exact h v ‹_›

/-- **The assignment of a trail** without repeated variables agrees with it. -/
theorem agrees_ofTrail (M : Trail) (hM : (Trail.vars M).Nodup) : (ofTrail M).Agrees M :=
  agrees_assignTrail (fun v => by simp [Assign.value]) M hM

end Assign

end Cslib.Algorithms.Lean.CDCL
