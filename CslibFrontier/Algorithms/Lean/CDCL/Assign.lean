/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.System
public import CslibFrontier.Algorithms.WordRAM.ClauseCode
public import CslibFrontier.Foundations.Data.Array.SetGrow

/-! # Assignments indexed by variable

The value of each variable on the trail, in an array indexed by variable, as MiniSat's `assigns`:
whether a literal is true, or a variable assigned, is read in constant time instead of by a scan
of the trail. `Assign.Agrees A M` says that the array `A` holds exactly the literals of the trail
`M`. It survives assigning a new variable (`Assign.Agrees.cons`), and undoing the newest literals
of a trail, over variables not on the rest (`Assign.Agrees.drop`), as Backjump does; any trail
without repeated variables has an array agreeing with it (`Assign.agrees_ofTrail`).

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.Assign`: the value of each variable, if any.
* `Cslib.Algorithms.Lean.CDCL.Assign.holds`, `Cslib.Algorithms.Lean.CDCL.Assign.isFalse`,
  `Cslib.Algorithms.Lean.CDCL.Assign.falsifies`: whether a literal is true or false, and whether a
  clause is false.
* `Cslib.Algorithms.Lean.CDCL.Assign.Agrees`: the array holds the literals of a trail.

## Main results

* `Cslib.Algorithms.Lean.CDCL.Assign.Agrees.holds_iff`,
  `Cslib.Algorithms.Lean.CDCL.Assign.Agrees.isFalse_iff`,
  `Cslib.Algorithms.Lean.CDCL.Assign.Agrees.assigned_iff`: a literal holds when it is on the trail,
  is false when its negation is, and a variable is assigned when it is a variable of the trail.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL
open Cslib.Algorithms.WordRAM.ClauseCode (litCode litCodeBy litCode_injective)

/-- **An assignment indexed by variable**: the value of each variable, if it has one, stored as a
small number (`Assign.code`): `0` for none, `1` for `false`, `2` for `true`. Small numbers are
unboxed at run time, so reading a value touches no reference count. -/
structure Assign where
  /-- The codes of the values, indexed by variable. -/
  vals : Array ℕ

namespace Assign

/-- The code of a value: `0` for none, `1` for `false`, `2` for `true`. -/
@[inline] def code : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- The value of a code: `0` is none, `1` is `false`, and any other code `true`. Irreducible, so
that unification does not try to compute the code of an assignment it cannot evaluate; the kernel
still runs it. -/
@[irreducible] def decode : ℕ → Option Bool
  | 0 => none
  | 1 => some false
  | _ => some true

@[simp] theorem decode_zero : decode 0 = none := by unfold decode; rfl

@[simp] theorem decode_code (x : Option Bool) : decode (code x) = x := by
  unfold decode; rcases x with _ | _ | _ <;> rfl

/-- The value of the variable `v`, `none` past the end of the array. -/
def value (A : Assign) (v : ℕ) : Option Bool := decode (A.vals.getD v 0)

/-- **Whether the literal `l` is true**, read on the code of its variable. -/
@[inline] def holds (A : Assign) (l : Literal ℕ) : Bool :=
  match A.vals.getD l.1 0 with
  | 0 => false
  | 1 => !l.2
  | _ => l.2

/-- **Whether the literal `l` is false**: `holds` of its negation, without building the negation. -/
@[inline] def isFalse (A : Assign) (l : Literal ℕ) : Bool :=
  match A.vals.getD l.1 0 with
  | 0 => false
  | 1 => l.2
  | _ => !l.2

private theorem holds_eq_true (A : Assign) (l : Literal ℕ) :
    A.holds l = true ↔ A.value l.1 = some l.2 := by
  unfold holds value
  obtain ⟨v, x⟩ := l
  generalize A.vals.getD v 0 = c
  rcases c with _ | _ | c <;> cases x <;> simp [decode]

private theorem isFalse_eq_holds_negate (A : Assign) (l : Literal ℕ) :
    A.isFalse l = A.holds l.negate := by
  unfold isFalse holds
  obtain ⟨v, x⟩ := l
  simp only [Std.Sat.Literal.negate]
  generalize A.vals.getD v 0 = c
  rcases c with _ | _ | c <;> cases x <;> rfl

/-- **Whether the variable `v` is assigned.** -/
@[inline] def assigned (A : Assign) (v : ℕ) : Bool := A.vals.getD v 0 != 0

/-- A variable is assigned when it has a value. -/
theorem assigned_eq_isSome (A : Assign) (v : ℕ) : A.assigned v = (A.value v).isSome := by
  unfold assigned value decode
  generalize A.vals.getD v 0 = c
  rcases c with _ | _ | c <;> rfl

/-- Setting the value of `v` to `x`, growing the array if needed. -/
@[inline] def set (A : Assign) (v : ℕ) (x : Option Bool) : Assign := ⟨A.vals.setGrow v 0 (code x)⟩

/-- Assigning the literal `l`. -/
@[inline] def assign (A : Assign) (l : Literal ℕ) : Assign := A.set l.1 (some l.2)

/-- Unassigning the variable `v`: an update within the array, which is left as it is if `v` is past
its end, since `v` then has no value. -/
@[inline] def clear (A : Assign) (v : ℕ) : Assign := ⟨A.vals.setIfInBounds v 0⟩

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
  unfold value set
  rw [Array.getD_setGrow]
  split <;> simp

theorem assigned_set (A : Assign) (v w : ℕ) (x : Option Bool) :
    (A.set v x).assigned w = if w = v then x.isSome else A.assigned w := by
  simp only [assigned_eq_isSome, value_set]
  split <;> rfl

theorem value_clear (A : Assign) (v w : ℕ) :
    (A.clear v).value w = if w = v then none else A.value w := by
  unfold clear value
  rw [Array.getD_setIfInBounds_self]
  split <;> simp

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
  rw [holds_eq_true]
  exact h l.1 l.2

/-- **A literal is false exactly when its negation is on the trail.** -/
theorem Agrees.isFalse_iff (h : A.Agrees M) (l : Literal ℕ) :
    A.isFalse l = true ↔ l.negate ∈ Trail.lits M := by
  rw [isFalse_eq_holds_negate, h.holds_iff]

/-- **A variable is assigned exactly when it is a variable of the trail.** -/
theorem Agrees.assigned_iff (h : A.Agrees M) (v : ℕ) :
    A.assigned v = true ↔ v ∈ Trail.vars M := by
  simp only [assigned_eq_isSome, Option.isSome_iff_exists]
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
def falsifies (A : Assign) (c : Clause ℕ) : Bool := c.all fun l => A.isFalse l

theorem Agrees.falsifies_iff (h : A.Agrees M) (c : Clause ℕ) :
    A.falsifies c = true ↔ Trail.Falsifies M c := by
  simp only [falsifies, List.all_eq_true, h.isFalse_iff]

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

/-- **Marking the variables `vs`** in `A`: each is given the value `true`. Marking on top of an
array with no value, and clearing the same variables afterwards, reuses the array instead of
allocating one by the greatest variable. -/
def mark (A : Assign) (vs : List ℕ) : Assign := vs.foldl (fun A v => A.set v (some true)) A

theorem value_mark (A : Assign) (vs : List ℕ) (v : ℕ) :
    (A.mark vs).value v = if v ∈ vs then some true else A.value v := by
  induction vs generalizing A with
  | nil => simp [mark]
  | cons w vs ih =>
    change ((A.set w (some true)).mark vs).value v = _
    rw [ih, value_set]
    by_cases h₁ : v ∈ vs <;> by_cases h₂ : v = w <;> simp [h₁, h₂]

theorem assigned_mark (A : Assign) (vs : List ℕ) (v : ℕ) :
    (A.mark vs).assigned v = true ↔ v ∈ vs ∨ A.assigned v = true := by
  simp only [assigned_eq_isSome, value_mark]
  split <;> simp_all

/-- **Marking the variables of the literals `C`**: `mark` of their variables (`markLits_eq`),
without listing them. -/
def markLits (A : Assign) (C : List (Literal ℕ)) : Assign :=
  C.foldl (fun A y => A.set y.1 (some true)) A

theorem markLits_eq (A : Assign) (C : List (Literal ℕ)) : A.markLits C = A.mark (C.map Prod.fst) :=
  by rw [markLits, mark, List.foldl_map]

/-- **Unassigning the variables of the literals `C`**: `unassign` of their variables
(`unassignLits_eq`), without listing them. -/
def unassignLits (A : Assign) (C : List (Literal ℕ)) : Assign := C.foldl (fun A y => A.clear y.1) A

theorem unassignLits_eq (A : Assign) (C : List (Literal ℕ)) :
    A.unassignLits C = A.unassign (C.map Prod.fst) := by
  rw [unassignLits, unassign, List.foldl_map]

/-- An array in which exactly the variables `vs` are assigned. It is sized once for the greatest
of them, so that marking never grows it. -/
def marks (vs : List ℕ) : Assign := (⟨Array.replicate (vs.foldl max 0 + 1) 0⟩ : Assign).mark vs

theorem assigned_marks (vs : List ℕ) (v : ℕ) : (marks vs).assigned v = true ↔ v ∈ vs := by
  rw [marks, assigned_mark]
  simp only [assigned, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> simp

/-- **The assignment of a trail** without repeated variables agrees with it. -/
theorem agrees_ofTrail (M : Trail) (hM : (Trail.vars M).Nodup) : (ofTrail M).Agrees M :=
  agrees_assignTrail (fun v => by simp [Assign.value]) M hM

end Assign

/-! ### Removing repetitions in linear time -/

/-- The elements of `xs` not yet marked in `m` by their keys, in order, after `acc` reversed, and
the marks with those elements marked too. A caller that keeps its marks between lists reads both
(`dedupWith`); `dedupKey` reads the first. -/
@[specialize] def dedupKeyGo {α : Type} (key : α → ℕ) :
    List α → Array Bool → List α → List α × Array Bool
  | [], m, acc => (acc.reverse, m)
  | x :: xs, m, acc =>
    if m.getD (key x) false then dedupKeyGo key xs m acc
    else dedupKeyGo key xs (m.setIfInBounds (key x) true) (x :: acc)

/-- **Removing repetitions** from `xs`, keeping first occurrences: an element is kept unless its
key is already marked, in an array sized to the greatest key. For keys computed in constant time
this takes time and space `O(xs.length + greatest key + 1)`: linear in the list when the keys are
dense, as they are for literals once `solveCompact` has renamed the variables to `0, …, k - 1`, but
not for sparse keys. With an injective key, the elements are those of `xs` (`mem_dedupKey`), each
once (`nodup_dedupKey`). -/
@[specialize] def dedupKey {α : Type} (key : α → ℕ) (xs : List α) : List α :=
  (dedupKeyGo key xs (Array.replicate (xs.foldl (fun a x => max a (key x)) 0 + 1) false) []).1

theorem lt_foldl_max {α : Type} (key : α → ℕ) :
    ∀ (xs : List α) (a : ℕ), (∀ x ∈ xs, key x < xs.foldl (fun a x => max a (key x)) a + 1) ∧
      a ≤ xs.foldl (fun a x => max a (key x)) a
  | [], a => ⟨by simp, le_rfl⟩
  | x :: xs, a => by
    obtain ⟨h₁, h₂⟩ := lt_foldl_max key xs (max a (key x))
    refine ⟨fun y hy => ?_, le_trans (le_max_left _ _) h₂⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · have := le_trans (le_max_right a (key y)) h₂
      simp only [List.foldl_cons]; omega
    · exact h₁ y hy

theorem dedupKeyGo_spec {α : Type} {key : α → ℕ} (hkey : Function.Injective key) :
    ∀ (xs : List α) (m : Array Bool) (acc : List α), (∀ x ∈ xs, key x < m.size) →
      (∀ y, m.getD (key y) false = true ↔ y ∈ acc) → acc.Nodup →
      (∀ y, y ∈ (dedupKeyGo key xs m acc).1 ↔ y ∈ acc ∨ y ∈ xs) ∧
        (dedupKeyGo key xs m acc).1.Nodup ∧
        ∀ y, (dedupKeyGo key xs m acc).2.getD (key y) false = true ↔
          y ∈ (dedupKeyGo key xs m acc).1
  | [], m, acc, _, hm, hnd =>
    ⟨fun y => by simp [dedupKeyGo], by simpa [dedupKeyGo] using hnd,
      fun y => by simpa [dedupKeyGo] using hm y⟩
  | x :: xs, m, acc, hsize, hm, hnd => by
    have hx : key x < m.size := hsize x List.mem_cons_self
    have hsize' : ∀ y ∈ xs, key y < m.size := fun y hy => hsize y (List.mem_cons_of_mem _ hy)
    rw [dedupKeyGo]
    by_cases hmark : m.getD (key x) false = true
    · rw [ite_eq_left hmark]
      obtain ⟨h₁, h₂, h₃⟩ := dedupKeyGo_spec hkey xs m acc hsize' hm hnd
      refine ⟨fun y => ?_, h₂, h₃⟩
      rw [h₁]
      have hxa : x ∈ acc := (hm x).1 hmark
      simp only [List.mem_cons]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl h
        · exact .inl hxa
        · exact .inr h
    · rw [ite_eq_right hmark]
      have hm' : ∀ y, (m.setIfInBounds (key x) true).getD (key y) false = true ↔ y ∈ x :: acc :=
        fun y => by
          simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, List.mem_cons]
          by_cases hyx : key x = key y
          · have := hkey hyx
            subst this
            simp [hx]
          · rw [ite_eq_right hyx]
            have := hm y
            simp only [Array.getD_eq_getD_getElem?] at this
            rw [this]
            exact ⟨.inr, fun h => h.resolve_left fun h' => hyx (h' ▸ rfl)⟩
      have hnd' : (x :: acc).Nodup := List.nodup_cons.2 ⟨fun h => hmark ((hm x).2 h), hnd⟩
      obtain ⟨h₁, h₂, h₃⟩ := dedupKeyGo_spec hkey xs _ (x :: acc)
        (fun y hy => by simpa using hsize' y hy) hm' hnd'
      refine ⟨fun y => ?_, h₂, h₃⟩
      rw [h₁]
      simp only [List.mem_cons]
      tauto

theorem dedupKey_spec {α : Type} {key : α → ℕ} (hkey : Function.Injective key) (xs : List α) :
    (∀ y, y ∈ dedupKey key xs ↔ y ∈ [] ∨ y ∈ xs) ∧ (dedupKey key xs).Nodup :=
  (dedupKeyGo_spec hkey xs (Array.replicate (xs.foldl (fun a x => max a (key x)) 0 + 1) false) []
    (fun x hx => by simpa using (lt_foldl_max key xs 0).1 x hx)
    (fun y => by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, List.not_mem_nil,
        iff_false]
      split <;> simp)
    List.nodup_nil).imp_right And.left

/-- With an injective key, removing repetitions keeps the elements. -/
theorem mem_dedupKey {α : Type} {key : α → ℕ} (hkey : Function.Injective key) {xs : List α}
    {y : α} : y ∈ dedupKey key xs ↔ y ∈ xs := by
  simpa using (dedupKey_spec hkey xs).1 y

/-- With an injective key, removing repetitions leaves each element once. -/
theorem nodup_dedupKey {α : Type} {key : α → ℕ} (hkey : Function.Injective key) (xs : List α) :
    (dedupKey key xs).Nodup :=
  (dedupKey_spec hkey xs).2

theorem dedupKeyGo_of_nodup {α : Type} {key : α → ℕ} (hkey : Function.Injective key) :
    ∀ (xs : List α) (m : Array Bool) (acc : List α), xs.Nodup →
      (∀ x ∈ xs, m.getD (key x) false = false) → (dedupKeyGo key xs m acc).1 = acc.reverse ++ xs
  | [], _, _, _, _ => by simp [dedupKeyGo]
  | x :: xs, m, acc, hnd, hm => by
    rw [dedupKeyGo, ite_eq_right (by simp [hm x List.mem_cons_self])]
    rw [dedupKeyGo_of_nodup hkey xs _ (x :: acc) (List.nodup_cons.1 hnd).2 fun y hy => ?_]
    · simp
    · have hne : key x ≠ key y := fun h => (List.nodup_cons.1 hnd).1 (hkey h ▸ hy)
      have := hm y (List.mem_cons_of_mem _ hy)
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at this ⊢
      rw [ite_eq_right hne]
      exact this

/-- **A list without repetitions is its own removal of repetitions**, with an injective key. -/
theorem dedupKey_of_nodup {α : Type} {key : α → ℕ} (hkey : Function.Injective key) {xs : List α}
    (h : xs.Nodup) : dedupKey key xs = xs := by
  unfold dedupKey
  rw [dedupKeyGo_of_nodup hkey xs _ [] h fun x _ => ?_]
  · simp
  · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> simp

/-! The *key* of a literal is its word code `Cslib.Algorithms.WordRAM.ClauseCode.litCode`:
`2 * v + 1` for `v` and `2 * v` for `¬v`. It keys the removal of repeated literals (`dedupLits`),
indexes the watch lists, and is how the watch store holds literals. -/

/-- The key of the negation of `l`, computed without building the negation. -/
def negKey (l : Literal ℕ) : ℕ := 2 * l.1 + if l.2 then 0 else 1

theorem litCode_negate (l : Literal ℕ) : litCode l.negate = negKey l := by
  obtain ⟨v, b⟩ := l
  cases b <;> rfl

/-- **The literal of a key**: the variable is the key divided by two, and the literal is positive
when the key is odd. It inverts `litCode` (`litOfKey_litCode`, `litCode_litOfKey`), so every number
is the key of exactly one literal. -/
@[inline] def litOfKey (n : ℕ) : Literal ℕ := (n / 2, n % 2 == 1)

@[simp] theorem litOfKey_litCode (l : Literal ℕ) : litOfKey (litCode l) = l := by
  obtain ⟨v, b⟩ := l
  cases b
  · simp only [litOfKey, litCodeBy, id, Bool.toNat_false]
    ext <;> simp
  · simp only [litOfKey, litCodeBy, id, Bool.toNat_true]
    ext <;> simp
    omega

@[simp] theorem litCode_litOfKey (n : ℕ) : litCode (litOfKey n) = n := by
  simp only [litOfKey, litCodeBy, id]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

/-- The key of the negation of a literal is its key with the low bit flipped. -/
theorem litOfKey_negKey (l : Literal ℕ) : litOfKey (negKey l) = l.negate := by
  rw [← litCode_negate, litOfKey_litCode]

/-- **Whether the literal of the key `c` is true**, read on the key, without building the
literal. -/
@[inline] def Assign.holdsKey (A : Assign) (c : ℕ) : Bool :=
  match A.vals.getD (c / 2) 0 with
  | 0 => false
  | 1 => !(c % 2 == 1)
  | _ => c % 2 == 1

/-- **Whether the literal of the key `c` is false**, read on the key. -/
@[inline] def Assign.isFalseKey (A : Assign) (c : ℕ) : Bool :=
  match A.vals.getD (c / 2) 0 with
  | 0 => false
  | 1 => c % 2 == 1
  | _ => !(c % 2 == 1)

theorem Assign.holdsKey_eq (A : Assign) (c : ℕ) : A.holdsKey c = A.holds (litOfKey c) := rfl

theorem Assign.isFalseKey_eq (A : Assign) (c : ℕ) : A.isFalseKey c = A.isFalse (litOfKey c) := rfl

/-- Removing repeated literals, in linear time. -/
abbrev dedupLits (c : Clause ℕ) : Clause ℕ := dedupKey litCode c

/-- Removing repeated literals keeps as many as `List.dedup`. -/
theorem length_dedupLits (c : Clause ℕ) : (dedupLits c).length = c.dedup.length :=
  ((List.perm_ext_iff_of_nodup (nodup_dedupKey litCode_injective c) (List.nodup_dedup c)).2
    fun _ => by rw [mem_dedupKey litCode_injective, List.mem_dedup]).length_eq

/-- Removing repeated variables, in linear time. -/
abbrev dedupVars (vs : List ℕ) : List ℕ := dedupKey id vs

end Cslib.Algorithms.Lean.CDCL
