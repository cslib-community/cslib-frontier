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
  simp only [assigned, value_mark]
  split <;> simp_all

/-- An array in which exactly the variables `vs` are assigned. -/
def marks (vs : List ℕ) : Assign := (⟨#[]⟩ : Assign).mark vs

theorem assigned_marks (vs : List ℕ) (v : ℕ) : (marks vs).assigned v = true ↔ v ∈ vs := by
  rw [marks, assigned_mark]
  simp [assigned, value]

/-- **The assignment of a trail** without repeated variables agrees with it. -/
theorem agrees_ofTrail (M : Trail) (hM : (Trail.vars M).Nodup) : (ofTrail M).Agrees M :=
  agrees_assignTrail (fun v => by simp [Assign.value]) M hM

end Assign

/-! ### Removing repetitions in linear time -/

/-- The elements of `xs` not yet marked in `m` by their keys, in order, after `acc` reversed. -/
def dedupKeyGo {α : Type} (key : α → ℕ) : List α → Array Bool → List α → List α
  | [], _, acc => acc.reverse
  | x :: xs, m, acc =>
    if m.getD (key x) false then dedupKeyGo key xs m acc
    else dedupKeyGo key xs (m.setIfInBounds (key x) true) (x :: acc)

/-- **Removing repetitions** from `xs`, keeping first occurrences: an element is kept unless its
key is already marked, in an array sized to the greatest key. For keys computed in constant time
this takes time and space `O(xs.length + greatest key + 1)`: linear in the list when the keys are
dense, as they are for literals once `solveCompact` has renamed the variables to `0, …, k - 1`, but
not for sparse keys. With an injective key, the elements are those of `xs` (`mem_dedupKey`), each
once (`nodup_dedupKey`). -/
def dedupKey {α : Type} (key : α → ℕ) (xs : List α) : List α :=
  dedupKeyGo key xs (Array.replicate (xs.foldl (fun a x => max a (key x)) 0 + 1) false) []

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
      (∀ y, y ∈ dedupKeyGo key xs m acc ↔ y ∈ acc ∨ y ∈ xs) ∧ (dedupKeyGo key xs m acc).Nodup
  | [], m, acc, _, _, hnd => ⟨fun y => by simp [dedupKeyGo], by simpa [dedupKeyGo] using hnd⟩
  | x :: xs, m, acc, hsize, hm, hnd => by
    have hx : key x < m.size := hsize x List.mem_cons_self
    have hsize' : ∀ y ∈ xs, key y < m.size := fun y hy => hsize y (List.mem_cons_of_mem _ hy)
    rw [dedupKeyGo]
    by_cases hmark : m.getD (key x) false = true
    · rw [ite_eq_left hmark]
      obtain ⟨h₁, h₂⟩ := dedupKeyGo_spec hkey xs m acc hsize' hm hnd
      refine ⟨fun y => ?_, h₂⟩
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
      obtain ⟨h₁, h₂⟩ := dedupKeyGo_spec hkey xs _ (x :: acc)
        (fun y hy => by simpa using hsize' y hy) hm' hnd'
      refine ⟨fun y => ?_, h₂⟩
      rw [h₁]
      simp only [List.mem_cons]
      tauto

theorem dedupKey_spec {α : Type} {key : α → ℕ} (hkey : Function.Injective key) (xs : List α) :
    (∀ y, y ∈ dedupKey key xs ↔ y ∈ [] ∨ y ∈ xs) ∧ (dedupKey key xs).Nodup :=
  dedupKeyGo_spec hkey xs (Array.replicate (xs.foldl (fun a x => max a (key x)) 0 + 1) false) []
    (fun x hx => by simpa using (lt_foldl_max key xs 0).1 x hx)
    (fun y => by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, List.not_mem_nil,
        iff_false]
      split <;> simp)
    List.nodup_nil

/-- With an injective key, removing repetitions keeps the elements. -/
theorem mem_dedupKey {α : Type} {key : α → ℕ} (hkey : Function.Injective key) {xs : List α}
    {y : α} : y ∈ dedupKey key xs ↔ y ∈ xs := by
  simpa using (dedupKey_spec hkey xs).1 y

/-- With an injective key, removing repetitions leaves each element once. -/
theorem nodup_dedupKey {α : Type} {key : α → ℕ} (hkey : Function.Injective key) (xs : List α) :
    (dedupKey key xs).Nodup :=
  (dedupKey_spec hkey xs).2

/-- **The index of a literal**: `2 * v + 1` for `v` and `2 * v` for `¬v`. It keys the removal of
repeated literals (`dedupLits`) and indexes the watch lists. -/
def litKey (l : Literal ℕ) : ℕ := 2 * l.1 + if l.2 then 1 else 0

theorem litKey_injective : Function.Injective litKey := by
  intro ⟨v, x⟩ ⟨w, y⟩ h
  simp only [litKey] at h
  cases x <;> cases y <;> simp at h ⊢ <;> omega

/-- Removing repeated literals, in linear time. -/
abbrev dedupLits (c : Clause ℕ) : Clause ℕ := dedupKey litKey c

/-- Removing repeated literals keeps as many as `List.dedup`. -/
theorem length_dedupLits (c : Clause ℕ) : (dedupLits c).length = c.dedup.length :=
  ((List.perm_ext_iff_of_nodup (nodup_dedupKey litKey_injective c) (List.nodup_dedup c)).2
    fun _ => by rw [mem_dedupKey litKey_injective, List.mem_dedup]).length_eq

/-- Removing repeated variables, in linear time. -/
abbrev dedupVars (vs : List ℕ) : List ℕ := dedupKey id vs

end Cslib.Algorithms.Lean.CDCL
