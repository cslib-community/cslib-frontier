/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.Assign
public import CslibFrontier.Algorithms.Lean.CDCL.Heap
public import Mathlib.Data.List.MinMax

/-! # VSIDS: variable activities for the CDCL solver

MiniSat's branching heuristic, *variable state independent decaying sum*. Every variable has an
*activity*. After each conflict, the variables of the clauses met by the conflict analysis are
*bumped*: the current *increment* is added to their activity. These are all the variables of the
conflict clause and of the reasons resolved on, including variables assigned at decision level
`0`. MiniSat bumps a variable only when it is assigned above level `0` (`level(var(q)) > 0` in
`analyze`), so this rule is a variant of MiniSat's. The increment then becomes `inc + inc / 19`,
with integer division: at most the factor `1 / 0.95` (MiniSat's `var_decay = 0.95`), so older bumps
weigh exponentially less. The solver decides an unassigned variable of greatest activity.

Activities and the increment are natural numbers, so the kernel can run the solver. The decay
step sets the increment to `inc + inc / 19`, with integer division, in place of MiniSat's
floating-point `inc / 0.95`. As in MiniSat, when an activity reaches a limit (here `2 ^ 60`, tested
by a shift so that no large literal is built at run time) all activities and the increment are
scaled down (here by `2 ^ 20`, with truncation). The increment starts at `2 ^ 40`. An activity is
then below the limit plus the increment, and the increment at most `20 / 19` times the limit, so
every value stays below `2 ^ 62`: compiled code keeps them as
unboxed machine integers, with no arbitrary-precision arithmetic. The truncations can make the
increment grow less than by `1 / 0.95` and turn different activities into ties (an activity more
than about `2 ^ 60` times smaller than the increment becomes `0`), so decisions can differ from
those of floating-point activities.

The same structure, indexed by clause number and decaying by `1 / 0.999`, holds MiniSat's clause
activities.

**The variable order** (`VarOrder`, MiniSat's `order_heap`) finds the decision variable without
scanning the variables for the greatest activity: a binary max-heap of variables, ordered by
activity and then by variable (`Activity.keyOrd`), with the position of each variable in it
(MiniSat's `indices`). As in MiniSat, bumping a variable in the heap moves it up
(`VarOrder.increase`), a variable undone by a backjump is inserted unless it is in the heap
(`VarOrder.addAll`, MiniSat's `insertVarOrder`), and popping removes assigned variables from the
top until it finds an unassigned one (`VarOrder.pop`, MiniSat's `pickBranchLit`). The sifting
functions compute Batteries' `heapifyUp` and `heapifyDown` (`VarOrder.siftUp_fst`,
`VarOrder.siftDown_fst`), updating the positions as they swap, so that Batteries' proofs apply.
Scaling the activities down can turn different activities into ties, which the order breaks by
variable, so the heap is then rebuilt (`VarOrder.rebuild`); scaling is rare, once every few hundred
conflicts.

The invariant (`VarOrder.Inv`) asks that the heap be well formed in the order of the current
activities, that the positions be consistent with it (`VarOrder.PosOK`), that every variable have
room in the position array, and that every unassigned variable admitted by the solver be in the
heap. Bumping a variable raises its activity alone, so moving it up restores the heap
(`Batteries.BinaryHeap.topDown_heapifyUp_of_isGE`). Under the invariant, the variable popped has the
greatest activity among the unassigned variables (`VarOrder.pop_spec`), and among ties the greatest
variable.

The choice of variable does not affect correctness: the solver only needs an unassigned variable
of the database, or the fact that there is none. `Activity.pick` scans for one of greatest
activity (`Activity.pick_some`, `Activity.pick_none`, `Activity.pick_max`); the solver uses it,
with every activity `0`, when VSIDS is off. With VSIDS, the order runs out only when every
admitted variable is assigned (`VarOrder.pop_none`).

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.Activity`: activities and the increment.
* `Cslib.Algorithms.Lean.CDCL.Activity.bump`: bumping the variables met by an analysis, then
  decaying.
* `Cslib.Algorithms.Lean.CDCL.Activity.grow`: making room for more indices.
* `Cslib.Algorithms.Lean.CDCL.Activity.pick`: an unassigned variable of greatest activity.
* `Cslib.Algorithms.Lean.CDCL.VarOrder`, `Cslib.Algorithms.Lean.CDCL.VarOrder.Inv`: the variable
  order and its invariant.
* `Cslib.Algorithms.Lean.CDCL.VarOrder.insert`, `Cslib.Algorithms.Lean.CDCL.VarOrder.addAll`:
  inserting variables not in the heap.
* `Cslib.Algorithms.Lean.CDCL.VarOrder.bump`: bumping the variables met by an analysis, in the
  activities and in the heap.
* `Cslib.Algorithms.Lean.CDCL.VarOrder.pop`: popping the decision variable.

## Main results

* `Cslib.Algorithms.Lean.CDCL.Activity.pick_some`, `Cslib.Algorithms.Lean.CDCL.Activity.pick_none`,
  `Cslib.Algorithms.Lean.CDCL.Activity.pick_max`: what `pick` returns.
* `Cslib.Algorithms.Lean.CDCL.Activity.get_bump_le`: bumping does not raise the other activities.
* `Cslib.Algorithms.Lean.CDCL.VarOrder.bump_fst`: bumping in the order bumps the activities as
  `Activity.bump` does.
* `Cslib.Algorithms.Lean.CDCL.VarOrder.bump_spec`,
  `Cslib.Algorithms.Lean.CDCL.VarOrder.addAll_spec`: bumping and inserting keep the heap well formed
  and the positions consistent.
* `Cslib.Algorithms.Lean.CDCL.VarOrder.pop_spec`: the variable popped has the greatest activity
  among the unassigned variables, and the order keeps its invariant.
* `Cslib.Algorithms.Lean.CDCL.VarOrder.pop_none`: with enough fuel, popping finds no variable
  only by emptying the heap.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL

/-- **Variable activities**: a score for each variable, by index, and the current increment. -/
structure Activity where
  /-- The activity of each variable; variables past the end have activity `0`. -/
  score : Array ℕ
  /-- The amount added to the activity of a bumped variable. -/
  inc : ℕ

/-- The initial activities of the variables below `n`: all `0`, with increment `2 ^ 40`. -/
def Activity.init (n : ℕ) : Activity := ⟨Array.replicate n 0, 2 ^ 40⟩

/-- The activity of the variable `v`. -/
@[inline] def Activity.get (A : Activity) (v : ℕ) : ℕ := A.score.getD v 0

/-- **Bumping** `v`: its activity grows by the increment; if it reaches `2 ^ 60`, every activity
and the increment are divided by `2 ^ 20`. The activities are an array indexed by variable: for
`v` beyond its end, `Array.modify` leaves it unchanged, so bumping `v` does nothing and its
activity stays `0`. The solver's variables are all within the array (`WExec.init` sizes it by the
largest variable of the formula). -/
def Activity.bumpVar (A : Activity) (v : ℕ) : Activity :=
  let score := A.score.modify v (· + A.inc)
  if score.getD v 0 >>> 60 != 0 then ⟨score.map (· >>> 20), A.inc >>> 20⟩
  else ⟨score, A.inc⟩

/-- **After a conflict**: bump each variable met by the analysis once, then set the increment to
`inc + inc / decay`, with integer division (by default `decay = 19`): at most the factor
`1 + 1 / decay` (`1 / 0.95` by default), and less by the truncation. -/
def Activity.bump (A : Activity) (vs : List ℕ) (decay : ℕ := 19) : Activity :=
  let A := (dedupVars vs).foldl Activity.bumpVar A
  ⟨A.score, A.inc + A.inc / decay⟩

/-- **Bumping each index of `is`**, which has no repetitions, then growing the increment as
`Activity.bump` does. For the activities of clauses, whose numbers grow with the run: removing
repetitions in linear time would cost as much as the greatest number. -/
def Activity.bumpEach (A : Activity) (is : List ℕ) (decay : ℕ := 19) : Activity :=
  let A := is.foldl Activity.bumpVar A
  ⟨A.score, A.inc + A.inc / decay⟩

/-- The activities with room for the indices below `n`, the new ones `0`. -/
def Activity.grow (A : Activity) (n : ℕ) : Activity :=
  if A.score.size < n then ⟨A.score ++ Array.replicate (n - A.score.size) 0, A.inc⟩ else A

/-- **The decision variable**: a variable of `vs` unassigned in `asg`, of greatest activity, the
first one among ties. -/
def Activity.pick (A : Activity) (asg : Assign) (vs : List ℕ) : Option ℕ :=
  (vs.filter fun x => !asg.assigned x).argmax A.get

variable {asg : Assign} {M : Trail}

theorem Activity.pick_some {A : Activity} (hasg : asg.Agrees M) {vs : List ℕ} {x : ℕ}
    (h : A.pick asg vs = some x) : x ∈ vs ∧ x ∉ Trail.vars M := by
  have hm : x ∈ (vs.filter fun x => !asg.assigned x).argmax A.get := by
    change x ∈ A.pick asg vs; rw [h]; rfl
  have := List.mem_filter.1 (List.argmax_mem hm)
  refine ⟨this.1, fun hx => ?_⟩
  have := this.2
  rw [(hasg.assigned_iff x).2 hx] at this
  exact absurd this (by decide)

theorem Activity.pick_none {A : Activity} (hasg : asg.Agrees M) {vs : List ℕ}
    (h : A.pick asg vs = none) : ∀ x ∈ vs, x ∈ Trail.vars M := by
  intro x hx
  have := List.argmax_eq_none.1 h
  by_contra hxM
  have : x ∈ vs.filter fun x => !asg.assigned x :=
    List.mem_filter.2 ⟨hx, by simp [hasg.not_assigned hxM]⟩
  simp_all

/-- **The chosen variable has the greatest activity** among the unassigned variables of `vs`. -/
theorem Activity.pick_max {A : Activity} (hasg : asg.Agrees M) {vs : List ℕ} {x : ℕ}
    (h : A.pick asg vs = some x) {y : ℕ} (hy : y ∈ vs) (hyM : y ∉ Trail.vars M) :
    A.get y ≤ A.get x :=
  List.le_of_mem_argmax (List.mem_filter.2 ⟨hy, by simp [hasg.not_assigned hyM]⟩)
    (show x ∈ A.pick asg vs by rw [h]; rfl)

/-- Bumping another variable does not raise the activity of `u`. -/
theorem Activity.get_bumpVar_le {A : Activity} {u v : ℕ} (huv : u ≠ v) :
    (A.bumpVar v).get u ≤ A.get u := by
  have hmod : (A.score.modify v (· + A.inc)).getD u 0 = A.score.getD u 0 := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Ne.symm huv, ↓reduceIte]
  unfold Activity.bumpVar Activity.get
  dsimp only
  split
  · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map] at hmod ⊢
    cases h : (A.score.modify v (· + A.inc))[u]? with
    | none => simp
    | some x =>
      rw [h] at hmod
      simp only [Option.map_some, Option.getD_some] at hmod ⊢
      rw [← hmod]
      exact Nat.shiftRight_le x 20
  · exact hmod.le

theorem Activity.get_foldl_bumpVar_le {v : ℕ} :
    ∀ {A : Activity} {vs : List ℕ}, v ∉ vs → (vs.foldl Activity.bumpVar A).get v ≤ A.get v
  | _, [], _ => le_rfl
  | _, u :: us, hv => by
    simp only [List.mem_cons, not_or] at hv
    exact (Activity.get_foldl_bumpVar_le hv.2).trans (Activity.get_bumpVar_le hv.1)

/-- **Bumping does not raise the activity of the variables not bumped.** -/
theorem Activity.get_bump_le {A : Activity} {vs : List ℕ} {d : ℕ} {v : ℕ} (hv : v ∉ vs) :
    (A.bump vs d).get v ≤ A.get v :=
  Activity.get_foldl_bumpVar_le fun h => hv ((mem_dedupKey Function.injective_id).1 h)

/-! ### The variable order -/

/-- An entry of the variable order: a variable and the activity it is keyed by. (`variable` is a
keyword, so the field is `var`.) -/
structure OrderKey where
  /-- The activity the entry is keyed by. -/
  activity : ℕ
  /-- The variable. -/
  var : ℕ
  deriving DecidableEq

/-- An entry as a pair, activity first. -/
def OrderKey.toPair (k : OrderKey) : ℕ × ℕ := (k.activity, k.var)

section
attribute [local instance] lexOrd

/-- Entries compare by activity, then by variable: the lexicographic order on `toPair`, written
out so that comparing builds no pairs at run time. -/
instance : Ord OrderKey :=
  ⟨fun a b => (compare a.activity b.activity).then (compare a.var b.var)⟩

private theorem OrderKey.compare_eq (a b : OrderKey) :
    compare a b = compare a.toPair b.toPair := rfl

instance : Std.TransOrd OrderKey :=
  have h : Std.TransOrd (ℕ × ℕ) := inferInstance
  { eq_swap := fun {a b} => by
      rw [OrderKey.compare_eq, OrderKey.compare_eq]; exact h.eq_swap
    isLE_trans := fun {a b c} hab hbc => by
      rw [OrderKey.compare_eq] at hab hbc ⊢; exact h.isLE_trans hab hbc }

end

/-- **The order of the variables by the activities `A`**: by activity, then by variable, the order
of their entries `OrderKey.mk (A.get v) v`. A total order, so that the variable of the variable
order with the greatest activity, the greatest variable among ties, is well defined. -/
@[instance_reducible] def Activity.keyOrd (A : Activity) : Ord ℕ :=
  ⟨fun a b => compare (OrderKey.mk (A.get a) a) (OrderKey.mk (A.get b) b)⟩

instance Activity.transOrd (A : Activity) : @Std.TransOrd ℕ A.keyOrd :=
  have h : Std.TransOrd OrderKey := inferInstance
  @Std.TransCmp.mk ℕ _
    ⟨fun {a b} => h.eq_swap (a := OrderKey.mk (A.get a) a) (b := OrderKey.mk (A.get b) b)⟩
    (fun {a b c} => h.isLE_trans (a := OrderKey.mk (A.get a) a) (b := OrderKey.mk (A.get b) b)
      (c := OrderKey.mk (A.get c) c))

/-- Whether `a` comes before `b` in the order of the activities `A`: a lower activity, or the same
and a smaller variable. -/
@[inline] def Activity.below (A : Activity) (a b : ℕ) : Bool :=
  let x := A.get a
  let y := A.get b
  x < y || (x == y && a < b)

theorem Activity.below_iff (A : Activity) (a b : ℕ) :
    A.below a b = true ↔ A.get a < A.get b ∨ (A.get a = A.get b ∧ a < b) := by
  simp [Activity.below]

theorem Activity.isLT_compare (A : Activity) (a b : ℕ) :
    (@compare ℕ A.keyOrd a b).isLT = A.below a b := by
  change ((compare (A.get a) (A.get b)).then (compare a b)).isLT = _
  rcases Nat.lt_trichotomy (A.get a) (A.get b) with h | h | h
  · simp [Nat.compare_eq_lt.2 h, Ordering.then, Activity.below, h]
  · rcases Nat.lt_trichotomy a b with h' | h' | h'
    · simp [Nat.compare_eq_lt.2 h', Ordering.then, Activity.below, h, h']
    · subst h'; simp [Ordering.then, Activity.below]
    · simp [Nat.compare_eq_gt.2 h', Ordering.then, Activity.below, h, Nat.not_lt.2 h'.le]
  · simp only [Nat.compare_eq_gt.2 h, Ordering.then, Activity.below, Ordering.isLT_gt,
      Bool.false_eq, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_imp,
      beq_iff_eq]
    omega

/-- In the order of the activities `A`, `a` is at least `b` when `b` has a lower activity, or the
same and a variable at most `a`. -/
theorem Activity.isGE_compare_iff (A : Activity) (a b : ℕ) :
    (@compare ℕ A.keyOrd a b).isGE ↔ A.get b < A.get a ∨ (A.get b = A.get a ∧ b ≤ a) := by
  have : (@compare ℕ A.keyOrd a b).isGE = !(@compare ℕ A.keyOrd a b).isLT := by
    cases @compare ℕ A.keyOrd a b <;> rfl
  rw [this, Activity.isLT_compare, Bool.not_eq_true', ← Bool.not_eq_true, Activity.below_iff]
  omega

/-! #### Positions -/

/-- The value at `v` after setting `x` to `b`: `b` if `x = v` within the array. -/
private theorem VarOrder.getD_setIfInBounds (p : Array ℕ) (x b v : ℕ) :
    (p.setIfInBounds x b).getD v 0 = if x = v ∧ v < p.size then b else p.getD v 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : x = v <;> by_cases hv : v < p.size <;> simp [h, hv]

private theorem VarOrder.lt_size_of_getD_ne {p : Array ℕ} {v : ℕ} (h : p.getD v 0 ≠ 0) :
    v < p.size := by
  by_contra hv
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hv)] at h

/-- **Positions consistent with a heap array** `a` (MiniSat's `indices`): `p` holds at each
element of `a` its index plus one, and `0` at every other variable. -/
structure VarOrder.PosOK (a p : Array ℕ) : Prop where
  pos : ∀ i (h : i < a.size), p.getD a[i] 0 = i + 1
  get : ∀ v i, p.getD v 0 = i + 1 → ∃ h : i < a.size, a[i] = v

namespace VarOrder.PosOK

variable {a p : Array ℕ}

theorem lt_size (h : PosOK a p) {v : ℕ} (hv : v ∈ a) : v < p.size := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
  exact lt_size_of_getD_ne (by rw [h.pos i hi]; omega)

theorem mem_iff (h : PosOK a p) {v : ℕ} : v ∈ a ↔ p.getD v 0 ≠ 0 := by
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
    rw [h.pos i hi]; omega
  · intro hv
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hv
    obtain ⟨hlt, hget⟩ := h.get v i hi
    exact hget ▸ Array.getElem_mem hlt

theorem inj (h : PosOK a p) {i j : ℕ} (hi : i < a.size) (hj : j < a.size) (he : a[i] = a[j]) :
    i = j := by
  have := h.pos i hi
  rw [he, h.pos j hj] at this
  omega

/-- Empty positions for the empty heap. -/
theorem empty (n : ℕ) : PosOK #[] (Array.replicate n 0) where
  pos _ h := absurd h (by simp)
  get v i h := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h
    split at h <;> simp at h

end VarOrder.PosOK

/-- The positions after swapping the elements `x` at `i` and `y` at `j`. -/
def VarOrder.swapPos (p : Array ℕ) (x y i j : ℕ) : Array ℕ :=
  (p.setIfInBounds x (j + 1)).setIfInBounds y (i + 1)

theorem VarOrder.size_swapPos (p : Array ℕ) (x y i j : ℕ) : (swapPos p x y i j).size = p.size := by
  simp [swapPos]

theorem VarOrder.PosOK.swap {a p : Array ℕ} (h : PosOK a p) {i j : ℕ} (hi : i < a.size)
    (hj : j < a.size) : PosOK (a.swap i j hi hj) (swapPos p a[i] a[j] i j) := by
  have hx := h.lt_size (Array.getElem_mem hi)
  have hy := h.lt_size (Array.getElem_mem hj)
  constructor
  · intro k hk
    simp only [Array.size_swap] at hk
    rw [Array.getElem_swap]
    simp only [swapPos, getD_setIfInBounds, Array.size_setIfInBounds]
    by_cases hki : k = i
    · simp only [hki, ↓reduceIte]
      simp [hy]
    by_cases hkj : k = j
    · have hji : ¬ j = i := hkj ▸ hki
      have hne : ¬ a[j] = a[i] := fun e => hji (h.inj hj hi e)
      simp only [hkj, hji, ↓reduceIte]
      simp [hne, hx]
    · have h1 : ¬ a[i] = a[k] := fun e => hki (h.inj hk hi e.symm)
      have h2 : ¬ a[j] = a[k] := fun e => hkj (h.inj hk hj e.symm)
      simp only [hki, hkj, ↓reduceIte, h1, h2, false_and]
      exact h.pos k hk
  · intro v k hv
    simp only [swapPos, getD_setIfInBounds, Array.size_setIfInBounds] at hv
    split_ifs at hv with hvy hvx
    · obtain rfl : k = i := by omega
      refine ⟨by simp only [Array.size_swap]; omega, ?_⟩
      rw [Array.getElem_swap]
      simp [hvy.1]
    · obtain rfl : k = j := by omega
      have hji : ¬ k = i := fun e => hvy ⟨e ▸ hvx.1, hvx.2⟩
      refine ⟨by simp only [Array.size_swap]; omega, ?_⟩
      rw [Array.getElem_swap]
      simp [hji, hvx.1]
    · obtain ⟨hk, hget⟩ := h.get v k hv
      have hvp : v < p.size := lt_size_of_getD_ne (by rw [hv]; omega)
      have hki : ¬ k = i := fun e => hvx ⟨e ▸ hget, hvp⟩
      have hkj : ¬ k = j := fun e => hvy ⟨e ▸ hget, hvp⟩
      refine ⟨by simp only [Array.size_swap]; omega, ?_⟩
      rw [Array.getElem_swap]
      simp [hki, hkj, hget]

theorem VarOrder.PosOK.push {a p : Array ℕ} (h : PosOK a p) {v : ℕ} (hv : v < p.size)
    (h0 : p.getD v 0 = 0) : PosOK (a.push v) (p.setIfInBounds v (a.size + 1)) := by
  constructor
  · intro k hk
    rw [Array.getElem_push, getD_setIfInBounds]
    split
    · rename_i hk'
      have : ¬ v = a[k] := fun e => by have := h.pos k hk'; rw [← e, h0] at this; omega
      simp [this, h.pos k hk']
    · rename_i hk'
      simp only [Array.size_push] at hk
      simp [hv]; omega
  · intro w k hw
    rw [getD_setIfInBounds] at hw
    simp only [Array.size_push]
    by_cases hwv : v = w ∧ w < p.size
    · simp only [hwv, and_self, ↓reduceIte, Nat.add_right_cancel_iff] at hw
      subst hw
      exact ⟨by omega, by simp [hwv.1]⟩
    simp only [hwv, ↓reduceIte] at hw
    obtain ⟨hk, hget⟩ := h.get w k hw
    exact ⟨by omega, by rw [Array.getElem_push_lt hk]; exact hget⟩

theorem VarOrder.PosOK.pop {a p : Array ℕ} (h : PosOK a p) (hn : 0 < a.size) :
    PosOK a.pop (p.setIfInBounds a[a.size - 1] 0) := by
  constructor
  · intro k hk
    simp only [Array.size_pop] at hk
    rw [Array.getElem_pop, getD_setIfInBounds]
    have : ¬ a[a.size - 1] = a[k] := fun e => by
      have := h.inj (by omega) (by omega) e; omega
    simp [this, h.pos k (by omega)]
  · intro w k hw
    rw [getD_setIfInBounds] at hw
    simp only [Array.size_pop]
    by_cases hwz : a[a.size - 1] = w ∧ w < p.size
    · simp [hwz] at hw
    simp only [hwz, ↓reduceIte] at hw
    obtain ⟨hk, hget⟩ := h.get w k hw
    have hwp : w < p.size := lt_size_of_getD_ne (by rw [hw]; omega)
    have : k ≠ a.size - 1 := fun e => hwz ⟨by subst e; exact hget, hwp⟩
    exact ⟨by omega, by rw [Array.getElem_pop]; exact hget⟩

/-! #### Sifting, with positions -/

/-- `heapifyUpF` in the order of the activities `A`, also updating the positions `p`. -/
def VarOrder.siftUp (A : Activity) : (fuel : ℕ) → {n : ℕ} → Vector ℕ n → Array ℕ → Fin n →
    Vector ℕ n × Array ℕ
  | 0, _, a, p, _ => (a, p)
  | _ + 1, _, a, p, ⟨0, _⟩ => (a, p)
  | fuel + 1, _, a, p, ⟨i + 1, hi⟩ =>
    let j := i / 2
    let x := a[i + 1]
    let y := a[j]
    if A.below y x then
      VarOrder.siftUp A fuel (a.swap (i + 1) j) (swapPos p x y (i + 1) j) ⟨j, by omega⟩
    else (a, p)

theorem VarOrder.siftUp_fst (A : Activity) : ∀ (fuel : ℕ) {n : ℕ} (a : Vector ℕ n)
    (p : Array ℕ) (i : Fin n),
    (VarOrder.siftUp A fuel a p i).1 = @Batteries.BinaryHeap.heapifyUpF ℕ A.keyOrd fuel n a i
  | 0, _, _, _, _ => rfl
  | _ + 1, _, _, _, ⟨0, _⟩ => rfl
  | fuel + 1, _, a, p, ⟨i + 1, hi⟩ => by
    unfold VarOrder.siftUp Batteries.BinaryHeap.heapifyUpF
    simp only [Activity.isLT_compare]
    split
    · exact VarOrder.siftUp_fst A fuel _ _ _
    · rfl

theorem VarOrder.siftUp_size (A : Activity) : ∀ (fuel : ℕ) {n : ℕ} (a : Vector ℕ n)
    (p : Array ℕ) (i : Fin n), (VarOrder.siftUp A fuel a p i).2.size = p.size
  | 0, _, _, _, _ => rfl
  | _ + 1, _, _, _, ⟨0, _⟩ => rfl
  | fuel + 1, _, a, p, ⟨i + 1, hi⟩ => by
    rw [VarOrder.siftUp]
    split
    · exact (VarOrder.siftUp_size A fuel _ _ _).trans (size_swapPos ..)
    · rfl

theorem VarOrder.siftUp_pos (A : Activity) : ∀ (fuel : ℕ) {n : ℕ} (a : Vector ℕ n)
    (p : Array ℕ) (i : Fin n), VarOrder.PosOK a.toArray p →
    VarOrder.PosOK (VarOrder.siftUp A fuel a p i).1.toArray (VarOrder.siftUp A fuel a p i).2
  | 0, _, _, _, _, h => h
  | _ + 1, _, _, _, ⟨0, _⟩, h => h
  | fuel + 1, _, a, p, ⟨i + 1, hi⟩, h => by
    rw [VarOrder.siftUp]
    split
    · have h' := h.swap (i := i + 1) (j := i / 2) (by simpa using hi) (by simp; omega)
      exact VarOrder.siftUp_pos A fuel _ _ _ (by rw [Vector.toArray_swap]; exact h')
    · exact h

/-- The larger child, `maxChildF` in the order of the activities `A`. -/
def VarOrder.maxChild (A : Activity) {n : ℕ} (a : Vector ℕ n) (i : Fin n) : Option (Fin n) :=
  let left := 2 * i.1 + 1
  let right := left + 1
  if hleft : left < n then
    if hright : right < n then
      if A.below a[left] a[right] then some ⟨right, hright⟩ else some ⟨left, hleft⟩
    else some ⟨left, hleft⟩
  else none

theorem VarOrder.maxChild_eq (A : Activity) {n : ℕ} (a : Vector ℕ n) (i : Fin n) :
    VarOrder.maxChild A a i = @Batteries.BinaryHeap.maxChildF ℕ A.keyOrd n a i := by
  unfold VarOrder.maxChild Batteries.BinaryHeap.maxChildF
  simp only [Activity.isLT_compare]

/-- `heapifyDownF` in the order of the activities `A`, also updating the positions `p`. -/
def VarOrder.siftDown (A : Activity) : (fuel : ℕ) → {n : ℕ} → Vector ℕ n → Array ℕ → Fin n →
    Vector ℕ n × Array ℕ
  | 0, _, a, p, _ => (a, p)
  | fuel + 1, _, a, p, i =>
    match VarOrder.maxChild A a i with
    | none => (a, p)
    | some j =>
      let x := a[i]
      let y := a[j]
      if A.below x y then VarOrder.siftDown A fuel (a.swap i j) (swapPos p x y i j) j
      else (a, p)

theorem VarOrder.siftDown_fst (A : Activity) : ∀ (fuel : ℕ) {n : ℕ} (a : Vector ℕ n)
    (p : Array ℕ) (i : Fin n),
    (VarOrder.siftDown A fuel a p i).1 = @Batteries.BinaryHeap.heapifyDownF ℕ A.keyOrd fuel n a i
  | 0, _, _, _, _ => rfl
  | fuel + 1, _, a, p, i => by
    unfold VarOrder.siftDown Batteries.BinaryHeap.heapifyDownF
    rw [← VarOrder.maxChild_eq]
    cases VarOrder.maxChild A a i with
    | none => rfl
    | some j =>
      simp only [Activity.isLT_compare]
      split
      · exact VarOrder.siftDown_fst A fuel _ _ _
      · rfl

theorem VarOrder.siftDown_size (A : Activity) : ∀ (fuel : ℕ) {n : ℕ} (a : Vector ℕ n)
    (p : Array ℕ) (i : Fin n), (VarOrder.siftDown A fuel a p i).2.size = p.size
  | 0, _, _, _, _ => rfl
  | fuel + 1, _, a, p, i => by
    unfold VarOrder.siftDown
    cases VarOrder.maxChild A a i with
    | none => rfl
    | some j =>
      dsimp only
      split
      · exact (VarOrder.siftDown_size A fuel _ _ _).trans (size_swapPos ..)
      · rfl

theorem VarOrder.siftDown_pos (A : Activity) : ∀ (fuel : ℕ) {n : ℕ} (a : Vector ℕ n)
    (p : Array ℕ) (i : Fin n), VarOrder.PosOK a.toArray p →
    VarOrder.PosOK (VarOrder.siftDown A fuel a p i).1.toArray (VarOrder.siftDown A fuel a p i).2
  | 0, _, _, _, _, h => h
  | fuel + 1, _, a, p, i, h => by
    unfold VarOrder.siftDown
    cases VarOrder.maxChild A a i with
    | none => exact h
    | some j =>
      dsimp only
      split
      · have h' := h.swap (i := i) (j := j) (by simp) (by simp)
        exact VarOrder.siftDown_pos A fuel _ _ _ (by rw [Vector.toArray_swap]; exact h')
      · exact h

/-! #### The heap -/

/-- **The variable order**, MiniSat's `order_heap`: a binary max-heap of variables in the order of
their activities (`Activity.keyOrd`), with the position of each variable in it. A variable's
position is its index plus one, `0` when it is not in the heap (MiniSat's `indices`). Bumping a
variable in the heap moves it up (`VarOrder.increase`, MiniSat's `decrease`). -/
structure VarOrder where
  /-- The variables, as a binary heap. -/
  heap : Array ℕ
  /-- The position of each variable in `heap`, plus one; `0` for variables not in it. -/
  pos : Array ℕ

/-- The empty order, with room for the variables below `n`. -/
def VarOrder.empty (n : ℕ) : VarOrder := ⟨#[], Array.replicate n 0⟩

/-- **The heap is well formed** in the order of the activities `A`: as a Batteries heap, every
variable is at least its children. -/
def VarOrder.WF (H : VarOrder) (A : Activity) : Prop :=
  @Batteries.BinaryHeap.WF ℕ A.keyOrd (@Batteries.BinaryHeap.mk ℕ A.keyOrd H.heap)

/-- **Inserting** `v` with the activities `A`, if it is not in the heap and has a position. -/
def VarOrder.insert (A : Activity) (H : VarOrder) (v : ℕ) : VarOrder :=
  if H.pos.getD v 0 == 0 && v < H.pos.size then
    let n := H.heap.size
    let a : Vector ℕ n := ⟨H.heap, rfl⟩
    let r := VarOrder.siftUp A (n + 1) (a.push v) (H.pos.setIfInBounds v (n + 1))
      ⟨n, Nat.lt_succ_self _⟩
    ⟨r.1.toArray, r.2⟩
  else H

/-- **Moving `v` up** after its activity grew, the new activities being `A`, if it is in the
heap: MiniSat's `decrease`. -/
def VarOrder.increase (A : Activity) (H : VarOrder) (v : ℕ) : VarOrder :=
  let k := H.pos.getD v 0
  if h : k ≠ 0 ∧ k - 1 < H.heap.size then
    let r := VarOrder.siftUp A k (⟨H.heap, rfl⟩ : Vector ℕ H.heap.size) H.pos ⟨k - 1, h.2⟩
    ⟨r.1.toArray, r.2⟩
  else H

/-- **Removing the top** of the heap, in the order of the activities `A`: the last variable takes
its place and is moved down, as `popMaxF` does. -/
def VarOrder.removeTop (A : Activity) (H : VarOrder) (h : 0 < H.heap.size) : VarOrder :=
  let n := H.heap.size
  let a : Vector ℕ n := ⟨H.heap, rfl⟩
  let x := a[0]
  let y := a[n - 1]
  let p := (swapPos H.pos x y 0 (n - 1)).setIfInBounds x 0
  let a := (a.swap 0 (n - 1)).pop
  if h' : 0 < n - 1 then
    let r := VarOrder.siftDown A n a p ⟨0, h'⟩
    ⟨r.1.toArray, r.2⟩
  else ⟨a.toArray, p⟩

/-- **Inserting the variables `vs`** not in the heap, with the activities `A`: MiniSat's
`insertVarOrder` on each. -/
def VarOrder.addAll (A : Activity) (H : VarOrder) (vs : List ℕ) : VarOrder :=
  vs.foldl (VarOrder.insert A) H

/-- **Rebuilding** the heap with the activities `A`, after they were scaled down: scaling can turn
different activities into ties, which the order breaks by variable. -/
def VarOrder.rebuild (A : Activity) (H : VarOrder) : VarOrder :=
  H.heap.foldl (VarOrder.insert A) (VarOrder.empty H.pos.size)

/-! #### What the operations keep -/

theorem VarOrder.wf_empty (A : Activity) (n : ℕ) : (VarOrder.empty n).WF A := by
  let _ := A.keyOrd
  have := @Batteries.BinaryHeap.empty_wf ℕ A.keyOrd
  rw [← Batteries.BinaryHeap.emptyF_eq] at this
  exact this

/-- A comparison `x ≥ y` survives activities raised at `x` and unchanged at `y`. -/
theorem Activity.isGE_raise {A A' : Activity} {x y : ℕ} (hx : A.get x ≤ A'.get x)
    (hy : A'.get y = A.get y) (h : (@compare ℕ A.keyOrd x y).isGE) :
    (@compare ℕ A'.keyOrd x y).isGE := by
  rw [Activity.isGE_compare_iff] at h ⊢
  omega

/-- A heap stays well formed when the activities of its variables do not change. -/
theorem VarOrder.WF.congr {A A' : Activity} {H : VarOrder} (hwf : H.WF A)
    (h : ∀ w ∈ H.heap, A'.get w = A.get w) : H.WF A' :=
  Batteries.BinaryHeap.topDown_of_isGE (fun k j hkj =>
    Activity.isGE_raise (h _ (Array.getElem_mem k.2)).ge (h _ (Array.getElem_mem j.2)) hkj) hwf

theorem VarOrder.PosOK.nodup {a p : Array ℕ} (h : VarOrder.PosOK a p) : a.toList.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  simp only [Array.getElem_toList] at hij
  exact Fin.ext (h.inj (by simp) (by simp) hij)

/-- **What inserting keeps**: a well-formed heap stays well formed, the positions consistent and
the room the same; `v` is added if it has room. -/
theorem VarOrder.insert_spec (A : Activity) (H : VarOrder) (v : ℕ)
    (hp : VarOrder.PosOK H.heap H.pos) :
    (H.WF A → (H.insert A v).WF A) ∧ VarOrder.PosOK (H.insert A v).heap (H.insert A v).pos ∧
      (H.insert A v).pos.size = H.pos.size ∧
      ∀ w, w ∈ (H.insert A v).heap ↔ w ∈ H.heap ∨ (w = v ∧ v < H.pos.size) := by
  unfold VarOrder.insert
  split
  · rename_i hg
    let _ := A.keyOrd
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
    have hfst := VarOrder.siftUp_fst A (H.heap.size + 1) ((⟨H.heap, rfl⟩ : Vector ℕ _).push v)
      (H.pos.setIfInBounds v (H.heap.size + 1)) ⟨H.heap.size, Nat.lt_succ_self _⟩
    have heq : (VarOrder.siftUp A (H.heap.size + 1) ((⟨H.heap, rfl⟩ : Vector ℕ _).push v)
        (H.pos.setIfInBounds v (H.heap.size + 1)) ⟨H.heap.size, Nat.lt_succ_self _⟩).1.toArray =
        (Batteries.BinaryHeap.insert ⟨H.heap⟩ v).arr := by
      rw [← Batteries.BinaryHeap.insertF_eq, hfst]; rfl
    dsimp only
    refine ⟨fun hwf => ?_, ?_, ?_, fun w => ?_⟩
    · change Batteries.BinaryHeap.WF ⟨_⟩
      rw [heq]
      have := A.transOrd
      exact Batteries.BinaryHeap.insert_wf hwf
    · exact VarOrder.siftUp_pos A _ _ _ _ (by rw [Vector.toArray_push]; exact hp.push hg.2 hg.1)
    · simp only [VarOrder.siftUp_size, Array.size_setIfInBounds]
    · have := Batteries.BinaryHeap.mem_insert (heap := (⟨H.heap⟩ : Batteries.BinaryHeap ℕ))
        (x := v) (y := w)
      change w ∈ (Batteries.BinaryHeap.insert ⟨H.heap⟩ v).arr ↔ w ∈ H.heap ∨ w = v at this
      rw [heq, this]
      exact or_congr Iff.rfl ⟨fun h => ⟨h, hg.2⟩, fun h => h.1⟩
  · rename_i hg
    refine ⟨id, hp, rfl, fun w => ⟨.inl, fun h => h.elim id fun ⟨hw, hv⟩ => ?_⟩⟩
    subst hw
    refine hp.mem_iff.2 fun h0 => hg ?_
    simp [h0, hv]

/-- **What moving `v` up keeps**, after its activity alone grew from `A` to `A'`: the heap stays
well formed, the positions consistent, the room and the variables the same. -/
theorem VarOrder.increase_spec {A A' : Activity} {H : VarOrder} {v : ℕ}
    (hp : VarOrder.PosOK H.heap H.pos) (hwf : H.WF A) (hle : ∀ u, A.get u ≤ A'.get u)
    (heq : ∀ u, u ≠ v → A'.get u = A.get u) :
    (H.increase A' v).WF A' ∧ VarOrder.PosOK (H.increase A' v).heap (H.increase A' v).pos ∧
      (H.increase A' v).pos.size = H.pos.size ∧
      ∀ w, w ∈ (H.increase A' v).heap ↔ w ∈ H.heap := by
  unfold VarOrder.increase
  dsimp only
  split
  · rename_i h
    obtain ⟨hk, hget⟩ := hp.get v (H.pos.getD v 0 - 1) (by omega)
    have hfst₀ := VarOrder.siftUp_fst A' (H.pos.getD v 0) (⟨H.heap, rfl⟩ : Vector ℕ _) H.pos
      ⟨_, h.2⟩
    have hfst := hfst₀.trans
      (@Batteries.BinaryHeap.heapifyUpF_eq ℕ A'.keyOrd _ _ _ _ (by simp only; omega))
    refine ⟨?_, VarOrder.siftUp_pos A' _ _ _ _ hp, VarOrder.siftUp_size .., fun w => ?_⟩
    · change @Batteries.BinaryHeap.WF ℕ A'.keyOrd (@Batteries.BinaryHeap.mk ℕ A'.keyOrd _)
      rw [hfst]
      refine @Batteries.BinaryHeap.wf_of_topDown ℕ A'.keyOrd _ _ ?_
      refine @Batteries.BinaryHeap.topDown_heapifyUp_of_isGE ℕ A.keyOrd A'.keyOrd A.transOrd
        A'.transOrd _ _ _ (fun k j hj hkj => ?_) hwf
      refine Activity.isGE_raise (hle _) (heq _ fun e => hj (Fin.ext ?_)) hkj
      exact hp.inj j.2 hk (e.trans hget.symm)
    · rw [hfst₀, Vector.mem_toArray_iff,
        (@Batteries.BinaryHeap.heapifyUpF_perm ℕ A'.keyOrd _ _ _ _).mem_iff]
      simp
  · rename_i h
    refine ⟨hwf.congr fun w hw => heq w fun e => h ?_, hp, rfl, fun _ => Iff.rfl⟩
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hw
    rw [← e, hp.pos i hi]
    exact ⟨by omega, by omega⟩

/-- **What removing the top keeps**: a well-formed heap stays well formed, the positions consistent
and the room the same, and the variables left are the others. -/
theorem VarOrder.removeTop_spec (A : Activity) (H : VarOrder) (h : 0 < H.heap.size)
    (hp : VarOrder.PosOK H.heap H.pos) :
    (H.WF A → (H.removeTop A h).WF A) ∧
      VarOrder.PosOK (H.removeTop A h).heap (H.removeTop A h).pos ∧
      (H.removeTop A h).pos.size = H.pos.size ∧
      ∀ w, w ∈ (H.removeTop A h).heap ↔ w ∈ H.heap ∧ w ≠ H.heap[0] := by
  let _ := A.keyOrd
  have heq : (H.removeTop A h).heap = (Batteries.BinaryHeap.popMaxF ⟨H.heap⟩).arr := by
    unfold VarOrder.removeTop Batteries.BinaryHeap.popMaxF
    have hs : ¬ (⟨H.heap⟩ : Batteries.BinaryHeap ℕ).size = 0 := by
      change ¬ H.heap.size = 0; omega
    rw [dite_eq_right_of_eq_false (eq_false hs)]
    dsimp only
    split <;> split
    · simp only [VarOrder.siftDown_fst]; rfl
    · rename_i h₁ h₂; exact absurd h₁ h₂
    · rename_i h₁ h₂; exact absurd h₂ h₁
    · rfl
  have hn : H.heap.size - 1 < H.heap.size := by omega
  -- the positions after the swap and the pop, before sifting down
  have hp₁ : VarOrder.PosOK ((⟨H.heap, rfl⟩ : Vector ℕ _).swap 0 (H.heap.size - 1)).pop.toArray
      ((swapPos H.pos H.heap[0] H.heap[H.heap.size - 1] 0 (H.heap.size - 1)).setIfInBounds
        H.heap[0] 0) := by
    have h₁ := hp.swap h hn
    have h₂ := h₁.pop (by simpa using h)
    rw [Vector.toArray_pop, Vector.toArray_swap]
    have : (H.heap.swap 0 (H.heap.size - 1) h hn)[(H.heap.swap 0 (H.heap.size - 1) h hn).size - 1]'
        (by simp; omega) = H.heap[0] := by
      rw [Array.getElem_swap]
      by_cases h0 : H.heap.size - 1 = 0 <;> simp [h0]
    rw [this] at h₂
    exact h₂
  refine ⟨fun hwf => ?_, ?_, ?_, fun w => ?_⟩
  · change Batteries.BinaryHeap.WF ⟨_⟩
    rw [heq, Batteries.BinaryHeap.popMaxF_eq]
    have := A.transOrd
    exact Batteries.BinaryHeap.popMax_wf hwf
  · unfold VarOrder.removeTop
    dsimp only
    split
    · exact VarOrder.siftDown_pos A _ _ _ _ hp₁
    · exact hp₁
  · unfold VarOrder.removeTop
    dsimp only
    split <;> simp [VarOrder.siftDown_size, size_swapPos]
  · rw [heq]
    have hmax : (Batteries.BinaryHeap.maxF ⟨H.heap⟩ : Option ℕ) = some H.heap[0] := by
      simp [Batteries.BinaryHeap.maxF, h]
    constructor
    · intro hw
      have hw' : w ∈ (⟨H.heap⟩ : Batteries.BinaryHeap ℕ) :=
        Batteries.BinaryHeap.mem_of_mem_popMaxF hw
      refine ⟨hw', fun e => ?_⟩
      subst e
      have hperm := Batteries.BinaryHeap.popMax_perm (heap := (⟨H.heap⟩ : Batteries.BinaryHeap ℕ))
        h
      have hnd := hperm.nodup_iff.2 hp.nodup
      rw [Batteries.BinaryHeap.popMaxF_eq] at hw
      exact (List.nodup_cons.1 hnd).1 (Array.mem_toList_iff.2 hw)
    · rintro ⟨hw, hne⟩
      exact (Batteries.BinaryHeap.mem_popMaxF hmax hw).resolve_left hne


/-- **What inserting the variables `vs` keeps**: a well-formed heap stays well formed, the
positions consistent and the room the same; the variables of `vs` with room are added. -/
theorem VarOrder.addAll_spec (A : Activity) : ∀ (H : VarOrder) (vs : List ℕ),
    VarOrder.PosOK H.heap H.pos →
    (H.WF A → (H.addAll A vs).WF A) ∧ VarOrder.PosOK (H.addAll A vs).heap (H.addAll A vs).pos ∧
      (H.addAll A vs).pos.size = H.pos.size ∧
      ∀ w, w ∈ (H.addAll A vs).heap ↔ w ∈ H.heap ∨ (w ∈ vs ∧ w < H.pos.size)
  | H, [], hp => ⟨id, hp, rfl, fun w => by simp [VarOrder.addAll]⟩
  | H, v :: vs, hp => by
    obtain ⟨hwf₁, hp₁, hs₁, hm₁⟩ := VarOrder.insert_spec A H v hp
    obtain ⟨hwf₂, hp₂, hs₂, hm₂⟩ := VarOrder.addAll_spec A (H.insert A v) vs hp₁
    refine ⟨fun h => hwf₂ (hwf₁ h), hp₂, hs₂.trans hs₁, fun w => ?_⟩
    change w ∈ ((H.insert A v).addAll A vs).heap ↔ _
    rw [hm₂, hm₁, hs₁, List.mem_cons]
    grind

/-- **What rebuilding keeps**: the heap is well formed in the order of the new activities, the
positions consistent, the room and the variables the same. -/
theorem VarOrder.rebuild_spec (A : Activity) (H : VarOrder) (hp : VarOrder.PosOK H.heap H.pos) :
    (H.rebuild A).WF A ∧ VarOrder.PosOK (H.rebuild A).heap (H.rebuild A).pos ∧
      (H.rebuild A).pos.size = H.pos.size ∧ ∀ w, w ∈ (H.rebuild A).heap ↔ w ∈ H.heap := by
  have h : H.rebuild A = (VarOrder.empty H.pos.size).addAll A H.heap.toList := by
    rw [VarOrder.rebuild, VarOrder.addAll, Array.foldl_toList]
  obtain ⟨hwf, hp', hs, hm⟩ := VarOrder.addAll_spec A (VarOrder.empty H.pos.size) H.heap.toList
    (VarOrder.PosOK.empty _)
  rw [h]
  refine ⟨hwf (VarOrder.wf_empty A _), hp', by simpa [VarOrder.empty] using hs, fun w => ?_⟩
  rw [hm]
  simp only [VarOrder.empty, Array.mem_toList_iff, Array.size_replicate]
  exact ⟨fun h => h.elim (fun h => absurd h (by simp)) fun h => h.1,
    fun h' => .inr ⟨h', hp.lt_size h'⟩⟩

/-! #### Bumping -/

private theorem Activity.get_modify_ne (A : Activity) {u v : ℕ} (f : ℕ → ℕ) (i : ℕ)
    (huv : u ≠ v) : (⟨A.score.modify v f, i⟩ : Activity).get u = A.get u := by
  simp only [Activity.get, Array.getD_eq_getD_getElem?, Array.getElem?_modify, Ne.symm huv,
    ↓reduceIte]

private theorem Activity.le_get_modify (A : Activity) (u v c i : ℕ) :
    A.get u ≤ (⟨A.score.modify v (· + c), i⟩ : Activity).get u := by
  simp only [Activity.get, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  split
  · cases A.score[u]? <;> simp
  · exact le_rfl

/-- **Bumping `v`** in the activities `A` and the order `H`: `Activity.bumpVar`, and the variable is
moved up in the heap, or the heap is rebuilt if the activities were scaled down. -/
@[inline] def VarOrder.bumpVar (A : Activity) (H : VarOrder) (v : ℕ) : Activity × VarOrder :=
  let score := A.score.modify v (· + A.inc)
  if score.getD v 0 >>> 60 != 0 then
    let A' : Activity := ⟨score.map (· >>> 20), A.inc >>> 20⟩
    (A', H.rebuild A')
  else
    let A' : Activity := ⟨score, A.inc⟩
    (A', H.increase A' v)

theorem VarOrder.bumpVar_fst (A : Activity) (H : VarOrder) (v : ℕ) :
    (VarOrder.bumpVar A H v).1 = A.bumpVar v := by
  unfold VarOrder.bumpVar Activity.bumpVar
  dsimp only
  split <;> rfl

/-- What an operation on the order keeps, with the activities `A'` after it: a well-formed heap,
consistent positions, the room and the variables of the order `H` before. -/
structure VarOrder.Kept (H : VarOrder) (A' : Activity) (H' : VarOrder) : Prop where
  wf : H'.WF A'
  pos : VarOrder.PosOK H'.heap H'.pos
  size : H'.pos.size = H.pos.size
  mem : ∀ w, w ∈ H'.heap ↔ w ∈ H.heap

theorem VarOrder.Kept.trans {H H' H'' : VarOrder} {A' A'' : Activity} (h : VarOrder.Kept H A' H')
    (h' : VarOrder.Kept H' A'' H'') : VarOrder.Kept H A'' H'' :=
  ⟨h'.wf, h'.pos, h'.size.trans h.size, fun w => (h'.mem w).trans (h.mem w)⟩

theorem VarOrder.bumpVar_spec {A : Activity} {H : VarOrder} (v : ℕ) (hwf : H.WF A)
    (hp : VarOrder.PosOK H.heap H.pos) :
    VarOrder.Kept H (VarOrder.bumpVar A H v).1 (VarOrder.bumpVar A H v).2 := by
  unfold VarOrder.bumpVar
  dsimp only
  split
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := VarOrder.rebuild_spec ⟨(A.score.modify v (· + A.inc)).map
      (· >>> 20), A.inc >>> 20⟩ H hp
    exact ⟨h₁, h₂, h₃, h₄⟩
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := VarOrder.increase_spec (A' := ⟨A.score.modify v (· + A.inc), A.inc⟩)
      hp hwf (fun u => A.le_get_modify u v A.inc A.inc)
      (fun u hu => A.get_modify_ne _ _ hu)
    exact ⟨h₁, h₂, h₃, h₄⟩

/-- Bumping each variable of `vs` in turn (`VarOrder.bumpVar`). -/
def VarOrder.bumpAll : List ℕ → Activity → VarOrder → Activity × VarOrder
  | [], A, H => (A, H)
  | v :: vs, A, H =>
    let r := VarOrder.bumpVar A H v
    VarOrder.bumpAll vs r.1 r.2

theorem VarOrder.bumpAll_fst : ∀ (vs : List ℕ) (A : Activity) (H : VarOrder),
    (VarOrder.bumpAll vs A H).1 = vs.foldl Activity.bumpVar A
  | [], _, _ => rfl
  | v :: vs, A, H => by
    rw [VarOrder.bumpAll, VarOrder.bumpAll_fst vs, VarOrder.bumpVar_fst, List.foldl_cons]

theorem VarOrder.bumpAll_spec : ∀ (vs : List ℕ) {A : Activity} {H : VarOrder}, H.WF A →
    VarOrder.PosOK H.heap H.pos →
    VarOrder.Kept H (VarOrder.bumpAll vs A H).1 (VarOrder.bumpAll vs A H).2
  | [], _, _, hwf, hp => ⟨hwf, hp, rfl, fun _ => Iff.rfl⟩
  | v :: vs, A, H, hwf, hp => by
    have h₁ := VarOrder.bumpVar_spec v hwf hp
    exact h₁.trans (VarOrder.bumpAll_spec vs h₁.wf h₁.pos)

/-- **After a conflict**: bump each variable met by the analysis once, in the activities and in
the order, then grow the increment, as `Activity.bump` does. -/
def VarOrder.bump (A : Activity) (H : VarOrder) (vs : List ℕ) (decay : ℕ := 19) :
    Activity × VarOrder :=
  let r := VarOrder.bumpAll (dedupVars vs) A H
  (⟨r.1.score, r.1.inc + r.1.inc / decay⟩, r.2)

theorem VarOrder.bump_fst (A : Activity) (H : VarOrder) (vs : List ℕ) (decay : ℕ) :
    (VarOrder.bump A H vs decay).1 = A.bump vs decay := by
  simp only [VarOrder.bump, Activity.bump, VarOrder.bumpAll_fst]

theorem VarOrder.bump_spec {A : Activity} {H : VarOrder} (vs : List ℕ) (decay : ℕ) (hwf : H.WF A)
    (hp : VarOrder.PosOK H.heap H.pos) :
    VarOrder.Kept H (VarOrder.bump A H vs decay).1 (VarOrder.bump A H vs decay).2 := by
  have h := VarOrder.bumpAll_spec (dedupVars vs) hwf hp
  exact ⟨h.wf.congr fun _ _ => rfl, h.pos, h.size, h.mem⟩

/-- **Bumping variables listed once each**: `VarOrder.bump` without removing repetitions, which
costs an array as large as the greatest variable. The solver bumps the variables met by an
analysis, which lists each once (`Cslib.Algorithms.Lean.CDCL.Learned.seen_nodup`). -/
def VarOrder.bumpDistinct (A : Activity) (H : VarOrder) (vs : List ℕ) (decay : ℕ := 19) :
    Activity × VarOrder :=
  let r := VarOrder.bumpAll vs A H
  (⟨r.1.score, r.1.inc + r.1.inc / decay⟩, r.2)

theorem VarOrder.bumpDistinct_eq (A : Activity) (H : VarOrder) {vs : List ℕ} (h : vs.Nodup)
    (decay : ℕ) : VarOrder.bumpDistinct A H vs decay = VarOrder.bump A H vs decay := by
  simp only [VarOrder.bumpDistinct, VarOrder.bump, dedupKey_of_nodup Function.injective_id h]


/-! #### The invariant and popping -/

/-- **The invariant of the variable order** over the variables `V`, with the activities `A`, the
trail `M` and the variables `occ` admits: a well-formed heap with consistent positions, room for
every variable of `V`, and every variable of `V` admitted and not on the trail in the heap. -/
structure VarOrder.Inv (H : VarOrder) (A : Activity) (V : List ℕ) (M : Trail) (occ : ℕ → Bool) :
    Prop where
  wf : H.WF A
  pos : VarOrder.PosOK H.heap H.pos
  room : ∀ v ∈ V, v < H.pos.size
  covers : ∀ v ∈ V, v ∉ Trail.vars M → occ v = true → v ∈ H.heap

/-- **All the variables of `V` inserted** in an empty order with room for them: an order
satisfying the invariant whatever the trail. -/
theorem VarOrder.inv_addAll_empty (A : Activity) (V : List ℕ) (M : Trail) (occ : ℕ → Bool)
    {n : ℕ} (hn : ∀ v ∈ V, v < n) : ((VarOrder.empty n).addAll A V).Inv A V M occ := by
  obtain ⟨hwf, hp, hs, hm⟩ := VarOrder.addAll_spec A (VarOrder.empty n) V (VarOrder.PosOK.empty n)
  have hs' : ((VarOrder.empty n).addAll A V).pos.size = n := by simpa [VarOrder.empty] using hs
  refine ⟨hwf (VarOrder.wf_empty A n), hp, fun v hv => by rw [hs']; exact hn v hv,
    fun v hv _ _ => ?_⟩
  rw [hm]
  exact .inr ⟨hv, by simpa [VarOrder.empty] using hn v hv⟩

/-- The result of popping: the variable found, if any, and the order left. -/
structure VarOrder.Popped where
  /-- The variable found. -/
  var : Option ℕ
  /-- The order left. -/
  order : VarOrder

/-- **Popping the decision variable**, as MiniSat's `pickBranchLit`: the top of the heap is
removed until it is an unassigned variable admitted by `occ`. `none` if the heap runs out, or the
fuel does; with more fuel than variables in the heap, the heap runs out (`VarOrder.pop_none`). -/
def VarOrder.pop (A : Activity) (asg : Assign) (occ : ℕ → Bool) :
    (fuel : ℕ) → VarOrder → VarOrder.Popped
  | 0, H => ⟨none, H⟩
  | fuel + 1, H =>
    if h : 0 < H.heap.size then
      let v := H.heap[0]
      let H' := H.removeTop A h
      if asg.assigned v || !occ v then VarOrder.pop A asg occ fuel H' else ⟨some v, H'⟩
    else ⟨none, H⟩

/-- The top of a well-formed heap has the greatest activity. -/
theorem VarOrder.le_top {A : Activity} {H : VarOrder} (hwf : H.WF A) (h : 0 < H.heap.size)
    {y : ℕ} (hy : y ∈ H.heap) : A.get y ≤ A.get H.heap[0] := by
  let _ := A.keyOrd
  have := A.transOrd
  have hm : (⟨H.heap⟩ : Batteries.BinaryHeap ℕ).max = some H.heap[0] := by
    rw [← Batteries.BinaryHeap.maxF_eq]
    simp [Batteries.BinaryHeap.maxF, h]
  have hge := Batteries.BinaryHeap.max_ge_all hwf hy h
  simp only [hm, Option.get_some] at hge
  rw [Activity.isGE_compare_iff] at hge
  omega

/-- **What popping finds**: the order stays well formed, with consistent positions and the same
room; a variable found is unassigned, admitted, and of greatest activity among the unassigned
admitted variables of `V`; and every other unassigned admitted variable of `V` stays in the
heap. -/
theorem VarOrder.pop_spec {A : Activity} {asg : Assign} {M : Trail} {V : List ℕ}
    {occ : ℕ → Bool} (hasg : asg.Agrees M) :
    ∀ (fuel : ℕ) (H : VarOrder), H.WF A → VarOrder.PosOK H.heap H.pos →
    (∀ v ∈ V, v ∉ Trail.vars M → occ v = true → v ∈ H.heap) →
    (VarOrder.pop A asg occ fuel H).order.WF A ∧
    VarOrder.PosOK (VarOrder.pop A asg occ fuel H).order.heap
      (VarOrder.pop A asg occ fuel H).order.pos ∧
    (VarOrder.pop A asg occ fuel H).order.pos.size = H.pos.size ∧
    (∀ x, (VarOrder.pop A asg occ fuel H).var = some x →
      x ∉ Trail.vars M ∧ occ x = true ∧
        ∀ y ∈ V, y ∉ Trail.vars M → occ y = true → A.get y ≤ A.get x) ∧
    (∀ v ∈ V, v ∉ Trail.vars M → occ v = true → (VarOrder.pop A asg occ fuel H).var ≠ some v →
      v ∈ (VarOrder.pop A asg occ fuel H).order.heap)
  | 0, H, hwf, hp, hcov => ⟨hwf, hp, rfl, fun _ h => absurd h (by simp [VarOrder.pop]),
      fun v hv hvM hvo _ => hcov v hv hvM hvo⟩
  | fuel + 1, H, hwf, hp, hcov => by
    unfold VarOrder.pop
    split
    · rename_i h
      obtain ⟨hwf', hp', hs', hm'⟩ := VarOrder.removeTop_spec A H h hp
      dsimp only
      split
      · rename_i hskip
        have hcov' : ∀ v ∈ V, v ∉ Trail.vars M → occ v = true → v ∈ (H.removeTop A h).heap := by
          intro v hv hvM hvo
          refine (hm' v).2 ⟨hcov v hv hvM hvo, fun e => ?_⟩
          subst e
          rcases Bool.or_eq_true_iff.1 hskip with h' | h'
          · exact hvM ((hasg.assigned_iff _).1 h')
          · simp [hvo] at h'
        obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := VarOrder.pop_spec hasg fuel _ (hwf' hwf) hp' hcov'
        exact ⟨h₁, h₂, h₃.trans hs', h₄, h₅⟩
      · rename_i hskip
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Bool.not_eq_false'] at hskip
        refine ⟨hwf' hwf, hp', hs', fun x hx => ?_, fun v hv hvM hvo hne => ?_⟩
        · simp only [Option.some.injEq] at hx
          subst hx
          refine ⟨fun hM => ?_, by simpa using hskip.2, fun y hy hyM hyo =>
            VarOrder.le_top hwf h (hcov y hy hyM hyo)⟩
          have := hskip.1
          rw [(hasg.assigned_iff _).2 hM] at this
          exact absurd this (by decide)
        · exact (hm' v).2 ⟨hcov v hv hvM hvo, fun e => hne (by rw [e])⟩
    · exact ⟨hwf, hp, rfl, fun _ h => absurd h (by simp), fun v hv hvM hvo _ => hcov v hv hvM hvo⟩

private theorem VarOrder.size_removeTop (A : Activity) (H : VarOrder) (h : 0 < H.heap.size) :
    (H.removeTop A h).heap.size = H.heap.size - 1 := by
  unfold VarOrder.removeTop
  dsimp only
  split <;> simp

/-- **Popping with more fuel than variables** finds none only by emptying the heap. -/
theorem VarOrder.pop_none (A : Activity) (asg : Assign) (occ : ℕ → Bool) :
    ∀ (fuel : ℕ) (H : VarOrder), H.heap.size < fuel →
    (VarOrder.pop A asg occ fuel H).var = none → (VarOrder.pop A asg occ fuel H).order.heap.size = 0
  | 0, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | fuel + 1, H, hf, hn => by
    unfold VarOrder.pop at hn ⊢
    split
    · rename_i h
      simp only [h, ↓reduceDIte] at hn
      dsimp only at hn ⊢
      split
      · rename_i hskip
        simp only [hskip, ↓reduceIte] at hn
        exact VarOrder.pop_none A asg occ fuel _ (by rw [VarOrder.size_removeTop]; omega) hn
      · rename_i hskip
        simp only [hskip, Bool.false_eq_true, ↓reduceIte] at hn
        exact absurd hn (by simp)
    · rename_i h
      change H.heap.size = 0
      omega

end Cslib.Algorithms.Lean.CDCL
