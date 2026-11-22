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
scanning the variables for the greatest activity: a binary heap, from Batteries with its proofs,
of entries pairing a variable with an activity (`OrderKey`, compared by activity, then by
variable). Instead of moving a variable within
the heap when it is bumped, as MiniSat does with an index of positions, the solver inserts it
again, and stale entries are skipped when they reach the top (`VarOrder.pop`). Its invariant
(`VarOrder.Inv`) asks that every unassigned variable have an entry keyed at least at its
activity: bumping only raises the bumped variables (`Activity.get_bump_le`), which are inserted
again, and rescaling lowers every activity. Under it, the variable popped has the greatest
activity among the unassigned variables (`VarOrder.pop_spec`). An entry keyed above the activity,
left by a rescaling, is inserted again with the current activity when it reaches the top.

**Marks** (MiniSat's `inHeap`). An array marks variables certainly in the order: each marked
variable has an entry keyed at least at its activity, assigned or not (`VarOrder.Marked`, part of
the invariant). Inserting a variable marks it (`VarOrder.add`), and popping unmarks the variable of
each entry it removes. After a backjump, the variables undone are inserted only if they are not
marked (`VarOrder.addMissing`, MiniSat's `insertVarOrder`): a variable propagated, never popped,
keeps its entry. Marking less than this is always sound; a mark only saves an insertion.

The heap does not remove every scan. The fallback below scans the variables of the database, and
since bumping inserts a variable again instead of moving its entry, the heap can hold more entries
than there are variables. MiniSat's heap moves an entry in place.

The choice of variable does not affect correctness: the solver only needs an unassigned variable
of the database, or the fact that there is none. `Activity.pick` scans for one of greatest
activity (`Activity.pick_some`, `Activity.pick_none`, `Activity.pick_max`); the solver uses it
when the variable order runs out.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.Activity`: activities and the increment.
* `Cslib.Algorithms.Lean.CDCL.Activity.bump`: bumping the variables met by an analysis, then
  decaying.
* `Cslib.Algorithms.Lean.CDCL.Activity.grow`: making room for more indices.
* `Cslib.Algorithms.Lean.CDCL.Activity.pick`: an unassigned variable of greatest activity.
* `Cslib.Algorithms.Lean.CDCL.VarOrder`, `Cslib.Algorithms.Lean.CDCL.VarOrder.Inv`: the variable
  order and its invariant.
* `Cslib.Algorithms.Lean.CDCL.VarOrder.Marked`, `Cslib.Algorithms.Lean.CDCL.VarOrder.add`,
  `Cslib.Algorithms.Lean.CDCL.VarOrder.addMissing`: sound marks of the variables in the order, and
  inserting variables with them.
* `Cslib.Algorithms.Lean.CDCL.VarOrder.pop`: popping the decision variable.

## Main results

* `Cslib.Algorithms.Lean.CDCL.Activity.pick_some`, `Cslib.Algorithms.Lean.CDCL.Activity.pick_none`,
  `Cslib.Algorithms.Lean.CDCL.Activity.pick_max`: what `pick` returns.
* `Cslib.Algorithms.Lean.CDCL.Activity.get_bump_le`: bumping does not raise the other activities.
* `Cslib.Algorithms.Lean.CDCL.VarOrder.pop_spec`: the variable popped has the greatest activity
  among the unassigned variables, and the order keeps its invariant.
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
def Activity.get (A : Activity) (v : ℕ) : ℕ := A.score.getD v 0

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

/-- An entry at least another has at least its activity. -/
theorem OrderKey.activity_le_of_isGE {a b : OrderKey} (h : (compare a b).isGE) :
    b.activity ≤ a.activity := by
  change (compareLex (compareOn (·.1)) (compareOn (·.2)) a.toPair b.toPair).isGE at h
  simp only [compareLex, compareOn, Ordering.isGE_then_iff_or] at h
  rcases h with h | ⟨h, -⟩
  · exact (Nat.compare_eq_gt.1 h).le
  · exact (Nat.compare_eq_eq.1 h).ge

end

/-- **The variable order**, MiniSat's `order_heap`: a binary heap of variables keyed by activity.
Bumping a variable inserts it again with its new activity, so a variable may have stale entries,
which are skipped when they come to the top. -/
abbrev VarOrder : Type := Batteries.BinaryHeap OrderKey


/-- **The variable order covers** the variables `V` not on the trail `M` that `occ` admits, those
occurring in the database: each has an entry keyed at least at its activity. -/
def VarOrder.Covers (H : VarOrder) (A : Activity) (V : List ℕ) (M : Trail) (occ : ℕ → Bool) :
    Prop :=
  ∀ v ∈ V, v ∉ Trail.vars M → occ v = true → ∃ k, A.get v ≤ k ∧ OrderKey.mk k v ∈ H

/-! ### Marks: the variables certainly in the order -/

/-- Whether the variable `v` is marked in `I`; `false` past its end. -/
def VarOrder.marked (I : Array Bool) (v : ℕ) : Bool := I.getD v false

/-- Setting a mark changes only that variable's mark, and only within the array. -/
private theorem VarOrder.marked_setIfInBounds {I : Array Bool} {v w : ℕ} {b : Bool}
    (h : VarOrder.marked (I.setIfInBounds v b) w = true) :
    (w = v ∧ b = true) ∨ (w ≠ v ∧ VarOrder.marked I w = true) := by
  unfold VarOrder.marked at h ⊢
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at h ⊢
  by_cases hw : v = w
  · subst hw
    simp only [↓reduceIte] at h
    split at h
    · exact .inl ⟨rfl, by simpa using h⟩
    · rename_i hlt
      simp at h
  · simp only [hw, ↓reduceIte] at h
    exact .inr ⟨Ne.symm hw, h⟩

/-- **The marks are sound** (MiniSat's `inHeap`): each variable marked in `I` has an entry keyed at
least at its activity, whether it is assigned or not. A variable left unmarked may or may not have
one. -/
def VarOrder.Marked (H : VarOrder) (A : Activity) (I : Array Bool) : Prop :=
  ∀ v, VarOrder.marked I v = true → ∃ k, A.get v ≤ k ∧ OrderKey.mk k v ∈ H

/-- The marks stay sound with more entries and with activities no higher at the marked
variables. -/
private theorem VarOrder.Marked.mono {H H' : VarOrder} {A A' : Activity} {I : Array Bool}
    (h : VarOrder.Marked H A I) (hH : ∀ e ∈ H, e ∈ H')
    (hA : ∀ v, VarOrder.marked I v = true → A'.get v ≤ A.get v) : VarOrder.Marked H' A' I := by
  intro v hv
  obtain ⟨k, hk, hmem⟩ := h v hv
  exact ⟨k, (hA v hv).trans hk, hH _ hmem⟩

/-- **The invariant of the variable order** over the variables `V`, with the marks `I`, the
activities `A`, the trail `M` and the variables `occ` admits: a well-formed heap of variables of
`V`, covering those admitted and not on the trail, with sound marks. -/
structure VarOrder.Inv (H : VarOrder) (I : Array Bool) (A : Activity) (V : List ℕ) (M : Trail)
    (occ : ℕ → Bool) : Prop where
  wf : H.WF
  vars : ∀ e ∈ H, e.var ∈ V
  covers : H.Covers A V M occ
  marked : VarOrder.Marked H A I

/-- **Inserting the variables `vs`** with their activities `A`, and marking them in `I`. -/
def VarOrder.add (H : VarOrder) (I : Array Bool) (A : Activity) (vs : List ℕ) :
    VarOrder × Array Bool :=
  vs.foldl (fun (H, I) v => (H.insertF (OrderKey.mk (A.get v) v), I.setIfInBounds v true)) (H, I)

/-- **Inserting the variables of `vs` not marked in `I`**, with their activities `A`, and marking
them: MiniSat's `insertVarOrder`, which skips a variable already in the heap. -/
def VarOrder.addMissing (H : VarOrder) (I : Array Bool) (A : Activity) (vs : List ℕ) :
    VarOrder × Array Bool :=
  vs.foldl (fun (H, I) v =>
    if VarOrder.marked I v then (H, I)
    else (H.insertF (OrderKey.mk (A.get v) v), I.setIfInBounds v true)) (H, I)

/-- What inserting and marking `vs` keeps: a well-formed heap stays well formed, the entries are
the old ones and entries of variables of `vs` with their activities, the marks stay sound, and
every variable of `vs` gets an entry keyed at least at its activity. `addMissing` inserts only
the unmarked ones, so its result is described by the same properties. -/
structure VarOrder.Added (H : VarOrder) (I : Array Bool) (A : Activity) (vs : List ℕ)
    (r : VarOrder × Array Bool) : Prop where
  wf : H.WF → r.1.WF
  mem_old : ∀ e ∈ H, e ∈ r.1
  mem_new : ∀ e ∈ r.1, e ∈ H ∨ ∃ v ∈ vs, e = OrderKey.mk (A.get v) v
  marked : VarOrder.Marked H A I → VarOrder.Marked r.1 A r.2
  covers : VarOrder.Marked H A I → ∀ v ∈ vs, ∃ k, A.get v ≤ k ∧ OrderKey.mk k v ∈ r.1

/-- Inserting one variable and marking it. -/
private theorem VarOrder.added_one (H : VarOrder) (I : Array Bool) (A : Activity) (v : ℕ) :
    VarOrder.Added H I A [v]
      (H.insertF (OrderKey.mk (A.get v) v), I.setIfInBounds v true) := by
  have hmem : ∀ e,
      e ∈ H.insertF (OrderKey.mk (A.get v) v) ↔ e ∈ H ∨ e = OrderKey.mk (A.get v) v := fun e => by
    rw [Batteries.BinaryHeap.insertF_eq, Batteries.BinaryHeap.mem_insert]
  refine ⟨fun h => ?_, fun e he => (hmem e).2 (.inl he), fun e he => ?_, fun h w hw => ?_,
    fun h w hw => ?_⟩
  · rw [Batteries.BinaryHeap.insertF_eq]; exact Batteries.BinaryHeap.insert_wf h
  · rcases (hmem e).1 he with he | rfl
    · exact .inl he
    · exact .inr ⟨v, List.mem_singleton_self v, rfl⟩
  · rcases VarOrder.marked_setIfInBounds hw with ⟨rfl, -⟩ | ⟨-, hw⟩
    · exact ⟨_, le_rfl, (hmem _).2 (.inr rfl)⟩
    · obtain ⟨k, hk, hk'⟩ := h w hw
      exact ⟨k, hk, (hmem _).2 (.inl hk')⟩
  · rw [List.mem_singleton] at hw
    subst hw
    exact ⟨_, le_rfl, (hmem _).2 (.inr rfl)⟩

/-- Two insertions in turn. -/
private theorem VarOrder.Added.trans {H : VarOrder} {I : Array Bool} {A : Activity} {v : ℕ}
    {vs : List ℕ} {r s : VarOrder × Array Bool} (h₁ : VarOrder.Added H I A [v] r)
    (h₂ : VarOrder.Added r.1 r.2 A vs s) : VarOrder.Added H I A (v :: vs) s := by
  refine ⟨fun h => h₂.wf (h₁.wf h), fun e he => h₂.mem_old e (h₁.mem_old e he), fun e he => ?_,
    fun h => h₂.marked (h₁.marked h), fun h w hw => ?_⟩
  · rcases h₂.mem_new e he with he | ⟨w, hw, rfl⟩
    · rcases h₁.mem_new e he with he | ⟨w, hw, rfl⟩
      · exact .inl he
      · exact .inr ⟨w, by simp_all, rfl⟩
    · exact .inr ⟨w, List.mem_cons_of_mem _ hw, rfl⟩
  · rcases List.mem_cons.1 hw with rfl | hw
    · obtain ⟨k, hk, hmem⟩ := h₁.covers h w (List.mem_singleton_self w)
      exact ⟨k, hk, h₂.mem_old _ hmem⟩
    · exact h₂.covers (h₁.marked h) w hw

/-- Nothing inserted. -/
private theorem VarOrder.added_nil (H : VarOrder) (I : Array Bool) (A : Activity) :
    VarOrder.Added H I A [] (H, I) :=
  ⟨id, fun _ he => he, fun _ he => .inl he, id, fun _ _ hw => absurd hw List.not_mem_nil⟩

theorem VarOrder.added_add (H : VarOrder) (I : Array Bool) (A : Activity) (vs : List ℕ) :
    VarOrder.Added H I A vs (VarOrder.add H I A vs) := by
  induction vs generalizing H I with
  | nil => exact VarOrder.added_nil H I A
  | cons v vs ih => exact (VarOrder.added_one H I A v).trans (ih _ _)

/-- Inserting and marking `vs` gives each variable of `vs` an entry keyed at its activity, and
marks only the variables of `vs` besides those already marked. -/
theorem VarOrder.add_spec (H : VarOrder) (I : Array Bool) (A : Activity) (vs : List ℕ) :
    (∀ v ∈ vs, ∃ k, A.get v ≤ k ∧ OrderKey.mk k v ∈ (VarOrder.add H I A vs).1) ∧
    ∀ w, VarOrder.marked (VarOrder.add H I A vs).2 w = true →
      w ∈ vs ∨ VarOrder.marked I w = true := by
  induction vs generalizing H I with
  | nil => exact ⟨fun _ hv => absurd hv List.not_mem_nil, fun _ hw => .inr hw⟩
  | cons v vs ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (H.insertF (OrderKey.mk (A.get v) v)) (I.setIfInBounds v true)
    have hold := (VarOrder.added_add (H.insertF (OrderKey.mk (A.get v) v))
      (I.setIfInBounds v true) A vs).mem_old
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rcases List.mem_cons.1 hw with rfl | hw
      · refine ⟨_, le_rfl, hold _ ?_⟩
        rw [Batteries.BinaryHeap.insertF_eq]
        exact Batteries.BinaryHeap.mem_insert.2 (.inr rfl)
      · exact ih₁ w hw
    · rcases ih₂ w hw with hw | hw
      · exact .inl (List.mem_cons_of_mem _ hw)
      · rcases VarOrder.marked_setIfInBounds hw with ⟨rfl, -⟩ | ⟨-, hw⟩
        · exact .inl List.mem_cons_self
        · exact .inr hw

theorem VarOrder.added_addMissing (H : VarOrder) (I : Array Bool) (A : Activity) (vs : List ℕ) :
    VarOrder.Added H I A vs (VarOrder.addMissing H I A vs) := by
  induction vs generalizing H I with
  | nil => exact VarOrder.added_nil H I A
  | cons v vs ih =>
    change VarOrder.Added H I A (v :: vs) (VarOrder.addMissing
      (if VarOrder.marked I v then (H, I)
        else (H.insertF (OrderKey.mk (A.get v) v), I.setIfInBounds v true)).1
      (if VarOrder.marked I v then (H, I)
        else (H.insertF (OrderKey.mk (A.get v) v), I.setIfInBounds v true)).2 A vs)
    split
    · rename_i hv
      have h₂ := ih H I
      refine ⟨h₂.wf, h₂.mem_old, fun e he => ?_, h₂.marked, fun h w hw => ?_⟩
      · rcases h₂.mem_new e he with he | ⟨w, hw, rfl⟩
        · exact .inl he
        · exact .inr ⟨w, List.mem_cons_of_mem _ hw, rfl⟩
      · rcases List.mem_cons.1 hw with rfl | hw
        · obtain ⟨k, hk, hmem⟩ := h w hv
          exact ⟨k, hk, h₂.mem_old _ hmem⟩
        · exact h₂.covers h w hw
    · exact (VarOrder.added_one H I A v).trans (ih _ _)

/-- **Unmarking the variables `vs`**: as MiniSat bumps a variable in its heap only if it is there,
a variable whose activity grew is unmarked, to be inserted again when it is undone. -/
def VarOrder.unmark (I : Array Bool) (vs : List ℕ) : Array Bool :=
  vs.foldl (fun I v => I.setIfInBounds v false) I

/-- A variable still marked after unmarking `vs` is not among them, and was marked before. -/
theorem VarOrder.marked_unmark {I : Array Bool} {vs : List ℕ} {w : ℕ}
    (h : VarOrder.marked (VarOrder.unmark I vs) w = true) :
    w ∉ vs ∧ VarOrder.marked I w = true := by
  induction vs generalizing I with
  | nil => exact ⟨List.not_mem_nil, h⟩
  | cons v vs ih =>
    obtain ⟨hw, hI⟩ := ih h
    rcases VarOrder.marked_setIfInBounds hI with ⟨-, hf⟩ | ⟨hne, hI⟩
    · exact absurd hf (by decide)
    · exact ⟨fun hm => (List.mem_cons.1 hm).elim hne hw, hI⟩

/-- **All the variables of `V` inserted** in an empty order, with their activities: an order
satisfying the invariant whatever the trail, with any marks of no variable. -/
theorem VarOrder.inv_add_empty (A : Activity) (V : List ℕ) (M : Trail) (occ : ℕ → Bool) (n : ℕ) :
    (VarOrder.add Batteries.BinaryHeap.emptyF (Array.replicate n false) A (dedupVars V)).1.Inv
      (VarOrder.add Batteries.BinaryHeap.emptyF (Array.replicate n false) A (dedupVars V)).2
      A V M occ := by
  have hempty : (Batteries.BinaryHeap.emptyF : VarOrder).WF := by
    rw [Batteries.BinaryHeap.emptyF_eq]; exact Batteries.BinaryHeap.empty_wf
  have hnone : ∀ e, e ∉ (Batteries.BinaryHeap.emptyF : VarOrder) := fun e he => by
    rw [Batteries.BinaryHeap.emptyF_eq] at he
    exact Batteries.BinaryHeap.mem_empty he
  have h := VarOrder.added_add Batteries.BinaryHeap.emptyF (Array.replicate n false) A (dedupVars V)
  have hm : VarOrder.Marked Batteries.BinaryHeap.emptyF A (Array.replicate n false) :=
    fun v hv => by
      simp only [VarOrder.marked, Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hv
      split at hv <;> simp at hv
  refine ⟨h.wf hempty, fun e he => ?_, fun v hv _ _ =>
    h.covers hm v ((mem_dedupKey Function.injective_id).2 hv), h.marked hm⟩
  rcases h.mem_new e he with he | ⟨v, hv, rfl⟩
  · exact absurd he (hnone e)
  · exact (mem_dedupKey Function.injective_id).1 hv

/-- The result of popping: the variable found, if any, the order left and the marks left. -/
structure VarOrder.Popped where
  /-- The variable found. -/
  var : Option ℕ
  /-- The order left. -/
  order : VarOrder
  /-- The marks left. -/
  marks : Array Bool

/-- A popped entry's variable is unmarked; the marks of the other variables stay sound. -/
private theorem VarOrder.Marked.popMaxF {H : VarOrder} {A : Activity} {I : Array Bool}
    {e : OrderKey} (h : VarOrder.Marked H A I) (he : H.maxF = some e) :
    VarOrder.Marked H.popMaxF A (I.setIfInBounds e.var false) := fun v hv => by
  rcases VarOrder.marked_setIfInBounds hv with ⟨-, h'⟩ | ⟨hne, hv⟩
  · exact absurd h' (by decide)
  obtain ⟨k, hk, hmem⟩ := h v hv
  rcases Batteries.BinaryHeap.mem_popMaxF he hmem with h' | h'
  · exact absurd (by rw [← h']) hne
  · exact ⟨k, hk, h'⟩

/-- **Popping the decision variable**: the entries at the top are removed until one is of an
unassigned variable admitted by `occ`, with its current activity. An entry of an assigned or
unadmitted variable, or keyed below the variable's activity, is dropped; an entry keyed above it,
left by a rescaling of the activities, is inserted again with the current activity. The variable
of each entry removed is unmarked in `I`. `none` if the order runs out, or the fuel does. -/
def VarOrder.pop (A : Activity) (asg : Assign) (occ : ℕ → Bool) :
    (fuel : ℕ) → VarOrder → Array Bool → VarOrder.Popped
  | 0, H, I => ⟨none, H, I⟩
  | fuel + 1, H, I =>
    match H.maxF with
    | none => ⟨none, H, I⟩
    | some e =>
      let v := e.var
      let k := e.activity
      let H' := H.popMaxF
      let I' := I.setIfInBounds v false
      if asg.assigned v || !occ v then VarOrder.pop A asg occ fuel H' I'
      else if A.get v = k then ⟨some v, H', I'⟩
      else if A.get v < k then
        VarOrder.pop A asg occ fuel (H'.insertF (OrderKey.mk (A.get v) v)) I'
      else VarOrder.pop A asg occ fuel H' I'

/-- **What popping finds**: the order stays well formed over the variables `V`, with sound marks; a
variable found is in `V`, unassigned, admitted, and of greatest activity among the unassigned
admitted variables of `V`; and every other unassigned admitted variable of `V` stays covered. -/
theorem VarOrder.pop_spec {A : Activity} {V : List ℕ} {occ : ℕ → Bool} (hasg : asg.Agrees M) :
    ∀ (fuel : ℕ) (H : VarOrder) (I : Array Bool), H.WF → (∀ e ∈ H, e.var ∈ V) →
    H.Covers A V M occ → VarOrder.Marked H A I →
    (VarOrder.pop A asg occ fuel H I).order.WF ∧
    (∀ e ∈ (VarOrder.pop A asg occ fuel H I).order, e.var ∈ V) ∧
    (∀ x, (VarOrder.pop A asg occ fuel H I).var = some x →
      x ∈ V ∧ x ∉ Trail.vars M ∧ occ x = true ∧
        ∀ y ∈ V, y ∉ Trail.vars M → occ y = true → A.get y ≤ A.get x) ∧
    (∀ v ∈ V, v ∉ Trail.vars M → occ v = true → (VarOrder.pop A asg occ fuel H I).var ≠ some v →
      ∃ k, A.get v ≤ k ∧ OrderKey.mk k v ∈ (VarOrder.pop A asg occ fuel H I).order) ∧
    VarOrder.Marked (VarOrder.pop A asg occ fuel H I).order A
      (VarOrder.pop A asg occ fuel H I).marks
  | 0, H, I, hwf, hV, hcov, hI => ⟨hwf, hV, fun _ h => absurd h (by simp [VarOrder.pop]),
      fun v hv hvM hvo _ => hcov v hv hvM hvo, hI⟩
  | fuel + 1, H, I, hwf, hV, hcov, hI => by
    unfold VarOrder.pop
    split
    · exact ⟨hwf, hV, fun _ h => absurd h (by simp), fun v hv hvM hvo _ => hcov v hv hvM hvo, hI⟩
    · rename_i e he
      dsimp only
      have hwf' : H.popMaxF.WF := by
        rw [Batteries.BinaryHeap.popMaxF_eq]; exact Batteries.BinaryHeap.popMax_wf hwf
      have hV' : ∀ f ∈ H.popMaxF, f.var ∈ V := fun f hf =>
        hV f (Batteries.BinaryHeap.mem_of_mem_popMaxF hf)
      have hI' := VarOrder.Marked.popMaxF hI he
      have heH : e ∈ H := Batteries.BinaryHeap.mem_of_max he
      have hge : ∀ f ∈ H, f.activity ≤ e.activity := fun f hf => by
        rw [Batteries.BinaryHeap.maxF_eq] at he
        have := Batteries.BinaryHeap.max_ge_all hwf hf (Batteries.BinaryHeap.size_pos_of_max he)
        simp only [he, Option.get_some] at this
        exact OrderKey.activity_le_of_isGE this
      -- a covering entry other than `e` survives the removal of `e`
      have hkeep : ∀ v ∈ V, v ∉ Trail.vars M → occ v = true →
          (∀ k, A.get v ≤ k → OrderKey.mk k v = e → False) →
          ∃ k, A.get v ≤ k ∧ OrderKey.mk k v ∈ H.popMaxF := fun v hv hvM hvo hne => by
        obtain ⟨k, hk, hmem⟩ := hcov v hv hvM hvo
        rcases Batteries.BinaryHeap.mem_popMaxF he hmem with h | h
        · exact absurd h (hne k hk)
        · exact ⟨k, hk, h⟩
      have hother : ∀ v, v ≠ e.var → ∀ k, A.get v ≤ k → OrderKey.mk k v = e → False :=
        fun v hne k _ h => hne (by rw [← h])
      split
      · rename_i hskip
        refine VarOrder.pop_spec hasg fuel _ _ hwf' hV' (fun v hv hvM hvo =>
          hkeep v hv hvM hvo fun k _ h => ?_) hI'
        have hve : v = e.var := by rw [← h]
        subst hve
        rcases Bool.or_eq_true_iff.1 hskip with h' | h'
        · exact hvM ((hasg.assigned_iff _).1 h')
        · simp [hvo] at h'
      · rename_i hunskip
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Bool.not_eq_false'] at hunskip
        have hunassigned : e.var ∉ Trail.vars M := fun h => by
          have := hunskip.1; rw [(hasg.assigned_iff _).2 h] at this; exact absurd this (by decide)
        have hocc : occ e.var = true := by simpa using hunskip.2
        split
        · rename_i hk
          refine ⟨hwf', hV', fun x hx => ?_, fun v hv hvM hvo hne =>
            hkeep v hv hvM hvo (hother v fun h => hne (by rw [h])), hI'⟩
          simp only [Option.some.injEq] at hx
          subst hx
          refine ⟨hV e heH, hunassigned, hocc, fun y hy hyM hyo => ?_⟩
          obtain ⟨k, hk', hmem⟩ := hcov y hy hyM hyo
          exact hk'.trans (hk ▸ hge _ hmem)
        · split
          · rename_i hne hlt
            have hwf'' :
                (H.popMaxF.insertF (OrderKey.mk (A.get e.var) e.var)).WF := by
              rw [Batteries.BinaryHeap.insertF_eq]; exact Batteries.BinaryHeap.insert_wf hwf'
            have hsub : ∀ f ∈ H.popMaxF,
                f ∈ H.popMaxF.insertF (OrderKey.mk (A.get e.var) e.var) := fun f hf => by
                rw [Batteries.BinaryHeap.insertF_eq]
                exact Batteries.BinaryHeap.mem_insert.2 (.inl hf)
            refine VarOrder.pop_spec hasg fuel _ _ hwf'' (fun f hf => ?_) (fun v hv hvM hvo => ?_)
              (hI'.mono hsub fun _ _ => le_rfl)
            · rw [Batteries.BinaryHeap.insertF_eq, Batteries.BinaryHeap.mem_insert] at hf
              rcases hf with hf | rfl
              · exact hV' f hf
              · exact hV e heH
            · rw [Batteries.BinaryHeap.insertF_eq]
              by_cases hve : v = e.var
              · subst hve
                exact ⟨_, le_rfl, Batteries.BinaryHeap.mem_insert.2 (.inr rfl)⟩
              · obtain ⟨k, hk, hmem⟩ := hkeep v hv hvM hvo (hother v hve)
                exact ⟨k, hk, Batteries.BinaryHeap.mem_insert.2 (.inl hmem)⟩
          · rename_i hne hnlt
            refine VarOrder.pop_spec hasg fuel _ _ hwf' hV' (fun v hv hvM hvo =>
              hkeep v hv hvM hvo ?_) hI'
            intro k hk h
            have hv : v = e.var := by rw [← h]
            have hke : k = e.activity := by rw [← h]
            subst hv
            omega

end Cslib.Algorithms.Lean.CDCL
