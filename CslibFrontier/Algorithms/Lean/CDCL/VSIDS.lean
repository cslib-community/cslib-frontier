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
floating-point `inc / 0.95`. As in MiniSat, when an activity exceeds a limit (here `2 ^ 200`) all
activities and the increment are scaled down (here by `2 ^ 100`, with truncation). The increment
starts at `2 ^ 100`. The truncations can make the increment grow less than by `1 / 0.95` and turn
different activities into ties, so decisions can differ from those of floating-point activities.

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

The heap does not remove every scan. Testing whether a popped variable is assigned searches the
trail's variables (`Trail.vars`); the fallback below scans the variables of the database; and since
bumping inserts a variable again instead of moving its entry, the heap can hold more entries than
there are variables. MiniSat's heap moves an entry in place and reads an assignment array.

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

/-- The initial activities of the variables below `n`: all `0`, with increment `2 ^ 100`. -/
def Activity.init (n : ℕ) : Activity := ⟨Array.replicate n 0, 2 ^ 100⟩

/-- The activity of the variable `v`. -/
def Activity.get (A : Activity) (v : ℕ) : ℕ := A.score.getD v 0

/-- The activity above which every activity is scaled down. -/
def Activity.limit : ℕ := 2 ^ 200

/-- **Bumping** `v`: its activity grows by the increment; if it exceeds the limit, every activity
and the increment are divided by `2 ^ 100`. The activities are an array indexed by variable: for
`v` beyond its end, `Array.modify` leaves it unchanged, so bumping `v` does nothing and its
activity stays `0`. The solver's variables are all within the array (`WExec.init` sizes it by the
largest variable of the formula). -/
def Activity.bumpVar (A : Activity) (v : ℕ) : Activity :=
  let score := A.score.modify v (· + A.inc)
  if Activity.limit < score.getD v 0 then ⟨score.map (· >>> 100), A.inc >>> 100⟩
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
      exact Nat.shiftRight_le x 100
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

/-- Entries compare by activity, then by variable. -/
instance : Ord OrderKey := ⟨fun a b => compare a.toPair b.toPair⟩

instance : Std.TransOrd OrderKey :=
  have h : Std.TransOrd (ℕ × ℕ) := inferInstance
  { eq_swap := h.eq_swap, isLE_trans := h.isLE_trans }

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

/-- **The invariant of the variable order** over the variables `V`, with the activities `A`, the
trail `M` and the variables `occ` admits: a well-formed heap of variables of `V`, covering those
admitted and not on the trail. -/
structure VarOrder.Inv (H : VarOrder) (A : Activity) (V : List ℕ) (M : Trail) (occ : ℕ → Bool) :
    Prop where
  wf : H.WF
  vars : ∀ e ∈ H, e.var ∈ V
  covers : H.Covers A V M occ

/-- Inserting the variables `vs` with their activities. -/
def VarOrder.insertVars (H : VarOrder) (A : Activity) (vs : List ℕ) : VarOrder :=
  vs.foldl (fun H v => H.insertF (OrderKey.mk (A.get v) v)) H

theorem VarOrder.insertVars_wf {H : VarOrder} {A : Activity} {vs : List ℕ} (h : H.WF) :
    (H.insertVars A vs).WF := by
  induction vs generalizing H with
  | nil => exact h
  | cons v vs ih =>
    refine ih ?_
    dsimp only
    rw [Batteries.BinaryHeap.insertF_eq]
    exact Batteries.BinaryHeap.insert_wf h

theorem VarOrder.mem_insertVars {H : VarOrder} {A : Activity} {vs : List ℕ} {e : OrderKey} :
    e ∈ H.insertVars A vs ↔ e ∈ H ∨ ∃ v ∈ vs, e = OrderKey.mk (A.get v) v := by
  induction vs generalizing H with
  | nil => simp [VarOrder.insertVars]
  | cons v vs ih =>
    change e ∈ VarOrder.insertVars (H.insertF _) A vs ↔ _
    rw [ih, Batteries.BinaryHeap.insertF_eq, Batteries.BinaryHeap.mem_insert]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

/-- **All the variables of `V` inserted** in an empty order, with their activities: an order
satisfying the invariant whatever the trail. -/
theorem VarOrder.inv_insertVars_empty (A : Activity) (V : List ℕ) (M : Trail) (occ : ℕ → Bool) :
    (VarOrder.insertVars Batteries.BinaryHeap.emptyF A (dedupVars V)).Inv A V M occ := by
  have hempty : (Batteries.BinaryHeap.emptyF : VarOrder).WF := by
    rw [Batteries.BinaryHeap.emptyF_eq]; exact Batteries.BinaryHeap.empty_wf
  refine ⟨VarOrder.insertVars_wf hempty, fun e he => ?_, fun v hv _ _ =>
    ⟨_, le_rfl, VarOrder.mem_insertVars.2 (.inr ⟨v, (mem_dedupKey Function.injective_id).2 hv,
      rfl⟩)⟩⟩
  rcases VarOrder.mem_insertVars.1 he with he | ⟨v, hv, rfl⟩
  · rw [Batteries.BinaryHeap.emptyF_eq] at he
    exact absurd he Batteries.BinaryHeap.mem_empty
  · exact (mem_dedupKey Function.injective_id).1 hv

/-- **Popping the decision variable**: the entries at the top are removed until one is of an
unassigned variable admitted by `occ`, with its current activity. An entry of an assigned or
unadmitted variable, or keyed below the variable's activity, is dropped; an entry keyed above it,
left by a rescaling of the activities, is inserted again with the current activity. `none` if the
order runs out, or the fuel does. -/
def VarOrder.pop (A : Activity) (asg : Assign) (occ : ℕ → Bool) :
    (fuel : ℕ) → VarOrder → Option ℕ × VarOrder
  | 0, H => (none, H)
  | fuel + 1, H =>
    match H.maxF with
    | none => (none, H)
    | some e =>
      let v := e.var
      let k := e.activity
      let H' := H.popMaxF
      if asg.assigned v || !occ v then VarOrder.pop A asg occ fuel H'
      else if A.get v = k then (some v, H')
      else if A.get v < k then
        VarOrder.pop A asg occ fuel (H'.insertF (OrderKey.mk (A.get v) v))
      else VarOrder.pop A asg occ fuel H'

/-- **What popping finds**: the order stays well formed over the variables `V`; a variable found
is in `V`, unassigned, admitted, and of greatest activity among the unassigned admitted variables
of `V`; and every other unassigned admitted variable of `V` stays covered. -/
theorem VarOrder.pop_spec {A : Activity} {V : List ℕ} {occ : ℕ → Bool} (hasg : asg.Agrees M) :
    ∀ (fuel : ℕ) (H : VarOrder), H.WF → (∀ e ∈ H, e.var ∈ V) → H.Covers A V M occ →
    (VarOrder.pop A asg occ fuel H).2.WF ∧
    (∀ e ∈ (VarOrder.pop A asg occ fuel H).2, e.var ∈ V) ∧
    (∀ x, (VarOrder.pop A asg occ fuel H).1 = some x →
      x ∈ V ∧ x ∉ Trail.vars M ∧ occ x = true ∧
        ∀ y ∈ V, y ∉ Trail.vars M → occ y = true → A.get y ≤ A.get x) ∧
    (∀ v ∈ V, v ∉ Trail.vars M → occ v = true → (VarOrder.pop A asg occ fuel H).1 ≠ some v →
      ∃ k, A.get v ≤ k ∧ OrderKey.mk k v ∈ (VarOrder.pop A asg occ fuel H).2)
  | 0, H, hwf, hV, hcov => ⟨hwf, hV, fun _ h => absurd h (by simp [VarOrder.pop]),
      fun v hv hvM hvo _ => hcov v hv hvM hvo⟩
  | fuel + 1, H, hwf, hV, hcov => by
    unfold VarOrder.pop
    split
    · exact ⟨hwf, hV, fun _ h => absurd h (by simp), fun v hv hvM hvo _ => hcov v hv hvM hvo⟩
    · rename_i e he
      dsimp only
      have hwf' : H.popMaxF.WF := by
        rw [Batteries.BinaryHeap.popMaxF_eq]; exact Batteries.BinaryHeap.popMax_wf hwf
      have hV' : ∀ f ∈ H.popMaxF, f.var ∈ V := fun f hf =>
        hV f (Batteries.BinaryHeap.mem_of_mem_popMaxF hf)
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
        refine VarOrder.pop_spec hasg fuel _ hwf' hV' fun v hv hvM hvo =>
          hkeep v hv hvM hvo fun k _ h => ?_
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
            hkeep v hv hvM hvo (hother v fun h => hne (by rw [h]))⟩
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
            refine VarOrder.pop_spec hasg fuel _ hwf'' (fun f hf => ?_) fun v hv hvM hvo => ?_
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
            refine VarOrder.pop_spec hasg fuel _ hwf' hV' fun v hv hvM hvo =>
              hkeep v hv hvM hvo ?_
            intro k hk h
            have hv : v = e.var := by rw [← h]
            have hke : k = e.activity := by rw [← h]
            subst hv
            omega

end Cslib.Algorithms.Lean.CDCL
