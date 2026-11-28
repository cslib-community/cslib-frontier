/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Arborescence.ChuLiuEdmonds
import CslibFrontier.Foundations.Data.List.ArgMin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.MinMax

/-!
# Materialized-table Chu–Liu/Edmonds

Whereas `Cslib.Algorithms.Lean.Arborescence.edmonds` passes contracted adjacency predicates and cost
functions across recursive calls as unmemoised closures, this module materializes per-level `n × n`
`Vector` tables (`AdjTable`, `CostTable`) indexed through `FinEnum.equiv` and runs the contraction
algorithm over flat `Fin n`-indexed `Vector` arrays (`edmondsTable`, `edmondsOutTable`).

Each contraction level stores its contracted graph, costs, cycle membership mask, other-cycle-cost
sum, and best-entry / best-exit tables in flat `Fin n`-indexed `Vector` arrays before recursing, so
no level re-evaluates earlier levels. Transfer lemmas identify the returned parent map with
`ChuLiuEdmonds.edmonds` (`edmondsTable_eq_edmonds`, `edmondsOutTable_eq_edmondsOut`), transferring
all correctness and optimality theorems (`edmondsTable_spec`, `edmondsTable_optimal`,
`edmondsOutTable_spec`).

Machine-checked running-time bounds live in sibling modules:
`CslibFrontier.Algorithms.WordRAM.Arborescence` proves `O(n³)` Word-RAM running time on
materialized matrices, and `CslibFrontier.Algorithms.Lean.Arborescence.PolyTime` proves multi-tape
Turing-machine polynomial time (`P`) on binary integer weights.

## Main definitions

* `Cslib.Algorithms.Lean.Arborescence.AdjTable`, `CostTable`, `ParentTable`: materialized `Vector`
  tables on `Fin n`.
* `Cslib.Algorithms.Lean.Arborescence.SelectParentsResult`, `selectParents`, `findCycleTable`,
  `cycleMask`, `otherCycleCost`, `bestEntryTable`, `bestExitTable`, `contractAdjTable`,
  `contractCostTable`, `expandParentTable`: per-level `Vector`-table operations on `Fin n`.
* `Cslib.Algorithms.Lean.Arborescence.edmondsTableAux`: fuel-indexed contraction solver on `Fin n`.
* `Cslib.Algorithms.Lean.Arborescence.edmondsTable`,
  `Cslib.Algorithms.Lean.Arborescence.edmondsOutTable`: entry points for arbitrary `[FinEnum V]`,
  transported via `FinEnum.equiv`.

## Main results

* `Cslib.Algorithms.Lean.Arborescence.edmondsTableAux_eq_edmondsAux`,
  `Cslib.Algorithms.Lean.Arborescence.edmondsTable_eq_edmonds`,
  `Cslib.Algorithms.Lean.Arborescence.edmondsOutTable_eq_edmondsOut`: the materialized table
  algorithm returns the exact same parent map as `edmondsAux`, `edmonds`, and `edmondsOut`.
* `Cslib.Algorithms.Lean.Arborescence.edmondsTable_spec`,
  `Cslib.Algorithms.Lean.Arborescence.edmondsTable_optimal`,
  `Cslib.Algorithms.Lean.Arborescence.edmondsOutTable_spec`: transferred correctness and
  optimality.

## References

* [J. Edmonds, *Optimum Branchings*][Edmonds1967Branchings], Section 4
-/

public section

namespace Cslib.Algorithms.Lean.Arborescence

/-! ### Materialized tables and helpers -/

/-- An `n × n` materialized adjacency matrix over `Fin n`. -/
abbrev AdjTable (n : ℕ) : Type := Vector (Vector Bool n) n

/-- An `n × n` materialized arc-cost table over `Fin n`. -/
abbrev CostTable (β : Type*) (n : ℕ) : Type _ := Vector (Vector β n) n

/-- A materialized parent vector over `Fin n`. -/
abbrev ParentTable (n : ℕ) : Type := Vector (Fin n) n

/-- Materialize the `n × n` Boolean adjacency matrix of a relation on `Fin n`. -/
@[expose] def initAdjTable (n : ℕ) (adj : Fin n → Fin n → Bool) : AdjTable n :=
  Vector.ofFn fun u : Fin n => Vector.ofFn fun w : Fin n => adj u w

/-- Materialize the `n × n` cost matrix on `Fin n`. -/
@[expose] def initCostTable {β : Type*} (n : ℕ) (cost : Fin n → Fin n → β) : CostTable β n :=
  Vector.ofFn fun u : Fin n => Vector.ofFn fun w : Fin n => cost u w

@[simp]
theorem getElem_initAdjTable (n : ℕ) (adj : Fin n → Fin n → Bool) (u w : Fin n) :
    (initAdjTable n adj)[u.val][w.val] = adj u w := by
  simp [initAdjTable]

@[simp]
theorem getElem_initCostTable {β : Type*} (n : ℕ) (cost : Fin n → Fin n → β) (u w : Fin n) :
    (initCostTable n cost)[u.val][w.val] = cost u w := by
  simp [initCostTable]

/-- Scan `List.finRange n` for the first minimizer of `val` satisfying `pred`. -/
@[expose] def argMinFin {β : Type*} [LinearOrder β] (n : ℕ) (pred : Fin n → Bool)
    (val : Fin n → β) : Option (Fin n) :=
  (List.finRange n).foldl
    (fun acc i => if pred i then List.argAux (fun x y => val x < val y) acc i else acc)
    none

private theorem foldl_argAux_skip {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (pred : α → Bool) (l : List α) (acc : Option α) :
    l.foldl (fun a i => if pred i then List.argAux r a i else a) acc =
      (l.filter pred).foldl (List.argAux r) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons i l ih => cases h : pred i <;> simp [h, ih]

private theorem argMinFin_eq_argmin {β : Type*} [LinearOrder β] (n : ℕ) (pred : Fin n → Bool)
    (val : Fin n → β) :
    argMinFin n pred val = ((List.finRange n).filter pred).argmin val :=
  foldl_argAux_skip (fun x y => val x < val y) pred (List.finRange n) none

/-! ### Per-level subroutines -/

section Level

variable {β : Type*} [LinearOrder β] {n : ℕ}

/-- Result of selecting optimal parents. -/
structure SelectParentsResult (n : ℕ) where
  /-- True if every non-root node has at least one incoming edge, so a valid parent was found. -/
  feasible : Bool
  /-- The selected parents. -/
  parents : ParentTable n

/-- Select the cheapest outgoing candidate parent for every non-root vertex (`r` maps to `some r`),
check feasibility, and materialize the parent vector `f`. -/
@[expose] def selectParents (a : AdjTable n) (c : CostTable β n) (r : Fin n) :
    SelectParentsResult n :=
  let opts := Vector.ofFn fun v : Fin n =>
    if v = r then some r
    else argMinFin n (fun w => a[v.val][w.val] && w != v) (fun w => c[v.val][w.val])
  let feas := (List.finRange n).foldl (fun acc v => acc && opts[v.val].isSome) true
  let tbl := Vector.ofFn fun v : Fin n => opts[v.val].getD v
  { feasible := feas, parents := tbl }

private theorem selectParents_eq (a : AdjTable n) (c : CostTable β n) (r : Fin n) :
    let optFn : Fin n → Option (Fin n) := fun v =>
      if v = r then some r
      else ((List.finRange n).filter fun w => a[v.val][w.val] && w != v).argmin
        (fun w => c[v.val][w.val])
    selectParents a c r =
      { feasible := (List.finRange n).all (fun v => (optFn v).isSome)
      , parents := Vector.ofFn fun v => (optFn v).getD v } := by
  intro optFn
  have hopts : (Vector.ofFn fun v : Fin n =>
      if v = r then some r
      else argMinFin n (fun w => a[v.val][w.val] && w != v) (fun w => c[v.val][w.val])) =
      Vector.ofFn optFn := by
    ext i hi
    simp only [Vector.getElem_ofFn, optFn]
    split_ifs <;> simp [argMinFin_eq_argmin]
  have hfold : ∀ (l : List (Fin n)) (b : Bool),
      l.foldl (fun acc v => acc && (Vector.ofFn optFn)[v.val].isSome) b =
        (b && l.all fun v => (optFn v).isSome) := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      intro b; rw [List.foldl_cons, ih, List.all_cons, Vector.getElem_ofFn, Bool.and_assoc]
  unfold selectParents
  simp only [hopts, hfold, Bool.true_and]
  congr 1
  ext i hi
  simp [Vector.getElem_ofFn]

/-- Fold state for cycle search. -/
private structure CycleSearchState (n : ℕ) where
  /-- Current node in the traversal. -/
  current : Fin n
  /-- True if the traversal has hit the starting node again. -/
  hit : Bool

/-- Test whether iterating `f` starting from `x` returns to `x` within `n` steps. -/
def hasCycleFrom (x : Fin n) (f : ParentTable n) : Bool :=
  let st := (List.range n).foldl
    (fun (st : CycleSearchState n) _ =>
      let nxt := f[st.current.val]
      { current := nxt, hit := st.hit || (nxt == x) : CycleSearchState n })
    ({ current := x, hit := false } : CycleSearchState n)
  st.hit

theorem hasCycleFrom_eq (x : Fin n) (f : ParentTable n) :
    hasCycleFrom x f =
      (List.range n).any fun k => (fun i : Fin n => f[i.val])^[k + 1] x == x := by
  unfold hasCycleFrom
  have hinv : ∀ m : ℕ,
      (List.range m).foldl
        (fun (st : CycleSearchState n) _ =>
          { current := f[st.current.val], hit := st.hit || (f[st.current.val] == x) })
        { current := x, hit := false } =
      { current := (fun i : Fin n => f[i.val])^[m] x,
        hit := (List.range m).any fun k => (fun i : Fin n => f[i.val])^[k + 1] x == x } := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
        List.any_append, List.any_cons, List.any_nil, Bool.or_false, Function.iterate_succ_apply']
  exact congrArg CycleSearchState.hit (hinv n)

/-- Find the first vertex `x ≠ r` lying on a cycle of `f`, if any. -/
@[expose] def findCycleTable (r : Fin n) (f : ParentTable n) : Option (Fin n) :=
  (List.finRange n).foldl
    (fun acc x =>
      match acc with
      | some x0 => some x0
      | none =>
        if x == r then none
        else if hasCycleFrom x f then some x else none)
    none

private def findStep {α : Type*} (p : α → Bool) (a : Option α) (x : α) : Option α :=
  match a with
  | some x0 => some x0
  | none => if p x then some x else none

private theorem foldl_find_step {α : Type*} (p : α → Bool) :
    ∀ (l : List α) (acc : Option α),
      l.foldl (findStep p) acc =
      match acc with | some x0 => some x0 | none => l.find? p
  | [], acc => by cases acc <;> rfl
  | x :: l, some x0 => by
    simp only [List.foldl_cons, findStep]
    exact foldl_find_step p l (some x0)
  | x :: l, none => by
    cases h : p x
    · simp only [List.foldl_cons, findStep, List.find?_cons, h, Bool.false_eq_true, ↓reduceIte]
      exact foldl_find_step p l none
    · simp only [List.foldl_cons, findStep, List.find?_cons, h, ↓reduceIte]
      exact foldl_find_step p l (some x)

private theorem findCycleTable_eq (r : Fin n) (f : ParentTable n) :
    findCycleTable r f =
      (List.finRange n).find? fun x =>
        x != r && (List.range n).any fun k => (fun i : Fin n => f[i.val])^[k + 1] x == x := by
  unfold findCycleTable
  let p : Fin n → Bool := fun x =>
    x != r && (List.range n).any fun k => (fun i : Fin n => f[i.val])^[k + 1] x == x
  rw [show (fun acc x => _) = findStep p from funext fun acc => funext fun x => by
    cases acc with
    | some _ => rfl
    | none => by_cases hxr : x == r <;> simp [findStep, p, hxr, bne, hasCycleFrom_eq]]
  exact foldl_find_step p (List.finRange n) none

/-- Fold state for cycle masking. -/
private structure CycleMaskState (n : ℕ) where
  /-- Current node in the traversal. -/
  current : Fin n
  /-- Accumulator for the cycle mask. -/
  mask : Vector Bool n

/-- Materialize the cycle indicator vector `inCycle` of the orbit `cycleOf f x0`. -/
def cycleMask (f : ParentTable n) (x0 : Fin n) : Vector Bool n :=
  let init := Vector.ofFn fun _ : Fin n => false
  let st := (List.range n).foldl
    (fun (st : CycleMaskState n) _ =>
      let cur := st.current
      { current := f[cur.val], mask := st.mask.set cur.val true cur.isLt : CycleMaskState n })
    ({ current := x0, mask := init } : CycleMaskState n)
  st.mask

private theorem cycleMask_loop_spec (f : ParentTable n) (x0 : Fin n) :
    ∀ (m : ℕ) (init : Vector Bool n),
      let res := (List.range m).foldl
        (fun (st : CycleMaskState n) _ =>
          let cur := st.current
          { current := f[cur.val], mask := st.mask.set cur.val true cur.isLt : CycleMaskState n })
        ({ current := x0, mask := init } : CycleMaskState n)
      res.current = (fun i : Fin n => f[i.val])^[m] x0 ∧
        ∀ j : Fin n,
          (res.mask[j.val] = true ↔
            init[j.val] = true ∨ ∃ k < m, (fun i : Fin n => f[i.val])^[k] x0 = j)
  | 0, _ => by simp
  | m + 1, init => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨ih1, ih2⟩ := cycleMask_loop_spec f x0 m init
    refine ⟨by simp only [ih1, Function.iterate_succ_apply'], fun j => ?_⟩
    simp only [Vector.getElem_set, ih1, Nat.lt_succ_iff_lt_or_eq]
    by_cases hj : ((fun i : Fin n => f[i.val])^[m] x0).val = j.val
    · have hj' : (fun i : Fin n => f[i.val])^[m] x0 = j := Fin.ext hj
      simp only [hj, ↓reduceIte, true_iff]
      exact Or.inr ⟨m, Or.inr rfl, hj'⟩
    · simp only [hj, ↓reduceIte, ih2 j]
      refine or_congr_right ⟨fun ⟨k, hk, h⟩ => ⟨k, Or.inl hk, h⟩, ?_⟩
      rintro ⟨k, hk | rfl, h⟩
      · exact ⟨k, hk, h⟩
      · exact absurd (congrArg Fin.val h) hj

theorem getElem_cycleMask (f : ParentTable n) (x0 y : Fin n) :
    (cycleMask f x0)[y.val] = true ↔ ∃ k < n, (fun i : Fin n => f[i.val])^[k] x0 = y := by
  unfold cycleMask
  simpa using (cycleMask_loop_spec f x0 n (Vector.ofFn fun _ : Fin n => false)).2 y

/-- Materialize `bestEntry` for every vertex `u : Fin n`. -/
@[expose] def bestEntryTable (a : AdjTable n) (c : CostTable β n) (inCycle : Vector Bool n) :
    Vector (Option (Fin n)) n :=
  Vector.ofFn fun u : Fin n =>
    argMinFin n (fun y => inCycle[y.val] && a[u.val][y.val]) (fun y => c[u.val][y.val])

private theorem getElem_bestEntryTable (a : AdjTable n) (c : CostTable β n)
    (inCycle : Vector Bool n) (u : Fin n) :
    (bestEntryTable a c inCycle)[u.val] =
      ((List.finRange n).filter fun y => inCycle[y.val] && a[u.val][y.val]).argmin
        (fun y => c[u.val][y.val]) := by
  simp [bestEntryTable, argMinFin_eq_argmin]

section AddMonoidLevel

variable [AddCommMonoid β]

/-- Tabulate for every `x : Fin n` the sum `∑ y ∈ C.erase x, c y (f y)` when `x ∈ C`, without
using subtraction. -/
@[expose] def otherCycleCost (c : CostTable β n) (f : ParentTable n)
    (inCycle : Vector Bool n) : Vector β n :=
  Vector.ofFn fun x : Fin n =>
    if inCycle[x.val] then
      (List.finRange n).foldl
        (fun acc y => if inCycle[y.val] && y != x then acc + c[y.val][f[y.val].val] else acc)
        0
    else 0

omit [LinearOrder β] in
private theorem foldl_add_filter {α : Type*} (pred : α → Bool) (val : α → β) :
    ∀ (l : List α) (acc : β),
      l.foldl (fun a y => if pred y then a + val y else a) acc =
        acc + ((l.filter pred).map val).sum
  | [], acc => by simp
  | y :: l, acc => by
    cases h : pred y <;> simp [h, foldl_add_filter pred val l, add_assoc]

omit [LinearOrder β] in
private theorem getElem_otherCycleCost (c : CostTable β n) (f : ParentTable n)
    (inCycle : Vector Bool n) (C : Finset (Fin n)) (hC : ∀ y : Fin n, inCycle[y.val] = true ↔ y ∈ C)
    {x : Fin n} (hx : x ∈ C) :
    (otherCycleCost c f inCycle)[x.val] = ∑ y ∈ C.erase x, c[y.val][f[y.val].val] := by
  unfold otherCycleCost
  simp only [Vector.getElem_ofFn, (hC x).mpr hx, ↓reduceIte, foldl_add_filter, zero_add]
  rw [← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
  congr 1
  ext y
  simp [hC, and_comm]

/-- Materialize `bestExit` for every vertex `w : Fin n`. -/
@[expose] def bestExitTable (a : AdjTable n) (c : CostTable β n)
    (inCycle : Vector Bool n) (other : Vector β n) : Vector (Option (Fin n)) n :=
  Vector.ofFn fun w : Fin n =>
    argMinFin n (fun x => inCycle[x.val] && a[x.val][w.val])
      (fun x => c[x.val][w.val] + other[x.val])

private theorem getElem_bestExitTable (a : AdjTable n) (c : CostTable β n)
    (inCycle : Vector Bool n) (other : Vector β n) (w : Fin n) :
    (bestExitTable a c inCycle other)[w.val] =
      ((List.finRange n).filter fun x => inCycle[x.val] && a[x.val][w.val]).argmin
        (fun x => c[x.val][w.val] + other[x.val]) := by
  simp [bestExitTable, argMinFin_eq_argmin]

end AddMonoidLevel

/-- Materialize the contracted `n × n` adjacency table using `O(1)` table lookups per cell. -/
@[expose] def contractAdjTable (a : AdjTable n) (inCycle : Vector Bool n)
    (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 r : Fin n) : AdjTable n :=
  Vector.ofFn fun u : Fin n => Vector.ofFn fun w : Fin n =>
    if inCycle[u.val] then
      if u == x0 then !(inCycle[w.val]) && (bestExit[w.val]).isSome
      else w == r
    else
      if inCycle[w.val] then (w == x0) && (bestEntry[u.val]).isSome
      else a[u.val][w.val]

@[simp]
theorem getElem_contractAdjTable (a : AdjTable n) (inCycle : Vector Bool n)
    (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 r u w : Fin n) :
    (contractAdjTable a inCycle bestEntry bestExit x0 r)[u.val][w.val] =
      if inCycle[u.val] then
        if u == x0 then !(inCycle[w.val]) && (bestExit[w.val]).isSome
        else w == r
      else
        if inCycle[w.val] then (w == x0) && (bestEntry[u.val]).isSome
        else a[u.val][w.val] := by
  simp [contractAdjTable]

omit [LinearOrder β] in
/-- Materialize the contracted `n × n` cost table using `O(1)` table lookups per cell. -/
@[expose] def contractCostTable [AddCommMonoid β] (c : CostTable β n) (inCycle : Vector Bool n)
    (other : Vector β n) (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 : Fin n) :
    CostTable β n :=
  Vector.ofFn fun u : Fin n => Vector.ofFn fun w : Fin n =>
    if inCycle[u.val] then
      if u == x0 then
        match bestExit[w.val] with
        | some x => c[x.val][w.val] + other[x.val]
        | none => c[u.val][w.val]
      else 0
    else
      if w == x0 then
        match bestEntry[u.val] with
        | some y => c[u.val][y.val]
        | none => c[u.val][w.val]
      else c[u.val][w.val]

omit [LinearOrder β] in
@[simp]
theorem getElem_contractCostTable [AddCommMonoid β] (c : CostTable β n)
    (inCycle : Vector Bool n) (other : Vector β n)
    (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 u w : Fin n) :
    (contractCostTable c inCycle other bestEntry bestExit x0)[u.val][w.val] =
      if inCycle[u.val] then
        if u == x0 then
          match bestExit[w.val] with
          | some x => c[x.val][w.val] + other[x.val]
          | none => c[u.val][w.val]
        else 0
      else
        if w == x0 then
          match bestEntry[u.val] with
          | some y => c[u.val][y.val]
          | none => c[u.val][w.val]
        else c[u.val][w.val] := by
  simp [contractCostTable]

/-- Expand a contracted parent vector `q` using the precomputed level tables. -/
@[expose] def expandParentTable (f : ParentTable n) (inCycle : Vector Bool n)
    (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 : Fin n) (q : ParentTable n) :
    ParentTable n :=
  Vector.ofFn fun v : Fin n =>
    if inCycle[v.val] then
      match bestExit[(q[x0.val]).val] with
      | some x => if v == x then q[x0.val] else f[v.val]
      | none => f[v.val]
    else if q[v.val] == x0 then (bestEntry[v.val]).getD v
    else q[v.val]

@[simp]
theorem getElem_expandParentTable (f : ParentTable n) (inCycle : Vector Bool n)
    (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 : Fin n) (q : ParentTable n)
    (v : Fin n) :
    (expandParentTable f inCycle bestEntry bestExit x0 q)[v.val] =
      if inCycle[v.val] then
        match bestExit[(q[x0.val]).val] with
        | some x => if v == x then q[x0.val] else f[v.val]
        | none => f[v.val]
      else if q[v.val] == x0 then (bestEntry[v.val]).getD v
      else q[v.val] := by
  simp [expandParentTable]

end Level

/-! ### Full contraction solver -/

section Main

variable {β : Type*} [LinearOrder β] [AddCommMonoid β]

/-- Materialized-table Chu–Liu/Edmonds recursion with fuel `fuel` on `Fin n`. -/
@[expose] def edmondsTableAux {n : ℕ} (r : Fin n) :
    ℕ → AdjTable n → CostTable β n → Option (ParentTable n)
  | 0, _, _ => none
  | fuel + 1, a, c =>
    let sel := selectParents a c r
    if sel.feasible then
      match findCycleTable r sel.parents with
      | none => some sel.parents
      | some x0 =>
        let inCycle := cycleMask sel.parents x0
        let other := otherCycleCost c sel.parents inCycle
        let bEntry := bestEntryTable a c inCycle
        let bExit := bestExitTable a c inCycle other
        let a' := contractAdjTable a inCycle bEntry bExit x0 r
        let c' := contractCostTable c inCycle other bEntry bExit x0
        (edmondsTableAux r fuel a' c').map
          (expandParentTable sel.parents inCycle bEntry bExit x0)
    else none

/-! ### Equivalence with `edmondsAux` -/

section Transfer

omit [AddCommMonoid β] in
private theorem selectParents_spec {V : Type*} [FinEnum V]
    (a : AdjTable (FinEnum.card V)) (c : CostTable β (FinEnum.card V))
    (aV : V → V → Bool) (cV : V → V → β) (rV : V)
    (ha : ∀ u w, a[u.val][w.val] =
      aV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hc : ∀ u w, c[u.val][w.val] =
      cV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w)) :
    let sel := selectParents a c (@FinEnum.equiv V _ rV)
    (sel.feasible = true ↔ ∀ v : V, v ≠ rV → candidates aV v ≠ []) ∧
      ∀ i : Fin (FinEnum.card V),
        (@FinEnum.equiv V _).symm (sel.parents[i.val]) =
          cheapestParent aV cV rV ((@FinEnum.equiv V _).symm i) := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  let optFn : Fin (FinEnum.card V) → Option (Fin (FinEnum.card V)) := fun v =>
    if v = e rV then some (e rV)
    else ((List.finRange _).filter fun w => a[v.val][w.val] && w != v).argmin
      (fun w => c[v.val][w.val])
  have hcand (v : Fin (FinEnum.card V)) :
      ((List.finRange _).filter fun w => a[v.val][w.val] && w != v).map e.symm =
        candidates aV (e.symm v) := by
    unfold candidates FinEnum.toList
    rw [List.filter_map]
    refine congrArg (List.map e.symm) (List.filter_congr fun w _ => ?_)
    have hneq : (w != v) = (e.symm w != e.symm v) :=
      Bool.eq_iff_iff.mpr (by simp [bne_iff_ne, e.symm.injective.eq_iff])
    rw [ha v w, hneq]
    rfl
  have hopt_eq (v : Fin (FinEnum.card V)) :
      (optFn v).map e.symm =
        if e.symm v = rV then some rV
        else List.argmin (cV (e.symm v)) (candidates aV (e.symm v)) := by
    dsimp only [optFn]
    by_cases hv : v = e rV
    · subst hv
      simp [e]
    · have hvV : e.symm v ≠ rV := fun h => hv (e.symm_apply_eq.mp h)
      simp only [hv, ↓reduceIte, hvV, ← hcand v, ← List.argmin_map_equiv e.symm _ (cV (e.symm v))]
      congr 1
      exact congrArg (List.argmin · _) (funext (hc v))
  have hopt_some (v : Fin (FinEnum.card V)) :
      (optFn v).isSome = true ↔ (e.symm v = rV ∨ candidates aV (e.symm v) ≠ []) := by
    have h := congrArg Option.isSome (hopt_eq v)
    simp only [Option.isSome_map] at h
    rw [h]
    split_ifs with hvr <;> simp [hvr, Option.isSome_iff_ne_none, List.argmin_eq_none]
  rw [selectParents_eq]
  dsimp only
  constructor
  · rw [List.all_eq_true]
    exact ⟨fun h v hv =>
        by simpa [e, hv] using (hopt_some (e v)).mp (h (e v) (List.mem_finRange _)),
      fun h v _ => (hopt_some v).mpr ((em _).imp_right (h _))⟩
  · intro i
    have h := congrArg (Option.getD · (e.symm i)) (hopt_eq i)
    simp only [Vector.getElem_ofFn]
    unfold cheapestParent
    rw [show ∀ o : Option (Fin (FinEnum.card V)),
        e.symm (o.getD i) = (o.map e.symm).getD (e.symm i) from fun o => by cases o <;> rfl, h]
    by_cases hir : e.symm i = rV <;> simp [e, hir]

private theorem findCycleTable_spec {V : Type*} [FinEnum V] (f : ParentTable (FinEnum.card V))
    (fV : V → V)
    (hf : ∀ i : Fin (FinEnum.card V),
      (@FinEnum.equiv V _).symm f[i.val] = fV ((@FinEnum.equiv V _).symm i))
    (rV : V) :
    (findCycleTable (@FinEnum.equiv V _ rV) f).map (@FinEnum.equiv V _).symm =
      findCycle rV fV := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  have hsem : Function.Semiconj e.symm (fun i => f[i.val]) fV := hf
  rw [findCycleTable_eq]
  unfold findCycle FinEnum.toList
  rw [List.find?_map]
  congr 2
  funext x
  have hxr : (x != e rV) = (e.symm x != rV) :=
    Bool.eq_iff_iff.mpr (by simp [bne_iff_ne, e.symm_apply_eq])
  rw [hxr]
  congr 1
  refine congrArg (List.any _) (funext fun k => ?_)
  have hk := hsem.iterate_right (k + 1) x
  exact Bool.eq_iff_iff.mpr (by
    simp only [beq_iff_eq]
    exact ⟨fun h => by rw [← hk, h], fun h => e.symm.injective (hk ▸ h)⟩)

private theorem cycleMask_spec {V : Type*} [FinEnum V] (f : ParentTable (FinEnum.card V))
    (fV : V → V)
    (hf : ∀ i, (@FinEnum.equiv V _).symm f[i.val] = fV ((@FinEnum.equiv V _).symm i))
    (x0 y : Fin (FinEnum.card V)) :
    (cycleMask f x0)[y.val] = true ↔
      (@FinEnum.equiv V _).symm y ∈ cycleOf fV ((@FinEnum.equiv V _).symm x0) := by
  have hsem : Function.Semiconj (@FinEnum.equiv V _).symm (fun i => f[i.val]) fV := hf
  rw [getElem_cycleMask, mem_cycleOf]
  exact ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, by rw [← hsem.iterate_right k x0, h]⟩,
    fun ⟨k, hk, h⟩ => ⟨k, hk, (@FinEnum.equiv V _).symm.injective (by rw [hsem.iterate_right, h])⟩⟩

omit [LinearOrder β] in
private theorem otherCycleCost_spec {V : Type*} [FinEnum V]
    (c : CostTable β (FinEnum.card V)) (f : ParentTable (FinEnum.card V))
    (inCycle : Vector Bool (FinEnum.card V))
    (cV : V → V → β) (fV : V → V) (C : Finset V)
    (hc : ∀ u w, c[u.val][w.val] =
      cV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hf : ∀ i, (@FinEnum.equiv V _).symm f[i.val] = fV ((@FinEnum.equiv V _).symm i))
    (hmask : ∀ y, inCycle[y.val] = true ↔ (@FinEnum.equiv V _).symm y ∈ C)
    {x : Fin (FinEnum.card V)} (hx : inCycle[x.val] = true) :
    (otherCycleCost c f inCycle)[x.val] =
      ∑ y ∈ C.erase ((@FinEnum.equiv V _).symm x), cV y (fV y) := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  let CFin : Finset (Fin (FinEnum.card V)) := Finset.univ.filter fun y => inCycle[y.val] = true
  have hCFin y : inCycle[y.val] = true ↔ y ∈ CFin := by simp [CFin]
  rw [getElem_otherCycleCost c f inCycle CFin hCFin ((hCFin x).mp hx)]
  refine Finset.sum_bij (fun y _ => e.symm y)
    (fun y hy => by
      rw [Finset.mem_erase] at hy ⊢
      exact ⟨e.symm.injective.ne hy.1, (hmask y).mp ((hCFin y).mpr hy.2)⟩)
    (fun _ _ _ _ h => e.symm.injective h)
    (fun y hy => by
      rw [Finset.mem_erase] at hy
      exact ⟨e y, Finset.mem_erase.mpr ⟨fun h => hy.1 (by simpa [e] using congrArg e.symm h),
        (hCFin (e y)).mp ((hmask (e y)).mpr (by simpa [e] using hy.2))⟩, by simp [e]⟩)
    (fun y _ => by rw [hc y f[y.val], hf y])

omit [AddCommMonoid β] in
private theorem bestEntryTable_spec {V : Type*} [FinEnum V]
    (a : AdjTable (FinEnum.card V)) (c : CostTable β (FinEnum.card V))
    (inCycle : Vector Bool (FinEnum.card V))
    (aV : V → V → Bool) (cV : V → V → β) (C : Finset V)
    (ha : ∀ u w, a[u.val][w.val] =
      aV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hc : ∀ u w, c[u.val][w.val] =
      cV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hmask : ∀ y, inCycle[y.val] = true ↔ (@FinEnum.equiv V _).symm y ∈ C)
    (u : Fin (FinEnum.card V)) :
    (bestEntryTable a c inCycle)[u.val].map (@FinEnum.equiv V _).symm =
      bestEntry aV cV C ((@FinEnum.equiv V _).symm u) := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  rw [getElem_bestEntryTable]
  unfold bestEntry FinEnum.toList
  rw [show (fun y => c[u.val][y.val]) = cV (e.symm u) ∘ e.symm from funext (hc u),
    List.argmin_map_equiv e.symm, List.filter_map]
  refine congrArg (List.argmin _) (congrArg (List.map e.symm) (List.filter_congr fun y _ => ?_))
  have hy : inCycle[y.val] = decide (e.symm y ∈ C) := Bool.eq_iff_iff.mpr (by simpa using hmask y)
  rw [hy, ha u y]
  rfl

private theorem bestExitTable_spec {V : Type*} [FinEnum V]
    (a : AdjTable (FinEnum.card V)) (c : CostTable β (FinEnum.card V))
    (inCycle : Vector Bool (FinEnum.card V)) (other : Vector β (FinEnum.card V))
    (aV : V → V → Bool) (cV : V → V → β) (fV : V → V) (C : Finset V)
    (ha : ∀ u w, a[u.val][w.val] =
      aV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hc : ∀ u w, c[u.val][w.val] =
      cV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hmask : ∀ y, inCycle[y.val] = true ↔ (@FinEnum.equiv V _).symm y ∈ C)
    (hother : ∀ {x}, inCycle[x.val] = true →
      other[x.val] = ∑ y ∈ C.erase ((@FinEnum.equiv V _).symm x), cV y (fV y))
    (w : Fin (FinEnum.card V)) :
    (bestExitTable a c inCycle other)[w.val].map (@FinEnum.equiv V _).symm =
      bestExit aV cV fV C ((@FinEnum.equiv V _).symm w) := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  set l := (List.finRange (FinEnum.card V)).filter fun x => inCycle[x.val] && a[x.val][w.val]
  rw [getElem_bestExitTable]
  unfold bestExit FinEnum.toList
  have hcomp : l.argmin (fun x => c[x.val][w.val] + other[x.val]) =
      l.argmin ((fun x => exitCost cV fV C x (e.symm w)) ∘ e.symm) :=
    List.argmin_congr_mem l l (fun _ h => h) fun x hx => by
      have hxin : inCycle[x.val] = true := (Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp hx).2).1
      dsimp only [Function.comp_def, exitCost]
      rw [hc x w, hother hxin]
  rw [hcomp, List.argmin_map_equiv e.symm, List.filter_map]
  refine congrArg (List.argmin _) (congrArg (List.map e.symm) (List.filter_congr fun x _ => ?_))
  have hx : inCycle[x.val] = decide (e.symm x ∈ C) := Bool.eq_iff_iff.mpr (by simpa using hmask x)
  rw [hx, ha x w]
  rfl

omit [LinearOrder β] [AddCommMonoid β] in
private theorem contractAdjTable_eq {V : Type*} [FinEnum V] {n : ℕ} (e : V ≃ Fin n)
    (a : AdjTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n)
    (x0 : Fin n) (aV : V → V → Bool) (C : Finset V) (rV : V)
    (ha : ∀ u w, a[u.val][w.val] = aV (e.symm u) (e.symm w))
    (hmask : ∀ y, inCycle[y.val] = true ↔ e.symm y ∈ C)
    (hbEntry_isSome : ∀ u : Fin n, bEntry[u.val].isSome =
      ((List.finRange n).any fun y => inCycle[y.val] && a[u.val][y.val]))
    (hbExit_isSome : ∀ w : Fin n, bExit[w.val].isSome =
      ((List.finRange n).any fun x => inCycle[x.val] && a[x.val][w.val]))
    (u w : Fin n) :
    (contractAdjTable a inCycle bEntry bExit x0 (e rV))[u.val][w.val] =
      contractAdj aV C (e.symm x0) rV (e.symm u) (e.symm w) := by
  have hany : ∀ (p : Fin n → Bool) (q : V → Bool),
      (∀ x, p x = q (e.symm x)) → (List.finRange n).any p = (FinEnum.toList V).any q :=
    fun p q hpq => Bool.eq_iff_iff.mpr (by
      simp only [List.any_eq_true, FinEnum.mem_toList, List.mem_finRange, true_and]
      exact ⟨fun ⟨x, hx⟩ => ⟨e.symm x, hpq x ▸ hx⟩,
        fun ⟨y, hy⟩ => ⟨e y, by rw [hpq, e.symm_apply_apply]; exact hy⟩⟩)
  have hdec y : inCycle[y.val] = decide (e.symm y ∈ C) :=
    Bool.eq_iff_iff.mpr (by simpa using hmask y)
  have hex : bExit[w.val].isSome =
      (FinEnum.toList V).any (fun x => decide (x ∈ C) && aV x (e.symm w)) :=
    (hbExit_isSome w).trans (hany _ _ fun x => by rw [hdec, ha x w])
  have hen : bEntry[u.val].isSome =
      (FinEnum.toList V).any (fun y => decide (y ∈ C) && aV (e.symm u) y) :=
    (hbEntry_isSome u).trans (hany _ _ fun y => by rw [hdec, ha u y])
  have hwr : (w == e rV) = decide (e.symm w = rV) :=
    Bool.eq_iff_iff.mpr (by simp [beq_iff_eq, e.symm_apply_eq])
  have hwx : (w == x0) = decide (e.symm w = e.symm x0) :=
    Bool.eq_iff_iff.mpr (by simp [beq_iff_eq, e.symm.injective.eq_iff])
  rw [getElem_contractAdjTable]
  unfold contractAdj
  by_cases hu : inCycle[u.val] = true
  · simp only [hu, ↓reduceIte, (hmask u).mp hu]
    by_cases hux : u = x0
    · subst hux
      simp [hex, hdec w]
    · simp [hux, e.symm.injective.eq_iff, hwr]
  · simp only [hu, Bool.false_eq_true, ↓reduceIte, (hmask u).not.mp hu]
    by_cases hw : inCycle[w.val] = true
    · simp [hw, (hmask w).mp hw, hen, hwx]
    · simp [hw, (hmask w).not.mp hw, ha u w]

private theorem contractCostTable_spec {V : Type*} [FinEnum V]
    (c : CostTable β (FinEnum.card V)) (inCycle : Vector Bool (FinEnum.card V))
    (other : Vector β (FinEnum.card V))
    (bEntry bExit : Vector (Option (Fin (FinEnum.card V))) (FinEnum.card V))
    (x0 : Fin (FinEnum.card V))
    (aV : V → V → Bool) (cV : V → V → β) (fV : V → V) (C : Finset V)
    (hc : ∀ u w, c[u.val][w.val] =
      cV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hmask : ∀ y, inCycle[y.val] = true ↔ (@FinEnum.equiv V _).symm y ∈ C)
    (hother : ∀ {x}, inCycle[x.val] = true →
      other[x.val] = ∑ y ∈ C.erase ((@FinEnum.equiv V _).symm x), cV y (fV y))
    (hbEntry : ∀ u : Fin (FinEnum.card V), bEntry[u.val].map (@FinEnum.equiv V _).symm =
      bestEntry aV cV C ((@FinEnum.equiv V _).symm u))
    (hbExit : ∀ w : Fin (FinEnum.card V), bExit[w.val].map (@FinEnum.equiv V _).symm =
      bestExit aV cV fV C ((@FinEnum.equiv V _).symm w))
    (hbExit_mem : ∀ (w xs : Fin (FinEnum.card V)), bExit[w.val] = some xs → inCycle[xs.val] = true)
    (u w : Fin (FinEnum.card V)) :
    (contractCostTable c inCycle other bEntry bExit x0)[u.val][w.val] =
      contractCost aV cV fV C ((@FinEnum.equiv V _).symm x0)
        ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w) := by
  rw [getElem_contractCostTable]
  unfold contractCost
  by_cases hu : inCycle[u.val] = true
  · simp only [hu, ↓reduceIte, (hmask u).mp hu]
    by_cases hux' : u = x0
    · subst hux'
      rw [← hbExit w]
      simp only [beq_self_eq_true, ↓reduceIte]
      cases hbx : bExit[w.val] with
      | none => exact hc u w
      | some xs =>
        simp only [Option.map_some]
        rw [hc xs w, hother (hbExit_mem w xs hbx), exitCost]
    · simp [beq_iff_eq, hux', (@FinEnum.equiv V _).symm.injective.eq_iff]
  · simp only [hu, Bool.false_eq_true, ↓reduceIte, (hmask u).not.mp hu]
    by_cases hwx' : w = x0
    · subst hwx'
      rw [← hbEntry u]
      simp only [beq_self_eq_true, ↓reduceIte]
      cases bEntry[u.val] <;> simp [hc]
    · simp [beq_iff_eq, hwx', (@FinEnum.equiv V _).symm.injective.eq_iff, hc u w]

private theorem expandParentTable_spec {V : Type*} [FinEnum V]
    (f : ParentTable (FinEnum.card V)) (inCycle : Vector Bool (FinEnum.card V))
    (bEntry bExit : Vector (Option (Fin (FinEnum.card V))) (FinEnum.card V))
    (x0 : Fin (FinEnum.card V)) (q : ParentTable (FinEnum.card V))
    (aV : V → V → Bool) (cV : V → V → β) (fV : V → V) (C : Finset V) (qV : V → V)
    (hf : ∀ i, (@FinEnum.equiv V _).symm f[i.val] = fV ((@FinEnum.equiv V _).symm i))
    (hq : ∀ v, (@FinEnum.equiv V _).symm q[(@FinEnum.equiv V _ v).val] = qV v)
    (hmask : ∀ y, inCycle[y.val] = true ↔ (@FinEnum.equiv V _).symm y ∈ C)
    (hbEntry : ∀ u : Fin (FinEnum.card V), bEntry[u.val].map (@FinEnum.equiv V _).symm =
      bestEntry aV cV C ((@FinEnum.equiv V _).symm u))
    (hbExit : ∀ w : Fin (FinEnum.card V), bExit[w.val].map (@FinEnum.equiv V _).symm =
      bestExit aV cV fV C ((@FinEnum.equiv V _).symm w))
    (v : V) :
    (@FinEnum.equiv V _).symm
        ((expandParentTable f inCycle bEntry bExit x0 q)[(@FinEnum.equiv V _ v).val]) =
      expandParent aV cV fV C ((@FinEnum.equiv V _).symm x0) qV v := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  have hv : inCycle[(@FinEnum.equiv V _ v).val] = true ↔ v ∈ C := by
    simpa [e] using hmask (e v)
  rw [getElem_expandParentTable]
  unfold expandParent
  by_cases hvC : inCycle[(@FinEnum.equiv V _ v).val] = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hvC), ite_eq_left_of_eq_true _ _ (eq_true (hv.mp hvC))]
    have hqx0 : e.symm q[x0.val] = qV (e.symm x0) := by simpa [e] using hq (e.symm x0)
    have hbo := hbExit q[x0.val]
    rw [hqx0] at hbo
    cases hbx : bExit[q[x0.val].val] with
    | none => rw [← hbo, hbx]; simpa [e] using hf (e v)
    | some xs =>
      rw [← hbo, hbx, Option.map_some]
      dsimp only
      by_cases hvxs : @FinEnum.equiv V _ v = xs
      · subst hvxs
        simpa [e] using hqx0
      · have hvxs' : v ≠ (@FinEnum.equiv V _).symm xs := fun h => hvxs (by rw [h]; simp)
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [beq_iff_eq, hvxs])),
          ite_eq_right_of_eq_false _ _ (eq_false hvxs')]
        simpa [e] using hf (e v)
  · have hvV : v ∉ C := fun h => hvC (hv.mpr h)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hvC), ite_eq_right_of_eq_false _ _ (eq_false hvV)]
    by_cases hqeq : q[(@FinEnum.equiv V _ v).val] = x0
    · have hqV : qV v = (@FinEnum.equiv V _).symm x0 :=
        (hq v).symm.trans (congrArg (@FinEnum.equiv V _).symm hqeq)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mpr hqeq)),
        ite_eq_left_of_eq_true _ _ (eq_true hqV)]
      have hbi := hbEntry (@FinEnum.equiv V _ v)
      rw [show (@FinEnum.equiv V _).symm (@FinEnum.equiv V _ v) = v by simp] at hbi
      rw [← hbi]
      cases bEntry[(@FinEnum.equiv V _ v).val] <;> simp
    · have hqV : qV v ≠ (@FinEnum.equiv V _).symm x0 :=
        fun h => hqeq ((@FinEnum.equiv V _).symm.injective ((hq v).trans h))
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [beq_iff_eq, hqeq])),
        ite_eq_right_of_eq_false _ _ (eq_false hqV)]
      exact hq v

/-- **Exact equivalence with `ChuLiuEdmonds.edmondsAux`**: at every recursion depth `fuel`, the
materialized table solver `edmondsTableAux` computes the exact same parent map (up to
`FinEnum.equiv`) as `ChuLiuEdmonds.edmondsAux`. -/
theorem edmondsTableAux_eq_edmondsAux {V : Type*} [FinEnum V] :
    ∀ (fuel : ℕ) (a : AdjTable (FinEnum.card V)) (c : CostTable β (FinEnum.card V))
      (aV : V → V → Bool) (cV : V → V → β) (rV : V),
      (∀ u w, a[u.val][w.val] =
        aV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w)) →
      (∀ u w, c[u.val][w.val] =
        cV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w)) →
      (edmondsTableAux (@FinEnum.equiv V _ rV) fuel a c).map
        (fun p v => (@FinEnum.equiv V _).symm p[((@FinEnum.equiv V _) v).val]) =
        edmondsAux rV fuel aV cV
  | 0, _, _, _, _, _, _, _ => rfl
  | fuel + 1, a, c, aV, cV, rV, ha, hc => by
    let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
    obtain ⟨hfeas, hf⟩ := selectParents_spec a c aV cV rV ha hc
    set sel := selectParents a c (e rV)
    set fV := cheapestParent aV cV rV
    by_cases hcond : sel.feasible = true
    · have hcondV : ∀ v, v ≠ rV → candidates aV v ≠ [] := hfeas.mp hcond
      have hcyc := findCycleTable_spec sel.parents fV hf rV
      cases hcycm : findCycleTable (e rV) sel.parents with
      | none =>
        have hcycV : findCycle rV fV = none := by rw [← hcyc, hcycm]; rfl
        have hret : edmondsTableAux (e rV) (fuel + 1) a c = some sel.parents := by
          dsimp only [edmondsTableAux, sel]
          rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), hcycm]
        rw [hret, Option.map_some, edmondsAux, ite_eq_left_iff.mpr fun h => absurd hcondV h, hcycV]
        exact congrArg some (funext fun v => by simpa [e] using hf (e v))
      | some x0 =>
        have hcycV : findCycle rV fV = some (e.symm x0) := by rw [← hcyc, hcycm]; rfl
        set C := cycleOf fV (e.symm x0)
        set inCycle := cycleMask sel.parents x0
        set other := otherCycleCost c sel.parents inCycle
        set bEntry := bestEntryTable a c inCycle
        set bExit := bestExitTable a c inCycle other
        set a' := contractAdjTable a inCycle bEntry bExit x0 (e rV)
        set c' := contractCostTable c inCycle other bEntry bExit x0
        have hmask y : inCycle[y.val] = true ↔ e.symm y ∈ C := cycleMask_spec sel.parents fV hf x0 y
        have hother {x} (hx : inCycle[x.val] = true) :
            other[x.val] = ∑ y ∈ C.erase (e.symm x), cV y (fV y) :=
          otherCycleCost_spec c sel.parents inCycle cV fV C hc hf hmask hx
        have hbEntry u : bEntry[u.val].map e.symm = bestEntry aV cV C (e.symm u) :=
          bestEntryTable_spec a c inCycle aV cV C ha hc hmask u
        have hbExit w : bExit[w.val].map e.symm = bestExit aV cV fV C (e.symm w) :=
          bestExitTable_spec a c inCycle other aV cV fV C ha hc hmask hother w
        have hih := edmondsTableAux_eq_edmondsAux fuel a' c'
          (contractAdj aV C (e.symm x0) rV) (contractCost aV cV fV C (e.symm x0)) rV
          (contractAdjTable_eq e a inCycle bEntry bExit x0 aV C rV ha hmask
            (fun _ => by simp [bEntry, getElem_bestEntryTable, List.isSome_argmin_filter])
            (fun _ => by simp [bExit, getElem_bestExitTable, List.isSome_argmin_filter]))
          (contractCostTable_spec c inCycle other bEntry bExit x0 aV cV fV C hc hmask hother
            hbEntry hbExit fun w xs hbx => by
              simp only [bExit, getElem_bestExitTable] at hbx
              exact (Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp (List.argmin_mem hbx)).2).1)
        dsimp only [edmondsTableAux, sel]
        rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), hcycm]
        dsimp only
        rw [edmondsAux, ite_eq_left_iff.mpr fun h => absurd hcondV h, hcycV]
        dsimp only
        rw [← hih]
        cases edmondsTableAux (e rV) fuel a' c' with
        | none => rfl
        | some q =>
          simp only [Option.map_some]
          exact congrArg some (funext fun v =>
            expandParentTable_spec sel.parents inCycle bEntry bExit x0 q aV cV fV C
              (fun w => e.symm q[(e w).val]) hf (fun _ => rfl) hmask hbEntry hbExit v)
    · have hncondV : ¬ ∀ v, v ≠ rV → candidates aV v ≠ [] := fun h => hcond (hfeas.mpr h)
      have hret : edmondsTableAux (e rV) (fuel + 1) a c = none := by
        dsimp only [edmondsTableAux, sel]
        rw [ite_eq_right_of_eq_false _ _ (eq_false hcond)]
      rw [hret, Option.map_none, edmondsAux, ite_eq_right_iff.mpr fun h => absurd h hncondV]

end Transfer

/-! ### Top-level materialized solvers for `[FinEnum V]` -/

/-- Materialized-table Chu–Liu/Edmonds algorithm for spanning in-arborescences rooted at `r`,
transporting `G` and `c` onto flat `Fin (FinEnum.card V)` tables via `FinEnum.equiv`. -/
@[expose] def edmondsTable {V : Type*} [FinEnum V] (G : Digraph V) [DecidableRel G.Adj]
    (c : V → V → β) (r : V) : Option (V → V) :=
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  let a := initAdjTable (FinEnum.card V) fun u w => decide (G.Adj (e.symm u) (e.symm w))
  let ct := initCostTable (FinEnum.card V) fun u w => c (e.symm u) (e.symm w)
  (edmondsTableAux (e r) (FinEnum.card V) a ct).map fun p v => e.symm p[(e v).val]

/-- **Equivalence with `ChuLiuEdmonds.edmonds`:** `edmondsTable` returns the exact same parent
map as `edmonds`. -/
theorem edmondsTable_eq_edmonds {V : Type*} [FinEnum V] (G : Digraph V) [DecidableRel G.Adj]
    (c : V → V → β) (r : V) : edmondsTable G c r = edmonds G c r :=
  edmondsTableAux_eq_edmondsAux (FinEnum.card V) _ _
    (fun u w => decide (G.Adj u w)) c r
    (fun u w => getElem_initAdjTable _ _ u w) (fun u w => getElem_initCostTable _ _ u w)

/-- Materialized-table correctness for spanning in-arborescences, transferred from
`edmonds_spec`. -/
theorem edmondsTable_spec [IsOrderedAddMonoid β] {V : Type*} [FinEnum V]
    {G : Digraph V} [DecidableRel G.Adj] {c : V → V → β} {r : V} :
    (∀ p, edmondsTable G c r = some p →
      IsInArborescenceParent G.Adj r p ∧
        ∀ t, IsInArborescenceParent G.Adj r t → parentCost c r p ≤ parentCost c r t) ∧
    (edmondsTable G c r = none → ∀ t, ¬ IsInArborescenceParent G.Adj r t) := by
  rw [edmondsTable_eq_edmonds]
  exact edmonds_spec

/-- Materialized-table optimality over `Digraph.IsInArborescence`, transferred from
`edmonds_optimal`. -/
theorem edmondsTable_optimal [IsOrderedAddMonoid β] {V : Type*} [FinEnum V]
    {G : Digraph V} [DecidableRel G.Adj] {c : V → V → β} {r : V}
    {p : V → V} (hp : edmondsTable G c r = some p) :
    (Digraph.parentDigraph r p).IsInArborescence r ∧ Digraph.parentDigraph r p ≤ G ∧
      ∀ (T : Digraph V) [DecidableRel T.Adj], T.IsInArborescence r → T ≤ G →
        arcCost (Digraph.parentDigraph r p) c ≤ arcCost T c := by
  rw [edmondsTable_eq_edmonds] at hp
  exact edmonds_optimal hp

/-- Materialized-table Chu–Liu/Edmonds algorithm for out-arborescences (arcs directed away from
`r`). -/
@[expose] def edmondsOutTable {V : Type*} [FinEnum V] (G : Digraph V) [DecidableRel G.Adj]
    (c : V → V → β) (r : V) : Option (V → V) :=
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  let a := initAdjTable (FinEnum.card V) fun u w => decide (G.Adj (e.symm w) (e.symm u))
  let ct := initCostTable (FinEnum.card V) fun u w => c (e.symm w) (e.symm u)
  (edmondsTableAux (e r) (FinEnum.card V) a ct).map fun p v => e.symm p[(e v).val]

/-- `edmondsOutTable` computes the exact same parent map as `edmondsOut`. -/
theorem edmondsOutTable_eq_edmondsOut {V : Type*} [FinEnum V] (G : Digraph V)
    [DecidableRel G.Adj] (c : V → V → β) (r : V) :
    edmondsOutTable G c r = edmondsOut G c r :=
  edmondsTableAux_eq_edmondsAux (FinEnum.card V) _ _
    (fun u w => decide (G.Adj w u)) (fun u w => c w u) r
    (fun u w => getElem_initAdjTable _ _ u w) (fun u w => getElem_initCostTable _ _ u w)

/-- Materialized-table correctness for out-arborescences, transferred from `edmondsOut_spec`. -/
theorem edmondsOutTable_spec [IsOrderedAddMonoid β] {V : Type*} [FinEnum V]
    {G : Digraph V} [DecidableRel G.Adj] {c : V → V → β} {r : V} :
    (∀ p, edmondsOutTable G c r = some p →
      IsInArborescenceParent (fun u w => G.Adj w u) r p ∧
        ∀ t, IsInArborescenceParent (fun u w => G.Adj w u) r t →
          parentCost (fun u w => c w u) r p ≤ parentCost (fun u w => c w u) r t) ∧
    (edmondsOutTable G c r = none →
      ∀ t, ¬ IsInArborescenceParent (fun u w => G.Adj w u) r t) := by
  rw [edmondsOutTable_eq_edmondsOut]
  exact edmondsOut_spec

end Main

end Cslib.Algorithms.Lean.Arborescence
