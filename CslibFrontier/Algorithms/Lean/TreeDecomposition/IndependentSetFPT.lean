/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TreeDecomposition.BagMask
public import CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSet

/-!
# An executable FPT program for maximum-weight independent set

`mwisFPT R w L` is an executable pure program that computes the maximum total weight of an
independent set of `G`, given a rooted tree decomposition `R : G.RootedTreeDecomposition n`, vertex
weights `w : V → ℕ` and an ordering `L` of the bags (`IsBagOrder R L`). It materializes the
tables of `mwisValue` (`CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSet`) as arrays
indexed by bit masks and stores them in a `Vector` over the nodes. `mwisFPT_eq_mwisValue` proves
that it equals `mwisValue R w`, so it returns the optimum (`isGreatest_mwisFPT`).

Machine-level FPT running-time bounds on an array-encoded decomposition live in
`CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet`.

## The program

The tables are indexed by bit masks over the ordered bags (`ofMask`, `toMask`). The nodes are
processed in the order `n, n - 1, …, 1`, so every child is processed before its parent. Processing
a node `j` with bag list `LB` and parent bag list `LP` (`processNode`) runs two loops:

* the child pass (`childPass`) visits each of the `2 ^ |LB|` child masks `t`. It tests whether
  the subset `T` selected by `t` is independent, computes the parent-bag mask of `T` and the weight
  of the vertices of `T` outside the parent bag, and updates the entry of a zero-initialized array
  `best` at that parent-bag mask with the maximum of its old value and the weight plus the table
  entry of `j` at `t`;
* the parent pass (`parentPass`) visits each of the `2 ^ |LP|` parent masks `s`. It computes the
  parent-bag mask of `S ∩ B`, for the parent subset `S` selected by `s` and the child bag `B`, and
  adds the entry of `best` there to the parent's table entry at `s`.

The root pass (`rootPass`) returns the best weight plus table entry over the independent subsets
of the root bag. `getD_tablesFPT` shows that the arrays agree with `tables` on every subset of
every bag. It is proved one node at a time against `step` (`getD_processNode`). The only nontrivial
step is that the child pass computes `forget` (`getD_childPass_eq_forget`).

## Main definitions

* `Cslib.Algorithms.Lean.TreeDecomposition.mwisFPT`: the executable program.

## Main results

* `Cslib.Algorithms.Lean.TreeDecomposition.mwisFPT_eq_mwisValue`: the program computes
  `mwisValue R w`.
* `Cslib.Algorithms.Lean.TreeDecomposition.isGreatest_mwisFPT`: so it computes the maximum weight
  of an independent set.
* `Cslib.Algorithms.Lean.TreeDecomposition.mwisFPT_one_eq_indepNum`: with unit weights it computes
  the independence number.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Section 7.3.1][CyganEtAl2015]
-/

public section

namespace Cslib.Algorithms.Lean.TreeDecomposition

open SimpleGraph SimpleGraph.RootedTreeDecomposition

/-! ### The passes -/

section PassDefs

variable {V : Type*} [DecidableEq V]

/-- The parent pass: for each parent mask `s < c`, add the best child entry agreeing with `s` to
the old parent table. -/
@[expose] def parentPass (LB LP : List V) (old best : Array ℕ) : ℕ → Array ℕ
  | 0 => #[]
  | c + 1 =>
    (parentPass LB LP old best c).push (old.getD c 0 + best.getD (restrictMask LB LP c) 0)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The child pass over the child masks `t < c`: for each independent child subset, update the
entry of `best` at its parent-bag mask with the forgotten weight plus the child table entry. -/
@[expose] def childPass (w : V → ℕ) (LB LP : List V) (f init : Array ℕ) : ℕ → Array ℕ
  | 0 => init
  | c + 1 =>
    let best := childPass w LB LP f init c
    if indepMask G LB c then
      let key := keyMask LB LP c
      best.setIfInBounds key (max (best.getD key 0) (forgetWeight w LP LB c + f.getD c 0))
    else
      best

/-- The root pass over the root masks `t < c`: the best weight of an independent root subset plus
its table entry. -/
@[expose] def rootPass (w : V → ℕ) (L : List V) (tbl : Array ℕ) : ℕ → ℕ
  | 0 => 0
  | c + 1 =>
    let best := rootPass w L tbl c
    if indepMask G L c then max best (forgetWeight w [] L c + tbl.getD c 0) else best

end PassDefs

/-! ### The program -/

section Program

variable {V : Type*} {G : SimpleGraph V} {n : ℕ} [DecidableEq V] [DecidableRel G.Adj]

/-- Process node `j`: build its message to its parent and add it to the parent's table. -/
@[expose] def processNode (R : G.RootedTreeDecomposition n) (w : V → ℕ)
    (L : Fin (n + 1) → List V) (st : Vector (Array ℕ) (n + 1)) (j : Fin (n + 1)) :
    Vector (Array ℕ) (n + 1) :=
  let p := R.parent j
  let init := Array.replicate (2 ^ (L p).length) 0
  let best := childPass G w (L j) (L p) st[j] init (2 ^ (L j).length)
  let tp := parentPass (L j) (L p) st[p] best (2 ^ (L p).length)
  st.set p tp p.isLt

/-- The tables after processing the nodes `n, n - 1, …, n - t + 1`. -/
@[expose] def tablesFPT (R : G.RootedTreeDecomposition n) (w : V → ℕ)
    (L : Fin (n + 1) → List V) : ℕ → Vector (Array ℕ) (n + 1)
  | 0 => Vector.replicate (n + 1) #[]
  | t + 1 => processNode R w L (tablesFPT R w L t) (Fin.ofNat (n + 1) (n - t))

/-- The executable program: process every nonroot node, then combine at the root. -/
@[expose] def mwisFPT (R : G.RootedTreeDecomposition n) (w : V → ℕ)
    (L : Fin (n + 1) → List V) : ℕ :=
  let st := tablesFPT R w L n
  rootPass G w (L 0) st[(0 : Fin (n + 1))] (2 ^ (L 0).length)

end Program

/-! ### Correctness of the passes -/

section Passes

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem size_childPass (w : V → ℕ) (LB LP : List V) (f init : Array ℕ) (c : ℕ) :
    (childPass G w LB LP f init c).size = init.size := by
  induction c with
  | zero => rfl
  | succ c ih => dsimp only [childPass]; split_ifs <;> simp [ih]

/-- After the child masks `t < c`, the entry of `best` at a parent mask `k` is the best value over
the independent child subsets with parent mask `k`. -/
theorem getD_childPass (w : V → ℕ) {LB : List V} (hLB : LB.Nodup) (LP : List V)
    (f init : Array ℕ) (c : ℕ) {k : ℕ} (hk : k < init.size) :
    (childPass G w LB LP f init c).getD k 0 = max (init.getD k 0)
      (((Finset.range c).filter fun t => G.IsIndepSet (↑(ofMask LB t) : Set V) ∧
          toMask LP (ofMask LB t) = k).sup fun t =>
        (∑ v ∈ ofMask LB t \ LP.toFinset, w v) + f.getD t 0) := by
  induction c with
  | zero => simp [childPass]
  | succ c ih =>
    simp only [childPass, keyMask_eq_toMask, forgetWeight_eq_sum w LP hLB]
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hok : indepMask G LB c = true
    · have hind := (indepMask_eq_true_iff G LB c).1 hok
      rw [ite_eq_left hok]
      by_cases hkey : toMask LP (ofMask LB c) = k
      · rw [ite_eq_left ⟨hind, hkey⟩, Finset.sup_insert, hkey, Array.getD_eq_getD_getElem?,
          Array.getElem?_setIfInBounds, ite_eq_left rfl,
          ite_eq_left (by rw [size_childPass]; exact hk), Option.getD_some, ih]; omega
      · rw [ite_eq_right fun h => hkey h.2, Array.getD_eq_getD_getElem?,
          Array.getElem?_setIfInBounds, ite_eq_right hkey, ← Array.getD_eq_getD_getElem?, ih]
    · rw [ite_eq_right hok, ite_eq_right fun h => hok ((indepMask_eq_true_iff G LB c).2 h.1), ih]

/-- Started from a zero table, the child pass computes `forget` on every parent subset. -/
theorem getD_childPass_eq_forget (w : V → ℕ) {LB LP : List V} (hLB : LB.Nodup) (f : Array ℕ)
    (g : Finset V → ℕ) (hfg : ∀ t < 2 ^ LB.length, f.getD t 0 = g (ofMask LB t)) {S : Finset V}
    (hS : S ⊆ LP.toFinset) :
    (childPass G w LB LP f (Array.replicate (2 ^ LP.length) 0) (2 ^ LB.length)).getD
        (toMask LP (S ∩ LB.toFinset)) 0 =
      forget G w LB.toFinset LP.toFinset g S := by
  rw [getD_childPass G w hLB LP f _ _ (by rw [Array.size_replicate]; exact toMask_lt _ _),
    Array.getD_eq_getD_getElem?, Array.getElem?_replicate, ite_eq_left (toMask_lt _ _),
    Option.getD_some, Nat.zero_max, forget, powerset_toFinset_eq_image, Finset.filter_image,
    Finset.sup_image]
  refine Finset.sup_congr (Finset.filter_congr fun t _ => and_congr_right fun _ => ?_) fun t ht =>
    by simp only [Function.comp_apply, hfg t (Finset.mem_range.1 (Finset.mem_filter.1 ht).1)]
  rw [toMask_eq_toMask_iff]
  refine ⟨fun h => ?_, fun h => by
    rw [h]
    exact (Finset.inter_eq_left.2 (Finset.inter_subset_left.trans hS)).symm⟩
  ext x
  have hx := congrArg (x ∈ ·) h
  simp only [Finset.mem_inter, eq_iff_iff] at hx ⊢
  exact ⟨fun ⟨hxt, hxP⟩ => ⟨(hx.1 ⟨hxt, hxP⟩).1.1, ofMask_subset LB t hxt⟩,
    fun ⟨hxS, hxB⟩ => ⟨(hx.2 ⟨⟨hxS, hxB⟩, hS hxS⟩).1, hS hxS⟩⟩

omit [DecidableRel G.Adj] in
theorem size_parentPass (LB LP : List V) (old best : Array ℕ) (c : ℕ) :
    (parentPass LB LP old best c).size = c := by
  induction c <;> simp [parentPass, *]

omit [DecidableRel G.Adj] in
theorem getD_parentPass (LB : List V) {LP : List V} (hLP : LP.Nodup) (old best : Array ℕ)
    {c s : ℕ} (hs : s < c) :
    (parentPass LB LP old best c).getD s 0 =
      old.getD s 0 + best.getD (toMask LP (ofMask LP s ∩ LB.toFinset)) 0 := by
  induction c with
  | zero => omega
  | succ c ih =>
    simp only [parentPass, restrictMask_eq_toMask LB hLP]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, size_parentPass]
    rcases eq_or_ne s c with rfl | hsc
    · rw [ite_eq_left rfl, Option.getD_some]
    · rw [ite_eq_right hsc, ← Array.getD_eq_getD_getElem?, ih (by omega)]

theorem rootPass_eq_sup (w : V → ℕ) {L : List V} (hL : L.Nodup) (tbl : Array ℕ) (c : ℕ) :
    rootPass G w L tbl c =
      ((Finset.range c).filter fun t => G.IsIndepSet (↑(ofMask L t) : Set V)).sup fun t =>
        (∑ v ∈ ofMask L t, w v) + tbl.getD t 0 := by
  induction c with
  | zero => rfl
  | succ c ih =>
    simp only [rootPass, ih, forgetWeight_eq_sum w [] hL, List.toFinset_nil, Finset.sdiff_empty]
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hok : indepMask G L c = true
    · rw [ite_eq_left hok, ite_eq_left ((indepMask_eq_true_iff G L c).1 hok), Finset.sup_insert]
      omega
    · rw [ite_eq_right hok, ite_eq_right fun h => hok ((indepMask_eq_true_iff G L c).2 h)]

end Passes

/-! ### Correctness -/

section Correctness

variable {V : Type*} {G : SimpleGraph V} {n : ℕ} [DecidableEq V] [DecidableRel G.Adj]

/-- One step of the program refines `step`: if the materialized tables agree with `g` on every
subset of every bag, then after processing `j` they agree with `step R w g j`. -/
theorem getD_processNode (R : G.RootedTreeDecomposition n) (w : V → ℕ) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) (st : Vector (Array ℕ) (n + 1)) (g : Fin (n + 1) → Finset V → ℕ)
    (hg : ∀ i, ∀ s < 2 ^ (L i).length, st[i].getD s 0 = g i (ofMask (L i) s)) (j i : Fin (n + 1))
    {s : ℕ} (hs : s < 2 ^ (L i).length) :
    (processNode R w L st j)[i].getD s 0 = step R w g j i (ofMask (L i) s) := by
  dsimp only [processNode]; unfold step
  rcases eq_or_ne i (R.parent j) with rfl | hi
  · rw [Function.update_self, Fin.getElem_fin, Vector.getElem_set_self,
      getD_parentPass _ (hL _).1 _ _ hs, hg _ _ hs,
      getD_childPass_eq_forget G w (hL j).1 _ (g j) (hg j) (ofMask_subset _ _), (hL j).2,
      (hL (R.parent j)).2]
  · rw [Function.update_of_ne hi, Fin.getElem_fin,
      Vector.getElem_set_ne _ _ (fun h => hi (Fin.ext h).symm)]
    exact hg i s hs

/-- The materialized tables agree with the specification `tables` of
`CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSet` on every subset of every bag. -/
theorem getD_tablesFPT (R : G.RootedTreeDecomposition n) (w : V → ℕ) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) (t : ℕ) (i : Fin (n + 1)) {s : ℕ} (hs : s < 2 ^ (L i).length) :
    (tablesFPT R w L t)[i].getD s 0 = tables R w t i (ofMask (L i) s) := by
  induction t generalizing i s with
  | zero => simp [tablesFPT, tables]
  | succ t ih => exact getD_processNode R w hL _ (tables R w t) (fun i _ hs => ih i hs) _ i hs

/-- **Correctness.** The executable program computes the value of the dynamic program. -/
theorem mwisFPT_eq_mwisValue (R : G.RootedTreeDecomposition n) (w : V → ℕ)
    {L : Fin (n + 1) → List V} (hL : IsBagOrder R L) : mwisFPT R w L = mwisValue R w := by
  rw [mwisFPT, rootPass_eq_sup G w (hL 0).1, mwisValue, ← (hL 0).2, powerset_toFinset_eq_image,
    Finset.filter_image, Finset.sup_image]
  exact Finset.sup_congr rfl fun t ht => by
    simp only [Function.comp_apply, getD_tablesFPT R w hL n 0 (Finset.mem_range.1
      (Finset.mem_filter.1 ht).1)]

/-- The executable program computes the maximum weight of an independent set. -/
theorem isGreatest_mwisFPT (R : G.RootedTreeDecomposition n) (w : V → ℕ)
    {L : Fin (n + 1) → List V} (hL : IsBagOrder R L) :
    IsGreatest {x | ∃ I : Finset V, G.IsIndepSet (↑I : Set V) ∧ ∑ v ∈ I, w v = x}
      (mwisFPT R w L) :=
  mwisFPT_eq_mwisValue R w hL ▸ isGreatest_mwisValue R w

/-- With unit weights the executable program computes the independence number. -/
theorem mwisFPT_one_eq_indepNum (R : G.RootedTreeDecomposition n) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) : mwisFPT R (fun _ => 1) L = G.indepNum := by
  rw [mwisFPT_eq_mwisValue R _ hL, mwisValue_one_eq_indepNum]

end Correctness

end Cslib.Algorithms.Lean.TreeDecomposition
