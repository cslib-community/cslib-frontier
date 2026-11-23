/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSetFPT
public import CslibFrontier.Computability.WordRAM.Function
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Tactic.Realize
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

/-!
# Maximum-weight independent set over a tree decomposition on the Word-RAM

This module realizes the fixed-parameter dynamic program `mwisFPT`
(`CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSetFPT`) for maximum-weight
independent set over an array-encoded rooted tree decomposition on the exact-basis Word-RAM
(`Cslib.WordRAM.Basis.exact`). `Basis.exact` supplies unit-cost multiplication, division, and
remainder for `2`-power table sizing, bit-mask extraction (`m % 2`, `m / 2`), and row-major
adjacency-matrix indexing (`adjPtr + u * numVerts + v`) while certifying non-underflowing
subtraction and non-zero divisors in the machine semantics.

Every phase of the algorithm is executed in word-addressed memory and charged by the machine:
* parsing variable-length bag lists into 4-word node descriptors and zero-allocating all `n + 1`
  node DP tables (`initNodesProg`),
* pairwise bag independence tests via row-major adjacency-matrix reads (`noAdjScanProg`,
  `indepBagProg`),
* linear bag scans computing parent-bag masks, parent-mask restrictions, and forgotten-vertex
  weight sums (`selMemBagProg`, `keyMaskProg`, `restrictMaskProg`, `forgetWeightProg`),
* child-pass scratch-array materialization (`Memory.alloc`), in-place parent-table accumulation,
  bottom-up node traversal `n, n - 1, …, 1`, and final root maximization (`childPassProg`,
  `parentPassProg`, `processNodesProg`, `rootPassProg`).

Because every nonroot node `j ≥ 1` has `parents[j] < j`, a telescoping prefix-sum invariant over
unprocessed node tables bounds all intermediate and final table entries by
`(numNodes + 1) * maxBagLen * maxWeight`, so logarithmic word width suffices (no `2 ^ numNodes`
value growth). On any rooted tree decomposition `R : G.RootedTreeDecomposition n` of width `≤ k`,
one fixed Word-RAM program computes `mwisValue R wt` in
`O((n + 1) · 2 ^ (k + 1) · (k + 1) ^ 2)` instructions.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.encodeBag`: length-prefixed bag word list.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance`: flat word-serializable instance bundle
  with `MWISInstance.encode`, `MWISInstance.result`, `MWISInstance.maxBagLen`,
  `MWISInstance.maxWeight`, `MWISInstance.wordBound`, `MWISInstance.stepBound`, and
  `MWISInstance.ofRooted`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.mwisFPTBound`: closed-form width-`k` step bound
  `6 + (n + 1) * (2 ^ (k + 1) * (5 * (k + 1) ^ 2 + 6 * (k + 1) + 32))`.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.result_ofRooted`:
  `MWISInstance.ofRooted` computes `mwisValue R wt` (`= mwisFPT R wt L`).
* `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_mwis_treeDecomposition`: one fixed
  `Basis.exact` Word-RAM program computes `MWISInstance.result` in `O(inst.stepBound + 1)`
  instructions at every word width `w` satisfying `Fits w inst.wordBound` and
  `InputFits w inst.encode`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.uniformComputableInTime_mwis_treeDecomposition`:
  `UniformComputableInTime .exact` certificate for `MWISInstance.result`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_mwis_rooted`: FPT Word-RAM bound
  `O(mwisFPTBound n k + 1)` computing `mwisValue R wt` for any `R : G.RootedTreeDecomposition n` of
  width `R.width ≤ k`.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Section 7.3.1][CyganEtAl2015]
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Instance bundle, flat encoding, and bridge to `mwisFPT` / `mwisValue` -/

/-- Length-prefixed word serialization `[B.length] ++ B` of an ordered bag `B`. -/
@[expose] def encodeBag (B : List ℕ) : List ℕ :=
  B.length :: B

/-- Word-encoded instance of maximum-weight independent set over a rooted tree decomposition on
`numNodes + 1` nodes (`0` is the root) and `numVerts` graph vertices `0, …, numVerts - 1`. -/
structure MWISInstance where
  /-- Number of graph vertices `m`. -/
  numVerts : ℕ
  /-- Parameter `n` such that the decomposition has `n + 1` nodes `0, …, n`. -/
  numNodes : ℕ
  /-- Vertex weights `weights[0 .. m - 1]`. -/
  weights : List ℕ
  /-- Flattened row-major `m × m` adjacency indicators (`0` non-adjacent, nonzero adjacent). -/
  adjMatrix : List ℕ
  /-- Parent node indices `parents[0 .. n]`. -/
  parents : List ℕ
  /-- Ordered vertex lists `bags[0 .. n]`. -/
  bags : List (List ℕ)
  /-- `weights` has length `numVerts`. -/
  weights_len : weights.length = numVerts
  /-- `adjMatrix` has length `numVerts * numVerts`. -/
  adjMatrix_len : adjMatrix.length = numVerts * numVerts
  /-- `parents` has length `numNodes + 1`. -/
  parents_len : parents.length = numNodes + 1
  /-- `bags` has length `numNodes + 1`. -/
  bags_len : bags.length = numNodes + 1
  /-- Every nonroot node `1 ≤ i ≤ numNodes` has parent strictly preceding `i`. -/
  parents_lt : ∀ i : Fin parents.length, 1 ≤ i.val → parents[i] < i.val
  /-- Every vertex in every bag is `< numVerts`. -/
  bags_lt : ∀ B ∈ bags, ∀ v ∈ B, v < numVerts

private def noAdjInst (adj : ℕ → ℕ → Bool) (x : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | u :: L, m => noAdjInst adj x L (m / 2) && !(decide (m % 2 = 1) && adj x u)

private def indepInst (adj : ℕ → ℕ → Bool) : List ℕ → ℕ → Bool
  | [], _ => true
  | u :: L, m => indepInst adj L (m / 2) && (!decide (m % 2 = 1) || noAdjInst adj u L (m / 2))

private def childPassInst (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (LB LP : List ℕ)
    (f init : Array ℕ) : ℕ → Array ℕ
  | 0 => init
  | c + 1 =>
    let best := childPassInst adj wt LB LP f init c
    if indepInst adj LB c then
      let key := keyMask LB LP c
      best.setIfInBounds key (max (best.getD key 0) (forgetWeight wt LP LB c + f.getD c 0))
    else
      best

private def rootPassInst (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (L : List ℕ) (tbl : Array ℕ) :
    ℕ → ℕ
  | 0 => 0
  | c + 1 =>
    let best := rootPassInst adj wt L tbl c
    if indepInst adj L c then max best (forgetWeight wt [] L c + tbl.getD c 0) else best

private def processInstNode (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (n : ℕ)
    (par : Fin (n + 1) → Fin (n + 1)) (bags : Fin (n + 1) → List ℕ)
    (st : Vector (Array ℕ) (n + 1)) (j : Fin (n + 1)) : Vector (Array ℕ) (n + 1) :=
  let p := par j
  let init := Array.replicate (2 ^ (bags p).length) 0
  let best := childPassInst adj wt (bags j) (bags p) st[j] init (2 ^ (bags j).length)
  let tp := parentPass (bags j) (bags p) st[p] best (2 ^ (bags p).length)
  st.set p tp p.isLt

private def tablesInst (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (n : ℕ)
    (par : Fin (n + 1) → Fin (n + 1)) (bags : Fin (n + 1) → List ℕ) :
    ℕ → Vector (Array ℕ) (n + 1)
  | 0 => Vector.replicate (n + 1) #[]
  | t + 1 =>
    processInstNode adj wt n par bags (tablesInst adj wt n par bags t)
      (Fin.ofNat (n + 1) (n - t))

namespace MWISInstance

/-- Weight lookup `weights.getD u 0` of vertex `u`. -/
@[expose] def wt (inst : MWISInstance) (u : ℕ) : ℕ :=
  inst.weights.getD u 0

/-- Adjacency indicator `adjMatrix[u * numVerts + v] ≠ 0`. -/
@[expose] def adj (inst : MWISInstance) (u v : ℕ) : Bool :=
  decide (inst.adjMatrix.getD (u * inst.numVerts + v) 0 ≠ 0)

private def parFin (inst : MWISInstance) (i : Fin (inst.numNodes + 1)) :
    Fin (inst.numNodes + 1) :=
  if hi : 1 ≤ i.val then
    let idx : Fin inst.parents.length := ⟨i.val, by rw [inst.parents_len]; exact i.isLt⟩
    ⟨inst.parents[idx], (inst.parents_lt idx hi).trans i.isLt⟩
  else
    ⟨0, Nat.succ_pos _⟩

private def bagAt (inst : MWISInstance) (i : Fin (inst.numNodes + 1)) : List ℕ :=
  inst.bags[i.val]'(by rw [inst.bags_len]; exact i.isLt)

/-- Pure dynamic-programming value computed on `inst`. -/
def result (inst : MWISInstance) : ℕ :=
  let st := tablesInst inst.adj inst.wt inst.numNodes inst.parFin inst.bagAt inst.numNodes
  rootPassInst inst.adj inst.wt (inst.bagAt 0) st[(0 : Fin (inst.numNodes + 1))]
    (2 ^ (inst.bagAt 0).length)

/-- Flat word-list encoding `[numVerts, numNodes] ++ weights ++ adjMatrix ++ parents ++
bags.flatMap encodeBag`. -/
@[expose] def encode (inst : MWISInstance) : List ℕ :=
  [inst.numVerts, inst.numNodes] ++
    inst.weights ++ inst.adjMatrix ++ inst.parents ++ inst.bags.flatMap encodeBag

/-- Maximum bag length across `inst.bags` (`≤ k + 1` when `R.width ≤ k`). -/
@[expose] def maxBagLen (inst : MWISInstance) : ℕ :=
  (inst.bags.map List.length).foldl max 0

/-- Maximum vertex weight across `inst.weights` (`0` if `numVerts = 0`). -/
@[expose] def maxWeight (inst : MWISInstance) : ℕ :=
  inst.weights.foldl max 0

/-- Word-value upper bound covering literal constants, peak memory frontier across initial table
allocation and all `numNodes` scratch `best` allocations, `2 ^ maxBagLen`, and maximum DP table
value `(numNodes + 1) * maxBagLen * maxWeight`. -/
@[expose] def wordBound (inst : MWISInstance) : ℕ :=
  let n := inst.numNodes
  let M := inst.maxBagLen
  8 +
    (inst.encode.length + 1 + 4 * (n + 1) + (2 * n + 1) * 2 ^ M) +
    (n + 1) * M * inst.maxWeight

/-- Upper bound on the oracle memory cost (`memoryCost`) of the Word-RAM MWIS program on `inst`. -/
@[expose] def stepBound (inst : MWISInstance) : ℕ :=
  let n := inst.numNodes
  let M := inst.maxBagLen
  6 + (n + 1) * (2 ^ M * (5 * M ^ 2 + 6 * M + 32))

/-- Compile a graph `G : SimpleGraph V` (`e : V ≃ Fin m`), rooted tree decomposition
`R : G.RootedTreeDecomposition n`, vertex weights `w : V → ℕ`, and bag lists
`L : Fin (n + 1) → List V` into a flat `MWISInstance`. -/
@[expose] def ofRooted {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]
    {m n : ℕ} (e : V ≃ Fin m) (R : G.RootedTreeDecomposition n) (w : V → ℕ)
    (L : Fin (n + 1) → List V) : MWISInstance where
  numVerts := m
  numNodes := n
  weights := List.ofFn fun u : Fin m => w (e.symm u)
  adjMatrix := List.ofFn fun idx : Fin (m * m) =>
    have hm : 0 < m := Nat.pos_of_ne_zero fun h0 => by subst h0; exact Fin.elim0 idx
    if G.Adj (e.symm ⟨idx.val / m, Nat.div_lt_of_lt_mul idx.isLt⟩)
        (e.symm ⟨idx.val % m, Nat.mod_lt _ hm⟩) then 1 else 0
  parents := List.ofFn fun i : Fin (n + 1) => (R.parent i).val
  bags := List.ofFn fun i : Fin (n + 1) => (L i).map fun v => (e v).val
  weights_len := List.length_ofFn
  adjMatrix_len := List.length_ofFn
  parents_len := List.length_ofFn
  bags_len := List.length_ofFn
  parents_lt := fun idx h1 => by
    have hi : idx.val < n + 1 := by simpa only [List.length_ofFn] using idx.isLt
    have hne : (⟨idx.val, hi⟩ : Fin (n + 1)) ≠ 0 := fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_zero] at this
      omega
    have hget : (List.ofFn fun i : Fin (n + 1) => (R.parent i).val)[idx] =
        (R.parent ⟨idx.val, hi⟩).val := by
      simp only [Fin.getElem_fin, List.getElem_ofFn]
    rw [hget]
    exact R.parent_lt ⟨idx.val, hi⟩ hne
  bags_lt := fun B hB v hv => by
    rw [List.mem_ofFn] at hB
    obtain ⟨i, rfl⟩ := hB
    rw [List.mem_map] at hv
    obtain ⟨x, _, rfl⟩ := hv
    exact (e x).isLt

end MWISInstance

/-- Closed-form FPT step bound `6 + (n + 1) * (2 ^ (k + 1) * (5 * (k + 1) ^ 2 + 6 * (k + 1) + 32))`
for rooted tree decompositions on `n + 1` nodes of width at most `k`. -/
@[expose] def mwisFPTBound (n k : ℕ) : ℕ :=
  6 + (n + 1) * (2 ^ (k + 1) * (5 * (k + 1) ^ 2 + 6 * (k + 1) + 32))

/-! ### Bridge between `MWISInstance.ofRooted` and `mwisFPT` / `mwisValue` -/

section RootedBridge

private theorem memBag_map_inj {V : Type*} [DecidableEq V] {f : V → ℕ}
    (hf : Function.Injective f) (x : V) (L : List V) :
    memBag (f x) (L.map f) = memBag x L := by
  induction L with
  | nil => rfl
  | cons u L ih => simp only [List.map_cons, memBag, ih, hf.eq_iff]

private theorem selMemMask_map_inj {V : Type*} [DecidableEq V] {f : V → ℕ}
    (hf : Function.Injective f) (x : V) (L : List V) (m : ℕ) :
    selMemMask (f x) (L.map f) m = selMemMask x L m := by
  induction L generalizing m with
  | nil => rfl
  | cons u L ih => simp only [List.map_cons, selMemMask, ih, hf.eq_iff]

private theorem keyMask_map_inj {V : Type*} [DecidableEq V] {f : V → ℕ}
    (hf : Function.Injective f) (LB LP : List V) (t : ℕ) :
    keyMask (LB.map f) (LP.map f) t = keyMask LB LP t := by
  induction LP with
  | nil => rfl
  | cons u LP ih => simp only [List.map_cons, keyMask, ih, selMemMask_map_inj hf]

private theorem restrictMask_map_inj {V : Type*} [DecidableEq V] {f : V → ℕ}
    (hf : Function.Injective f) (LB LP : List V) (s : ℕ) :
    restrictMask (LB.map f) (LP.map f) s = restrictMask LB LP s := by
  induction LP generalizing s with
  | nil => rfl
  | cons u LP ih => simp only [List.map_cons, restrictMask, ih, memBag_map_inj hf]

private theorem forgetWeight_map_inj {V : Type*} [DecidableEq V] {f : V → ℕ}
    (hf : Function.Injective f) {wtNat : ℕ → ℕ} {w : V → ℕ}
    (LP LB : List V) (hw : ∀ u ∈ LB, wtNat (f u) = w u) (t : ℕ) :
    forgetWeight wtNat (LP.map f) (LB.map f) t = forgetWeight w LP LB t := by
  induction LB generalizing t with
  | nil => rfl
  | cons u LB ih =>
    simp only [List.map_cons, forgetWeight, memBag_map_inj hf,
      hw u List.mem_cons_self, ih (fun v hv => hw v (List.mem_cons_of_mem u hv))]

private theorem noAdjInst_map {V : Type*} {G : SimpleGraph V}
    [DecidableRel G.Adj] {f : V → ℕ} {adj : ℕ → ℕ → Bool}
    (hadj : ∀ x u, adj (f x) (f u) = decide (G.Adj x u)) (x : V) (L : List V) (m : ℕ) :
    noAdjInst adj (f x) (L.map f) m = noAdjMask G x L m := by
  induction L generalizing m with
  | nil => rfl
  | cons u L ih => simp [noAdjInst, noAdjMask, ih, hadj]

private theorem indepInst_map {V : Type*} {G : SimpleGraph V}
    [DecidableRel G.Adj] {f : V → ℕ} {adj : ℕ → ℕ → Bool}
    (hadj : ∀ x u, adj (f x) (f u) = decide (G.Adj x u)) (L : List V) (m : ℕ) :
    indepInst adj (L.map f) m = indepMask G L m := by
  induction L generalizing m with
  | nil => rfl
  | cons u L ih => simp [indepInst, indepMask, ih, noAdjInst_map hadj]

private theorem childPassInst_map {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {f : V → ℕ} (hf : Function.Injective f)
    {adj : ℕ → ℕ → Bool} (hadj : ∀ x u, adj (f x) (f u) = decide (G.Adj x u))
    {wtNat : ℕ → ℕ} {w : V → ℕ} (hw : ∀ x, wtNat (f x) = w x)
    (LB LP : List V) (tbl init : Array ℕ) (c : ℕ) :
    childPassInst adj wtNat (LB.map f) (LP.map f) tbl init c =
      childPass G w LB LP tbl init c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    simp only [childPassInst, childPass, ih, indepInst_map hadj, keyMask_map_inj hf,
      forgetWeight_map_inj hf LP LB (fun u _ => hw u)]

private theorem parentPass_map_inj {V : Type*} [DecidableEq V] {f : V → ℕ}
    (hf : Function.Injective f) (LB LP : List V) (old best : Array ℕ) (c : ℕ) :
    parentPass (LB.map f) (LP.map f) old best c = parentPass LB LP old best c := by
  induction c with
  | zero => rfl
  | succ c ih => simp [parentPass, ih, restrictMask_map_inj hf]

private theorem rootPassInst_map {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {f : V → ℕ} (hf : Function.Injective f)
    {adj : ℕ → ℕ → Bool} (hadj : ∀ x u, adj (f x) (f u) = decide (G.Adj x u))
    {wtNat : ℕ → ℕ} {w : V → ℕ} (hw : ∀ x, wtNat (f x) = w x)
    (L : List V) (tbl : Array ℕ) (c : ℕ) :
    rootPassInst adj wtNat (L.map f) tbl c = rootPass G w L tbl c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    have hfw := forgetWeight_map_inj hf (w := w) (wtNat := wtNat) [] L (fun u _ => hw u) c
    simp only [List.map_nil] at hfw
    simp only [rootPassInst, rootPass, ih, indepInst_map hadj, hfw]

/-- `MWISInstance.ofRooted` agrees with `mwisFPT R w L`, and equals `mwisValue R w` whenever
`IsBagOrder R L`. -/
theorem MWISInstance.result_ofRooted_eq_mwisFPT {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj] {m n : ℕ} (e : V ≃ Fin m)
    (R : G.RootedTreeDecomposition n) (w : V → ℕ) (L : Fin (n + 1) → List V) :
    (MWISInstance.ofRooted e R w L).result = mwisFPT R w L := by
  let inst := MWISInstance.ofRooted e R w L
  let f : V → ℕ := fun v => (e v).val
  have hf : Function.Injective f := fun a b h => e.injective (Fin.ext h)
  have hw : ∀ x, inst.wt (f x) = w x := fun x => by
    dsimp only [inst, MWISInstance.wt, MWISInstance.ofRooted, f]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left (e x).isLt,
      Option.getD_some, Fin.eta, Equiv.symm_apply_apply]
  have hadj : ∀ x u, inst.adj (f x) (f u) = decide (G.Adj x u) := fun x u => by
    dsimp only [inst, MWISInstance.adj, MWISInstance.ofRooted, f]
    have hm : 0 < m := Nat.zero_lt_of_lt (e x).isLt
    have hlt : (e x).val * m + (e u).val < m * m := by
      have hx := (e x).isLt
      have hu := (e u).isLt
      calc (e x).val * m + (e u).val < (e x).val * m + m := Nat.add_lt_add_left hu _
        _ = ((e x).val + 1) * m := by ring
        _ ≤ m * m := Nat.mul_le_mul_right m hx
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hlt, Option.getD_some]
    have hdiv : ((e x).val * m + (e u).val) / m = (e x).val := by
      rw [Nat.mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt (e u).isLt, Nat.add_zero]
    have hmod : ((e x).val * m + (e u).val) % m = (e u).val := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (e u).isLt]
    simp only [hdiv, hmod, Fin.eta, Equiv.symm_apply_apply]
    by_cases h : G.Adj x u <;> simp [h]
  have hpar : ∀ i : Fin (n + 1), (inst.parFin i).val = (R.parent i).val := fun i => by
    by_cases hi : 1 ≤ i.val
    · simp only [MWISInstance.parFin, hi, ↓reduceDIte, inst, MWISInstance.ofRooted,
        Fin.getElem_fin, List.getElem_ofFn, Fin.eta]
    · simp only [MWISInstance.parFin, hi, ↓reduceDIte]
      have hi0 : i = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      rw [hi0, R.parent_zero, Fin.val_zero]
  have hpar_eq : ∀ i : Fin (n + 1), inst.parFin i = R.parent i :=
    fun i => Fin.ext (hpar i)
  have hbag : ∀ i : Fin (n + 1), inst.bagAt i = (L i).map f := fun i => by
    simp only [MWISInstance.bagAt, inst, MWISInstance.ofRooted, List.getElem_ofFn, Fin.eta, f]
  have htbl : ∀ t,
      tablesInst inst.adj inst.wt n inst.parFin inst.bagAt t = tablesFPT R w L t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [tablesInst, tablesFPT, ih]
      dsimp only [processInstNode, processNode]
      simp only [hpar_eq, hbag, List.length_map, childPassInst_map hf hadj hw,
        parentPass_map_inj hf]
  change rootPassInst inst.adj inst.wt (inst.bagAt (0 : Fin (n + 1)))
      (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt n)[(0 : Fin (n + 1))]
      (2 ^ (inst.bagAt (0 : Fin (n + 1))).length) = mwisFPT R w L
  rw [htbl n, hbag (0 : Fin (n + 1)), List.length_map, rootPassInst_map hf hadj hw]
  rfl

/-- When `IsBagOrder R L`, `(MWISInstance.ofRooted e R w L).result = mwisValue R w`. -/
theorem MWISInstance.result_ofRooted {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj] {m n : ℕ} (e : V ≃ Fin m)
    (R : G.RootedTreeDecomposition n) (w : V → ℕ) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) :
    (MWISInstance.ofRooted e R w L).result = mwisValue R w :=
  (MWISInstance.result_ofRooted_eq_mwisFPT e R w L).trans (mwisFPT_eq_mwisValue R w hL)

theorem MWISInstance.maxBagLen_ofRooted_le {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj] {m n : ℕ} (e : V ≃ Fin m)
    (R : G.RootedTreeDecomposition n) (w : V → ℕ) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) {k : ℕ} (hk : R.width ≤ k) :
    (MWISInstance.ofRooted e R w L).maxBagLen ≤ k + 1 := by
  refine List.foldl_max_le (Nat.zero_le _) fun len hlen => ?_
  rw [List.mem_map] at hlen
  obtain ⟨B, hB, rfl⟩ := hlen
  dsimp only [MWISInstance.ofRooted] at hB
  rw [List.mem_ofFn] at hB
  obtain ⟨i, rfl⟩ := hB
  rw [List.length_map, ← List.toFinset_card_of_nodup (hL i).1, (hL i).2]
  exact R.width_le_iff.1 hk i

theorem MWISInstance.stepBound_ofRooted_le {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj] {m n : ℕ} (e : V ≃ Fin m)
    (R : G.RootedTreeDecomposition n) (w : V → ℕ) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) {k : ℕ} (hk : R.width ≤ k) :
    (MWISInstance.ofRooted e R w L).stepBound ≤ mwisFPTBound n k := by
  have hM := MWISInstance.maxBagLen_ofRooted_le e R w hL hk
  have hn : (MWISInstance.ofRooted e R w L).numNodes = n := rfl
  unfold MWISInstance.stepBound mwisFPTBound
  rw [hn]
  dsimp only
  have hpow : 2 ^ (MWISInstance.ofRooted e R w L).maxBagLen ≤ 2 ^ (k + 1) :=
    Nat.pow_le_pow_right (by decide) hM
  gcongr

end RootedBridge

/-! ### Word-RAM mask-scan primitives (`noAdjScanProg`, `indepBagProg`, `keyMaskProg`,
`restrictMaskProg`, `forgetWeightProg`) -/

private structure NoAdjArgs where
  numVerts : ℕ
  adjPtr : ℕ
  x : ℕ
  ptr : ℕ
  len : ℕ
  mask : ℕ

private def NoAdjArgs.equiv : NoAdjArgs ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := (((((a.numVerts, a.adjPtr), a.x), a.ptr), a.len), a.mask)
  invFun := fun (((((nv, ap), x), ptr), len), mask) => ⟨nv, ap, x, ptr, len, mask⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding NoAdjArgs := .ofEquiv NoAdjArgs.equiv

private structure NoAdjEnv where
  numVerts : ℕ
  adjPtr : ℕ
  x : ℕ

private def NoAdjEnv.equiv : NoAdjEnv ≃ (ℕ × ℕ) × ℕ where
  toFun e := ((e.numVerts, e.adjPtr), e.x)
  invFun := fun ((nv, ap), x) => ⟨nv, ap, x⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding NoAdjEnv := .ofEquiv NoAdjEnv.equiv

private structure NoAdjState where
  cur : ℕ
  curM : ℕ
  ok : ℕ

private def NoAdjState.equiv : NoAdjState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.cur, s.curM), s.ok)
  invFun := fun ((cur, curM), ok) => ⟨cur, curM, ok⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding NoAdjState := .ofEquiv NoAdjState.equiv

private def noAdjStep (p : NoAdjEnv × NoAdjState) : Memory.Prog NoAdjState := do
  let u ← Memory.read p.2.cur
  let entry ← Memory.read (p.1.adjPtr + p.1.x * p.1.numVerts + u)
  let bit := p.2.curM % 2
  let ok' := if p.2.ok = 1 then
      if bit = 1 then
        if entry = 0 then 1 else 0
      else 1
    else 0
  pure ⟨p.2.cur + 1, p.2.curM / 2, ok'⟩

private def noAdjScanProg (args : NoAdjArgs) : Memory.Prog ℕ := do
  let res ← iterate noAdjStep ⟨args.numVerts, args.adjPtr, args.x⟩ args.len
    ⟨args.ptr, args.mask, 1⟩
  pure res.ok

private theorem noAdjScanProg_state (args : NoAdjArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (noAdjScanProg args) = s := by
  unfold noAdjScanProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of noAdjStep ⟨args.numVerts, args.adjPtr, args.x⟩
    (fun _ _ => rfl) args.len ⟨args.ptr, args.mask, 1⟩ s

private theorem noAdjScanProg_spec {w : ℕ} (args : NoAdjArgs) {inst : MWISInstance}
    {xs : List ℕ} {s : Memory.State}
    (hadj : HoldsIn args.adjPtr inst.adjMatrix s) (hnv : args.numVerts = inst.numVerts)
    (hx : args.x < inst.numVerts) (hxs : HoldsIn args.ptr xs s) (hlen : xs.length = args.len)
    (hxs_lt : ∀ u ∈ xs, u < inst.numVerts) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (noAdjScanProg args)) ∧
    (Memory.spec 0).clientState s (noAdjScanProg args) = s ∧
    (Memory.spec 0).clientResult s (noAdjScanProg args) =
      (if noAdjInst inst.adj args.x xs args.mask then 1 else 0) ∧
    memoryCost (noAdjScanProg args) s ≤ 2 * args.len := by
  let env : NoAdjEnv := ⟨args.numVerts, args.adjPtr, args.x⟩
  have hcost : memoryCost (noAdjScanProg args) s ≤ 2 * args.len := by
    unfold noAdjScanProg
    rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
    have hle := memoryCost_iterate_le_of noAdjStep 2 env (fun _ _ => le_rfl)
      args.len ⟨args.ptr, args.mask, 1⟩ s
    omega
  suffices ∀ ys cur curM ok, HoldsIn cur ys s → (∀ u ∈ ys, u < inst.numVerts) →
      (ok = 0 ∨ ok = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate noAdjStep env ys.length ⟨cur, curM, ok⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate noAdjStep env ys.length ⟨cur, curM, ok⟩)).ok =
        if ok = 1 ∧ noAdjInst inst.adj args.x ys curM = true then 1 else 0 by
    have hrun := this xs args.ptr args.mask 1 hxs hxs_lt (.inr rfl)
    rw [hlen] at hrun
    refine ⟨?_, noAdjScanProg_state args s, ?_, hcost⟩
    · unfold noAdjScanProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold noAdjScanProg
      rw [StateTransitionSpec.clientResult_bind]
      change ((Memory.spec 0).clientResult s
        (iterate noAdjStep env args.len ⟨args.ptr, args.mask, 1⟩)).ok = _
      rw [hrun.2]
      cases noAdjInst inst.adj args.x xs args.mask <;> rfl
  intro ys
  induction ys with
  | nil =>
    intro cur curM ok _ _ hok
    have h0 : iterate noAdjStep env 0 ⟨cur, curM, ok⟩ = pure ⟨cur, curM, ok⟩ := rfl
    simp only [List.length_nil, h0, noAdjInst]
    refine ⟨validHistory_pure w s _, ?_⟩
    rcases hok with rfl | rfl <;> rfl
  | cons u rest ih =>
    intro cur curM ok hcur hus hok
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨hb, hmem_u, hrest⟩ := hcur
    have hu_lt : u < inst.numVerts := hus u List.mem_cons_self
    have hidx_lt : args.x * inst.numVerts + u < inst.adjMatrix.length := by
      rw [inst.adjMatrix_len]
      calc args.x * inst.numVerts + u
          < args.x * inst.numVerts + inst.numVerts := Nat.add_lt_add_left hu_lt _
        _ = (args.x + 1) * inst.numVerts := by ring
        _ ≤ inst.numVerts * inst.numVerts := Nat.mul_le_mul_right _ hx
    have hadj_addr_lt : args.adjPtr + args.x * args.numVerts + u < s.frontier := by
      have := hadj.1
      rw [hnv, Nat.add_assoc]
      omega
    have hadj_read : s.mem (args.adjPtr + args.x * args.numVerts + u) =
        inst.adjMatrix.getD (args.x * inst.numVerts + u) 0 := by
      rw [hnv, Nat.add_assoc, hadj.get _ hidx_lt,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt, Option.getD_some]
    let entry := s.mem (args.adjPtr + args.x * args.numVerts + u)
    let ok' := if ok = 1 then (if curM % 2 = 1 then (if entry = 0 then 1 else 0) else 1) else 0
    have hok' : ok' = 0 ∨ ok' = 1 := by
      dsimp only [ok']
      split_ifs <;> simp
    obtain ⟨hv_rest, hr_rest⟩ :=
      ih (cur + 1) (curM / 2) ok' hrest (fun v hv => hus v (List.mem_cons_of_mem u hv)) hok'
    have hcur_lt : cur < s.frontier := by omega
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (noAdjStep (env, ⟨cur, curM, ok⟩))) := by
      dsimp only [noAdjStep, env]
      refine validHistory_read_bind hcur_lt ?_
      rw [hmem_u]
      exact validHistory_read_bind hadj_addr_lt (validHistory_pure w s _)
    have hst_step : (Memory.spec 0).clientState s (noAdjStep (env, ⟨cur, curM, ok⟩)) = s := rfl
    have hres_step : (Memory.spec 0).clientResult s (noAdjStep (env, ⟨cur, curM, ok⟩)) =
        ⟨cur + 1, curM / 2, ok'⟩ := by
      dsimp only [noAdjStep, env, ok', entry]
      change (⟨cur + 1, curM / 2, _⟩ : NoAdjState) = _
      rw [hmem_u]
    simp only [List.length_cons]
    change (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (noAdjStep (env, ⟨cur, curM, ok⟩) >>= iterate noAdjStep env rest.length)) ∧
      ((Memory.spec 0).clientResult s
        (noAdjStep (env, ⟨cur, curM, ok⟩) >>= iterate noAdjStep env rest.length)).ok = _
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_⟩
    rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step, hr_rest]
    simp only [ok', entry, noAdjInst, MWISInstance.adj, hadj_read]
    rcases hok with rfl | rfl
    · simp
    · by_cases hna : noAdjInst inst.adj args.x rest (curM / 2) = true
      · by_cases hbit : curM % 2 = 1 <;> simp [hna, hbit]
      · simp [hna]

private theorem noAdjScanProg_realizes :
    Realizes .exact noAdjScanProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 2 ∧
        ∃ m adjL xs,
          adjL.length = m * m ∧ args.numVerts = m ∧ args.x < m ∧
          HoldsIn args.adjPtr adjL s ∧ HoldsIn args.ptr xs s ∧ xs.length = args.len ∧
          (∀ u ∈ xs, u < m) ∧
          Fits w (args.adjPtr + m * m) ∧ Fits w (args.ptr + args.len))
      (fun _ _ => 0) := by
  unfold noAdjScanProg
  realize
  · exact h.1.of_le (by decide)
  · obtain ⟨h2, m, adjL, xs, hadjL_len, hnv, hx_lt, hadj_h, hxs_h, hxs_len, hxs_lt,
      hadj_fit, hptr_fit⟩ := h
    have h1 : Fits w 1 := h2.of_le (by decide)
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : NoAdjState) (t : Memory.State) =>
        j ≤ d.len ∧ st.cur + j = d.ptr + d.len ∧ st.ok ≤ 1 ∧
        HoldsIn d.adjPtr adjL t ∧ HoldsIn st.cur (xs.drop (d.len - j)) t)
      (fun j st t ⟨hj_le, hcur, hok, hadj_t, hrem⟩ => ?_)
      ⟨le_rfl, rfl, le_rfl, hadj_h, by simpa only [Nat.sub_self, List.drop_zero] using hxs_h⟩
    dsimp only [noAdjStep]
    have hj_lt : d.len - (j + 1) < xs.length := by omega
    have hdrop_eq : xs.drop (d.len - (j + 1)) =
        xs[d.len - (j + 1)] :: xs.drop (d.len - j) := by
      have hsub : d.len - j = (d.len - (j + 1)) + 1 := by omega
      rw [hsub]
      exact List.drop_eq_getElem_cons hj_lt
    rw [hdrop_eq, HoldsIn.cons_iff] at hrem
    obtain ⟨_, hmem_u, hrem_next⟩ := hrem
    have hu_lt : t.mem st.cur < m := by
      rw [hmem_u]
      exact hxs_lt _ (List.getElem_mem hj_lt)
    have hprod_lt : d.x * m + t.mem st.cur < m * m := by
      calc d.x * m + t.mem st.cur < d.x * m + m := Nat.add_lt_add_left hu_lt _
        _ = (d.x + 1) * m := by ring
        _ ≤ m * m := Nat.mul_le_mul_right m hx_lt
    have hcur_fit : Fits w (st.cur + 1) := hptr_fit.of_le (by omega)
    have hmul_fit : Fits w (d.x * d.numVerts) := by
      rw [hnv]; exact hadj_fit.of_le (by omega)
    have hsum1_fit : Fits w (d.adjPtr + d.x * d.numVerts) := by
      rw [hnv]; exact hadj_fit.of_le (by omega)
    have hsum2_fit : Fits w (d.adjPtr + d.x * d.numVerts + t.mem st.cur) := by
      rw [hnv]; exact hadj_fit.of_le (by omega)
    have h2_ne : 2 ≠ 0 := by decide
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, hadj_t, hrem_next⟩
    · repeat (first | split | assumption | refine And.intro ?_ ?_)
    · change (st.cur + 1) + j = d.ptr + d.len
      omega
    · change (if st.ok = 1 then
          if st.curM % 2 = 1 then
            if t.mem (d.adjPtr + d.x * d.numVerts + t.mem st.cur) = 0 then 1 else 0
          else 1
        else 0) ≤ 1
      split_ifs <;> omega

private structure IndepBagArgs where
  numVerts : ℕ
  adjPtr : ℕ
  bagPtr : ℕ
  bagLen : ℕ
  mask : ℕ

private def IndepBagArgs.equiv : IndepBagArgs ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((a.numVerts, a.adjPtr), a.bagPtr), a.bagLen), a.mask)
  invFun := fun ((((nv, ap), bp), bl), m) => ⟨nv, ap, bp, bl, m⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding IndepBagArgs := .ofEquiv IndepBagArgs.equiv

private structure IndepBagState where
  cur : ℕ
  remLen : ℕ
  curM : ℕ
  ok : ℕ

private def IndepBagState.equiv : IndepBagState ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun s := (((s.cur, s.remLen), s.curM), s.ok)
  invFun := fun (((cur, rem), curM), ok) => ⟨cur, rem, curM, ok⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding IndepBagState := .ofEquiv IndepBagState.equiv

private def indepBagStep (p : (ℕ × ℕ) × IndepBagState) : Memory.Prog IndepBagState := do
  let u ← Memory.read p.2.cur
  let remLen' := p.2.remLen - 1
  let bit := p.2.curM % 2
  let nextM := p.2.curM / 2
  let na ← if bit = 1 then
      noAdjScanProg ⟨p.1.1, p.1.2, u, p.2.cur + 1, remLen', nextM⟩
    else
      pure 1
  let ok' := if p.2.ok = 1 then na else 0
  pure ⟨p.2.cur + 1, remLen', nextM, ok'⟩

private def indepBagProg (args : IndepBagArgs) : Memory.Prog ℕ := do
  let res ← iterate indepBagStep (args.numVerts, args.adjPtr) args.bagLen
    ⟨args.bagPtr, args.bagLen, args.mask, 1⟩
  pure res.ok

private theorem indepBagProg_state (args : IndepBagArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (indepBagProg args) = s := by
  unfold indepBagProg
  rw [StateTransitionSpec.clientState_bind]
  refine clientState_iterate_eq_of indepBagStep (args.numVerts, args.adjPtr)
    (fun st m => ?_) args.bagLen ⟨args.bagPtr, args.bagLen, args.mask, 1⟩ s
  unfold indepBagStep
  rw [StateTransitionSpec.clientState_bind]
  dsimp only
  split
  · rw [StateTransitionSpec.clientState_bind, noAdjScanProg_state]; rfl
  · rfl

private theorem indepBagProg_spec {w : ℕ} (args : IndepBagArgs) {inst : MWISInstance}
    {xs : List ℕ} {s : Memory.State}
    (hadj : HoldsIn args.adjPtr inst.adjMatrix s) (hnv : args.numVerts = inst.numVerts)
    (hxs : HoldsIn args.bagPtr xs s) (hlen : xs.length = args.bagLen)
    (hxs_lt : ∀ u ∈ xs, u < inst.numVerts) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (indepBagProg args)) ∧
    (Memory.spec 0).clientState s (indepBagProg args) = s ∧
    (Memory.spec 0).clientResult s (indepBagProg args) =
      (if indepInst inst.adj xs args.mask then 1 else 0) ∧
    memoryCost (indepBagProg args) s ≤ args.bagLen * (2 * args.bagLen + 1) := by
  let env := (args.numVerts, args.adjPtr)
  suffices ∀ ys cur curM ok, HoldsIn cur ys s → (∀ u ∈ ys, u < inst.numVerts) →
      (ok = 0 ∨ ok = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate indepBagStep env ys.length ⟨cur, ys.length, curM, ok⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate indepBagStep env ys.length ⟨cur, ys.length, curM, ok⟩)).ok =
        (if ok = 1 ∧ indepInst inst.adj ys curM = true then 1 else 0) ∧
      memoryCost (iterate indepBagStep env ys.length ⟨cur, ys.length, curM, ok⟩) s ≤
        ys.length * (2 * ys.length + 1) by
    have hrun := this xs args.bagPtr args.mask 1 hxs hxs_lt (.inr rfl)
    rw [hlen] at hrun
    refine ⟨?_, indepBagProg_state args s, ?_, ?_⟩
    · unfold indepBagProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold indepBagProg
      rw [StateTransitionSpec.clientResult_bind]
      change ((Memory.spec 0).clientResult s
        (iterate indepBagStep env args.bagLen ⟨args.bagPtr, args.bagLen, args.mask, 1⟩)).ok = _
      rw [hrun.2.1]
      cases indepInst inst.adj xs args.mask <;> rfl
    · unfold indepBagProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro ys
  induction ys with
  | nil =>
    intro cur curM ok _ _ hok
    have h0 : iterate indepBagStep env 0 ⟨cur, 0, curM, ok⟩ = pure ⟨cur, 0, curM, ok⟩ := rfl
    simp only [List.length_nil, h0, indepInst]
    refine ⟨validHistory_pure w s _, ?_, by simp [memoryCost_pure]⟩
    rcases hok with rfl | rfl <;> rfl
  | cons u rest ih =>
    intro cur curM ok hcur hus hok
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨hb, hmem_u, hrest⟩ := hcur
    have hu_lt : u < inst.numVerts := hus u List.mem_cons_self
    have hrest_lt : ∀ v ∈ rest, v < inst.numVerts :=
      fun v hv => hus v (List.mem_cons_of_mem u hv)
    have hcur_lt : cur < s.frontier := by omega
    let naPure : ℕ :=
      if curM % 2 = 1 then
        if noAdjInst inst.adj u rest (curM / 2) then 1 else 0
      else 1
    let ok' : ℕ := if ok = 1 then naPure else 0
    have hok' : ok' = 0 ∨ ok' = 1 := by
      dsimp only [ok', naPure]
      split_ifs <;> simp
    obtain ⟨hv_rest, hr_rest, hc_rest⟩ := ih (cur + 1) (curM / 2) ok' hrest hrest_lt hok'
    have hr_st (a : ℕ) : (Memory.spec 0).clientState s (Memory.read a) = s := rfl
    have hr_res (a : ℕ) : (Memory.spec 0).clientResult s (Memory.read a) = s.mem a := rfl
    obtain ⟨hv_na, hst_na, hr_na, hc_na⟩ :=
      noAdjScanProg_spec (w := w)
        ⟨args.numVerts, args.adjPtr, u, cur + 1, rest.length, curM / 2⟩
        hadj hnv hu_lt hrest rfl hrest_lt
    dsimp only at hr_na hc_na
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (indepBagStep (env, ⟨cur, (u :: rest).length, curM, ok⟩))) := by
      unfold indepBagStep
      simp only [env, List.length_cons, Nat.add_sub_cancel]
      refine validHistory_read_bind hcur_lt ?_
      rw [hmem_u]
      split
      · exact validHistory_bind_step hv_na (validHistory_pure w _ _)
      · rw [pure_bind]; exact validHistory_pure w s _
    have hst_step : (Memory.spec 0).clientState s
        (indepBagStep (env, ⟨cur, (u :: rest).length, curM, ok⟩)) = s := by
      unfold indepBagStep
      rw [StateTransitionSpec.clientState_bind, hr_st, hr_res]
      simp only [env, List.length_cons, Nat.add_sub_cancel]
      split
      · rw [StateTransitionSpec.clientState_bind, noAdjScanProg_state]; rfl
      · rfl
    have hres_step : (Memory.spec 0).clientResult s
        (indepBagStep (env, ⟨cur, (u :: rest).length, curM, ok⟩)) =
        ⟨cur + 1, rest.length, curM / 2, ok'⟩ := by
      unfold indepBagStep
      rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res, hmem_u]
      simp only [env, List.length_cons, Nat.add_sub_cancel, ok', naPure]
      split
      · rw [StateTransitionSpec.clientResult_bind, hst_na, hr_na]; rfl
      · rfl
    have hc_step : memoryCost (indepBagStep (env, ⟨cur, (u :: rest).length, curM, ok⟩)) s ≤
        2 * rest.length + 1 := by
      unfold indepBagStep
      rw [memoryCost_bind', memoryCost_read, hr_st, hr_res, hmem_u]
      simp only [env, List.length_cons, Nat.add_sub_cancel]
      split
      · rw [memoryCost_bind', hst_na, memoryCost_pure, Nat.add_zero]; omega
      · rw [pure_bind, memoryCost_pure]; omega
    have hiter_eq :
        iterate indepBagStep env (u :: rest).length ⟨cur, (u :: rest).length, curM, ok⟩ =
        (indepBagStep (env, ⟨cur, (u :: rest).length, curM, ok⟩) >>=
          iterate indepBagStep env rest.length) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step, hr_rest]
      dsimp only [ok', naPure, indepInst]
      rcases hok with rfl | rfl
      · simp
      · by_cases hbit : curM % 2 = 1 <;>
          by_cases hna : noAdjInst inst.adj u rest (curM / 2) = true <;>
          by_cases hind : indepInst inst.adj rest (curM / 2) = true <;>
          simp [hbit, hna, hind]
    · rw [memoryCost_bind', hst_step, hres_step]
      simp only [List.length_cons]
      calc memoryCost (indepBagStep (env, ⟨cur, (u :: rest).length, curM, ok⟩)) s +
            memoryCost
              (iterate indepBagStep env rest.length ⟨cur + 1, rest.length, curM / 2, ok'⟩) s
          ≤ (2 * rest.length + 1) + rest.length * (2 * rest.length + 1) :=
            Nat.add_le_add hc_step hc_rest
        _ ≤ (rest.length + 1) * (2 * (rest.length + 1) + 1) := by nlinarith

private theorem indepBagProg_realizes :
    Realizes .exact indepBagProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 2 ∧
        ∃ m adjL xs,
          adjL.length = m * m ∧ args.numVerts = m ∧
          HoldsIn args.adjPtr adjL s ∧ HoldsIn args.bagPtr xs s ∧ xs.length = args.bagLen ∧
          (∀ u ∈ xs, u < m) ∧
          Fits w (args.adjPtr + m * m) ∧ Fits w (args.bagPtr + args.bagLen))
      (fun _ _ => 0) := by
  unfold indepBagProg
  realize [noAdjScanProg_realizes]
  · exact h.1.of_le (by decide)
  · obtain ⟨h2, m, adjL, xs, hadjL_len, hnv, hadj_h, hxs_h, hxs_len, hxs_lt,
      hadj_fit, hptr_fit⟩ := h
    have h1 : Fits w 1 := h2.of_le (by decide)
    have h2_ne : 2 ≠ 0 := by decide
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : IndepBagState) (t : Memory.State) =>
        j ≤ d.bagLen ∧ st.remLen = j ∧ st.cur + j = d.bagPtr + d.bagLen ∧ st.ok ≤ 1 ∧
        HoldsIn d.adjPtr adjL t ∧ HoldsIn st.cur (xs.drop (d.bagLen - j)) t)
      (fun j st t ⟨hj_le, hrem_eq, hcur, hok, hadj_t, hrem⟩ => ?_)
      ⟨le_rfl, rfl, rfl, le_rfl, hadj_h,
        by simpa only [Nat.sub_self, List.drop_zero] using hxs_h⟩
    have hj_lt : d.bagLen - (j + 1) < xs.length := by omega
    have hdrop_eq : xs.drop (d.bagLen - (j + 1)) =
        xs[d.bagLen - (j + 1)] :: xs.drop (d.bagLen - j) := by
      have hsub : d.bagLen - j = (d.bagLen - (j + 1)) + 1 := by omega
      rw [hsub]
      exact List.drop_eq_getElem_cons hj_lt
    rw [hdrop_eq, HoldsIn.cons_iff] at hrem
    obtain ⟨_, hmem_u, hrem_next⟩ := hrem
    have hu_lt : t.mem st.cur < m := by
      rw [hmem_u]
      exact hxs_lt _ (List.getElem_mem hj_lt)
    have hcur_fit : Fits w (st.cur + 1) := hptr_fit.of_le (by omega)
    have hrem_ge1 : 1 ≤ st.remLen := by omega
    have htail_len : (xs.drop (d.bagLen - j)).length = st.remLen - 1 := by
      rw [List.length_drop]; omega
    have htail_lt : ∀ v ∈ xs.drop (d.bagLen - j), v < m :=
      fun v hv => hxs_lt v (List.mem_of_mem_drop hv)
    have hnoAdj_safe : Fits w 2 ∧ ∃ m' adjL' xs',
        adjL'.length = m' * m' ∧ d.numVerts = m' ∧ t.mem st.cur < m' ∧
        HoldsIn d.adjPtr adjL' t ∧ HoldsIn (st.cur + 1) xs' t ∧ xs'.length = st.remLen - 1 ∧
        (∀ u ∈ xs', u < m') ∧ Fits w (d.adjPtr + m' * m') ∧
        Fits w ((st.cur + 1) + (st.remLen - 1)) :=
      ⟨h2, m, adjL, xs.drop (d.bagLen - j), hadjL_len, hnv, hu_lt, hadj_t, hrem_next,
        htail_len, htail_lt, hadj_fit, hptr_fit.of_le (by omega)⟩
    have hst_body : (Memory.spec 0).clientState t
        (indepBagStep ((d.numVerts, d.adjPtr), st)) = t := by
      unfold indepBagStep
      rw [StateTransitionSpec.clientState_bind]
      dsimp only
      split
      · rw [StateTransitionSpec.clientState_bind, noAdjScanProg_state]; rfl
      · rfl
    have hr_st (a : ℕ) : (Memory.spec 0).clientState t (Memory.read a) = t := rfl
    have hr_res (a : ℕ) : (Memory.spec 0).clientResult t (Memory.read a) = t.mem a := rfl
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_, ?_, ?_⟩
    · repeat (first | split | exact hnoAdj_safe | assumption | refine And.intro ?_ ?_)
    · unfold indepBagStep
      rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res]
      dsimp only
      split <;> [rw [StateTransitionSpec.clientResult_bind, noAdjScanProg_state]; skip] <;>
        (change st.remLen - 1 = j; omega)
    · unfold indepBagStep
      rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res]
      dsimp only
      split <;> [rw [StateTransitionSpec.clientResult_bind, noAdjScanProg_state]; skip] <;>
        (change (st.cur + 1) + j = d.bagPtr + d.bagLen; omega)
    · unfold indepBagStep
      rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res]
      dsimp only
      split
      · rw [StateTransitionSpec.clientResult_bind, noAdjScanProg_state]
        have hinst_dummy : ∃ okv, okv ≤ 1 ∧
            (Memory.spec 0).clientResult t
              (noAdjScanProg ⟨d.numVerts, d.adjPtr, t.mem st.cur, st.cur + 1,
                st.remLen - 1, st.curM / 2⟩) = okv := by
          let resv := (Memory.spec 0).clientResult t
            (noAdjScanProg ⟨d.numVerts, d.adjPtr, t.mem st.cur, st.cur + 1,
              st.remLen - 1, st.curM / 2⟩)
          refine ⟨resv, ?_, rfl⟩
          unfold resv noAdjScanProg
          rw [StateTransitionSpec.clientResult_bind]
          change ((Memory.spec 0).clientResult t (iterate noAdjStep _ _ _)).ok ≤ 1
          suffices ∀ k st₀, st₀.ok ≤ 1 →
              ((Memory.spec 0).clientResult t (iterate noAdjStep _ k st₀)).ok ≤ 1 from
            this _ _ le_rfl
          intro k
          induction k with
          | zero => intro st₀ h0; exact h0
          | succ k ihk =>
            intro st₀ _
            have hit : iterate noAdjStep ⟨d.numVerts, d.adjPtr, t.mem st.cur⟩ (k + 1) st₀ =
                (noAdjStep (⟨d.numVerts, d.adjPtr, t.mem st.cur⟩, st₀) >>=
                  iterate noAdjStep ⟨d.numVerts, d.adjPtr, t.mem st.cur⟩ k) := rfl
            rw [hit, StateTransitionSpec.clientResult_bind]
            have hs_step : (Memory.spec 0).clientState t
                (noAdjStep (⟨d.numVerts, d.adjPtr, t.mem st.cur⟩, st₀)) = t := rfl
            rw [hs_step]
            refine ihk _ ?_
            change (if st₀.ok = 1 then _ else 0) ≤ 1
            split_ifs <;> omega
        obtain ⟨okv, hokv, heq⟩ := hinst_dummy
        rw [heq]
        change (if st.ok = 1 then okv else 0) ≤ 1
        split_ifs <;> omega
      · change (if st.ok = 1 then 1 else 0) ≤ 1
        split_ifs <;> omega
    · rw [hst_body]; exact hadj_t
    · rw [hst_body]
      unfold indepBagStep
      rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res]
      dsimp only
      split <;> [rw [StateTransitionSpec.clientResult_bind, noAdjScanProg_state]; skip] <;>
        exact hrem_next

/-! ### Selected-membership and parent-bag mask (`selMemBagProg`, `keyMaskProg`) -/

private structure SelMemArgs where
  target : ℕ
  ptr : ℕ
  len : ℕ
  mask : ℕ

private def SelMemArgs.equiv : SelMemArgs ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun a := (((a.target, a.ptr), a.len), a.mask)
  invFun := fun (((t, p), l), m) => ⟨t, p, l, m⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding SelMemArgs := .ofEquiv SelMemArgs.equiv

private structure SelMemState where
  cur : ℕ
  curM : ℕ
  found : ℕ

private def SelMemState.equiv : SelMemState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.cur, s.curM), s.found)
  invFun := fun ((c, m), f) => ⟨c, m, f⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding SelMemState := .ofEquiv SelMemState.equiv

private def selMemStep (p : ℕ × SelMemState) : Memory.Prog SelMemState := do
  let u ← Memory.read p.2.cur
  let bit := p.2.curM % 2
  let found' := if bit = 1 then (if p.1 = u then 1 else p.2.found) else p.2.found
  pure ⟨p.2.cur + 1, p.2.curM / 2, found'⟩

private def selMemBagProg (args : SelMemArgs) : Memory.Prog ℕ := do
  let res ← iterate selMemStep args.target args.len ⟨args.ptr, args.mask, 0⟩
  pure res.found

private theorem selMemBagProg_state (args : SelMemArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (selMemBagProg args) = s := by
  unfold selMemBagProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of selMemStep args.target (fun _ _ => rfl)
    args.len ⟨args.ptr, args.mask, 0⟩ s

private theorem selMemBagProg_spec {w : ℕ} (args : SelMemArgs) {xs : List ℕ} {s : Memory.State}
    (hxs : HoldsIn args.ptr xs s) (hlen : xs.length = args.len) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (selMemBagProg args)) ∧
    (Memory.spec 0).clientState s (selMemBagProg args) = s ∧
    (Memory.spec 0).clientResult s (selMemBagProg args) =
      (if selMemMask args.target xs args.mask then 1 else 0) ∧
    memoryCost (selMemBagProg args) s ≤ args.len := by
  have hcost : memoryCost (selMemBagProg args) s ≤ args.len := by
    unfold selMemBagProg
    rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
    simpa only [Nat.one_mul] using
      memoryCost_iterate_le_of selMemStep 1 args.target (fun _ _ => le_rfl)
        args.len ⟨args.ptr, args.mask, 0⟩ s
  suffices ∀ ys cur curM found, HoldsIn cur ys s → (found = 0 ∨ found = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate selMemStep args.target ys.length ⟨cur, curM, found⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate selMemStep args.target ys.length ⟨cur, curM, found⟩)).found =
        if found = 1 ∨ selMemMask args.target ys curM = true then 1 else 0 by
    have hrun := this xs args.ptr args.mask 0 hxs (.inl rfl)
    rw [hlen] at hrun
    refine ⟨?_, selMemBagProg_state args s, ?_, hcost⟩
    · unfold selMemBagProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold selMemBagProg
      rw [StateTransitionSpec.clientResult_bind]
      change ((Memory.spec 0).clientResult s
        (iterate selMemStep args.target args.len ⟨args.ptr, args.mask, 0⟩)).found = _
      rw [hrun.2]
      cases selMemMask args.target xs args.mask <;> rfl
  intro ys
  induction ys with
  | nil =>
    intro cur curM found _ hfd
    have h0 : iterate selMemStep args.target 0 ⟨cur, curM, found⟩ = pure ⟨cur, curM, found⟩ := rfl
    simp only [List.length_nil, h0, selMemMask]
    refine ⟨validHistory_pure w s _, ?_⟩
    rcases hfd with rfl | rfl <;> rfl
  | cons u rest ih =>
    intro cur curM found hcur hfd
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨hb, hmem_u, hrest⟩ := hcur
    have hcur_lt : cur < s.frontier := by omega
    let found' := if curM % 2 = 1 then (if args.target = u then 1 else found) else found
    have hfd' : found' = 0 ∨ found' = 1 := by
      dsimp only [found']
      split_ifs <;> [exact .inr rfl; exact hfd; exact hfd]
    obtain ⟨hv_rest, hr_rest⟩ := ih (cur + 1) (curM / 2) found' hrest hfd'
    have hres_step :
        (Memory.spec 0).clientResult s (selMemStep (args.target, ⟨cur, curM, found⟩)) =
        ⟨cur + 1, curM / 2, found'⟩ := by
      dsimp only [selMemStep, found']
      change (⟨cur + 1, curM / 2, _⟩ : SelMemState) = _
      rw [hmem_u]
    simp only [List.length_cons]
    change (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (selMemStep (args.target, ⟨cur, curM, found⟩) >>=
            iterate selMemStep args.target rest.length)) ∧
      ((Memory.spec 0).clientResult s
        (selMemStep (args.target, ⟨cur, curM, found⟩) >>=
          iterate selMemStep args.target rest.length)).found = _
    refine ⟨validHistory_bind_step (validHistory_read_bind hcur_lt (validHistory_pure w s _)) ?_,
      ?_⟩
    · change (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate selMemStep args.target rest.length
            ((Memory.spec 0).clientResult s (selMemStep (args.target, ⟨cur, curM, found⟩)))))
      rwa [hres_step]
    · rw [StateTransitionSpec.clientResult_bind]
      change ((Memory.spec 0).clientResult s
        (iterate selMemStep args.target rest.length
          ((Memory.spec 0).clientResult s
            (selMemStep (args.target, ⟨cur, curM, found⟩))))).found = _
      rw [hres_step, hr_rest]
      dsimp only [found', selMemMask]
      rcases hfd with rfl | rfl
      · by_cases hbit : curM % 2 = 1
        · by_cases heq : args.target = u <;> simp [hbit, heq]
        · simp [hbit]
      · simp only [ite_self, true_or, ↓reduceIte]

private theorem selMemBagProg_realizes :
    Realizes .exact selMemBagProg WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w 2 ∧ Fits w (args.ptr + args.len))
      (fun _ _ => 0) := by
  unfold selMemBagProg
  realize
  obtain ⟨h2, hfit⟩ := h
  have h1 : Fits w 1 := h2.of_le (by decide)
  have h2_ne : 2 ≠ 0 := by decide
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : SelMemState) (_ : Memory.State) =>
      st.cur + j = d.ptr + d.len ∧ st.found ≤ 1)
    (fun j st m ⟨hcur, hfd⟩ => ?_)
    ⟨rfl, Nat.zero_le _⟩
  dsimp only [selMemStep]
  have hcur_fit : Fits w (st.cur + 1) := hfit.of_le (by omega)
  refine ⟨?_, ?_, ?_⟩
  · repeat (first | split | assumption | refine And.intro ?_ ?_)
  · change (st.cur + 1) + j = d.ptr + d.len
    omega
  · change (if st.curM % 2 = 1 then
        if d.target = m.mem st.cur then 1 else st.found
      else st.found) ≤ 1
    split_ifs <;> omega

private structure MaskTransArgs where
  bagBPtr : ℕ
  bagBLen : ℕ
  bagPPtr : ℕ
  bagPLen : ℕ
  mask : ℕ

private def MaskTransArgs.equiv : MaskTransArgs ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((a.bagBPtr, a.bagBLen), a.bagPPtr), a.bagPLen), a.mask)
  invFun := fun ((((bp, bl), pp), pl), m) => ⟨bp, bl, pp, pl, m⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding MaskTransArgs := .ofEquiv MaskTransArgs.equiv

private structure KeyMaskEnv where
  bagBPtr : ℕ
  bagBLen : ℕ
  mask : ℕ

private def KeyMaskEnv.equiv : KeyMaskEnv ≃ (ℕ × ℕ) × ℕ where
  toFun e := ((e.bagBPtr, e.bagBLen), e.mask)
  invFun := fun ((bp, bl), m) => ⟨bp, bl, m⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding KeyMaskEnv := .ofEquiv KeyMaskEnv.equiv

private structure KeyMaskState where
  curP : ℕ
  pow2 : ℕ
  acc : ℕ

private def KeyMaskState.equiv : KeyMaskState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.curP, s.pow2), s.acc)
  invFun := fun ((c, p), a) => ⟨c, p, a⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding KeyMaskState := .ofEquiv KeyMaskState.equiv

private def keyMaskStep (p : KeyMaskEnv × KeyMaskState) : Memory.Prog KeyMaskState := do
  let u ← Memory.read p.2.curP
  let sel ← selMemBagProg ⟨u, p.1.bagBPtr, p.1.bagBLen, p.1.mask⟩
  let addTerm := if sel = 1 then p.2.pow2 else 0
  pure ⟨p.2.curP + 1, 2 * p.2.pow2, p.2.acc + addTerm⟩

private def keyMaskProg (args : MaskTransArgs) : Memory.Prog ℕ := do
  let res ← iterate keyMaskStep ⟨args.bagBPtr, args.bagBLen, args.mask⟩ args.bagPLen
    ⟨args.bagPPtr, 1, 0⟩
  pure res.acc

private theorem keyMaskProg_state (args : MaskTransArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (keyMaskProg args) = s := by
  unfold keyMaskProg
  rw [StateTransitionSpec.clientState_bind]
  refine clientState_iterate_eq_of keyMaskStep ⟨args.bagBPtr, args.bagBLen, args.mask⟩
    (fun st m => ?_) args.bagPLen ⟨args.bagPPtr, 1, 0⟩ s
  unfold keyMaskStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind]
  change (Memory.spec 0).clientState m
    (selMemBagProg ⟨m.mem st.curP, args.bagBPtr, args.bagBLen, args.mask⟩ >>= _) = m
  rw [StateTransitionSpec.clientState_bind, selMemBagProg_state]
  rfl

private theorem keyMaskProg_spec {w : ℕ} (args : MaskTransArgs) {LB LP : List ℕ}
    {s : Memory.State}
    (hLB : HoldsIn args.bagBPtr LB s) (hlenB : LB.length = args.bagBLen)
    (hLP : HoldsIn args.bagPPtr LP s) (hlenP : LP.length = args.bagPLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (keyMaskProg args)) ∧
    (Memory.spec 0).clientState s (keyMaskProg args) = s ∧
    (Memory.spec 0).clientResult s (keyMaskProg args) = keyMask LB LP args.mask ∧
    memoryCost (keyMaskProg args) s ≤ args.bagPLen * (args.bagBLen + 1) := by
  let env : KeyMaskEnv := ⟨args.bagBPtr, args.bagBLen, args.mask⟩
  suffices ∀ ys curP pow2 acc, HoldsIn curP ys s →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate keyMaskStep env ys.length ⟨curP, pow2, acc⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate keyMaskStep env ys.length ⟨curP, pow2, acc⟩)).acc =
        acc + pow2 * keyMask LB ys args.mask ∧
      memoryCost (iterate keyMaskStep env ys.length ⟨curP, pow2, acc⟩) s ≤
        ys.length * (args.bagBLen + 1) by
    have hrun := this LP args.bagPPtr 1 0 hLP
    rw [hlenP] at hrun
    refine ⟨?_, keyMaskProg_state args s, ?_, ?_⟩
    · unfold keyMaskProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold keyMaskProg
      rw [StateTransitionSpec.clientResult_bind]
      change ((Memory.spec 0).clientResult s
        (iterate keyMaskStep env args.bagPLen ⟨args.bagPPtr, 1, 0⟩)).acc = _
      rw [hrun.2.1, Nat.zero_add, Nat.one_mul]
    · unfold keyMaskProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro ys
  induction ys with
  | nil =>
    intro curP pow2 acc _
    have h0 : iterate keyMaskStep env 0 ⟨curP, pow2, acc⟩ = pure ⟨curP, pow2, acc⟩ := rfl
    simp only [List.length_nil, h0, keyMask, Nat.mul_zero, Nat.add_zero]
    exact ⟨validHistory_pure w s _, rfl, by simp [memoryCost_pure]⟩
  | cons u rest ih =>
    intro curP pow2 acc hcur
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨hb, hmem_u, hrest⟩ := hcur
    have hcur_lt : curP < s.frontier := by omega
    obtain ⟨hv_sel, hst_sel, hr_sel, hc_sel⟩ :=
      selMemBagProg_spec (w := w) ⟨u, args.bagBPtr, args.bagBLen, args.mask⟩ hLB hlenB
    let addTerm := if selMemMask u LB args.mask then pow2 else 0
    obtain ⟨hv_rest, hr_rest, hc_rest⟩ := ih (curP + 1) (2 * pow2) (acc + addTerm) hrest
    dsimp only at hr_sel hc_sel
    have hadd_eq :
        (if (if selMemMask u LB args.mask then 1 else 0) = 1 then pow2 else 0) = addTerm := by
      dsimp only [addTerm]
      cases selMemMask u LB args.mask <;> rfl
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (keyMaskStep (env, ⟨curP, pow2, acc⟩))) := by
      unfold keyMaskStep
      dsimp only [env]
      refine validHistory_read_bind hcur_lt ?_
      rw [hmem_u]
      exact validHistory_bind_step hv_sel (validHistory_pure w _ _)
    have hst_step : (Memory.spec 0).clientState s (keyMaskStep (env, ⟨curP, pow2, acc⟩)) = s := by
      unfold keyMaskStep
      dsimp only [env]
      rw [StateTransitionSpec.clientState_bind]
      change (Memory.spec 0).clientState s
        (selMemBagProg ⟨s.mem curP, args.bagBPtr, args.bagBLen, args.mask⟩ >>= _) = s
      rw [StateTransitionSpec.clientState_bind, selMemBagProg_state]
      rfl
    have hres_step : (Memory.spec 0).clientResult s (keyMaskStep (env, ⟨curP, pow2, acc⟩)) =
        ⟨curP + 1, 2 * pow2, acc + addTerm⟩ := by
      unfold keyMaskStep
      dsimp only [env]
      rw [StateTransitionSpec.clientResult_bind]
      change (Memory.spec 0).clientResult s
        (selMemBagProg ⟨s.mem curP, args.bagBPtr, args.bagBLen, args.mask⟩ >>= _) = _
      rw [hmem_u, StateTransitionSpec.clientResult_bind, hst_sel, hr_sel, hadd_eq]
      rfl
    have hc_step : memoryCost (keyMaskStep (env, ⟨curP, pow2, acc⟩)) s ≤ args.bagBLen + 1 := by
      unfold keyMaskStep
      dsimp only [env]
      rw [memoryCost_bind', memoryCost_read]
      change 1 + memoryCost
        (selMemBagProg ⟨s.mem curP, args.bagBPtr, args.bagBLen, args.mask⟩ >>= _) s ≤ _
      rw [hmem_u, memoryCost_bind', hst_sel, memoryCost_pure, Nat.add_zero]
      omega
    simp only [List.length_cons]
    have hiter_eq : iterate keyMaskStep env (rest.length + 1) ⟨curP, pow2, acc⟩ =
        (keyMaskStep (env, ⟨curP, pow2, acc⟩) >>= iterate keyMaskStep env rest.length) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step, hr_rest]
      dsimp only [addTerm, keyMask]
      by_cases hsm : selMemMask u LB args.mask = true <;>
        simp only [hsm, Bool.false_eq_true, ↓reduceIte] <;> ring
    · rw [memoryCost_bind', hst_step, hres_step]
      calc memoryCost (keyMaskStep (env, ⟨curP, pow2, acc⟩)) s +
            memoryCost (iterate keyMaskStep env rest.length
              ⟨curP + 1, 2 * pow2, acc + addTerm⟩) s
          ≤ (args.bagBLen + 1) + rest.length * (args.bagBLen + 1) :=
            Nat.add_le_add hc_step hc_rest
        _ = (rest.length + 1) * (args.bagBLen + 1) := by ring

private theorem keyMaskProg_realizes :
    Realizes .exact keyMaskProg WordEncoding.encode WordEncoding.encode
      (fun w args _ =>
        Fits w 2 ∧ Fits w (args.bagBPtr + args.bagBLen) ∧ Fits w (args.bagPPtr + args.bagPLen) ∧
        Fits w (2 ^ args.bagPLen))
      (fun _ _ => 0) := by
  unfold keyMaskProg
  realize [selMemBagProg_realizes]
  · exact h.1.of_le (by decide)
  · obtain ⟨h2, hfitB, hfitP, hpow⟩ := h
    have h1 : Fits w 1 := h2.of_le (by decide)
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : KeyMaskState) (_ : Memory.State) =>
        j ≤ d.bagPLen ∧ st.curP + j = d.bagPPtr + d.bagPLen ∧
        st.pow2 = 2 ^ (d.bagPLen - j) ∧ st.acc < st.pow2)
      (fun j st m ⟨hj_le, hcur, hp2, hacc_lt⟩ => ?_)
      ⟨le_rfl, rfl, by simp only [Nat.sub_self, Nat.pow_zero], Nat.zero_lt_one⟩
    have hsub : d.bagPLen - j = (d.bagPLen - (j + 1)) + 1 := by omega
    have hp2_next : 2 * st.pow2 = 2 ^ (d.bagPLen - j) := by
      rw [hp2, hsub, Nat.pow_succ, Nat.mul_comm]
    have hp2_le : 2 * st.pow2 ≤ 2 ^ d.bagPLen := by
      rw [hp2_next]
      exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    have hp2_fit : Fits w (2 * st.pow2) := hpow.of_le hp2_le
    have hcur_fit : Fits w (st.curP + 1) := hfitP.of_le (by omega)
    have hacc1_fit : Fits w (st.acc + st.pow2) := hp2_fit.of_le (by omega)
    have hacc0_fit : Fits w (st.acc + 0) := hp2_fit.of_le (by omega)
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_⟩
    · repeat (first | split | assumption | refine And.intro ?_ ?_)
    · unfold keyMaskStep
      dsimp only
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        selMemBagProg_state]
      change (st.curP + 1) + j = d.bagPPtr + d.bagPLen
      omega
    · unfold keyMaskStep
      dsimp only
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        selMemBagProg_state]
      exact hp2_next
    · unfold keyMaskStep
      dsimp only
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        selMemBagProg_state]
      change st.acc + (if _ then st.pow2 else 0) < 2 * st.pow2
      split_ifs <;> omega

/-! ### Parent-mask restriction (`restrictMaskProg`) and forgotten weight (`forgetWeightProg`) -/

private structure RestrictState where
  curP : ℕ
  curS : ℕ
  pow2 : ℕ
  acc : ℕ

private def RestrictState.equiv : RestrictState ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun s := (((s.curP, s.curS), s.pow2), s.acc)
  invFun := fun (((cp, cs), p2), a) => ⟨cp, cs, p2, a⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding RestrictState := .ofEquiv RestrictState.equiv

private def restrictStep (p : (ℕ × ℕ) × RestrictState) : Memory.Prog RestrictState := do
  let u ← Memory.read p.2.curP
  let inB ← bagMemProg ⟨u, p.1.1, p.1.2⟩
  let bit := p.2.curS % 2
  let addTerm := if bit = 1 then (if inB = 1 then p.2.pow2 else 0) else 0
  pure ⟨p.2.curP + 1, p.2.curS / 2, 2 * p.2.pow2, p.2.acc + addTerm⟩

private def restrictMaskProg (args : MaskTransArgs) : Memory.Prog ℕ := do
  let res ← iterate restrictStep (args.bagBPtr, args.bagBLen) args.bagPLen
    ⟨args.bagPPtr, args.mask, 1, 0⟩
  pure res.acc

private theorem restrictMaskProg_state (args : MaskTransArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (restrictMaskProg args) = s := by
  unfold restrictMaskProg
  rw [StateTransitionSpec.clientState_bind]
  refine clientState_iterate_eq_of restrictStep (args.bagBPtr, args.bagBLen)
    (fun st m => ?_) args.bagPLen ⟨args.bagPPtr, args.mask, 1, 0⟩ s
  unfold restrictStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind, bagMemProg_state]
  rfl

private theorem restrictMaskProg_spec {w : ℕ} (args : MaskTransArgs) {LB LP : List ℕ}
    {s : Memory.State}
    (hLB : HoldsIn args.bagBPtr LB s) (hlenB : LB.length = args.bagBLen)
    (hLP : HoldsIn args.bagPPtr LP s) (hlenP : LP.length = args.bagPLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (restrictMaskProg args)) ∧
    (Memory.spec 0).clientState s (restrictMaskProg args) = s ∧
    (Memory.spec 0).clientResult s (restrictMaskProg args) = restrictMask LB LP args.mask ∧
    memoryCost (restrictMaskProg args) s ≤ args.bagPLen * (args.bagBLen + 1) := by
  let env := (args.bagBPtr, args.bagBLen)
  suffices ∀ ys curP curS pow2 acc, HoldsIn curP ys s →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate restrictStep env ys.length ⟨curP, curS, pow2, acc⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate restrictStep env ys.length ⟨curP, curS, pow2, acc⟩)).acc =
        acc + pow2 * restrictMask LB ys curS ∧
      memoryCost (iterate restrictStep env ys.length ⟨curP, curS, pow2, acc⟩) s ≤
        ys.length * (args.bagBLen + 1) by
    have hrun := this LP args.bagPPtr args.mask 1 0 hLP
    rw [hlenP] at hrun
    refine ⟨?_, restrictMaskProg_state args s, ?_, ?_⟩
    · unfold restrictMaskProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold restrictMaskProg
      rw [StateTransitionSpec.clientResult_bind]
      change ((Memory.spec 0).clientResult s
        (iterate restrictStep env args.bagPLen ⟨args.bagPPtr, args.mask, 1, 0⟩)).acc = _
      rw [hrun.2.1, Nat.zero_add, Nat.one_mul]
    · unfold restrictMaskProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro ys
  induction ys with
  | nil =>
    intro curP curS pow2 acc _
    have h0 : iterate restrictStep env 0 ⟨curP, curS, pow2, acc⟩ =
        pure ⟨curP, curS, pow2, acc⟩ := rfl
    simp only [List.length_nil, h0, restrictMask, Nat.mul_zero, Nat.add_zero]
    exact ⟨validHistory_pure w s _, rfl, by simp [memoryCost_pure]⟩
  | cons u rest ih =>
    intro curP curS pow2 acc hcur
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨hb, hmem_u, hrest⟩ := hcur
    have hcur_lt : curP < s.frontier := by omega
    obtain ⟨hv_bm, hst_bm, hr_bm, hc_bm⟩ :=
      bagMemProg_spec (w := w) ⟨u, args.bagBPtr, args.bagBLen⟩ hLB hlenB
    let addTerm := if curS % 2 = 1 ∧ memBag u LB = true then pow2 else 0
    obtain ⟨hv_rest, hr_rest, hc_rest⟩ :=
      ih (curP + 1) (curS / 2) (2 * pow2) (acc + addTerm) hrest
    have hadd_eq :
        (if curS % 2 = 1 then
          if (if memBag u LB then 1 else 0) = 1 then pow2 else 0
        else 0) = addTerm := by
      dsimp only [addTerm]
      by_cases hbit : curS % 2 = 1 <;> cases memBag u LB <;> simp [hbit]
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (restrictStep (env, ⟨curP, curS, pow2, acc⟩))) := by
      unfold restrictStep
      dsimp only [env]
      refine validHistory_read_bind hcur_lt ?_
      rw [hmem_u]
      exact validHistory_bind_step hv_bm (validHistory_pure w _ _)
    have hst_step : (Memory.spec 0).clientState s
        (restrictStep (env, ⟨curP, curS, pow2, acc⟩)) = s := by
      unfold restrictStep
      dsimp only [env]
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        bagMemProg_state]
      rfl
    have hres_step : (Memory.spec 0).clientResult s
        (restrictStep (env, ⟨curP, curS, pow2, acc⟩)) =
        ⟨curP + 1, curS / 2, 2 * pow2, acc + addTerm⟩ := by
      unfold restrictStep
      dsimp only [env]
      rw [StateTransitionSpec.clientResult_bind]
      change (Memory.spec 0).clientResult s
        (bagMemProg ⟨s.mem curP, args.bagBPtr, args.bagBLen⟩ >>= _) = _
      rw [hmem_u, StateTransitionSpec.clientResult_bind, hst_bm, hr_bm, hadd_eq]
      rfl
    have hc_step : memoryCost (restrictStep (env, ⟨curP, curS, pow2, acc⟩)) s ≤
        args.bagBLen + 1 := by
      dsimp only at hc_bm
      unfold restrictStep
      dsimp only [env]
      rw [memoryCost_bind', memoryCost_read]
      change 1 + memoryCost (bagMemProg ⟨s.mem curP, args.bagBPtr, args.bagBLen⟩ >>= _) s ≤ _
      rw [hmem_u, memoryCost_bind', hst_bm, memoryCost_pure, Nat.add_zero]
      omega
    simp only [List.length_cons]
    have hiter_eq : iterate restrictStep env (rest.length + 1) ⟨curP, curS, pow2, acc⟩ =
        (restrictStep (env, ⟨curP, curS, pow2, acc⟩) >>= iterate restrictStep env rest.length) :=
      rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step, hr_rest]
      dsimp only [addTerm, restrictMask]
      by_cases hbit : curS % 2 = 1 <;> by_cases hin : u ∈ LB <;> simp [hbit, hin] <;> ring
    · rw [memoryCost_bind', hst_step, hres_step]
      calc memoryCost (restrictStep (env, ⟨curP, curS, pow2, acc⟩)) s +
            memoryCost (iterate restrictStep env rest.length
              ⟨curP + 1, curS / 2, 2 * pow2, acc + addTerm⟩) s
          ≤ (args.bagBLen + 1) + rest.length * (args.bagBLen + 1) :=
            Nat.add_le_add hc_step hc_rest
        _ = (rest.length + 1) * (args.bagBLen + 1) := by ring

private theorem restrictMaskProg_realizes :
    Realizes .exact restrictMaskProg WordEncoding.encode WordEncoding.encode
      (fun w args _ =>
        Fits w 2 ∧ Fits w (args.bagBPtr + args.bagBLen) ∧ Fits w (args.bagPPtr + args.bagPLen) ∧
        Fits w (2 ^ args.bagPLen))
      (fun _ _ => 0) := by
  unfold restrictMaskProg
  realize [bagMemProg_realizes]
  · exact h.1.of_le (by decide)
  · obtain ⟨h2, hfitB, hfitP, hpow⟩ := h
    have h1 : Fits w 1 := h2.of_le (by decide)
    have h2_ne : 2 ≠ 0 := by decide
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : RestrictState) (_ : Memory.State) =>
        j ≤ d.bagPLen ∧ st.curP + j = d.bagPPtr + d.bagPLen ∧
        st.pow2 = 2 ^ (d.bagPLen - j) ∧ st.acc < st.pow2)
      (fun j st m ⟨hj_le, hcur, hp2, hacc_lt⟩ => ?_)
      ⟨le_rfl, rfl, by simp only [Nat.sub_self, Nat.pow_zero], Nat.zero_lt_one⟩
    have hsub : d.bagPLen - j = (d.bagPLen - (j + 1)) + 1 := by omega
    have hp2_next : 2 * st.pow2 = 2 ^ (d.bagPLen - j) := by
      rw [hp2, hsub, Nat.pow_succ, Nat.mul_comm]
    have hp2_fit : Fits w (2 * st.pow2) :=
      hpow.of_le (by rw [hp2_next]; exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
    have hcur_fit : Fits w (st.curP + 1) := hfitP.of_le (by omega)
    have hacc1_fit : Fits w (st.acc + st.pow2) := hp2_fit.of_le (by omega)
    have hacc0_fit : Fits w (st.acc + 0) := hp2_fit.of_le (by omega)
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_⟩
    · repeat (first | split | assumption | refine And.intro ?_ ?_)
    · unfold restrictStep
      dsimp only
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        bagMemProg_state]
      change (st.curP + 1) + j = d.bagPPtr + d.bagPLen
      omega
    · unfold restrictStep
      dsimp only
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        bagMemProg_state]
      exact hp2_next
    · unfold restrictStep
      dsimp only
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        bagMemProg_state]
      change st.acc + (if _ then _ else 0) < 2 * st.pow2
      split_ifs <;> omega

private structure ForgetWeightArgs where
  wtPtr : ℕ
  bagPPtr : ℕ
  bagPLen : ℕ
  bagBPtr : ℕ
  bagBLen : ℕ
  mask : ℕ

private def ForgetWeightArgs.equiv : ForgetWeightArgs ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := (((((a.wtPtr, a.bagPPtr), a.bagPLen), a.bagBPtr), a.bagBLen), a.mask)
  invFun := fun (((((wp, pp), pl), bp), bl), m) => ⟨wp, pp, pl, bp, bl, m⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ForgetWeightArgs := .ofEquiv ForgetWeightArgs.equiv

private structure ForgetWeightEnv where
  wtPtr : ℕ
  bagPPtr : ℕ
  bagPLen : ℕ

private def ForgetWeightEnv.equiv : ForgetWeightEnv ≃ (ℕ × ℕ) × ℕ where
  toFun e := ((e.wtPtr, e.bagPPtr), e.bagPLen)
  invFun := fun ((wp, pp), pl) => ⟨wp, pp, pl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ForgetWeightEnv := .ofEquiv ForgetWeightEnv.equiv

private structure ForgetWeightState where
  curB : ℕ
  curT : ℕ
  acc : ℕ

private def ForgetWeightState.equiv : ForgetWeightState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.curB, s.curT), s.acc)
  invFun := fun ((cb, ct), a) => ⟨cb, ct, a⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ForgetWeightState := .ofEquiv ForgetWeightState.equiv

private def forgetWeightStep (p : ForgetWeightEnv × ForgetWeightState) :
    Memory.Prog ForgetWeightState := do
  let u ← Memory.read p.2.curB
  let wu ← Memory.read (p.1.wtPtr + u)
  let inP ← bagMemProg ⟨u, p.1.bagPPtr, p.1.bagPLen⟩
  let bit := p.2.curT % 2
  let addW := if bit = 1 then (if inP = 0 then wu else 0) else 0
  pure ⟨p.2.curB + 1, p.2.curT / 2, p.2.acc + addW⟩

private def forgetWeightProg (args : ForgetWeightArgs) : Memory.Prog ℕ := do
  let res ← iterate forgetWeightStep ⟨args.wtPtr, args.bagPPtr, args.bagPLen⟩ args.bagBLen
    ⟨args.bagBPtr, args.mask, 0⟩
  pure res.acc

private theorem forgetWeightProg_state (args : ForgetWeightArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (forgetWeightProg args) = s := by
  unfold forgetWeightProg
  rw [StateTransitionSpec.clientState_bind]
  refine clientState_iterate_eq_of forgetWeightStep ⟨args.wtPtr, args.bagPPtr, args.bagPLen⟩
    (fun _ m => ?_) args.bagBLen ⟨args.bagBPtr, args.mask, 0⟩ s
  unfold forgetWeightStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientState_bind, bagMemProg_state]
  rfl

private theorem forgetWeight_le_mul_maxWeight (inst : MWISInstance) (LP : List ℕ) :
    ∀ (LB : List ℕ) (t : ℕ),
      (∀ u ∈ LB, u < inst.numVerts) →
      forgetWeight inst.wt LP LB t ≤ LB.length * inst.maxWeight
  | [], _, _ => by simp [forgetWeight]
  | u :: rest, t, hus => by
    have hu_lt : u < inst.weights.length := by
      rw [inst.weights_len]; exact hus u List.mem_cons_self
    have hwu : inst.wt u ≤ inst.maxWeight := by
      unfold MWISInstance.wt MWISInstance.maxWeight
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu_lt, Option.getD_some]
      exact List.mem_le_foldl_max (List.getElem_mem hu_lt)
    have hrest := forgetWeight_le_mul_maxWeight inst LP rest (t / 2)
      (fun v hv => hus v (List.mem_cons_of_mem u hv))
    simp only [forgetWeight, List.length_cons]
    have hhead : (if t % 2 = 1 ∧ memBag u LP = false then inst.wt u else 0) ≤ inst.maxWeight := by
      split_ifs <;> [exact hwu; exact Nat.zero_le _]
    calc (if t % 2 = 1 ∧ memBag u LP = false then inst.wt u else 0) +
            forgetWeight inst.wt LP rest (t / 2)
        ≤ inst.maxWeight + rest.length * inst.maxWeight := Nat.add_le_add hhead hrest
      _ = (rest.length + 1) * inst.maxWeight := by ring

private theorem forgetWeightProg_spec {w : ℕ} (args : ForgetWeightArgs) {inst : MWISInstance}
    {LP LB : List ℕ} {s : Memory.State}
    (hwt : HoldsIn args.wtPtr inst.weights s)
    (hLP : HoldsIn args.bagPPtr LP s) (hlenP : LP.length = args.bagPLen)
    (hLB : HoldsIn args.bagBPtr LB s) (hlenB : LB.length = args.bagBLen)
    (hLB_lt : ∀ u ∈ LB, u < inst.numVerts) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (forgetWeightProg args)) ∧
    (Memory.spec 0).clientState s (forgetWeightProg args) = s ∧
    (Memory.spec 0).clientResult s (forgetWeightProg args) = forgetWeight inst.wt LP LB args.mask ∧
    memoryCost (forgetWeightProg args) s ≤ args.bagBLen * (args.bagPLen + 2) := by
  let env : ForgetWeightEnv := ⟨args.wtPtr, args.bagPPtr, args.bagPLen⟩
  suffices ∀ ys curB curT acc, HoldsIn curB ys s → (∀ u ∈ ys, u < inst.numVerts) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate forgetWeightStep env ys.length ⟨curB, curT, acc⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate forgetWeightStep env ys.length ⟨curB, curT, acc⟩)).acc =
        acc + forgetWeight inst.wt LP ys curT ∧
      memoryCost (iterate forgetWeightStep env ys.length ⟨curB, curT, acc⟩) s ≤
        ys.length * (args.bagPLen + 2) by
    have hrun := this LB args.bagBPtr args.mask 0 hLB hLB_lt
    rw [hlenB] at hrun
    refine ⟨?_, forgetWeightProg_state args s, ?_, ?_⟩
    · unfold forgetWeightProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold forgetWeightProg
      rw [StateTransitionSpec.clientResult_bind]
      change ((Memory.spec 0).clientResult s
        (iterate forgetWeightStep env args.bagBLen ⟨args.bagBPtr, args.mask, 0⟩)).acc = _
      rw [hrun.2.1, Nat.zero_add]
    · unfold forgetWeightProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro ys
  induction ys with
  | nil =>
    intro curB curT acc _ _
    have h0 : iterate forgetWeightStep env 0 ⟨curB, curT, acc⟩ = pure ⟨curB, curT, acc⟩ := rfl
    simp only [List.length_nil, h0, forgetWeight, Nat.add_zero]
    exact ⟨validHistory_pure w s _, rfl, by simp [memoryCost_pure]⟩
  | cons u rest ih =>
    intro curB curT acc hcur hus
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨hb, hmem_u, hrest⟩ := hcur
    have hu_lt : u < inst.weights.length := by
      rw [inst.weights_len]; exact hus u List.mem_cons_self
    have hwt_lt : args.wtPtr + u < s.frontier := by have := hwt.1; omega
    have hwt_read : s.mem (args.wtPtr + u) = inst.wt u := by
      rw [hwt.get u hu_lt]
      unfold MWISInstance.wt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu_lt, Option.getD_some]
    have hcur_lt : curB < s.frontier := by omega
    obtain ⟨hv_bm, hst_bm, hr_bm, hc_bm⟩ :=
      bagMemProg_spec (w := w) ⟨u, args.bagPPtr, args.bagPLen⟩ hLP hlenP
    let addW := if curT % 2 = 1 ∧ memBag u LP = false then inst.wt u else 0
    obtain ⟨hv_rest, hr_rest, hc_rest⟩ :=
      ih (curB + 1) (curT / 2) (acc + addW) hrest (fun v hv => hus v (List.mem_cons_of_mem u hv))
    have hadd_eq :
        (if curT % 2 = 1 then
          if (if memBag u LP then 1 else 0) = 0 then inst.wt u else 0
        else 0) = addW := by
      dsimp only [addW]
      by_cases hbit : curT % 2 = 1 <;> cases memBag u LP <;> simp [hbit]
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (forgetWeightStep (env, ⟨curB, curT, acc⟩))) := by
      unfold forgetWeightStep
      dsimp only [env]
      refine validHistory_read_bind hcur_lt ?_
      rw [hmem_u]
      refine validHistory_read_bind hwt_lt ?_
      exact validHistory_bind_step hv_bm (validHistory_pure w _ _)
    have hst_step : (Memory.spec 0).clientState s
        (forgetWeightStep (env, ⟨curB, curT, acc⟩)) = s := by
      unfold forgetWeightStep
      dsimp only [env]
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_bind, bagMemProg_state]
      rfl
    have hres_step : (Memory.spec 0).clientResult s
        (forgetWeightStep (env, ⟨curB, curT, acc⟩)) =
        ⟨curB + 1, curT / 2, acc + addW⟩ := by
      have hr_st (a : ℕ) : (Memory.spec 0).clientState s (Memory.read a) = s := rfl
      have hr_res (a : ℕ) : (Memory.spec 0).clientResult s (Memory.read a) = s.mem a := rfl
      unfold forgetWeightStep
      dsimp only [env]
      rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res, hmem_u,
        StateTransitionSpec.clientResult_bind, hr_st, hr_res, hwt_read,
        StateTransitionSpec.clientResult_bind, hst_bm, hr_bm, hadd_eq]
      rfl
    have hc_step : memoryCost (forgetWeightStep (env, ⟨curB, curT, acc⟩)) s ≤
        args.bagPLen + 2 := by
      have hr_st (a : ℕ) : (Memory.spec 0).clientState s (Memory.read a) = s := rfl
      have hr_res (a : ℕ) : (Memory.spec 0).clientResult s (Memory.read a) = s.mem a := rfl
      dsimp only at hc_bm
      unfold forgetWeightStep
      dsimp only [env]
      rw [memoryCost_bind', memoryCost_read, hr_st, hr_res, hmem_u,
        memoryCost_bind', memoryCost_read, hr_st, hr_res,
        memoryCost_bind', hst_bm, memoryCost_pure, Nat.add_zero]
      omega
    simp only [List.length_cons]
    have hiter_eq : iterate forgetWeightStep env (rest.length + 1) ⟨curB, curT, acc⟩ =
        (forgetWeightStep (env, ⟨curB, curT, acc⟩) >>=
          iterate forgetWeightStep env rest.length) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step, hr_rest]
      dsimp only [addW, forgetWeight]
      omega
    · rw [memoryCost_bind', hst_step, hres_step]
      calc memoryCost (forgetWeightStep (env, ⟨curB, curT, acc⟩)) s +
            memoryCost (iterate forgetWeightStep env rest.length
              ⟨curB + 1, curT / 2, acc + addW⟩) s
          ≤ (args.bagPLen + 2) + rest.length * (args.bagPLen + 2) :=
            Nat.add_le_add hc_step hc_rest
        _ = (rest.length + 1) * (args.bagPLen + 2) := by ring

private theorem forgetWeightProg_realizes :
    Realizes .exact forgetWeightProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 2 ∧
        ∃ wtL LB,
          HoldsIn args.wtPtr wtL s ∧ HoldsIn args.bagBPtr LB s ∧ LB.length = args.bagBLen ∧
          (∀ u ∈ LB, u < wtL.length) ∧
          Fits w (args.wtPtr + wtL.length) ∧
          Fits w (args.bagPPtr + args.bagPLen) ∧ Fits w (args.bagBPtr + args.bagBLen) ∧
          Fits w (args.bagBLen * wtL.foldl max 0))
      (fun _ _ => 0) := by
  unfold forgetWeightProg
  realize [bagMemProg_realizes]
  obtain ⟨h2, wtL, LB, hwt_h, hLB_h, hLB_len, hLB_lt, hfitW, hfitP, hfitB, hfitSum⟩ := h
  have h1 : Fits w 1 := h2.of_le (by decide)
  have h2_ne : 2 ≠ 0 := by decide
  let W := wtL.foldl max 0
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : ForgetWeightState) (t : Memory.State) =>
      j ≤ d.bagBLen ∧ st.curB + j = d.bagBPtr + d.bagBLen ∧
      HoldsIn d.wtPtr wtL t ∧ HoldsIn st.curB (LB.drop (d.bagBLen - j)) t ∧
      st.acc ≤ (d.bagBLen - j) * W)
    (fun j st t ⟨hj_le, hcur, hwt_t, hrem, hacc_le⟩ => ?_)
    ⟨le_rfl, rfl, hwt_h, by simpa only [Nat.sub_self, List.drop_zero] using hLB_h, by simp⟩
  have hj_lt : d.bagBLen - (j + 1) < LB.length := by omega
  have hdrop_eq : LB.drop (d.bagBLen - (j + 1)) =
      LB[d.bagBLen - (j + 1)] :: LB.drop (d.bagBLen - j) := by
    have hsub : d.bagBLen - j = (d.bagBLen - (j + 1)) + 1 := by omega
    rw [hsub]
    exact List.drop_eq_getElem_cons hj_lt
  rw [hdrop_eq, HoldsIn.cons_iff] at hrem
  obtain ⟨_, hmem_u, hrem_next⟩ := hrem
  have hu_lt : t.mem st.curB < wtL.length := by
    rw [hmem_u]
    exact hLB_lt _ (List.getElem_mem hj_lt)
  have hwu_le : t.mem (d.wtPtr + t.mem st.curB) ≤ W := by
    rw [hwt_t.get _ hu_lt]
    exact List.mem_le_foldl_max (List.getElem_mem hu_lt)
  have hsub : d.bagBLen - j = (d.bagBLen - (j + 1)) + 1 := by omega
  have hacc_next_le : st.acc + t.mem (d.wtPtr + t.mem st.curB) ≤ (d.bagBLen - j) * W := by
    calc st.acc + t.mem (d.wtPtr + t.mem st.curB)
        ≤ (d.bagBLen - (j + 1)) * W + W := Nat.add_le_add hacc_le hwu_le
      _ = ((d.bagBLen - (j + 1)) + 1) * W := by ring
      _ = (d.bagBLen - j) * W := by rw [← hsub]
  have hacc_max : (d.bagBLen - j) * W ≤ d.bagBLen * W :=
    Nat.mul_le_mul_right W (Nat.sub_le _ _)
  have hcur_fit : Fits w (st.curB + 1) := hfitB.of_le (by omega)
  have hwt_fit : Fits w (d.wtPtr + t.mem st.curB) := hfitW.of_le (by omega)
  have hadd_fit : Fits w (st.acc + t.mem (d.wtPtr + t.mem st.curB)) :=
    hfitSum.of_le (hacc_next_le.trans hacc_max)
  have hacc_fit : Fits w (st.acc + 0) :=
    hfitSum.of_le ((by omega : st.acc + 0 ≤ (d.bagBLen - j) * W).trans hacc_max)
  have hst_body : (Memory.spec 0).clientState t
      (forgetWeightStep (⟨d.wtPtr, d.bagPPtr, d.bagPLen⟩, st)) = t := by
    unfold forgetWeightStep
    dsimp only
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, bagMemProg_state]
    rfl
  refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_, ?_⟩
  · repeat (first | split | assumption | refine And.intro ?_ ?_)
  · unfold forgetWeightStep
    dsimp only
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_bind, bagMemProg_state]
    change (st.curB + 1) + j = d.bagBPtr + d.bagBLen
    omega
  · rw [hst_body]; exact hwt_t
  · rw [hst_body]
    unfold forgetWeightStep
    dsimp only
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_bind, bagMemProg_state]
    exact hrem_next
  · unfold forgetWeightStep
    dsimp only
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_bind, bagMemProg_state]
    change st.acc + (if _ then _ else 0) ≤ (d.bagBLen - j) * W
    split_ifs <;> [exact hacc_next_le; omega; omega]

/-! ### Child, parent, and root DP passes (`childPassProg`, `parentPassProg`, `rootPassProg`) -/

private theorem keyMask_lt_two_pow (LB LP : List ℕ) (t : ℕ) : keyMask LB LP t < 2 ^ LP.length := by
  induction LP with
  | nil => simp [keyMask]
  | cons u rest ih =>
    simp only [keyMask, List.length_cons, Nat.pow_succ]
    by_cases hsm : selMemMask u LB t = true <;>
      simp only [hsm, Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem restrictMask_lt_two_pow (LB LP : List ℕ) (s : ℕ) :
    restrictMask LB LP s < 2 ^ LP.length := by
  induction LP generalizing s with
  | nil => simp [restrictMask]
  | cons u rest ih =>
    have hrec := ih (s / 2)
    simp only [restrictMask, List.length_cons, Nat.pow_succ]
    by_cases hbit : s % 2 = 1 <;> by_cases hin : u ∈ LB <;> simp [hbit, hin] <;> omega

private def childPassList (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (LB LP tblB init : List ℕ) :
    ℕ → List ℕ
  | 0 => init
  | c + 1 =>
    let best := childPassList adj wt LB LP tblB init c
    if indepInst adj LB c then
      let key := keyMask LB LP c
      best.set key (max (best.getD key 0) (forgetWeight wt LP LB c + tblB.getD c 0))
    else
      best

private theorem length_childPassList (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ)
    (LB LP tblB init : List ℕ) (c : ℕ) :
    (childPassList adj wt LB LP tblB init c).length = init.length := by
  induction c with
  | zero => rfl
  | succ c ih =>
    dsimp only [childPassList]
    split_ifs
    · rw [List.length_set, ih]
    · exact ih

private theorem size_childPassInst (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ)
    (LB LP : List ℕ) (f init : Array ℕ) (c : ℕ) :
    (childPassInst adj wt LB LP f init c).size = init.size := by
  induction c with
  | zero => rfl
  | succ c ih =>
    dsimp only [childPassInst]
    split_ifs
    · rw [Array.size_setIfInBounds, ih]
    · exact ih

private theorem getD_childPassList_eq (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ)
    (LB LP tblB : List ℕ) (f : Array ℕ) (c : ℕ)
    (htbl : ∀ t < c, tblB.getD t 0 = f.getD t 0) :
    ∀ k < 2 ^ LP.length,
      (childPassList adj wt LB LP tblB (List.replicate (2 ^ LP.length) 0) c).getD k 0 =
        (childPassInst adj wt LB LP f (Array.replicate (2 ^ LP.length) 0) c).getD k 0 := by
  induction c with
  | zero =>
    intro k hk
    simp only [childPassList, childPassInst, List.getD_eq_getElem?_getD,
      List.getElem?_replicate, Array.getD_eq_getD_getElem?, Array.getElem?_replicate,
      hk, ↓reduceIte, Option.getD_some]
  | succ c ih =>
    intro k hk
    have hih := ih (fun t ht => htbl t (Nat.lt_succ_of_lt ht))
    dsimp only [childPassList, childPassInst]
    by_cases hind : indepInst adj LB c = true
    · simp only [hind, ↓reduceIte]
      have hkey_lt : keyMask LB LP c < 2 ^ LP.length := keyMask_lt_two_pow LB LP c
      have hlenL : (childPassList adj wt LB LP tblB (List.replicate (2 ^ LP.length) 0) c).length =
          2 ^ LP.length := by
        rw [length_childPassList, List.length_replicate]
      have hszA : (childPassInst adj wt LB LP f (Array.replicate (2 ^ LP.length) 0) c).size =
          2 ^ LP.length := by
        rw [size_childPassInst, Array.size_replicate]
      rw [List.getD_eq_getElem?_getD, List.getElem?_set, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds]
      by_cases heq : keyMask LB LP c = k
      · subst heq
        simp only [↓reduceIte, hkey_lt.trans_eq hlenL.symm, hkey_lt.trans_eq hszA.symm,
          Option.getD_some, hih _ hkey_lt, htbl c (Nat.lt_succ_self c)]
      · simp only [heq, ↓reduceIte, ← List.getD_eq_getElem?_getD,
          ← Array.getD_eq_getD_getElem?, hih k hk]
    · simp only [hind, Bool.false_eq_true, ↓reduceIte, hih k hk]

private theorem mem_childPassList_le {adj : ℕ → ℕ → Bool} {wt : ℕ → ℕ}
    {LB LP tblB init : List ℕ} {cap c : ℕ}
    (hinit : ∀ x ∈ init, x ≤ cap)
    (hstep : ∀ t < c, forgetWeight wt LP LB t + tblB.getD t 0 ≤ cap) :
    ∀ x ∈ childPassList adj wt LB LP tblB init c, x ≤ cap := by
  induction c with
  | zero => exact hinit
  | succ c ih =>
    have hih := ih (fun t ht => hstep t (Nat.lt_succ_of_lt ht))
    dsimp only [childPassList]
    split_ifs with hind
    · intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hmem | rfl
      · exact hih x hmem
      · refine max_le ?_ (hstep c (Nat.lt_succ_self c))
        rw [List.getD_eq_getElem?_getD]
        cases hget :
            (childPassList adj wt LB LP tblB init c)[keyMask LB LP c]? with
        | none => exact Nat.zero_le _
        | some v => exact hih v (List.mem_of_getElem? hget)
    · exact hih

private def parentPassPrefix (LB LP oldL bestL : List ℕ) (k : ℕ) : List ℕ :=
  List.ofFn fun i : Fin oldL.length =>
    if i.val < k then oldL[i] + bestL.getD (restrictMask LB LP i.val) 0 else oldL[i]

private theorem length_parentPassPrefix (LB LP oldL bestL : List ℕ) (k : ℕ) :
    (parentPassPrefix LB LP oldL bestL k).length = oldL.length :=
  List.length_ofFn

private theorem parentPassPrefix_zero (LB LP oldL bestL : List ℕ) :
    parentPassPrefix LB LP oldL bestL 0 = oldL := by
  apply List.ext_getElem
  · exact List.length_ofFn
  · intro i hi1 hi2
    simp [parentPassPrefix]

private theorem parentPassPrefix_step (LB LP oldL bestL : List ℕ) {k : ℕ}
    (hk : k < oldL.length) :
    (parentPassPrefix LB LP oldL bestL k).set k
        (oldL[k] + bestL.getD (restrictMask LB LP k) 0) =
      parentPassPrefix LB LP oldL bestL (k + 1) := by
  apply List.ext_getElem
  · simp [parentPassPrefix]
  · intro i hi1 hi2
    rw [List.getElem_set]
    simp only [parentPassPrefix, List.getElem_ofFn]
    by_cases hik : k = i
    · subst hik
      simp
    · have hiff : (i < k) ↔ (i < k + 1) := by omega
      simp [hik, hiff]

private theorem getD_parentPass_raw (LB LP : List ℕ) (old best : Array ℕ) {c s : ℕ}
    (hs : s < c) :
    (parentPass LB LP old best c).getD s 0 =
      old.getD s 0 + best.getD (restrictMask LB LP s) 0 := by
  induction c with
  | zero => omega
  | succ c ih =>
    simp only [parentPass]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, size_parentPass]
    by_cases hsc : s = c
    · subst hsc
      simp
    · simp only [hsc, ↓reduceIte, ← Array.getD_eq_getD_getElem?, ih (by omega)]

private theorem mem_parentPassPrefix_le {LB LP oldL bestL : List ℕ} {capO capB k : ℕ}
    (hold : ∀ x ∈ oldL, x ≤ capO) (hbest : ∀ x ∈ bestL, x ≤ capB) :
    ∀ x ∈ parentPassPrefix LB LP oldL bestL k, x ≤ capO + capB := by
  intro x hx
  unfold parentPassPrefix at hx
  rw [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  have ho : oldL[i] ≤ capO := hold _ (List.getElem_mem i.isLt)
  split_ifs
  · refine Nat.add_le_add ho ?_
    rw [List.getD_eq_getElem?_getD]
    cases hget : bestL[restrictMask LB LP i.val]? with
    | none => exact Nat.zero_le _
    | some v => exact hbest v (List.mem_of_getElem? hget)
  · omega

private structure ChildPassArgs where
  numVerts : ℕ
  adjPtr : ℕ
  wtPtr : ℕ
  bagBPtr : ℕ
  bagBLen : ℕ
  tblBPtr : ℕ
  tblBLen : ℕ
  bagPPtr : ℕ
  bagPLen : ℕ
  bestPtr : ℕ

private def ChildPassArgs.equiv :
    ChildPassArgs ≃
      ((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    (((((((((a.numVerts, a.adjPtr), a.wtPtr), a.bagBPtr), a.bagBLen),
      a.tblBPtr), a.tblBLen), a.bagPPtr), a.bagPLen), a.bestPtr)
  invFun := fun (((((((((nv, ap), wp), bbp), bbl), tbp), tbl), bpp), bpl), bp) =>
    ⟨nv, ap, wp, bbp, bbl, tbp, tbl, bpp, bpl, bp⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ChildPassArgs := .ofEquiv ChildPassArgs.equiv

private theorem forgetWeightProg_result_le (args : ForgetWeightArgs) {wtL LB : List ℕ}
    {t : Memory.State} (hwt_t : HoldsIn args.wtPtr wtL t)
    (hLB_t : HoldsIn args.bagBPtr LB t) (hLB_len : LB.length = args.bagBLen)
    (hLB_lt_wt : ∀ u ∈ LB, u < wtL.length) :
    (Memory.spec 0).clientResult t (forgetWeightProg args) ≤ args.bagBLen * wtL.foldl max 0 := by
  unfold forgetWeightProg
  rw [StateTransitionSpec.clientResult_bind]
  change ((Memory.spec 0).clientResult t (iterate forgetWeightStep _ args.bagBLen _)).acc ≤ _
  suffices ∀ rem cb ct acc, rem ≤ args.bagBLen →
      HoldsIn cb (LB.drop (args.bagBLen - rem)) t →
      acc + (LB.drop (args.bagBLen - rem)).length * wtL.foldl max 0 ≤
        args.bagBLen * wtL.foldl max 0 →
      ((Memory.spec 0).clientResult t
        (iterate forgetWeightStep ⟨args.wtPtr, args.bagPPtr, args.bagPLen⟩ rem
          ⟨cb, ct, acc⟩)).acc ≤
        args.bagBLen * wtL.foldl max 0 by
    refine this args.bagBLen args.bagBPtr args.mask 0 le_rfl
      (by simpa only [Nat.sub_self, List.drop_zero] using hLB_t) ?_
    simp only [Nat.sub_self, List.drop_zero, hLB_len, Nat.zero_add, le_rfl]
  intro rem
  induction rem with
  | zero => intro cb ct acc _ _ hle; exact le_trans (Nat.le_add_right _ _) hle
  | succ rem ihr =>
    intro cb ct acc hr_le hrem_cb hle_cb
    let env : ForgetWeightEnv := ⟨args.wtPtr, args.bagPPtr, args.bagPLen⟩
    have hit : iterate forgetWeightStep env (rem + 1) ⟨cb, ct, acc⟩ =
        (forgetWeightStep (env, ⟨cb, ct, acc⟩) >>= iterate forgetWeightStep env rem) := rfl
    rw [hit, StateTransitionSpec.clientResult_bind]
    have hst_fw_step :
        (Memory.spec 0).clientState t (forgetWeightStep (env, ⟨cb, ct, acc⟩)) = t := by
      unfold forgetWeightStep
      dsimp only
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_bind, bagMemProg_state]
      rfl
    rw [hst_fw_step]
    have hrem_lt : args.bagBLen - (rem + 1) < LB.length := by omega
    have hsub_r : args.bagBLen - rem = (args.bagBLen - (rem + 1)) + 1 := by omega
    have hdrop_r : LB.drop (args.bagBLen - (rem + 1)) =
        LB[args.bagBLen - (rem + 1)] :: LB.drop (args.bagBLen - rem) := by
      rw [hsub_r]; exact List.drop_eq_getElem_cons hrem_lt
    rw [hdrop_r, HoldsIn.cons_iff] at hrem_cb
    obtain ⟨_, hmem_cb, hnext_cb⟩ := hrem_cb
    have hu_cb : t.mem cb < wtL.length := by
      rw [hmem_cb]; exact hLB_lt_wt _ (List.getElem_mem hrem_lt)
    have hwu_cb : t.mem (args.wtPtr + t.mem cb) ≤ wtL.foldl max 0 := by
      rw [hwt_t.get _ hu_cb]; exact List.mem_le_foldl_max (List.getElem_mem hu_cb)
    have hres_cb : (Memory.spec 0).clientResult t (forgetWeightStep (env, ⟨cb, ct, acc⟩)) =
        ⟨cb + 1, ct / 2,
          acc + (if ct % 2 = 1 then
            if (Memory.spec 0).clientResult t
                (bagMemProg ⟨t.mem cb, args.bagPPtr, args.bagPLen⟩) = 0 then
              t.mem (args.wtPtr + t.mem cb)
            else 0
          else 0)⟩ := by
      unfold forgetWeightStep
      dsimp only [env]
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientResult_bind, bagMemProg_state]
      rfl
    rw [hres_cb]
    refine ihr (cb + 1) (ct / 2) _ (Nat.le_of_succ_le hr_le) hnext_cb ?_
    rw [hdrop_r, List.length_cons] at hle_cb
    have hadd_le : (if ct % 2 = 1 then
        if (Memory.spec 0).clientResult t
            (bagMemProg ⟨t.mem cb, args.bagPPtr, args.bagPLen⟩) = 0 then
          t.mem (args.wtPtr + t.mem cb)
        else 0
      else 0) ≤ wtL.foldl max 0 := by
      split_ifs <;> [exact hwu_cb; omega; omega]
    nlinarith

private def childPassStep (p : ChildPassArgs × ℕ) : Memory.Prog ℕ := do
  let a := p.1
  let curC := p.2
  let fc ← Memory.read (a.tblBPtr + curC)
  let ind ← indepBagProg ⟨a.numVerts, a.adjPtr, a.bagBPtr, a.bagBLen, curC⟩
  let key ← keyMaskProg ⟨a.bagBPtr, a.bagBLen, a.bagPPtr, a.bagPLen, curC⟩
  let fw ← forgetWeightProg ⟨a.wtPtr, a.bagPPtr, a.bagPLen, a.bagBPtr, a.bagBLen, curC⟩
  let oldBest ← Memory.read (a.bestPtr + key)
  let cand := fw + fc
  let upd := if oldBest < cand then cand else oldBest
  let nextVal := if ind = 1 then upd else oldBest
  Memory.write (a.bestPtr + key) nextVal
  pure (curC + 1)

private def childPassProg (args : ChildPassArgs) : Memory.Prog Unit := do
  let _ ← iterate childPassStep args args.tblBLen 0
  pure ()

private theorem childPassStep_eval (a : ChildPassArgs) (curC : ℕ) (t : Memory.State) :
    let fc := t.mem (a.tblBPtr + curC)
    let ind := (Memory.spec 0).clientResult t
      (indepBagProg ⟨a.numVerts, a.adjPtr, a.bagBPtr, a.bagBLen, curC⟩)
    let key := (Memory.spec 0).clientResult t
      (keyMaskProg ⟨a.bagBPtr, a.bagBLen, a.bagPPtr, a.bagPLen, curC⟩)
    let fw := (Memory.spec 0).clientResult t
      (forgetWeightProg ⟨a.wtPtr, a.bagPPtr, a.bagPLen, a.bagBPtr, a.bagBLen, curC⟩)
    let oldBest := t.mem (a.bestPtr + key)
    let cand := fw + fc
    let nextVal := if ind = 1 then (if oldBest < cand then cand else oldBest) else oldBest
    (Memory.spec 0).clientState t (childPassStep (a, curC)) =
      ⟨Function.update t.mem (a.bestPtr + key) nextVal, t.frontier⟩ ∧
    (Memory.spec 0).clientResult t (childPassStep (a, curC)) = curC + 1 := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold childPassStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    indepBagProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    keyMaskProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    forgetWeightProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    hr_st, hr_res]
  exact ⟨rfl, rfl⟩

private theorem childPassProg_spec {w : ℕ} (args : ChildPassArgs) {inst : MWISInstance}
    {LB LP tblB initL : List ℕ} {cap : ℕ} {s : Memory.State}
    (hadj : HoldsIn args.adjPtr inst.adjMatrix s)
    (hadj_end : args.adjPtr + inst.adjMatrix.length ≤ args.bestPtr)
    (hwt : HoldsIn args.wtPtr inst.weights s)
    (hwt_end : args.wtPtr + inst.weights.length ≤ args.bestPtr)
    (hnv : args.numVerts = inst.numVerts)
    (hLB : HoldsIn args.bagBPtr LB s) (hlenB : LB.length = args.bagBLen)
    (hLB_end : args.bagBPtr + args.bagBLen ≤ args.bestPtr)
    (hLB_lt : ∀ u ∈ LB, u < inst.numVerts)
    (htblB : HoldsIn args.tblBPtr tblB s) (htblB_len : tblB.length = args.tblBLen)
    (htblB_end : args.tblBPtr + args.tblBLen ≤ args.bestPtr)
    (hLP : HoldsIn args.bagPPtr LP s) (hlenP : LP.length = args.bagPLen)
    (hLP_end : args.bagPPtr + args.bagPLen ≤ args.bestPtr)
    (hinit : HoldsIn args.bestPtr initL s) (hinit_len : initL.length = 2 ^ LP.length)
    (hinit_le : ∀ x ∈ initL, x ≤ cap)
    (hcand_le : ∀ t < args.tblBLen, forgetWeight inst.wt LP LB t + tblB.getD t 0 ≤ cap)
    (hfit_cap : Fits w cap) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (childPassProg args)) ∧
    ((Memory.spec 0).clientState s (childPassProg args)).frontier = s.frontier ∧
    PreservesBelow args.bestPtr s ((Memory.spec 0).clientState s (childPassProg args)) ∧
    HoldsIn args.bestPtr (childPassList inst.adj inst.wt LB LP tblB initL args.tblBLen)
      ((Memory.spec 0).clientState s (childPassProg args)) ∧
    memoryCost (childPassProg args) s ≤
      args.tblBLen *
        (args.bagBLen * (2 * args.bagBLen + 1) +
          args.bagPLen * (args.bagBLen + 1) +
          args.bagBLen * (args.bagPLen + 2) + 3) := by
  let stepCost :=
    args.bagBLen * (2 * args.bagBLen + 1) +
      args.bagPLen * (args.bagBLen + 1) +
      args.bagBLen * (args.bagPLen + 2) + 3
  suffices ∀ rem curC st,
      curC + rem = args.tblBLen →
      st.frontier = s.frontier →
      PreservesBelow args.bestPtr s st →
      HoldsIn args.bestPtr (childPassList inst.adj inst.wt LB LP tblB initL curC) st →
      (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (iterate childPassStep args rem curC)) ∧
      ((Memory.spec 0).clientState st (iterate childPassStep args rem curC)).frontier =
        s.frontier ∧
      PreservesBelow args.bestPtr s
        ((Memory.spec 0).clientState st (iterate childPassStep args rem curC)) ∧
      HoldsIn args.bestPtr (childPassList inst.adj inst.wt LB LP tblB initL (curC + rem))
        ((Memory.spec 0).clientState st (iterate childPassStep args rem curC)) ∧
      memoryCost (iterate childPassStep args rem curC) st ≤ rem * stepCost by
    have hbest_le : args.bestPtr ≤ s.frontier := by have := hinit.1; omega
    have hrun := this args.tblBLen 0 s (Nat.zero_add _) rfl (PreservesBelow.refl hbest_le) hinit
    rw [Nat.zero_add] at hrun
    unfold childPassProg
    refine ⟨validHistory_bind_step hrun.1 (validHistory_pure w _ ()), ?_, ?_, ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind]; exact hrun.2.1
    · rw [StateTransitionSpec.clientState_bind]; exact hrun.2.2.1
    · rw [StateTransitionSpec.clientState_bind]; exact hrun.2.2.2.1
    · rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]; exact hrun.2.2.2.2
  intro rem
  induction rem with
  | zero =>
    intro curC st _ hfr hpres hbest_st
    have h0 : iterate childPassStep args 0 curC = pure curC := rfl
    rw [h0, Nat.add_zero]
    exact ⟨validHistory_pure w st curC, hfr, hpres, hbest_st, by simp [memoryCost_pure]⟩
  | succ rem ih =>
    intro curC st hsum hfr hpres hbest_st
    have hcur_lt : curC < args.tblBLen := by omega
    have hadj_st : HoldsIn args.adjPtr inst.adjMatrix st := hadj.mono hadj_end hpres
    have hwt_st : HoldsIn args.wtPtr inst.weights st := hwt.mono hwt_end hpres
    have hLB_st : HoldsIn args.bagBPtr LB st := hLB.mono (by omega) hpres
    have htblB_st : HoldsIn args.tblBPtr tblB st := htblB.mono (by omega) hpres
    have hLP_st : HoldsIn args.bagPPtr LP st := hLP.mono (by omega) hpres
    obtain ⟨hv_ind, hst_ind, hr_ind, hc_ind⟩ :=
      indepBagProg_spec (w := w) ⟨args.numVerts, args.adjPtr, args.bagBPtr, args.bagBLen, curC⟩
        hadj_st hnv hLB_st hlenB hLB_lt
    obtain ⟨hv_key, hst_key, hr_key, hc_key⟩ :=
      keyMaskProg_spec (w := w) ⟨args.bagBPtr, args.bagBLen, args.bagPPtr, args.bagPLen, curC⟩
        hLB_st hlenB hLP_st hlenP
    obtain ⟨hv_fw, hst_fw, hr_fw, hc_fw⟩ :=
      forgetWeightProg_spec (w := w)
        ⟨args.wtPtr, args.bagPPtr, args.bagPLen, args.bagBPtr, args.bagBLen, curC⟩
        hwt_st hLP_st hlenP hLB_st hlenB hLB_lt
    dsimp only at hr_ind hc_ind hr_key hc_key hr_fw hc_fw
    let bestCur := childPassList inst.adj inst.wt LB LP tblB initL curC
    have hbest_len : bestCur.length = 2 ^ LP.length := by
      rw [length_childPassList, hinit_len]
    let key := keyMask LB LP curC
    have hkey_lt : key < bestCur.length := by
      rw [hbest_len]; exact keyMask_lt_two_pow LB LP curC
    have hcur_tbl_lt : curC < tblB.length := by omega
    have hfc_addr_lt : args.tblBPtr + curC < st.frontier := by have := htblB_st.1; omega
    have hbest_addr_lt : args.bestPtr + key < st.frontier := by
      have h1 := hbest_st.1
      change args.bestPtr + bestCur.length ≤ st.frontier at h1
      omega
    have hfc_eq : st.mem (args.tblBPtr + curC) = tblB.getD curC 0 := by
      rw [htblB_st.get curC hcur_tbl_lt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hcur_tbl_lt, Option.getD_some]
    have holdBest_eq : st.mem (args.bestPtr + key) = bestCur.getD key 0 := by
      rw [hbest_st.get key hkey_lt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hkey_lt, Option.getD_some]
    let fw := forgetWeight inst.wt LP LB curC
    let fc := st.mem (args.tblBPtr + curC)
    let oldBest := st.mem (args.bestPtr + key)
    let cand := fw + fc
    let nextVal :=
      if (if indepInst inst.adj LB curC then 1 else 0) = 1 then
        if oldBest < cand then cand else oldBest
      else oldBest
    have holdBest_le : oldBest ≤ cap := by
      have hmem := mem_childPassList_le (adj := inst.adj) hinit_le
        (fun t ht => hcand_le t (lt_trans ht hcur_lt))
      dsimp only [oldBest]
      rw [hbest_st.get key hkey_lt]
      exact hmem _ (List.getElem_mem hkey_lt)
    have hcand_val_le : cand ≤ cap := by
      dsimp only [cand, fw, fc]
      rw [hfc_eq]
      exact hcand_le curC hcur_lt
    have hnext_le : nextVal ≤ cap := by
      dsimp only [nextVal]
      split_ifs <;> omega
    have hnext_fit : Fits w nextVal := hfit_cap.of_le hnext_le
    let st₁ : Memory.State := ⟨Function.update st.mem (args.bestPtr + key) nextVal, st.frontier⟩
    obtain ⟨hst_step, hres_step⟩ := childPassStep_eval args curC st
    rw [hr_ind, hr_key, hr_fw] at hst_step
    have hv_step : (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (childPassStep (args, curC))) := by
      unfold childPassStep
      dsimp only
      refine validHistory_read_bind hfc_addr_lt ?_
      refine validHistory_bind_step hv_ind ?_
      rw [hst_ind, hr_ind]
      refine validHistory_bind_step hv_key ?_
      rw [hst_key, hr_key]
      refine validHistory_bind_step hv_fw ?_
      rw [hst_fw, hr_fw]
      refine validHistory_read_bind hbest_addr_lt ?_
      exact validHistory_write_bind hbest_addr_lt hnext_fit (validHistory_pure w st₁ _)
    have hp₁ : PreservesBelow args.bestPtr st st₁ :=
      preservesBelow_write (Nat.le_add_right _ _) hbest_addr_lt
    have hbest_next : HoldsIn args.bestPtr
        (childPassList inst.adj inst.wt LB LP tblB initL (curC + 1)) st₁ := by
      have hset : HoldsIn args.bestPtr (bestCur.set key nextVal) st₁ :=
        holdsIn_set hbest_st
      have hlist_eq : bestCur.set key nextVal =
          childPassList inst.adj inst.wt LB LP tblB initL (curC + 1) := by
        have hval : nextVal =
            if (if indepInst inst.adj LB curC then 1 else 0) = 1 then
              if bestCur.getD key 0 < forgetWeight inst.wt LP LB curC + tblB.getD curC 0 then
                forgetWeight inst.wt LP LB curC + tblB.getD curC 0
              else bestCur.getD key 0
            else bestCur.getD key 0 := by
          dsimp only [nextVal, cand, fw, fc, oldBest]
          simp only [hfc_eq, holdBest_eq]
        rw [hval]
        dsimp only [bestCur, key, childPassList]
        by_cases hind : indepInst inst.adj LB curC = true
        · simp only [hind, ↓reduceIte]
          congr 1
          split_ifs <;> omega
        · simp only [Bool.eq_false_iff.2 hind, Bool.false_eq_true, ↓reduceIte]
          have hget_eq :
              (childPassList inst.adj inst.wt LB LP tblB initL curC).getD
                (keyMask LB LP curC) 0 =
              (childPassList inst.adj inst.wt LB LP tblB initL curC)[keyMask LB LP curC] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkey_lt, Option.getD_some]
          rw [hget_eq]
          exact List.set_getElem_self hkey_lt
      rwa [hlist_eq] at hset
    have hc_step : memoryCost (childPassStep (args, curC)) st ≤ stepCost := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState st (Memory.read x) = st := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult st (Memory.read x) = st.mem x := rfl
      unfold childPassStep
      dsimp only
      rw [memoryCost_bind', memoryCost_read, hr_s, hr_r,
        memoryCost_bind', hst_ind, hr_ind,
        memoryCost_bind', hst_key, hr_key,
        memoryCost_bind', hst_fw, hr_fw,
        memoryCost_bind', memoryCost_read, hr_s, hr_r,
        memoryCost_bind', memoryCost_write, memoryCost_pure]
      dsimp only [stepCost]
      omega
    obtain ⟨hv_rem, hfr_rem, hp_rem, hbest_rem, hc_rem⟩ :=
      ih (curC + 1) st₁ (by omega) hfr (hpres.trans hp₁) hbest_next
    have hiter_eq : iterate childPassStep args (rem + 1) curC =
        (childPassStep (args, curC) >>= iterate childPassStep args rem) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_, ?_, ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind, hst_step, hres_step]; exact hfr_rem
    · rw [StateTransitionSpec.clientState_bind, hst_step, hres_step]; exact hp_rem
    · rw [StateTransitionSpec.clientState_bind, hst_step, hres_step]
      have hadd : curC + (rem + 1) = curC + 1 + rem := by omega
      rwa [hadd]
    · rw [memoryCost_bind', hst_step, hres_step]
      calc memoryCost (childPassStep (args, curC)) st +
            memoryCost (iterate childPassStep args rem (curC + 1)) st₁
          ≤ stepCost + rem * stepCost := Nat.add_le_add hc_step hc_rem
        _ = (rem + 1) * stepCost := by ring

private theorem childPassProg_realizes :
    Realizes .exact childPassProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 2 ∧
        ∃ m adjL wtL LB LP tblB initL cap,
          adjL.length = m * m ∧ wtL.length = m ∧ args.numVerts = m ∧
          HoldsIn args.adjPtr adjL s ∧ args.adjPtr + adjL.length ≤ args.bestPtr ∧
          HoldsIn args.wtPtr wtL s ∧ args.wtPtr + wtL.length ≤ args.bestPtr ∧
          HoldsIn args.bagBPtr LB s ∧ LB.length = args.bagBLen ∧
          args.bagBPtr + args.bagBLen ≤ args.bestPtr ∧ (∀ u ∈ LB, u < m) ∧
          HoldsIn args.tblBPtr tblB s ∧ tblB.length = args.tblBLen ∧
          args.tblBPtr + args.tblBLen ≤ args.bestPtr ∧
          HoldsIn args.bagPPtr LP s ∧ LP.length = args.bagPLen ∧
          args.bagPPtr + args.bagPLen ≤ args.bestPtr ∧
          HoldsIn args.bestPtr initL s ∧ initL.length = 2 ^ args.bagPLen ∧
          args.bagBLen * wtL.foldl max 0 + tblB.foldl max 0 ≤ cap ∧
          Fits w (args.adjPtr + m * m) ∧ Fits w (args.wtPtr + m) ∧
          Fits w (args.bagBPtr + args.bagBLen) ∧ Fits w (args.tblBPtr + args.tblBLen) ∧
          Fits w (args.bagPPtr + args.bagPLen) ∧ Fits w (2 ^ args.bagPLen) ∧
          Fits w (args.bestPtr + 2 ^ args.bagPLen) ∧ Fits w cap)
      (fun _ _ => 0) := by
  unfold childPassProg
  realize [indepBagProg_realizes, keyMaskProg_realizes, forgetWeightProg_realizes]
  obtain ⟨h2, m, adjL, wtL, LB, LP, tblB, initL, cap,
    hadjL_len, hwtL_len, hnv, hadj_h, hadj_end, hwt_h, hwt_end,
    hLB_h, hLB_len, hLB_end, hLB_lt, htblB_h, htblB_len, htblB_end,
    hLP_h, hLP_len, hLP_end, hinit_h, hinit_len, hcap_bound,
    hfit_adj, hfit_wt, hfit_bagB, hfit_tblB, hfit_bagP, hfit_powP, hfit_best, hfit_cap⟩ := h
  have h1 : Fits w 1 := h2.of_le (by decide)
  have hbest_le_fr : d.bestPtr ≤ s.frontier := by have := hinit_h.1; omega
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (curC : ℕ) (t : Memory.State) =>
      j ≤ d.tblBLen ∧ curC + j = d.tblBLen ∧
      t.frontier = s.frontier ∧
      PreservesBelow d.bestPtr s t ∧
      ∃ bestL, bestL.length = 2 ^ d.bagPLen ∧ HoldsIn d.bestPtr bestL t)
    (fun j curC t ⟨hj_le, hcur, hfr, hpres, bestL, hbest_len, hbest_t⟩ => ?_)
    ⟨le_rfl, Nat.zero_add _, rfl, PreservesBelow.refl hbest_le_fr, initL, hinit_len, hinit_h⟩
  have hadj_t : HoldsIn d.adjPtr adjL t := hadj_h.mono hadj_end hpres
  have hwt_t : HoldsIn d.wtPtr wtL t := hwt_h.mono hwt_end hpres
  have hLB_t : HoldsIn d.bagBPtr LB t := hLB_h.mono (by omega) hpres
  have htblB_t : HoldsIn d.tblBPtr tblB t := htblB_h.mono (by omega) hpres
  have hLP_t : HoldsIn d.bagPPtr LP t := hLP_h.mono (by omega) hpres
  have hLB_lt_wt : ∀ u ∈ LB, u < wtL.length := by rw [hwtL_len]; exact hLB_lt
  have hfit_wtL : Fits w (d.wtPtr + wtL.length) := by rwa [hwtL_len]
  have hfit_sumW : Fits w (d.bagBLen * wtL.foldl max 0) := hfit_cap.of_le (by omega)
  have hind_safe : Fits w 2 ∧ ∃ m' adjL' xs',
      adjL'.length = m' * m' ∧ d.numVerts = m' ∧
      HoldsIn d.adjPtr adjL' t ∧ HoldsIn d.bagBPtr xs' t ∧ xs'.length = d.bagBLen ∧
      (∀ u ∈ xs', u < m') ∧ Fits w (d.adjPtr + m' * m') ∧ Fits w (d.bagBPtr + d.bagBLen) :=
    ⟨h2, m, adjL, LB, hadjL_len, hnv, hadj_t, hLB_t, hLB_len, hLB_lt, hfit_adj, hfit_bagB⟩
  have hkey_safe : Fits w 2 ∧ Fits w (d.bagBPtr + d.bagBLen) ∧
      Fits w (d.bagPPtr + d.bagPLen) ∧ Fits w (2 ^ d.bagPLen) :=
    ⟨h2, hfit_bagB, hfit_bagP, hfit_powP⟩
  have hfw_safe : Fits w 2 ∧ ∃ wtL' LB',
      HoldsIn d.wtPtr wtL' t ∧ HoldsIn d.bagBPtr LB' t ∧ LB'.length = d.bagBLen ∧
      (∀ u ∈ LB', u < wtL'.length) ∧ Fits w (d.wtPtr + wtL'.length) ∧
      Fits w (d.bagPPtr + d.bagPLen) ∧ Fits w (d.bagBPtr + d.bagBLen) ∧
      Fits w (d.bagBLen * wtL'.foldl max 0) :=
    ⟨h2, wtL, LB, hwt_t, hLB_t, hLB_len, hLB_lt_wt, hfit_wtL, hfit_bagP, hfit_bagB, hfit_sumW⟩
  obtain ⟨_, _, hr_key, _⟩ :=
    keyMaskProg_spec (w := w) ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curC⟩
      hLB_t hLB_len hLP_t hLP_len
  dsimp only at hr_key
  have hkey_lt_pow : (Memory.spec 0).clientResult t
      (keyMaskProg ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curC⟩) < 2 ^ d.bagPLen := by
    rw [hr_key, ← hLP_len]
    exact keyMask_lt_two_pow LB LP curC
  have hfw_le : (Memory.spec 0).clientResult t
      (forgetWeightProg ⟨d.wtPtr, d.bagPPtr, d.bagPLen, d.bagBPtr, d.bagBLen, curC⟩) ≤
      d.bagBLen * wtL.foldl max 0 :=
    forgetWeightProg_result_le _ hwt_t hLB_t hLB_len hLB_lt_wt
  have hcur_tbl : curC < tblB.length := by omega
  have hfc_le : t.mem (d.tblBPtr + curC) ≤ tblB.foldl max 0 := by
    rw [htblB_t.get curC hcur_tbl]
    exact List.mem_le_foldl_max (List.getElem_mem hcur_tbl)
  have hfit_tbl_addr : Fits w (d.tblBPtr + curC) := hfit_tblB.of_le (by omega)
  have hfit_best_addr : Fits w (d.bestPtr +
      (Memory.spec 0).clientResult t
        (keyMaskProg ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curC⟩)) :=
    hfit_best.of_le (by omega)
  have hfit_cand : Fits w ((Memory.spec 0).clientResult t
      (forgetWeightProg ⟨d.wtPtr, d.bagPPtr, d.bagPLen, d.bagBPtr, d.bagBLen, curC⟩) +
      t.mem (d.tblBPtr + curC)) :=
    hfit_cap.of_le (by omega)
  have hfit_cur1 : Fits w (curC + 1) := hfit_tblB.of_le (by omega)
  obtain ⟨hst_ev, hres_ev⟩ := childPassStep_eval d curC t
  refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_, ?_⟩
  · dsimp only [childPassStep]
    rw [indepBagProg_state, keyMaskProg_state, forgetWeightProg_state]
    repeat (
      first
      | split
      | exact hind_safe
      | exact hkey_safe
      | exact hfw_safe
      | exact trivial
      | assumption
      | refine And.intro ?_ ?_)
  · rw [hres_ev]; omega
  · rw [hst_ev]; exact hfr
  · rw [hst_ev]
    refine hpres.trans (preservesBelow_write (Nat.le_add_right _ _) ?_)
    have := hbest_t.1; omega
  · rw [hst_ev]
    exact ⟨bestL.set _ _, by rw [List.length_set, hbest_len], holdsIn_set hbest_t⟩

private structure ParentPassArgs where
  bagBPtr : ℕ
  bagBLen : ℕ
  bagPPtr : ℕ
  bagPLen : ℕ
  tblPPtr : ℕ
  tblPLen : ℕ
  bestPtr : ℕ

private def ParentPassArgs.equiv :
    ParentPassArgs ≃ (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    ((((((a.bagBPtr, a.bagBLen), a.bagPPtr), a.bagPLen), a.tblPPtr), a.tblPLen), a.bestPtr)
  invFun := fun ((((((bbp, bbl), bpp), bpl), tpp), tpl), bp) => ⟨bbp, bbl, bpp, bpl, tpp, tpl, bp⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ParentPassArgs := .ofEquiv ParentPassArgs.equiv

private def parentPassStep (p : ParentPassArgs × ℕ) : Memory.Prog ℕ := do
  let a := p.1
  let curS := p.2
  let oldVal ← Memory.read (a.tblPPtr + curS)
  let rKey ← restrictMaskProg ⟨a.bagBPtr, a.bagBLen, a.bagPPtr, a.bagPLen, curS⟩
  let bestVal ← Memory.read (a.bestPtr + rKey)
  Memory.write (a.tblPPtr + curS) (oldVal + bestVal)
  pure (curS + 1)

private def parentPassProg (args : ParentPassArgs) : Memory.Prog Unit := do
  let _ ← iterate parentPassStep args args.tblPLen 0
  pure ()

private theorem parentPassStep_eval (a : ParentPassArgs) (curS : ℕ) (t : Memory.State) :
    let oldVal := t.mem (a.tblPPtr + curS)
    let rKey := (Memory.spec 0).clientResult t
      (restrictMaskProg ⟨a.bagBPtr, a.bagBLen, a.bagPPtr, a.bagPLen, curS⟩)
    let bestVal := t.mem (a.bestPtr + rKey)
    (Memory.spec 0).clientState t (parentPassStep (a, curS)) =
      ⟨Function.update t.mem (a.tblPPtr + curS) (oldVal + bestVal), t.frontier⟩ ∧
    (Memory.spec 0).clientResult t (parentPassStep (a, curS)) = curS + 1 := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold parentPassStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    restrictMaskProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res]
  exact ⟨rfl, rfl⟩

private theorem parentPassProg_spec {w : ℕ} (args : ParentPassArgs)
    {LB LP oldL bestL : List ℕ} {capO capB : ℕ} {s : Memory.State}
    (hLB : HoldsIn args.bagBPtr LB s) (hlenB : LB.length = args.bagBLen)
    (hLB_disj : args.bagBPtr + args.bagBLen ≤ args.tblPPtr)
    (hLP : HoldsIn args.bagPPtr LP s) (hlenP : LP.length = args.bagPLen)
    (hLP_disj : args.bagPPtr + args.bagPLen ≤ args.tblPPtr)
    (hold : HoldsIn args.tblPPtr oldL s) (hold_len : oldL.length = args.tblPLen)
    (htblP_pow : args.tblPLen = 2 ^ LP.length)
    (hbest_disj : args.tblPPtr + args.tblPLen ≤ args.bestPtr)
    (hbest : HoldsIn args.bestPtr bestL s) (hbest_len : bestL.length = 2 ^ LP.length)
    (hold_le : ∀ x ∈ oldL, x ≤ capO) (hbest_le : ∀ x ∈ bestL, x ≤ capB)
    (hfit_sum : Fits w (capO + capB)) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (parentPassProg args)) ∧
    ((Memory.spec 0).clientState s (parentPassProg args)).frontier = s.frontier ∧
    (∀ addr, (addr < args.tblPPtr ∨ args.tblPPtr + args.tblPLen ≤ addr) →
      ((Memory.spec 0).clientState s (parentPassProg args)).mem addr = s.mem addr) ∧
    HoldsIn args.tblPPtr (parentPassPrefix LB LP oldL bestL args.tblPLen)
      ((Memory.spec 0).clientState s (parentPassProg args)) ∧
    memoryCost (parentPassProg args) s ≤
      args.tblPLen * (args.bagPLen * (args.bagBLen + 1) + 3) := by
  let stepCost := args.bagPLen * (args.bagBLen + 1) + 3
  suffices ∀ rem curS st,
      curS + rem = args.tblPLen →
      st.frontier = s.frontier →
      (∀ addr, (addr < args.tblPPtr ∨ args.tblPPtr + args.tblPLen ≤ addr) →
        st.mem addr = s.mem addr) →
      HoldsIn args.tblPPtr (parentPassPrefix LB LP oldL bestL curS) st →
      (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (iterate parentPassStep args rem curS)) ∧
      ((Memory.spec 0).clientState st (iterate parentPassStep args rem curS)).frontier =
        s.frontier ∧
      (∀ addr, (addr < args.tblPPtr ∨ args.tblPPtr + args.tblPLen ≤ addr) →
        ((Memory.spec 0).clientState st (iterate parentPassStep args rem curS)).mem addr =
          s.mem addr) ∧
      HoldsIn args.tblPPtr (parentPassPrefix LB LP oldL bestL (curS + rem))
        ((Memory.spec 0).clientState st (iterate parentPassStep args rem curS)) ∧
      memoryCost (iterate parentPassStep args rem curS) st ≤ rem * stepCost by
    have h0_eq : parentPassPrefix LB LP oldL bestL 0 = oldL :=
      parentPassPrefix_zero LB LP oldL bestL
    have hrun := this args.tblPLen 0 s (Nat.zero_add _) rfl (fun _ _ => rfl)
      (by rwa [h0_eq])
    rw [Nat.zero_add] at hrun
    unfold parentPassProg
    refine ⟨validHistory_bind_step hrun.1 (validHistory_pure w _ ()), ?_, ?_, ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind]; exact hrun.2.1
    · rw [StateTransitionSpec.clientState_bind]; exact hrun.2.2.1
    · rw [StateTransitionSpec.clientState_bind]; exact hrun.2.2.2.1
    · rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]; exact hrun.2.2.2.2
  intro rem
  induction rem with
  | zero =>
    intro curS st _ hfr hout hcur_st
    have h0 : iterate parentPassStep args 0 curS = pure curS := rfl
    rw [h0, Nat.add_zero]
    exact ⟨validHistory_pure w st curS, hfr, hout, hcur_st, by simp [memoryCost_pure]⟩
  | succ rem ih =>
    intro curS st hsum hfr hout hcur_st
    have hcur_lt : curS < oldL.length := by omega
    have hLB_st : HoldsIn args.bagBPtr LB st :=
      ⟨by rw [hfr]; exact hLB.1,
        hLB.2.frame fun a _ ha => hout a (.inl (by omega))⟩
    have hLP_st : HoldsIn args.bagPPtr LP st :=
      ⟨by rw [hfr]; exact hLP.1,
        hLP.2.frame fun a _ ha => hout a (.inl (by omega))⟩
    have hbest_st : HoldsIn args.bestPtr bestL st :=
      ⟨by rw [hfr]; exact hbest.1,
        hbest.2.frame fun a ha _ => hout a (.inr (by omega))⟩
    obtain ⟨hv_rk, hst_rk, hr_rk, hc_rk⟩ :=
      restrictMaskProg_spec (w := w)
        ⟨args.bagBPtr, args.bagBLen, args.bagPPtr, args.bagPLen, curS⟩
        hLB_st hlenB hLP_st hlenP
    dsimp only at hr_rk hc_rk
    let rKey := restrictMask LB LP curS
    have hrk_lt : rKey < bestL.length := by
      rw [hbest_len]; exact restrictMask_lt_two_pow LB LP curS
    have hcur_pfx_lt : curS < (parentPassPrefix LB LP oldL bestL curS).length := by
      rw [length_parentPassPrefix]; exact hcur_lt
    have hold_addr_lt : args.tblPPtr + curS < st.frontier := by have := hcur_st.1; omega
    have hbest_addr_lt : args.bestPtr + rKey < st.frontier := by have := hbest_st.1; omega
    have holdVal_eq : st.mem (args.tblPPtr + curS) = oldL[curS] := by
      rw [hcur_st.get curS hcur_pfx_lt]
      simp [parentPassPrefix]
    have hbestVal_eq : st.mem (args.bestPtr + rKey) = bestL.getD rKey 0 := by
      rw [hbest_st.get rKey hrk_lt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hrk_lt, Option.getD_some]
    have hnew_le : st.mem (args.tblPPtr + curS) + st.mem (args.bestPtr + rKey) ≤ capO + capB := by
      rw [holdVal_eq, hbest_st.get rKey hrk_lt]
      exact Nat.add_le_add (hold_le _ (List.getElem_mem hcur_lt))
        (hbest_le _ (List.getElem_mem hrk_lt))
    have hnew_fit : Fits w (st.mem (args.tblPPtr + curS) + st.mem (args.bestPtr + rKey)) :=
      hfit_sum.of_le hnew_le
    let newVal := st.mem (args.tblPPtr + curS) + st.mem (args.bestPtr + rKey)
    let st₁ : Memory.State := ⟨Function.update st.mem (args.tblPPtr + curS) newVal, st.frontier⟩
    obtain ⟨hst_step, hres_step⟩ := parentPassStep_eval args curS st
    rw [hr_rk] at hst_step
    have hv_step : (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (parentPassStep (args, curS))) := by
      unfold parentPassStep
      dsimp only
      refine validHistory_read_bind hold_addr_lt ?_
      refine validHistory_bind_step hv_rk ?_
      rw [hst_rk, hr_rk]
      refine validHistory_read_bind hbest_addr_lt ?_
      exact validHistory_write_bind hold_addr_lt hnew_fit (validHistory_pure w st₁ _)
    have hout₁ : ∀ addr, (addr < args.tblPPtr ∨ args.tblPPtr + args.tblPLen ≤ addr) →
        st₁.mem addr = s.mem addr := fun addr haddr => by
      have hne : addr ≠ args.tblPPtr + curS := by omega
      change Function.update st.mem (args.tblPPtr + curS) newVal addr = s.mem addr
      rw [Function.update_of_ne hne]
      exact hout addr haddr
    have hpfx_next : HoldsIn args.tblPPtr (parentPassPrefix LB LP oldL bestL (curS + 1)) st₁ := by
      have hset : HoldsIn args.tblPPtr
          ((parentPassPrefix LB LP oldL bestL curS).set curS newVal) st₁ :=
        holdsIn_set (idx := curS) (v := newVal) hcur_st
      have heq_list : (parentPassPrefix LB LP oldL bestL curS).set curS newVal =
          parentPassPrefix LB LP oldL bestL (curS + 1) := by
        have heq_val : newVal = oldL[curS] + bestL.getD (restrictMask LB LP curS) 0 := by
          dsimp only [newVal, rKey]
          rw [holdVal_eq, hbestVal_eq]
        rw [heq_val, parentPassPrefix_step LB LP oldL bestL hcur_lt]
      rwa [heq_list] at hset
    have hc_step : memoryCost (parentPassStep (args, curS)) st ≤ stepCost := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState st (Memory.read x) = st := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult st (Memory.read x) = st.mem x := rfl
      unfold parentPassStep
      dsimp only
      rw [memoryCost_bind', memoryCost_read, hr_s, hr_r,
        memoryCost_bind', hst_rk, hr_rk,
        memoryCost_bind', memoryCost_read, hr_s, hr_r,
        memoryCost_bind', memoryCost_write, memoryCost_pure]
      dsimp only [stepCost]
      omega
    obtain ⟨hv_rem, hfr_rem, hout_rem, hpfx_rem, hc_rem⟩ :=
      ih (curS + 1) st₁ (by omega) hfr hout₁ hpfx_next
    have hiter_eq : iterate parentPassStep args (rem + 1) curS =
        (parentPassStep (args, curS) >>= iterate parentPassStep args rem) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_, ?_, ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind, hst_step, hres_step]; exact hfr_rem
    · rw [StateTransitionSpec.clientState_bind, hst_step, hres_step]; exact hout_rem
    · rw [StateTransitionSpec.clientState_bind, hst_step, hres_step]
      have hadd : curS + (rem + 1) = curS + 1 + rem := by omega
      rwa [hadd]
    · rw [memoryCost_bind', hst_step, hres_step]
      calc memoryCost (parentPassStep (args, curS)) st +
            memoryCost (iterate parentPassStep args rem (curS + 1)) st₁
          ≤ stepCost + rem * stepCost := Nat.add_le_add hc_step hc_rem
        _ = (rem + 1) * stepCost := by ring

private theorem parentPassProg_realizes :
    Realizes .exact parentPassProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 2 ∧
        ∃ LB LP oldL bestL capO capB,
          HoldsIn args.bagBPtr LB s ∧ LB.length = args.bagBLen ∧
          args.bagBPtr + args.bagBLen ≤ args.tblPPtr ∧
          HoldsIn args.bagPPtr LP s ∧ LP.length = args.bagPLen ∧
          args.bagPPtr + args.bagPLen ≤ args.tblPPtr ∧
          HoldsIn args.tblPPtr oldL s ∧ oldL.length = args.tblPLen ∧
          args.tblPLen = 2 ^ args.bagPLen ∧
          args.tblPPtr + args.tblPLen ≤ args.bestPtr ∧
          HoldsIn args.bestPtr bestL s ∧ bestL.length = 2 ^ args.bagPLen ∧
          oldL.foldl max 0 ≤ capO ∧ bestL.foldl max 0 ≤ capB ∧
          Fits w (args.bagBPtr + args.bagBLen) ∧ Fits w (args.bagPPtr + args.bagPLen) ∧
          Fits w (args.tblPPtr + args.tblPLen) ∧ Fits w (2 ^ args.bagPLen) ∧
          Fits w (args.bestPtr + 2 ^ args.bagPLen) ∧ Fits w (capO + capB))
      (fun _ _ => 0) := by
  unfold parentPassProg
  realize [restrictMaskProg_realizes]
  obtain ⟨h2, LB, LP, oldL, bestL, capO, capB,
    hLB_h, hLB_len, hLB_disj, hLP_h, hLP_len, hLP_disj,
    hold_h, hold_len, htblP_pow, hbest_disj, hbest_h, hbest_len,
    hold_cap, hbest_cap,
    hfit_bagB, hfit_bagP, hfit_tblP, hfit_powP, hfit_best, hfit_sum⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (curS : ℕ) (t : Memory.State) =>
      j ≤ d.tblPLen ∧ curS + j = d.tblPLen ∧
      t.frontier = s.frontier ∧
      (∀ addr, (addr < d.tblPPtr ∨ d.tblPPtr + d.tblPLen ≤ addr) → t.mem addr = s.mem addr) ∧
      HoldsIn d.tblPPtr (parentPassPrefix LB LP oldL bestL curS) t)
    (fun j curS t ⟨hj_le, hcur, hfr, hout, hpfx_t⟩ => ?_)
    ⟨le_rfl, Nat.zero_add _, rfl, fun _ _ => rfl,
      by rw [parentPassPrefix_zero]; exact hold_h⟩
  have hLB_t : HoldsIn d.bagBPtr LB t :=
    ⟨by rw [hfr]; exact hLB_h.1, hLB_h.2.frame fun a _ ha => hout a (.inl (by omega))⟩
  have hLP_t : HoldsIn d.bagPPtr LP t :=
    ⟨by rw [hfr]; exact hLP_h.1, hLP_h.2.frame fun a _ ha => hout a (.inl (by omega))⟩
  have hbest_t : HoldsIn d.bestPtr bestL t :=
    ⟨by rw [hfr]; exact hbest_h.1, hbest_h.2.frame fun a ha _ => hout a (.inr (by omega))⟩
  obtain ⟨_, _, hr_rk, _⟩ :=
    restrictMaskProg_spec (w := w) ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curS⟩
      hLB_t hLB_len hLP_t hLP_len
  dsimp only at hr_rk
  have hrk_lt : (Memory.spec 0).clientResult t
      (restrictMaskProg ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curS⟩) < bestL.length := by
    rw [hr_rk, hbest_len, ← hLP_len]
    exact restrictMask_lt_two_pow LB LP curS
  have hcur_lt : curS < oldL.length := by omega
  have hcur_pfx_lt : curS < (parentPassPrefix LB LP oldL bestL curS).length := by
    rw [length_parentPassPrefix]; exact hcur_lt
  have hold_val : t.mem (d.tblPPtr + curS) = oldL[curS] := by
    rw [hpfx_t.get curS hcur_pfx_lt]; simp [parentPassPrefix]
  have hold_le : t.mem (d.tblPPtr + curS) ≤ capO := by
    rw [hold_val]
    exact (List.mem_le_foldl_max (List.getElem_mem hcur_lt)).trans hold_cap
  have hbest_le : t.mem (d.bestPtr +
      (Memory.spec 0).clientResult t
        (restrictMaskProg ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curS⟩)) ≤ capB := by
    rw [hbest_t.get _ hrk_lt]
    exact (List.mem_le_foldl_max (List.getElem_mem hrk_lt)).trans hbest_cap
  have hrk_safe : Fits w 2 ∧ Fits w (d.bagBPtr + d.bagBLen) ∧
      Fits w (d.bagPPtr + d.bagPLen) ∧ Fits w (2 ^ d.bagPLen) :=
    ⟨h2, hfit_bagB, hfit_bagP, hfit_powP⟩
  have hfit_old_addr : Fits w (d.tblPPtr + curS) := hfit_tblP.of_le (by omega)
  have hfit_best_addr : Fits w (d.bestPtr +
      (Memory.spec 0).clientResult t
        (restrictMaskProg ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curS⟩)) :=
    hfit_best.of_le (by omega)
  have hfit_new : Fits w (t.mem (d.tblPPtr + curS) +
      t.mem (d.bestPtr +
        (Memory.spec 0).clientResult t
          (restrictMaskProg ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curS⟩))) :=
    hfit_sum.of_le (Nat.add_le_add hold_le hbest_le)
  have hfit_cur1 : Fits w (curS + 1) := hfit_tblP.of_le (by omega)
  obtain ⟨hst_ev, hres_ev⟩ := parentPassStep_eval d curS t
  refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_, ?_⟩
  · dsimp only [parentPassStep]
    rw [restrictMaskProg_state]
    repeat (first | exact hrk_safe | assumption | refine And.intro ?_ ?_)
  · rw [hres_ev]; omega
  · rw [hst_ev]; exact hfr
  · rw [hst_ev]
    intro addr haddr
    change Function.update t.mem (d.tblPPtr + curS) _ addr = s.mem addr
    rw [Function.update_of_ne (by omega)]
    exact hout addr haddr
  · have hrk_lt' : restrictMask LB LP curS < bestL.length := by rwa [← hr_rk]
    have heq_v : t.mem (d.tblPPtr + curS) +
        t.mem (d.bestPtr +
          (Memory.spec 0).clientResult t
            (restrictMaskProg ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curS⟩)) =
        oldL[curS] + bestL.getD (restrictMask LB LP curS) 0 := by
      rw [hold_val, hr_rk, hbest_t.get _ hrk_lt', List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hrk_lt', Option.getD_some]
    rw [hst_ev, hres_ev, ← parentPassPrefix_step LB LP oldL bestL hcur_lt, ← heq_v]
    exact holdsIn_set hpfx_t

private structure RootPassArgs where
  numVerts : ℕ
  adjPtr : ℕ
  wtPtr : ℕ
  bag0Ptr : ℕ
  bag0Len : ℕ
  tbl0Ptr : ℕ
  tbl0Len : ℕ

private def RootPassArgs.equiv :
    RootPassArgs ≃ (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((((a.numVerts, a.adjPtr), a.wtPtr), a.bag0Ptr), a.bag0Len), a.tbl0Ptr), a.tbl0Len)
  invFun := fun ((((((nv, ap), wp), b0p), b0l), t0p), t0l) => ⟨nv, ap, wp, b0p, b0l, t0p, t0l⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding RootPassArgs := .ofEquiv RootPassArgs.equiv

private structure RootState where
  curC : ℕ
  best : ℕ

private def RootState.equiv : RootState ≃ ℕ × ℕ where
  toFun s := (s.curC, s.best)
  invFun := fun (c, b) => ⟨c, b⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding RootState := .ofEquiv RootState.equiv

private def rootPassStep (p : RootPassArgs × RootState) : Memory.Prog RootState := do
  let a := p.1
  let st := p.2
  let fc ← Memory.read (a.tbl0Ptr + st.curC)
  let ind ← indepBagProg ⟨a.numVerts, a.adjPtr, a.bag0Ptr, a.bag0Len, st.curC⟩
  let fw ← forgetWeightProg ⟨a.wtPtr, a.bag0Ptr, 0, a.bag0Ptr, a.bag0Len, st.curC⟩
  let cand := fw + fc
  let upd := if st.best < cand then cand else st.best
  let best' := if ind = 1 then upd else st.best
  pure ⟨st.curC + 1, best'⟩

private def rootPassProg (args : RootPassArgs) : Memory.Prog ℕ := do
  let res ← iterate rootPassStep args args.tbl0Len ⟨0, 0⟩
  pure res.best

private theorem rootPassStep_eval (a : RootPassArgs) (st : RootState) (t : Memory.State) :
    let fc := t.mem (a.tbl0Ptr + st.curC)
    let ind := (Memory.spec 0).clientResult t
      (indepBagProg ⟨a.numVerts, a.adjPtr, a.bag0Ptr, a.bag0Len, st.curC⟩)
    let fw := (Memory.spec 0).clientResult t
      (forgetWeightProg ⟨a.wtPtr, a.bag0Ptr, 0, a.bag0Ptr, a.bag0Len, st.curC⟩)
    let cand := fw + fc
    let best' := if ind = 1 then (if st.best < cand then cand else st.best) else st.best
    (Memory.spec 0).clientState t (rootPassStep (a, st)) = t ∧
    (Memory.spec 0).clientResult t (rootPassStep (a, st)) = ⟨st.curC + 1, best'⟩ := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold rootPassStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    indepBagProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    forgetWeightProg_state]
  exact ⟨rfl, rfl⟩

private theorem rootPassProg_state (args : RootPassArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (rootPassProg args) = s := by
  unfold rootPassProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of rootPassStep args
    (fun st m => (rootPassStep_eval args st m).1) args.tbl0Len ⟨0, 0⟩ s

private theorem rootPassProg_spec {w : ℕ} (args : RootPassArgs) {inst : MWISInstance}
    {L0 tbl0 : List ℕ} {arr0 : Array ℕ} {s : Memory.State}
    (hadj : HoldsIn args.adjPtr inst.adjMatrix s)
    (hwt : HoldsIn args.wtPtr inst.weights s)
    (hnv : args.numVerts = inst.numVerts)
    (hL0 : HoldsIn args.bag0Ptr L0 s) (hlen0 : L0.length = args.bag0Len)
    (hL0_lt : ∀ u ∈ L0, u < inst.numVerts)
    (htbl0 : HoldsIn args.tbl0Ptr tbl0 s) (htbl0_len : tbl0.length = args.tbl0Len)
    (harr0 : ∀ c < args.tbl0Len, tbl0.getD c 0 = arr0.getD c 0) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (rootPassProg args)) ∧
    (Memory.spec 0).clientState s (rootPassProg args) = s ∧
    (Memory.spec 0).clientResult s (rootPassProg args) =
      rootPassInst inst.adj inst.wt L0 arr0 args.tbl0Len ∧
    memoryCost (rootPassProg args) s ≤
      args.tbl0Len * (args.bag0Len * (2 * args.bag0Len + 1) + args.bag0Len * 2 + 1) := by
  let stepCost := args.bag0Len * (2 * args.bag0Len + 1) + args.bag0Len * 2 + 1
  have hnil : HoldsIn args.bag0Ptr [] s := HoldsIn.nil (by have := hL0.1; omega)
  suffices ∀ rem curC,
      curC + rem = args.tbl0Len →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate rootPassStep args rem ⟨curC, rootPassInst inst.adj inst.wt L0 arr0 curC⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate rootPassStep args rem ⟨curC, rootPassInst inst.adj inst.wt L0 arr0 curC⟩)).best =
        rootPassInst inst.adj inst.wt L0 arr0 (curC + rem) ∧
      memoryCost
        (iterate rootPassStep args rem ⟨curC, rootPassInst inst.adj inst.wt L0 arr0 curC⟩) s ≤
        rem * stepCost by
    have hrun := this args.tbl0Len 0 (Nat.zero_add _)
    rw [Nat.zero_add] at hrun
    refine ⟨?_, rootPassProg_state args s, ?_, ?_⟩
    · unfold rootPassProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold rootPassProg
      rw [StateTransitionSpec.clientResult_bind]
      exact hrun.2.1
    · unfold rootPassProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro rem
  induction rem with
  | zero =>
    intro curC _
    have h0 : iterate rootPassStep args 0
        ⟨curC, rootPassInst inst.adj inst.wt L0 arr0 curC⟩ =
        pure ⟨curC, rootPassInst inst.adj inst.wt L0 arr0 curC⟩ := rfl
    rw [h0, Nat.add_zero]
    exact ⟨validHistory_pure w s _, rfl, by simp [memoryCost_pure]⟩
  | succ rem ih =>
    intro curC hsum
    let bCur := rootPassInst inst.adj inst.wt L0 arr0 curC
    have hcur_lt : curC < args.tbl0Len := by omega
    have hcur_tbl : curC < tbl0.length := by omega
    obtain ⟨hv_ind, hst_ind, hr_ind, hc_ind⟩ :=
      indepBagProg_spec (w := w) ⟨args.numVerts, args.adjPtr, args.bag0Ptr, args.bag0Len, curC⟩
        hadj hnv hL0 hlen0 hL0_lt
    obtain ⟨hv_fw, hst_fw, hr_fw, hc_fw⟩ :=
      forgetWeightProg_spec (w := w)
        ⟨args.wtPtr, args.bag0Ptr, 0, args.bag0Ptr, args.bag0Len, curC⟩
        hwt hnil rfl hL0 hlen0 hL0_lt
    dsimp only at hr_ind hc_ind hr_fw hc_fw
    have hfc_addr : args.tbl0Ptr + curC < s.frontier := by have := htbl0.1; omega
    have hfc_eq : s.mem (args.tbl0Ptr + curC) = arr0.getD curC 0 := by
      rw [htbl0.get curC hcur_tbl, ← harr0 curC hcur_lt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hcur_tbl, Option.getD_some]
    obtain ⟨hst_step, hres_step⟩ := rootPassStep_eval args ⟨curC, bCur⟩ s
    have hb_next : (if (if indepInst inst.adj L0 curC then 1 else 0) = 1 then
          if bCur < forgetWeight inst.wt [] L0 curC + s.mem (args.tbl0Ptr + curC) then
            forgetWeight inst.wt [] L0 curC + s.mem (args.tbl0Ptr + curC)
          else bCur
        else bCur) = rootPassInst inst.adj inst.wt L0 arr0 (curC + 1) := by
      dsimp only [rootPassInst, bCur]
      rw [hfc_eq]
      by_cases hind : indepInst inst.adj L0 curC = true
      · simp only [hind, ↓reduceIte]
        by_cases hlt :
            rootPassInst inst.adj inst.wt L0 arr0 curC <
              forgetWeight inst.wt [] L0 curC + arr0.getD curC 0 <;>
          simp only [hlt, ↓reduceIte] <;> omega
      · simp [hind]
    rw [hr_ind, hr_fw, hb_next] at hres_step
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (rootPassStep (args, ⟨curC, bCur⟩))) := by
      unfold rootPassStep
      dsimp only
      refine validHistory_read_bind hfc_addr ?_
      refine validHistory_bind_step hv_ind ?_
      rw [hst_ind, hr_ind]
      exact validHistory_bind_step hv_fw (validHistory_pure w _ _)
    have hc_step : memoryCost (rootPassStep (args, ⟨curC, bCur⟩)) s ≤ stepCost := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
      unfold rootPassStep
      dsimp only
      rw [memoryCost_bind', memoryCost_read, hr_s, hr_r,
        memoryCost_bind', hst_ind, hr_ind,
        memoryCost_bind', hst_fw, memoryCost_pure]
      dsimp only [stepCost]
      omega
    obtain ⟨hv_rem, hr_rem, hc_rem⟩ := ih (curC + 1) (by omega)
    have hiter_eq : iterate rootPassStep args (rem + 1) ⟨curC, bCur⟩ =
        (rootPassStep (args, ⟨curC, bCur⟩) >>= iterate rootPassStep args rem) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step]
      have hadd : curC + (rem + 1) = curC + 1 + rem := by omega
      rwa [hadd]
    · rw [memoryCost_bind', hst_step, hres_step]
      calc memoryCost (rootPassStep (args, ⟨curC, bCur⟩)) s +
            memoryCost
              (iterate rootPassStep args rem
                ⟨curC + 1, rootPassInst inst.adj inst.wt L0 arr0 (curC + 1)⟩) s
          ≤ stepCost + rem * stepCost := Nat.add_le_add hc_step hc_rem
        _ = (rem + 1) * stepCost := by ring

private theorem rootPassProg_realizes :
    Realizes .exact rootPassProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 2 ∧
        ∃ m adjL wtL L0 tbl0 cap,
          adjL.length = m * m ∧ wtL.length = m ∧ args.numVerts = m ∧
          HoldsIn args.adjPtr adjL s ∧ HoldsIn args.wtPtr wtL s ∧
          HoldsIn args.bag0Ptr L0 s ∧ L0.length = args.bag0Len ∧ (∀ u ∈ L0, u < m) ∧
          HoldsIn args.tbl0Ptr tbl0 s ∧ tbl0.length = args.tbl0Len ∧
          args.bag0Len * wtL.foldl max 0 + tbl0.foldl max 0 ≤ cap ∧
          Fits w (args.adjPtr + m * m) ∧ Fits w (args.wtPtr + m) ∧
          Fits w (args.bag0Ptr + args.bag0Len) ∧ Fits w (args.tbl0Ptr + args.tbl0Len) ∧
          Fits w cap)
      (fun _ _ => 0) := by
  unfold rootPassProg
  realize [indepBagProg_realizes, forgetWeightProg_realizes]
  obtain ⟨h2, m, adjL, wtL, L0, tbl0, cap,
    hadjL_len, hwtL_len, hnv, hadj_h, hwt_h,
    hL0_h, hL0_len, hL0_lt, htbl0_h, htbl0_len, hcap_bound,
    hfit_adj, hfit_wt, hfit_bag0, hfit_tbl0, hfit_cap⟩ := h
  have h1 : Fits w 1 := h2.of_le (by decide)
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : RootState) (t : Memory.State) =>
      j ≤ d.tbl0Len ∧ st.curC + j = d.tbl0Len ∧ st.best ≤ cap ∧
      HoldsIn d.adjPtr adjL t ∧ HoldsIn d.wtPtr wtL t ∧
      HoldsIn d.bag0Ptr L0 t ∧ HoldsIn d.tbl0Ptr tbl0 t)
    (fun j st t ⟨hj_le, hcur, hbest_le, hadj_t, hwt_t, hL0_t, htbl0_t⟩ => ?_)
    ⟨le_rfl, Nat.zero_add _, Nat.zero_le _, hadj_h, hwt_h, hL0_h, htbl0_h⟩
  have hL0_lt_wt : ∀ u ∈ L0, u < wtL.length := by rw [hwtL_len]; exact hL0_lt
  have hfit_wtL : Fits w (d.wtPtr + wtL.length) := by rwa [hwtL_len]
  have hfit_bag0_zero : Fits w (d.bag0Ptr + 0) := hfit_bag0.of_le (by omega)
  have hfit_sumW : Fits w (d.bag0Len * wtL.foldl max 0) := hfit_cap.of_le (by omega)
  have hind_safe : Fits w 2 ∧ ∃ m' adjL' xs',
      adjL'.length = m' * m' ∧ d.numVerts = m' ∧
      HoldsIn d.adjPtr adjL' t ∧ HoldsIn d.bag0Ptr xs' t ∧ xs'.length = d.bag0Len ∧
      (∀ u ∈ xs', u < m') ∧ Fits w (d.adjPtr + m' * m') ∧ Fits w (d.bag0Ptr + d.bag0Len) :=
    ⟨h2, m, adjL, L0, hadjL_len, hnv, hadj_t, hL0_t, hL0_len, hL0_lt, hfit_adj, hfit_bag0⟩
  have hfw_safe : Fits w 2 ∧ ∃ wtL' LB',
      HoldsIn d.wtPtr wtL' t ∧ HoldsIn d.bag0Ptr LB' t ∧ LB'.length = d.bag0Len ∧
      (∀ u ∈ LB', u < wtL'.length) ∧ Fits w (d.wtPtr + wtL'.length) ∧
      Fits w (d.bag0Ptr + 0) ∧ Fits w (d.bag0Ptr + d.bag0Len) ∧
      Fits w (d.bag0Len * wtL'.foldl max 0) :=
    ⟨h2, wtL, L0, hwt_t, hL0_t, hL0_len, hL0_lt_wt, hfit_wtL, hfit_bag0_zero, hfit_bag0,
      hfit_sumW⟩
  have hfw_le : (Memory.spec 0).clientResult t
      (forgetWeightProg ⟨d.wtPtr, d.bag0Ptr, 0, d.bag0Ptr, d.bag0Len, st.curC⟩) ≤
      d.bag0Len * wtL.foldl max 0 :=
    forgetWeightProg_result_le _ hwt_t hL0_t hL0_len hL0_lt_wt
  have hcur_tbl : st.curC < tbl0.length := by omega
  have hfc_le : t.mem (d.tbl0Ptr + st.curC) ≤ tbl0.foldl max 0 := by
    rw [htbl0_t.get st.curC hcur_tbl]
    exact List.mem_le_foldl_max (List.getElem_mem hcur_tbl)
  have hcand_le : (Memory.spec 0).clientResult t
      (forgetWeightProg ⟨d.wtPtr, d.bag0Ptr, 0, d.bag0Ptr, d.bag0Len, st.curC⟩) +
      t.mem (d.tbl0Ptr + st.curC) ≤ cap := by omega
  have hfit_tbl_addr : Fits w (d.tbl0Ptr + st.curC) := hfit_tbl0.of_le (by omega)
  have hfit_cand : Fits w ((Memory.spec 0).clientResult t
      (forgetWeightProg ⟨d.wtPtr, d.bag0Ptr, 0, d.bag0Ptr, d.bag0Len, st.curC⟩) +
      t.mem (d.tbl0Ptr + st.curC)) := hfit_cap.of_le hcand_le
  have hfit_cur1 : Fits w (st.curC + 1) := hfit_tbl0.of_le (by omega)
  obtain ⟨hst_ev, hres_ev⟩ := rootPassStep_eval d st t
  refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [rootPassStep]
    rw [indepBagProg_state]
    repeat (
      first
      | split
      | exact hind_safe
      | exact hfw_safe
      | assumption
      | refine And.intro ?_ ?_)
  · rw [hres_ev]; change (st.curC + 1) + j = d.tbl0Len; omega
  · rw [hres_ev]
    change (if _ then (if _ then _ else st.best) else st.best) ≤ cap
    split_ifs <;> omega
  · rw [hst_ev]; exact hadj_t
  · rw [hst_ev]; exact hwt_t
  · rw [hst_ev]; exact hL0_t
  · rw [hst_ev]; exact htbl0_t

/-! ### Node descriptor initialization, bottom-up node loop, and top-level runner -/

private theorem MWISInstance.bagAt_length_le (inst : MWISInstance)
    (i : Fin (inst.numNodes + 1)) : (inst.bagAt i).length ≤ inst.maxBagLen := by
  have hmem : inst.bagAt i ∈ inst.bags := List.getElem_mem _
  exact List.mem_le_foldl_max (List.mem_map_of_mem hmem)

private theorem MWISInstance.bagAt_mem_lt (inst : MWISInstance)
    (i : Fin (inst.numNodes + 1)) : ∀ u ∈ inst.bagAt i, u < inst.numVerts :=
  inst.bags_lt (inst.bagAt i) (List.getElem_mem _)

private structure NodeLayout (inst : MWISInstance) (descBase : ℕ)
    (tblList : Fin (inst.numNodes + 1) → List ℕ) (s : Memory.State) : Prop where
  wt_holds : HoldsIn 3 inst.weights s
  adj_holds : HoldsIn (3 + inst.numVerts) inst.adjMatrix s
  par_holds : HoldsIn (3 + inst.numVerts + inst.numVerts * inst.numVerts) inst.parents s
  desc_lo : 3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1) ≤ descBase
  desc_hi : descBase + 4 * (inst.numNodes + 1) ≤ s.frontier
  bags_holds : ∀ i : Fin (inst.numNodes + 1),
    s.mem (descBase + 4 * i.val + 1) = (inst.bagAt i).length ∧
    s.mem (descBase + 4 * i.val + 3) = 2 ^ (inst.bagAt i).length ∧
    s.mem (descBase + 4 * i.val) + (inst.bagAt i).length ≤ descBase ∧
    HoldsIn (s.mem (descBase + 4 * i.val)) (inst.bagAt i) s
  tbl_holds : ∀ i : Fin (inst.numNodes + 1),
    (tblList i).length = 2 ^ (inst.bagAt i).length ∧
    descBase + 4 * (inst.numNodes + 1) ≤ s.mem (descBase + 4 * i.val + 2) ∧
    HoldsIn (s.mem (descBase + 4 * i.val + 2)) (tblList i) s
  tbl_disj : ∀ i j : Fin (inst.numNodes + 1), i.val < j.val →
    s.mem (descBase + 4 * i.val + 2) + 2 ^ (inst.bagAt i).length ≤
      s.mem (descBase + 4 * j.val + 2)

private theorem NodeLayout.mono_frontier {inst : MWISInstance} {descBase : ℕ}
    {tblList : Fin (inst.numNodes + 1) → List ℕ} {s s' : Memory.State}
    (h : NodeLayout inst descBase tblList s) (hp : PreservesBelow s.frontier s s') :
    NodeLayout inst descBase tblList s' where
  wt_holds := h.wt_holds.mono_frontier hp
  adj_holds := h.adj_holds.mono_frontier hp
  par_holds := h.par_holds.mono_frontier hp
  desc_lo := h.desc_lo
  desc_hi := h.desc_hi.trans hp.2.1
  bags_holds i := by
    obtain ⟨h1, h3, hlo, hb⟩ := h.bags_holds i
    have hd_hi := h.desc_hi
    have hi_lt := i.isLt
    have hm0 : s'.mem (descBase + 4 * i.val) = s.mem (descBase + 4 * i.val) :=
      hp.2.2 _ (by omega)
    have hm1 : s'.mem (descBase + 4 * i.val + 1) = s.mem (descBase + 4 * i.val + 1) :=
      hp.2.2 _ (by omega)
    have hm3 : s'.mem (descBase + 4 * i.val + 3) = s.mem (descBase + 4 * i.val + 3) :=
      hp.2.2 _ (by omega)
    rw [hm0, hm1, hm3]
    exact ⟨h1, h3, hlo, hb.mono_frontier hp⟩
  tbl_holds i := by
    obtain ⟨hlen, hlo, ht⟩ := h.tbl_holds i
    have hd_hi := h.desc_hi
    have hi_lt := i.isLt
    have hm2 : s'.mem (descBase + 4 * i.val + 2) = s.mem (descBase + 4 * i.val + 2) :=
      hp.2.2 _ (by omega)
    rw [hm2]
    exact ⟨hlen, hlo, ht.mono_frontier hp⟩
  tbl_disj i j hij := by
    have hd_hi := h.desc_hi
    have hi_lt := i.isLt
    have hj_lt := j.isLt
    rw [hp.2.2 (descBase + 4 * i.val + 2) (by omega),
      hp.2.2 (descBase + 4 * j.val + 2) (by omega)]
    exact h.tbl_disj i j hij

private theorem NodeLayout.update_table {inst : MWISInstance} {descBase : ℕ}
    {tblList : Fin (inst.numNodes + 1) → List ℕ} {s s' : Memory.State}
    (h : NodeLayout inst descBase tblList s)
    (p : Fin (inst.numNodes + 1)) (newP : List ℕ)
    (hnew_len : newP.length = 2 ^ (inst.bagAt p).length)
    (hfr : s'.frontier = s.frontier)
    (hout : ∀ addr,
      (addr < s.mem (descBase + 4 * p.val + 2) ∨
        s.mem (descBase + 4 * p.val + 2) + 2 ^ (inst.bagAt p).length ≤ addr) →
      s'.mem addr = s.mem addr)
    (hholdP : HoldsIn (s.mem (descBase + 4 * p.val + 2)) newP s') :
    NodeLayout inst descBase (Function.update tblList p newP) s' := by
  have hp_lo : descBase + 4 * (inst.numNodes + 1) ≤ s.mem (descBase + 4 * p.val + 2) :=
    (h.tbl_holds p).2.1
  have hdesc_lo := h.desc_lo
  have hlow_eq : ∀ addr < descBase + 4 * (inst.numNodes + 1), s'.mem addr = s.mem addr :=
    fun addr ha => hout addr (.inl (lt_of_lt_of_le ha hp_lo))
  refine
    { wt_holds := ⟨by rw [hfr]; exact h.wt_holds.1,
        h.wt_holds.2.frame fun a _ ha =>
          hlow_eq a (by rw [inst.weights_len] at ha; omega)⟩
      adj_holds := ⟨by rw [hfr]; exact h.adj_holds.1,
        h.adj_holds.2.frame fun a _ ha =>
          hlow_eq a (by rw [inst.adjMatrix_len] at ha; omega)⟩
      par_holds := ⟨by rw [hfr]; exact h.par_holds.1,
        h.par_holds.2.frame fun a _ ha =>
          hlow_eq a (by rw [inst.parents_len] at ha; omega)⟩
      desc_lo := h.desc_lo
      desc_hi := by rw [hfr]; exact h.desc_hi
      bags_holds := fun i => by
        obtain ⟨h1, h3, hblo, hb⟩ := h.bags_holds i
        have hi_lt := i.isLt
        rw [hlow_eq (descBase + 4 * i.val) (by omega),
          hlow_eq (descBase + 4 * i.val + 1) (by omega),
          hlow_eq (descBase + 4 * i.val + 3) (by omega)]
        exact ⟨h1, h3, hblo,
          ⟨by rw [hfr]; exact hb.1, hb.2.frame fun a _ ha => hlow_eq a (by omega)⟩⟩
      tbl_holds := fun i => by
        have hi_lt := i.isLt
        rw [hlow_eq (descBase + 4 * i.val + 2) (by omega)]
        by_cases hip : i = p
        · subst hip
          rw [Function.update_self]
          exact ⟨hnew_len, hp_lo, hholdP⟩
        · rw [Function.update_of_ne hip]
          obtain ⟨hlen, hlo, ht⟩ := h.tbl_holds i
          refine ⟨hlen, hlo, ⟨by rw [hfr]; exact ht.1, ht.2.frame fun a ha1 ha2 => ?_⟩⟩
          have hne_val : i.val ≠ p.val := fun hv => hip (Fin.ext hv)
          rcases Nat.lt_or_gt_of_ne hne_val with hilt | hpilt
          · have hdisj := h.tbl_disj i p hilt
            exact hout a (.inl (by omega))
          · have hdisj := h.tbl_disj p i hpilt
            exact hout a (.inr (by omega))
      tbl_disj := fun i j hij => by
        have hi_lt := i.isLt
        have hj_lt := j.isLt
        rw [hlow_eq (descBase + 4 * i.val + 2) (by omega),
          hlow_eq (descBase + 4 * j.val + 2) (by omega)]
        exact h.tbl_disj i j hij }

private def nodeMax {n : ℕ} (tblList : Fin (n + 1) → List ℕ) (i : ℕ) : ℕ :=
  if hi : i < n + 1 then (tblList ⟨i, hi⟩).foldl max 0 else 0

private def prefixMaxSum {n : ℕ} (tblList : Fin (n + 1) → List ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (m + 1), nodeMax tblList i

private theorem prefixMaxSum_replicate_zero {n : ℕ} (len : Fin (n + 1) → ℕ) (m : ℕ) :
    prefixMaxSum (fun i => List.replicate (len i) 0) m = 0 := by
  unfold prefixMaxSum
  refine Finset.sum_eq_zero fun i _ => ?_
  unfold nodeMax
  split_ifs with hi
  · refine Nat.eq_zero_of_le_zero (List.foldl_max_le le_rfl fun x hx => ?_)
    rw [List.eq_of_mem_replicate hx]
  · rfl

private theorem nodeMax_le_prefixMaxSum {n : ℕ} (tblList : Fin (n + 1) → List ℕ)
    {i m : ℕ} (him : i ≤ m) :
    nodeMax tblList i ≤ prefixMaxSum tblList m :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le him))

private theorem foldl_max_le_prefixMaxSum {n : ℕ} (tblList : Fin (n + 1) → List ℕ)
    (i : Fin (n + 1)) {m : ℕ} (him : i.val ≤ m) :
    (tblList i).foldl max 0 ≤ prefixMaxSum tblList m := by
  have h := nodeMax_le_prefixMaxSum tblList him
  unfold nodeMax at h
  rwa [dite_eq_left i.isLt, Fin.eta] at h

private theorem prefixMaxSum_update_le {n : ℕ} (tblList : Fin (n + 1) → List ℕ)
    {k B : ℕ} (hk : k + 1 ≤ n) (p : Fin (n + 1)) (hp_lt : p.val < k + 1)
    (newP : List ℕ)
    (hnew : newP.foldl max 0 ≤
      (tblList p).foldl max 0 + B + (tblList ⟨k + 1, by omega⟩).foldl max 0) :
    prefixMaxSum (Function.update tblList p newP) k ≤ prefixMaxSum tblList (k + 1) + B := by
  have hp_mem : p.val ∈ Finset.range (k + 1) := Finset.mem_range.2 hp_lt
  have hsum_succ : prefixMaxSum tblList (k + 1) =
      prefixMaxSum tblList k + (tblList ⟨k + 1, by omega⟩).foldl max 0 := by
    unfold prefixMaxSum
    rw [Finset.sum_range_succ]
    unfold nodeMax
    rw [dite_eq_left (by omega)]
  have herase_old : nodeMax tblList p.val +
      ∑ i ∈ (Finset.range (k + 1)).erase p.val, nodeMax tblList i =
      prefixMaxSum tblList k := Finset.add_sum_erase _ _ hp_mem
  have herase_new : prefixMaxSum (Function.update tblList p newP) k =
      nodeMax (Function.update tblList p newP) p.val +
      ∑ i ∈ (Finset.range (k + 1)).erase p.val,
        nodeMax (Function.update tblList p newP) i :=
    (Finset.add_sum_erase _ _ hp_mem).symm
  have hrest_eq : ∑ i ∈ (Finset.range (k + 1)).erase p.val,
      nodeMax (Function.update tblList p newP) i =
      ∑ i ∈ (Finset.range (k + 1)).erase p.val, nodeMax tblList i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hine : i ≠ p.val := (Finset.mem_erase.1 hi).1
    unfold nodeMax
    split_ifs with hlt
    · rw [Function.update_of_ne (fun h => hine (congrArg Fin.val h))]
    · rfl
  have hp_new : nodeMax (Function.update tblList p newP) p.val = newP.foldl max 0 := by
    unfold nodeMax
    rw [dite_eq_left p.isLt, Fin.eta, Function.update_self]
  have hp_old : nodeMax tblList p.val = (tblList p).foldl max 0 := by
    unfold nodeMax
    rw [dite_eq_left p.isLt, Fin.eta]
  rw [herase_new, hrest_eq, hp_new, hsum_succ, ← herase_old, hp_old]
  omega

private structure InitNodeState where
  curRaw : ℕ
  curIdx : ℕ

private def InitNodeState.equiv : InitNodeState ≃ ℕ × ℕ where
  toFun s := (s.curRaw, s.curIdx)
  invFun := fun (r, i) => ⟨r, i⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding InitNodeState := .ofEquiv InitNodeState.equiv

private def initNodeStep (p : ℕ × InitNodeState) : Memory.Prog InitNodeState := do
  let descBase := p.1
  let st := p.2
  let bagLen ← Memory.read st.curRaw
  let bagPtr := st.curRaw + 1
  let tblLen ← powProg ⟨2, bagLen⟩
  let tblPtr ← Memory.alloc tblLen
  let dAddr := descBase + 4 * st.curIdx
  Memory.write dAddr bagPtr
  Memory.write (dAddr + 1) bagLen
  Memory.write (dAddr + 2) tblPtr
  Memory.write (dAddr + 3) tblLen
  pure ⟨bagPtr + bagLen, st.curIdx + 1⟩

private def initNodesProg (args : ℕ × ℕ) : Memory.Prog ℕ := do
  let rawBagsPtr := args.1
  let count := args.2
  let descBase ← Memory.allocDirty (4 * count)
  let _ ← iterate initNodeStep descBase count ⟨rawBagsPtr, 0⟩
  pure descBase

private theorem initNodeStep_eval (descBase : ℕ) (st : InitNodeState) (t : Memory.State) :
    let bagLen := t.mem st.curRaw
    let bagPtr := st.curRaw + 1
    let tblLen := 2 ^ bagLen
    let tblPtr := t.frontier
    let dAddr := descBase + 4 * st.curIdx
    let m0 := clear t.mem tblPtr tblLen
    let m1 := Function.update m0 dAddr bagPtr
    let m2 := Function.update m1 (dAddr + 1) bagLen
    let m3 := Function.update m2 (dAddr + 2) tblPtr
    let m4 := Function.update m3 (dAddr + 3) tblLen
    (Memory.spec 0).clientState t (initNodeStep (descBase, st)) = ⟨m4, t.frontier + tblLen⟩ ∧
    (Memory.spec 0).clientResult t (initNodeStep (descBase, st)) =
      ⟨bagPtr + bagLen, st.curIdx + 1⟩ := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold initNodeStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    powProg_state, powProg_result]
  exact ⟨rfl, rfl⟩

private theorem initNodesProg_spec {w : ℕ} (inst : MWISInstance) {s₀ : Memory.State}
    (hwt₀ : HoldsIn 3 inst.weights s₀)
    (hadj₀ : HoldsIn (3 + inst.numVerts) inst.adjMatrix s₀)
    (hpar₀ : HoldsIn (3 + inst.numVerts + inst.numVerts * inst.numVerts) inst.parents s₀)
    (hbags₀ : HoldsIn
      (3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1))
      (inst.bags.flatMap encodeBag) s₀)
    (hfit_peak : Fits w (s₀.frontier + 4 * (inst.numNodes + 1) +
      (inst.numNodes + 1) * 2 ^ inst.maxBagLen))
    (hfit_raw : Fits w (s₀.frontier)) :
    let rawBagsPtr := 3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1)
    let count := inst.numNodes + 1
    let s₁ := (Memory.spec 0).clientState s₀ (initNodesProg (rawBagsPtr, count))
    let descBase := (Memory.spec 0).clientResult s₀ (initNodesProg (rawBagsPtr, count))
    (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (initNodesProg (rawBagsPtr, count))) ∧
    descBase = s₀.frontier ∧
    s₁.frontier ≤ s₀.frontier + 4 * count + count * 2 ^ inst.maxBagLen ∧
    NodeLayout inst descBase
      (fun i => List.replicate (2 ^ (inst.bagAt i).length) 0) s₁ ∧
    memoryCost (initNodesProg (rawBagsPtr, count)) s₀ ≤
      1 + count * (2 ^ inst.maxBagLen + inst.maxBagLen + 6) := by
  let rawBagsPtr := 3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1)
  let count := inst.numNodes + 1
  let M := inst.maxBagLen
  let descBase := s₀.frontier
  have hraw_def : rawBagsPtr =
      3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1) := rfl
  have hcount_def : count = inst.numNodes + 1 := rfl
  have hM_def : M = inst.maxBagLen := rfl
  have hdesc_def : descBase = s₀.frontier := rfl
  let s_d := (Memory.spec 0).clientState s₀ (Memory.allocDirty (4 * count))
  have hs_d_fr : s_d.frontier = descBase + 4 * count := rfl
  have hp_d : PreservesBelow descBase s₀ s_d := preservesBelow_allocDirty s₀ (4 * count)
  have hfit_d : Fits w (s₀.frontier + 4 * count) := hfit_peak.of_le (by omega)
  have hv_d : (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (Memory.allocDirty (4 * count))) :=
    validHistory_allocDirty hfit_d
  have hraw_lo : rawBagsPtr ≤ descBase := by have := hbags₀.1; omega
  let stepCost := 2 ^ M + M + 6
  have hstepCost_def : stepCost = 2 ^ M + M + 6 := rfl
  suffices ∀ rem k curRaw st,
      (hsum : k + rem = count) →
      descBase + 4 * count ≤ st.frontier →
      st.frontier ≤ descBase + 4 * count + k * 2 ^ M →
      PreservesBelow descBase s₀ st →
      HoldsIn curRaw ((inst.bags.drop k).flatMap encodeBag) st →
      curRaw + ((inst.bags.drop k).flatMap encodeBag).length ≤ descBase →
      (∀ i (hi : i < k),
        have hif : i < count := lt_of_lt_of_le hi (by omega)
        st.mem (descBase + 4 * i + 1) = (inst.bagAt ⟨i, hif⟩).length ∧
        st.mem (descBase + 4 * i + 3) = 2 ^ (inst.bagAt ⟨i, hif⟩).length ∧
        st.mem (descBase + 4 * i) + (inst.bagAt ⟨i, hif⟩).length ≤ descBase ∧
        HoldsIn (st.mem (descBase + 4 * i)) (inst.bagAt ⟨i, hif⟩) st ∧
        descBase + 4 * count ≤ st.mem (descBase + 4 * i + 2) ∧
        HoldsIn (st.mem (descBase + 4 * i + 2))
          (List.replicate (2 ^ (inst.bagAt ⟨i, hif⟩).length) 0) st) →
      (∀ i j (hi : i < k) (hj : j < k), i < j →
        st.mem (descBase + 4 * i + 2) +
          2 ^ (inst.bagAt ⟨i, lt_of_lt_of_le hi (by omega)⟩).length ≤
          st.mem (descBase + 4 * j + 2)) →
      (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (iterate initNodeStep descBase rem ⟨curRaw, k⟩)) ∧
      (let sEnd := (Memory.spec 0).clientState st (iterate initNodeStep descBase rem ⟨curRaw, k⟩)
       descBase + 4 * count ≤ sEnd.frontier ∧
       sEnd.frontier ≤ descBase + 4 * count + count * 2 ^ M ∧
       PreservesBelow descBase s₀ sEnd ∧
       (∀ i : Fin count,
         sEnd.mem (descBase + 4 * i.val + 1) = (inst.bagAt i).length ∧
         sEnd.mem (descBase + 4 * i.val + 3) = 2 ^ (inst.bagAt i).length ∧
         sEnd.mem (descBase + 4 * i.val) + (inst.bagAt i).length ≤ descBase ∧
         HoldsIn (sEnd.mem (descBase + 4 * i.val)) (inst.bagAt i) sEnd ∧
         descBase + 4 * count ≤ sEnd.mem (descBase + 4 * i.val + 2) ∧
         HoldsIn (sEnd.mem (descBase + 4 * i.val + 2))
           (List.replicate (2 ^ (inst.bagAt i).length) 0) sEnd) ∧
       (∀ i j : Fin count, i.val < j.val →
         sEnd.mem (descBase + 4 * i.val + 2) + 2 ^ (inst.bagAt i).length ≤
           sEnd.mem (descBase + 4 * j.val + 2))) ∧
      memoryCost (iterate initNodeStep descBase rem ⟨curRaw, k⟩) st ≤ rem * stepCost by
    have hrun := this count 0 rawBagsPtr s_d (Nat.zero_add _)
      (by rw [hs_d_fr]) (by rw [hs_d_fr]; omega) hp_d
      (by simpa only [List.drop_zero] using hbags₀.mono_frontier hp_d)
      hbags₀.1
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (fun _ _ hi _ _ => absurd hi (Nat.not_lt_zero _))
    obtain ⟨hv_loop, ⟨hfr_lo, hfr_hi, hpres_end, hnodes_end, hdisj_end⟩, hc_loop⟩ := hrun
    unfold initNodesProg
    dsimp only
    have ha_st : (Memory.spec 0).clientState s₀ (Memory.allocDirty (4 * count)) = s_d := rfl
    have ha_res : (Memory.spec 0).clientResult s₀ (Memory.allocDirty (4 * count)) = descBase := rfl
    refine ⟨validHistory_bind_step hv_d ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha_st, ha_res]
      exact validHistory_bind_step hv_loop (validHistory_pure w _ _)
    · rw [StateTransitionSpec.clientResult_bind, ha_st, ha_res,
        StateTransitionSpec.clientResult_bind]
      rfl
    · rw [StateTransitionSpec.clientState_bind, ha_st, ha_res,
        StateTransitionSpec.clientState_bind]
      exact hfr_hi
    · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
        ha_st, ha_res, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
      change NodeLayout inst descBase _
        ((Memory.spec 0).clientState s_d (iterate initNodeStep descBase count ⟨rawBagsPtr, 0⟩))
      exact
        { wt_holds := hwt₀.mono_frontier hpres_end
          adj_holds := hadj₀.mono_frontier hpres_end
          par_holds := hpar₀.mono_frontier hpres_end
          desc_lo := hraw_lo
          desc_hi := hfr_lo
          bags_holds := fun i =>
            ⟨(hnodes_end i).1, (hnodes_end i).2.1, (hnodes_end i).2.2.1, (hnodes_end i).2.2.2.1⟩
          tbl_holds := fun i =>
            ⟨List.length_replicate, (hnodes_end i).2.2.2.2.1, (hnodes_end i).2.2.2.2.2⟩
          tbl_disj := hdisj_end }
    · rw [memoryCost_bind', memoryCost_allocDirty, ha_st, ha_res,
        memoryCost_bind', memoryCost_pure, Nat.add_zero]
      dsimp only [count, stepCost, M, descBase, rawBagsPtr] at hc_loop ⊢
      omega
  intro rem
  induction rem with
  | zero =>
    intro k curRaw st hsum hfr_lo hfr_hi hpres _ _ hdone hdisj
    have hk_eq : k = count := by omega
    subst hk_eq
    have h0 : iterate initNodeStep descBase 0 ⟨curRaw, count⟩ = pure ⟨curRaw, count⟩ := rfl
    rw [h0]
    refine ⟨validHistory_pure w st _, ⟨hfr_lo, hfr_hi, hpres, ?_, ?_⟩,
      by simp [memoryCost_pure]⟩
    · intro i
      exact hdone i.val i.isLt
    · intro i j hij
      exact hdisj i.val j.val i.isLt j.isLt hij
  | succ rem ih =>
    intro k curRaw st hsum hfr_lo hfr_hi hpres hdrop hdrop_end hdone hdisj
    have hk_lt : k < count := by omega
    have hk_bags : k < inst.bags.length := by rw [inst.bags_len]; exact hk_lt
    let kFin : Fin count := ⟨k, hk_lt⟩
    have hdrop_cons : inst.bags.drop k = inst.bagAt kFin :: inst.bags.drop (k + 1) :=
      List.drop_eq_getElem_cons hk_bags
    rw [hdrop_cons, List.flatMap_cons, encodeBag, List.cons_append] at hdrop hdrop_end
    rw [HoldsIn.cons_iff] at hdrop
    obtain ⟨_, hmem_len, hafter_len⟩ := hdrop
    rw [HoldsIn.append_iff] at hafter_len
    obtain ⟨hbag_k, hrest_raw⟩ := hafter_len
    let bagLen := (inst.bagAt kFin).length
    let bagPtr := curRaw + 1
    let tblLen := 2 ^ bagLen
    let tblPtr := st.frontier
    let dAddr := descBase + 4 * k
    have hbagLen_def : bagLen = (inst.bagAt kFin).length := rfl
    have hbagPtr_def : bagPtr = curRaw + 1 := rfl
    have htblLen_def : tblLen = 2 ^ bagLen := rfl
    have htblPtr_def : tblPtr = st.frontier := rfl
    have hdAddr_def : dAddr = descBase + 4 * k := rfl
    have hbagLen_le : bagLen ≤ M := inst.bagAt_length_le kFin
    have htblLen_le : tblLen ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) hbagLen_le
    have hcur_lt_fr : curRaw < st.frontier := by omega
    have hfr_pos : 0 < st.frontier := by omega
    obtain ⟨hv_pow, hst_pow, hr_pow, hc_pow⟩ := powProg_spec (w := w) ⟨2, bagLen⟩ hfr_pos
    dsimp only at hr_pow hc_pow
    have hfr_next_le : st.frontier + tblLen ≤ descBase + 4 * count + (k + 1) * 2 ^ M := by
      calc st.frontier + tblLen
          ≤ (descBase + 4 * count + k * 2 ^ M) + 2 ^ M := Nat.add_le_add hfr_hi htblLen_le
        _ = descBase + 4 * count + (k + 1) * 2 ^ M := by ring
    have hdrop_end_len : curRaw + 1 + (inst.bagAt kFin).length +
        ((inst.bags.drop (k + 1)).flatMap encodeBag).length ≤ descBase := by
      simp only [List.length_cons, List.length_append] at hdrop_end
      omega
    have hfit_alloc : Fits w (st.frontier + tblLen) := hfit_peak.of_le (by
      have hk1 : k + 1 ≤ count := by omega
      have hmul : (k + 1) * 2 ^ M ≤ count * 2 ^ M := Nat.mul_le_mul_right _ hk1
      dsimp only [count, M, descBase] at hfr_next_le hmul ⊢
      omega)
    have hv_alloc : (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (Memory.alloc tblLen)) :=
      validHistory_alloc hfit_alloc
    have hbagPtr_fit : Fits w bagPtr := hfit_raw.of_le (by
      dsimp only [bagPtr, bagLen, descBase] at *; omega)
    have hbagLen_fit : Fits w bagLen := hfit_raw.of_le (by
      dsimp only [bagPtr, bagLen, descBase] at *; omega)
    have htblPtr_fit : Fits w tblPtr := hfit_alloc.of_le (Nat.le_add_right _ _)
    have htblLen_fit : Fits w tblLen := hfit_alloc.of_le (Nat.le_add_left _ _)
    let st_a := (Memory.spec 0).clientState st (Memory.alloc tblLen)
    have hst_a_fr : st_a.frontier = st.frontier + tblLen := rfl
    have hp_a : PreservesBelow st.frontier st st_a := preservesBelow_alloc st tblLen
    have htbl_zero_a : HoldsIn tblPtr (List.replicate tblLen 0) st_a :=
      holdsIn_alloc_zero st tblLen
    let m1 := Function.update st_a.mem dAddr bagPtr
    let m2 := Function.update m1 (dAddr + 1) bagLen
    let m3 := Function.update m2 (dAddr + 2) tblPtr
    let m4 := Function.update m3 (dAddr + 3) tblLen
    let st₁ : Memory.State := ⟨m4, st.frontier + tblLen⟩
    have hst₁_fr : st₁.frontier = st.frontier + tblLen := rfl
    obtain ⟨hst_step, hres_step⟩ := initNodeStep_eval descBase ⟨curRaw, k⟩ st
    have hst_step' : (Memory.spec 0).clientState st (initNodeStep (descBase, ⟨curRaw, k⟩)) =
        st₁ := by
      rw [hst_step]
      dsimp only [st₁, m4, m3, m2, m1, st_a, bagLen, bagPtr, tblLen, tblPtr, dAddr]
      simp only [hmem_len]
      rfl
    have hres_step' : (Memory.spec 0).clientResult st (initNodeStep (descBase, ⟨curRaw, k⟩)) =
        ⟨bagPtr + bagLen, k + 1⟩ := by
      rw [hres_step]
      dsimp only [bagPtr, bagLen]
      simp only [hmem_len]
    have hd3_lt : dAddr + 3 < st.frontier + tblLen := by omega
    have hv_step : (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (initNodeStep (descBase, ⟨curRaw, k⟩))) := by
      unfold initNodeStep
      dsimp only
      refine validHistory_read_bind hcur_lt_fr ?_
      rw [hmem_len]
      refine validHistory_bind_step hv_pow ?_
      rw [hst_pow, hr_pow]
      refine validHistory_bind_step hv_alloc ?_
      change (Memory.spec w).ValidHistory st_a
        ((Memory.spec w).clientHistory st_a
          (Memory.write dAddr bagPtr >>= fun _ =>
            Memory.write (dAddr + 1) bagLen >>= fun _ =>
            Memory.write (dAddr + 2) tblPtr >>= fun _ =>
            Memory.write (dAddr + 3) tblLen >>= fun _ => pure _))
      have hd0 : dAddr < st_a.frontier := by change dAddr < st.frontier + tblLen; omega
      have hd1 : dAddr + 1 < st_a.frontier := by change dAddr + 1 < st.frontier + tblLen; omega
      have hd2 : dAddr + 2 < st_a.frontier := by change dAddr + 2 < st.frontier + tblLen; omega
      have hd3 : dAddr + 3 < st_a.frontier := hd3_lt
      exact validHistory_write_bind hd0 hbagPtr_fit
        (validHistory_write_bind hd1 hbagLen_fit
          (validHistory_write_bind hd2 htblPtr_fit
            (validHistory_write_bind hd3 htblLen_fit
              (validHistory_pure w st₁ _))))
    have hp_writes : ∀ addr, (addr < dAddr ∨ dAddr + 4 ≤ addr) → st₁.mem addr = st_a.mem addr :=
      fun addr haddr => by
        change m4 addr = st_a.mem addr
        dsimp only [m4, m3, m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hpres₁ : PreservesBelow descBase s₀ st₁ := by
      refine ⟨hpres.1, hpres.2.1.trans (Nat.le_add_right _ _), fun a ha => ?_⟩
      rw [hp_writes a (.inl (by omega)), hp_a.2.2 a (by omega), hpres.2.2 a ha]
    have hbag_k_st₁ : HoldsIn bagPtr (inst.bagAt kFin) st₁ :=
      hbag_k.mono (F := descBase) (by dsimp only [bagPtr, bagLen, descBase, kFin] at *; omega)
        ⟨by dsimp only [bagPtr, bagLen, tblLen, descBase, kFin] at *; omega,
         by dsimp only [bagPtr, bagLen, tblLen, descBase, kFin] at *; omega,
         fun a ha => by
          rw [hp_writes a
              (.inl (by dsimp only [bagPtr, bagLen, dAddr, descBase, kFin] at *; omega)),
            hp_a.2.2 a (by dsimp only [bagPtr, bagLen, descBase, kFin] at *; omega)]⟩
    have hrest_st₁ : HoldsIn (bagPtr + bagLen) ((inst.bags.drop (k + 1)).flatMap encodeBag) st₁ :=
      hrest_raw.mono (F := descBase) (by dsimp only [bagPtr, bagLen, descBase, kFin] at *; omega)
        ⟨by dsimp only [bagPtr, bagLen, tblLen, descBase, kFin] at *; omega,
         by dsimp only [bagPtr, bagLen, tblLen, descBase, kFin] at *; omega,
         fun a ha => by
          rw [hp_writes a
              (.inl (by dsimp only [bagPtr, bagLen, dAddr, descBase, kFin] at *; omega)),
            hp_a.2.2 a (by dsimp only [bagPtr, bagLen, descBase, kFin] at *; omega)]⟩
    have htbl_k_st₁ : HoldsIn tblPtr (List.replicate tblLen 0) st₁ :=
      ⟨htbl_zero_a.1, htbl_zero_a.2.frame fun a ha _ =>
        hp_writes a (.inr (by dsimp only [tblPtr, tblLen, dAddr, descBase, count] at *; omega))⟩
    have hm4_0 : st₁.mem dAddr = bagPtr := by
      change m4 dAddr = bagPtr
      dsimp only [m4, m3, m2, m1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    have hm4_1 : st₁.mem (dAddr + 1) = bagLen := by
      change m4 (dAddr + 1) = bagLen
      dsimp only [m4, m3, m2, m1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    have hm4_2 : st₁.mem (dAddr + 2) = tblPtr := by
      change m4 (dAddr + 2) = tblPtr
      dsimp only [m4, m3, m2, m1]
      rw [Function.update_of_ne (by omega), Function.update_self]
    have hm4_3 : st₁.mem (dAddr + 3) = tblLen := by
      change m4 (dAddr + 3) = tblLen
      dsimp only [m4]
      rw [Function.update_self]
    have hdone₁ : ∀ i (hi : i < k + 1),
        have hif : i < count := lt_of_lt_of_le hi (by omega)
        st₁.mem (descBase + 4 * i + 1) = (inst.bagAt ⟨i, hif⟩).length ∧
        st₁.mem (descBase + 4 * i + 3) = 2 ^ (inst.bagAt ⟨i, hif⟩).length ∧
        st₁.mem (descBase + 4 * i) + (inst.bagAt ⟨i, hif⟩).length ≤ descBase ∧
        HoldsIn (st₁.mem (descBase + 4 * i)) (inst.bagAt ⟨i, hif⟩) st₁ ∧
        descBase + 4 * count ≤ st₁.mem (descBase + 4 * i + 2) ∧
        HoldsIn (st₁.mem (descBase + 4 * i + 2))
          (List.replicate (2 ^ (inst.bagAt ⟨i, hif⟩).length) 0) st₁ := by
      intro i hi
      by_cases hik : i = k
      · subst hik
        rw [hm4_0, hm4_1, hm4_2, hm4_3]
        refine ⟨rfl, rfl, ?_, hbag_k_st₁, hfr_lo, htbl_k_st₁⟩
        dsimp only [bagPtr, bagLen, descBase, kFin] at *
        omega
      · have hik_lt : i < k := by omega
        obtain ⟨h1, h3, hblo, hb, htlo, ht⟩ := hdone i hik_lt
        have heq_m0 : st₁.mem (descBase + 4 * i) = st.mem (descBase + 4 * i) := by
          rw [hp_writes _ (.inl (by dsimp only [dAddr]; omega)),
            hp_a.2.2 _ (by dsimp only [descBase, count] at *; omega)]
        have heq_m (off : ℕ) (hoff : off < 4) :
            st₁.mem (descBase + 4 * i + off) = st.mem (descBase + 4 * i + off) := by
          rw [hp_writes _ (.inl (by dsimp only [dAddr]; omega)),
            hp_a.2.2 _ (by dsimp only [descBase, count] at *; omega)]
        rw [heq_m0, heq_m 1 (by decide), heq_m 2 (by decide), heq_m 3 (by decide)]
        refine ⟨h1, h3, hblo, ?_, htlo, ?_⟩
        · exact hb.mono hblo
            ⟨by dsimp only [descBase, count] at *; omega,
             by dsimp only [descBase, count] at *; omega,
             fun a ha => by
              rw [hp_writes a (.inl (by dsimp only [dAddr, descBase] at *; omega)),
                hp_a.2.2 a (by dsimp only [descBase, count] at *; omega)]⟩
        · refine ⟨ht.1.trans (Nat.le_add_right _ _), ht.2.frame fun a ha hlt => ?_⟩
          rw [hp_writes a (.inr (by dsimp only [dAddr, descBase, count] at *; omega)),
            hp_a.2.2 a (lt_of_lt_of_le hlt ht.1)]
    have hdisj₁ : ∀ i j (hi : i < k + 1) (hj : j < k + 1), i < j →
        st₁.mem (descBase + 4 * i + 2) +
          2 ^ (inst.bagAt ⟨i, lt_of_lt_of_le hi (by omega)⟩).length ≤
          st₁.mem (descBase + 4 * j + 2) := by
      intro i j hi hj hij
      have hi_lt_k : i < k := by omega
      have hmi : st₁.mem (descBase + 4 * i + 2) = st.mem (descBase + 4 * i + 2) := by
        rw [hp_writes _ (.inl (by dsimp only [dAddr]; omega)),
          hp_a.2.2 _ (by dsimp only [descBase, count] at *; omega)]
      rw [hmi]
      by_cases hjk : j = k
      · subst hjk
        rw [hm4_2]
        have hti := (hdone i hi_lt_k).2.2.2.2.2.1
        simpa only [List.length_replicate] using hti
      · have hj_lt_k : j < k := by omega
        have hmj : st₁.mem (descBase + 4 * j + 2) = st.mem (descBase + 4 * j + 2) := by
          rw [hp_writes _ (.inl (by dsimp only [dAddr]; omega)),
            hp_a.2.2 _ (by dsimp only [descBase, count] at *; omega)]
        rw [hmj]
        exact hdisj i j hi_lt_k hj_lt_k hij
    have hc_step : memoryCost (initNodeStep (descBase, ⟨curRaw, k⟩)) st ≤ stepCost := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState st (Memory.read x) = st := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult st (Memory.read x) = st.mem x := rfl
      unfold initNodeStep
      dsimp only
      rw [memoryCost_bind', memoryCost_read, hr_s, hr_r, hmem_len,
        memoryCost_bind', hst_pow, hr_pow,
        memoryCost_bind', memoryCost_alloc]
      change 1 + (memoryCost (powProg ⟨2, bagLen⟩) st +
        ((tblLen + 1) + memoryCost
          (Memory.write dAddr bagPtr >>= fun _ =>
            Memory.write (dAddr + 1) bagLen >>= fun _ =>
            Memory.write (dAddr + 2) tblPtr >>= fun _ =>
            Memory.write (dAddr + 3) tblLen >>= fun _ => pure _) st_a)) ≤ stepCost
      rw [memoryCost_bind', memoryCost_write,
        memoryCost_bind', memoryCost_write,
        memoryCost_bind', memoryCost_write,
        memoryCost_bind', memoryCost_write, memoryCost_pure]
      dsimp only [stepCost]
      omega
    obtain ⟨hv_rem, hprops_rem, hc_rem⟩ :=
      ih (k + 1) (bagPtr + bagLen) st₁ (by omega) (by omega) hfr_next_le hpres₁ hrest_st₁
        (by simp only [List.length_cons, List.length_append] at hdrop_end; omega)
        hdone₁ hdisj₁
    have hiter_eq : iterate initNodeStep descBase (rem + 1) ⟨curRaw, k⟩ =
        (initNodeStep (descBase, ⟨curRaw, k⟩) >>= iterate initNodeStep descBase rem) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step', hres_step']), ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind, hst_step', hres_step']
      exact hprops_rem
    · rw [memoryCost_bind', hst_step', hres_step']
      calc memoryCost (initNodeStep (descBase, ⟨curRaw, k⟩)) st +
            memoryCost (iterate initNodeStep descBase rem ⟨bagPtr + bagLen, k + 1⟩) st₁
          ≤ stepCost + rem * stepCost := Nat.add_le_add hc_step hc_rem
        _ = (rem + 1) * stepCost := by ring

private theorem initNodesProg_realizes :
    Realizes .exact initNodesProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 4 ∧
        ∃ (bags : List (List ℕ)) (M : ℕ),
          bags.length = args.2 ∧
          (∀ B ∈ bags, B.length ≤ M) ∧
          HoldsIn args.1 (bags.flatMap encodeBag) s ∧
          Fits w (s.frontier + 4 * args.2 + args.2 * 2 ^ M))
      (fun _ _ => 0) := by
  unfold initNodesProg
  realize [powProg_realizes]
  · obtain ⟨_, _, _, _, _, _, hfit_peak⟩ := h
    exact hfit_peak.of_le (by omega)
  · exact h.1
  · obtain ⟨h4, bags, M, hbags_len, hbags_M, hraw_h, hfit_peak⟩ := h
    have h1 : Fits w 1 := h4.of_le (by decide)
    have h2 : Fits w 2 := h4.of_le (by decide)
    have h3 : Fits w 3 := h4.of_le (by decide)
    let descBase := s.frontier
    have hdesc_def : descBase = s.frontier := rfl
    let s_d := (Memory.spec 0).clientState s (Memory.allocDirty (4 * d.2))
    have hp_d : PreservesBelow descBase s s_d := preservesBelow_allocDirty s (4 * d.2)
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : InitNodeState) (t : Memory.State) =>
        j ≤ d.2 ∧ st.curIdx + j = d.2 ∧
        descBase + 4 * d.2 ≤ t.frontier ∧
        t.frontier ≤ descBase + 4 * d.2 + st.curIdx * 2 ^ M ∧
        HoldsIn st.curRaw ((bags.drop st.curIdx).flatMap encodeBag) t ∧
        st.curRaw + ((bags.drop st.curIdx).flatMap encodeBag).length ≤ descBase)
      (fun j st t ⟨hj_le, hidx, hfr_lo, hfr_hi, hrem_raw, hrem_end⟩ => ?_)
      ⟨le_rfl, Nat.zero_add _, le_rfl, by simp [descBase],
        by
          dsimp only
          rw [List.drop_zero]
          exact hraw_h.mono_frontier hp_d,
        hraw_h.1⟩
    have hk_lt : st.curIdx < bags.length := by omega
    have hdrop_cons : bags.drop st.curIdx = bags[st.curIdx] :: bags.drop (st.curIdx + 1) :=
      List.drop_eq_getElem_cons hk_lt
    rw [hdrop_cons, List.flatMap_cons, encodeBag, List.cons_append] at hrem_raw hrem_end
    rw [HoldsIn.cons_iff] at hrem_raw
    obtain ⟨_, hmem_len, hafter_len⟩ := hrem_raw
    rw [HoldsIn.append_iff] at hafter_len
    obtain ⟨_, hrest_raw⟩ := hafter_len
    have hblen_le : t.mem st.curRaw ≤ M := by
      rw [hmem_len]
      exact hbags_M _ (List.getElem_mem hk_lt)
    have hpow_le : 2 ^ t.mem st.curRaw ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) hblen_le
    have hfr_next : t.frontier + 2 ^ t.mem st.curRaw ≤
        descBase + 4 * d.2 + (st.curIdx + 1) * 2 ^ M := by
      calc t.frontier + 2 ^ t.mem st.curRaw
          ≤ (descBase + 4 * d.2 + st.curIdx * 2 ^ M) + 2 ^ M := Nat.add_le_add hfr_hi hpow_le
        _ = descBase + 4 * d.2 + (st.curIdx + 1) * 2 ^ M := by ring
    have hpeak_sub : descBase + 4 * d.2 + (st.curIdx + 1) * 2 ^ M ≤
        descBase + 4 * d.2 + d.2 * 2 ^ M := by
      have hle_d2 : st.curIdx + 1 ≤ d.2 := by omega
      have hmul : (st.curIdx + 1) * 2 ^ M ≤ d.2 * 2 ^ M := Nat.mul_le_mul_right _ hle_d2
      omega
    have hpow_safe : Fits w 1 ∧ Fits w (2 ^ t.mem st.curRaw) :=
      ⟨h1, hfit_peak.of_le (by omega)⟩
    have hpow_res : (Memory.spec 0).clientResult t (powProg ⟨2, t.mem st.curRaw⟩) =
        2 ^ t.mem st.curRaw := powProg_result _ t
    simp only [List.length_cons, List.length_append] at hrem_end
    have hfit_bp : Fits w (st.curRaw + 1) := hfit_peak.of_le (by omega)
    have hfit_mul4 : Fits w (4 * st.curIdx) := hfit_peak.of_le (by omega)
    have hfit_d0 : Fits w (descBase + 4 * st.curIdx) := hfit_peak.of_le (by omega)
    have hfit_d1 : Fits w (descBase + 4 * st.curIdx + 1) := hfit_peak.of_le (by omega)
    have hfit_d2 : Fits w (descBase + 4 * st.curIdx + 2) := hfit_peak.of_le (by omega)
    have hfit_d3 : Fits w (descBase + 4 * st.curIdx + 3) := hfit_peak.of_le (by omega)
    have hfit_next_raw : Fits w (st.curRaw + 1 + t.mem st.curRaw) :=
      hfit_peak.of_le (by omega)
    have hfit_next_idx : Fits w (st.curIdx + 1) := hfit_peak.of_le (by omega)
    obtain ⟨hst_ev, hres_ev⟩ := initNodeStep_eval descBase st t
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [initNodeStep]
      repeat (first | exact hpow_safe | assumption | refine And.intro ?_ ?_)
    · rw [hres_ev]; change (st.curIdx + 1) + j = d.2; omega
    · rw [hst_ev]; change descBase + 4 * d.2 ≤ t.frontier + _; omega
    · rw [hst_ev, hres_ev]; exact hfr_next
    · rw [hst_ev, hres_ev]
      change HoldsIn (st.curRaw + 1 + t.mem st.curRaw)
        ((bags.drop (st.curIdx + 1)).flatMap encodeBag) _
      rw [hmem_len]
      refine ⟨hrest_raw.1.trans (Nat.le_add_right _ _), hrest_raw.2.frame fun a _ ha => ?_⟩
      dsimp only
      rw [Function.update_of_ne (by dsimp only [descBase] at *; omega),
        Function.update_of_ne (by dsimp only [descBase] at *; omega),
        Function.update_of_ne (by dsimp only [descBase] at *; omega),
        Function.update_of_ne (by dsimp only [descBase] at *; omega)]
      exact clear_of_not_owns (by dsimp only [Block.Owns, descBase] at *; omega)
    · rw [hres_ev]
      change (st.curRaw + 1 + t.mem st.curRaw) + _ ≤ descBase
      dsimp only [descBase] at *
      omega

private structure ProcessNodesArgs where
  numVerts : ℕ
  adjPtr : ℕ
  wtPtr : ℕ
  parPtr : ℕ
  descBase : ℕ
  numNodes : ℕ

private def ProcessNodesArgs.equiv :
    ProcessNodesArgs ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := (((((a.numVerts, a.adjPtr), a.wtPtr), a.parPtr), a.descBase), a.numNodes)
  invFun := fun (((((nv, ap), wp), pp), db), nn) => ⟨nv, ap, wp, pp, db, nn⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ProcessNodesArgs := .ofEquiv ProcessNodesArgs.equiv

private def processNodeStep (q : ProcessNodesArgs × ℕ) : Memory.Prog ℕ := do
  let a := q.1
  let curNode := q.2
  let p ← Memory.read (a.parPtr + curNode)
  let dJ := a.descBase + 4 * curNode
  let bagBPtr ← Memory.read dJ
  let bagBLen ← Memory.read (dJ + 1)
  let tblBPtr ← Memory.read (dJ + 2)
  let tblBLen ← Memory.read (dJ + 3)
  let dP := a.descBase + 4 * p
  let bagPPtr ← Memory.read dP
  let bagPLen ← Memory.read (dP + 1)
  let tblPPtr ← Memory.read (dP + 2)
  let tblPLen ← Memory.read (dP + 3)
  let bestPtr ← Memory.alloc tblPLen
  let _ ← childPassProg
    ⟨a.numVerts, a.adjPtr, a.wtPtr, bagBPtr, bagBLen, tblBPtr, tblBLen,
      bagPPtr, bagPLen, bestPtr⟩
  let _ ← parentPassProg
    ⟨bagBPtr, bagBLen, bagPPtr, bagPLen, tblPPtr, tblPLen, bestPtr⟩
  pure (curNode - 1)

private def processNodesProg (args : ProcessNodesArgs) : Memory.Prog Unit := do
  let _ ← iterate processNodeStep args args.numNodes args.numNodes
  pure ()

private theorem processNodeStep_eval (a : ProcessNodesArgs) (curNode : ℕ) (t : Memory.State) :
    let p := t.mem (a.parPtr + curNode)
    let dJ := a.descBase + 4 * curNode
    let bagBPtr := t.mem dJ
    let bagBLen := t.mem (dJ + 1)
    let tblBPtr := t.mem (dJ + 2)
    let tblBLen := t.mem (dJ + 3)
    let dP := a.descBase + 4 * p
    let bagPPtr := t.mem dP
    let bagPLen := t.mem (dP + 1)
    let tblPPtr := t.mem (dP + 2)
    let tblPLen := t.mem (dP + 3)
    let bestPtr := t.frontier
    let t_a := (Memory.spec 0).clientState t (Memory.alloc tblPLen)
    let t_c := (Memory.spec 0).clientState t_a
      (childPassProg ⟨a.numVerts, a.adjPtr, a.wtPtr, bagBPtr, bagBLen, tblBPtr, tblBLen,
        bagPPtr, bagPLen, bestPtr⟩)
    let t_p := (Memory.spec 0).clientState t_c
      (parentPassProg ⟨bagBPtr, bagBLen, bagPPtr, bagPLen, tblPPtr, tblPLen, bestPtr⟩)
    (Memory.spec 0).clientState t (processNodeStep (a, curNode)) = t_p ∧
    (Memory.spec 0).clientResult t (processNodeStep (a, curNode)) = curNode - 1 := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold processNodeStep
  dsimp only
  iterate 9 rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    hr_st, hr_res]
  have ha_res : (Memory.spec 0).clientResult t
      (Memory.alloc (t.mem (a.descBase + 4 * t.mem (a.parPtr + curNode) + 3))) = t.frontier := rfl
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, ha_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
  exact ⟨rfl, rfl⟩

private theorem cp_cost_poly_le {bj bp M : ℕ} (hj : bj ≤ M) (hp : bp ≤ M) :
    bj * (2 * bj + 1) + bp * (bj + 1) + bj * (bp + 2) + 3 ≤ 4 * M ^ 2 + 4 * M + 3 := by
  nlinarith

private theorem pp_cost_poly_le {bj bp M : ℕ} (hj : bj ≤ M) (hp : bp ≤ M) :
    bp * (bj + 1) + 3 ≤ M ^ 2 + M + 3 := by
  nlinarith

private theorem step_pow_sum_le {P t : ℕ} (ht : t ≤ P) (M : ℕ) :
    P * (4 * M ^ 2 + 4 * M + 3) + P * (M ^ 2 + M + 3) + t ≤ P * (5 * M ^ 2 + 5 * M + 7) := by
  nlinarith

private theorem rp_cost_poly_le {b0 M : ℕ} (h0 : b0 ≤ M) :
    b0 * (2 * b0 + 1) + b0 * 2 + 1 ≤ 5 * M ^ 2 + 5 * M + 17 := by
  nlinarith

private theorem total_stepBound_le {n M cInit cProc cRp : ℕ} (hP : 1 ≤ 2 ^ M)
    (h1 : cInit ≤ 1 + (n + 1) * (2 ^ M + M + 6))
    (h2 : cProc ≤ n * (10 + 2 ^ M * (5 * M ^ 2 + 5 * M + 7)))
    (h3 : cRp ≤ 2 ^ M * (5 * M ^ 2 + 5 * M + 17)) :
    1 + (1 + (cInit + (cProc + (1 + (1 + (1 + (1 + cRp))))))) ≤
      6 + (n + 1) * (2 ^ M * (5 * M ^ 2 + 6 * M + 32)) := by
  have hInit' : (n + 1) * (2 ^ M + M + 6) ≤ (n + 1) * (2 ^ M * (M + 7)) := by
    refine Nat.mul_le_mul_left (n + 1) ?_
    nlinarith
  have hProc' : n * (10 + 2 ^ M * (5 * M ^ 2 + 5 * M + 7)) ≤
      n * (2 ^ M * (5 * M ^ 2 + 5 * M + 17)) := by
    refine Nat.mul_le_mul_left n ?_
    nlinarith
  calc 1 + (1 + (cInit + (cProc + (1 + (1 + (1 + (1 + cRp)))))))
      ≤ 1 + (1 + ((1 + (n + 1) * (2 ^ M * (M + 7))) +
          (n * (2 ^ M * (5 * M ^ 2 + 5 * M + 17)) +
            (1 + (1 + (1 + (1 + 2 ^ M * (5 * M ^ 2 + 5 * M + 17)))))))) := by omega
    _ = 7 + (n + 1) * (2 ^ M * (5 * M ^ 2 + 6 * M + 24)) := by ring
    _ ≤ 6 + (n + 1) * (2 ^ M * (5 * M ^ 2 + 6 * M + 32)) := by
        have : 1 ≤ (n + 1) * (2 ^ M * 8) := by nlinarith
        linarith

private theorem processNodeStep_full {w : ℕ} (inst : MWISInstance) (descBase : ℕ)
    {a : ProcessNodesArgs}
    (ha : a = ⟨inst.numVerts, 3 + inst.numVerts, 3,
      3 + inst.numVerts + inst.numVerts * inst.numVerts, descBase, inst.numNodes⟩)
    {k : ℕ} (hk : k + 1 ≤ inst.numNodes)
    {tblList : Fin (inst.numNodes + 1) → List ℕ} {t : Memory.State}
    (hlay : NodeLayout inst descBase tblList t)
    (hpfx : prefixMaxSum tblList (k + 1) ≤
      (inst.numNodes - (k + 1)) * (inst.maxBagLen * inst.maxWeight))
    (hfit_fr : Fits w (t.frontier + 2 ^ inst.maxBagLen))
    (hfit_val : Fits w ((inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight)) :
    let jFin : Fin (inst.numNodes + 1) := ⟨k + 1, by omega⟩
    let pFin := inst.parFin jFin
    let bestL := childPassList inst.adj inst.wt (inst.bagAt jFin) (inst.bagAt pFin)
      (tblList jFin) (List.replicate (2 ^ (inst.bagAt pFin).length) 0)
      (2 ^ (inst.bagAt jFin).length)
    let newTblP := parentPassPrefix (inst.bagAt jFin) (inst.bagAt pFin)
      (tblList pFin) bestL (2 ^ (inst.bagAt pFin).length)
    let tblList' := Function.update tblList pFin newTblP
    let t' := (Memory.spec 0).clientState t (processNodeStep (a, k + 1))
    (Memory.spec w).ValidHistory t
      ((Memory.spec w).clientHistory t (processNodeStep (a, k + 1))) ∧
    (Memory.spec 0).clientResult t (processNodeStep (a, k + 1)) = k ∧
    t'.frontier ≤ t.frontier + 2 ^ inst.maxBagLen ∧
    NodeLayout inst descBase tblList' t' ∧
    prefixMaxSum tblList' k ≤ (inst.numNodes - k) * (inst.maxBagLen * inst.maxWeight) ∧
    memoryCost (processNodeStep (a, k + 1)) t ≤
      10 + 2 ^ inst.maxBagLen * (5 * inst.maxBagLen ^ 2 + 5 * inst.maxBagLen + 7) := by
  subst ha
  let a : ProcessNodesArgs := ⟨inst.numVerts, 3 + inst.numVerts, 3,
    3 + inst.numVerts + inst.numVerts * inst.numVerts, descBase, inst.numNodes⟩
  let m := inst.numVerts
  let n := inst.numNodes
  let M := inst.maxBagLen
  let W := inst.maxWeight
  let B := M * W
  have hm_def : m = inst.numVerts := rfl
  have hn_def : n = inst.numNodes := rfl
  have hM_def : M = inst.maxBagLen := rfl
  have hW_def : W = inst.maxWeight := rfl
  have hB_def : B = M * W := rfl
  let jFin : Fin (inst.numNodes + 1) := ⟨k + 1, by omega⟩
  have hj_val : jFin.val = k + 1 := rfl
  let pFin := inst.parFin jFin
  have hp_idx : k + 1 < inst.parents.length := by rw [inst.parents_len]; omega
  have hp_lt : pFin.val < k + 1 := by
    dsimp only [pFin, MWISInstance.parFin, jFin]
    rw [dite_eq_left (by omega)]
    exact inst.parents_lt ⟨k + 1, hp_idx⟩ (by omega)
  have hp_read :
      t.mem (3 + inst.numVerts + inst.numVerts * inst.numVerts + (k + 1)) = pFin.val := by
    dsimp only [pFin, MWISInstance.parFin, jFin]
    rw [dite_eq_left (by omega), hlay.par_holds.get (k + 1) hp_idx]
    rfl
  obtain ⟨hj_len_m, hj_pow_m, hj_blo, hj_bag⟩ := hlay.bags_holds jFin
  rw [hj_val] at hj_len_m hj_pow_m hj_blo
  obtain ⟨hj_tlen, hj_tlo, hj_tbl⟩ := hlay.tbl_holds jFin
  obtain ⟨hp_len_m, hp_pow_m, hp_blo, hp_bag⟩ := hlay.bags_holds pFin
  obtain ⟨hp_tlen, hp_tlo, hp_tbl⟩ := hlay.tbl_holds pFin
  have hj_len_le : (inst.bagAt jFin).length ≤ M := inst.bagAt_length_le jFin
  have hp_len_le : (inst.bagAt pFin).length ≤ M := inst.bagAt_length_le pFin
  have hj_pow_le : 2 ^ (inst.bagAt jFin).length ≤ 2 ^ M :=
    Nat.pow_le_pow_right (by decide) hj_len_le
  have hp_pow_le : 2 ^ (inst.bagAt pFin).length ≤ 2 ^ M :=
    Nat.pow_le_pow_right (by decide) hp_len_le
  let tblPLen := 2 ^ (inst.bagAt pFin).length
  let bestPtr := t.frontier
  have htblPLen_def : tblPLen = 2 ^ (inst.bagAt pFin).length := rfl
  have hbestPtr_def : bestPtr = t.frontier := rfl
  let t_a := (Memory.spec 0).clientState t (Memory.alloc tblPLen)
  have ht_a_fr : t_a.frontier = t.frontier + tblPLen := rfl
  have hp_a : PreservesBelow t.frontier t t_a := preservesBelow_alloc t tblPLen
  have hlay_a : NodeLayout inst descBase tblList t_a := hlay.mono_frontier hp_a
  have hbest_init : HoldsIn bestPtr (List.replicate tblPLen 0) t_a :=
    holdsIn_alloc_zero t tblPLen
  have hfit_alloc : Fits w (t.frontier + tblPLen) := hfit_fr.of_le (by
    dsimp only [tblPLen, M] at hp_pow_le ⊢; omega)
  have hv_alloc : (Memory.spec w).ValidHistory t
      ((Memory.spec w).clientHistory t (Memory.alloc tblPLen)) :=
    validHistory_alloc hfit_alloc
  let capB := B + (tblList jFin).foldl max 0
  let capO := (tblList pFin).foldl max 0
  have hcapB_def : capB = B + (tblList jFin).foldl max 0 := rfl
  have hcapO_def : capO = (tblList pFin).foldl max 0 := rfl
  have hsum_split : prefixMaxSum tblList (k + 1) =
      prefixMaxSum tblList k + (tblList jFin).foldl max 0 := by
    unfold prefixMaxSum
    rw [Finset.sum_range_succ]
    unfold nodeMax
    rw [dite_eq_left jFin.isLt]
  have hcapO_le : capO ≤ prefixMaxSum tblList k :=
    foldl_max_le_prefixMaxSum tblList pFin (by omega)
  have hsum_caps_le : capO + capB ≤ (n + 1) * M * W := by
    have hcb : capO + capB ≤ prefixMaxSum tblList (k + 1) + B := by
      dsimp only [capO, capB] at hcapO_le ⊢
      omega
    calc capO + capB
        ≤ prefixMaxSum tblList (k + 1) + B := hcb
      _ ≤ (inst.numNodes - (k + 1)) * B + B := Nat.add_le_add_right hpfx B
      _ = (inst.numNodes - (k + 1) + 1) * B := by ring
      _ ≤ (n + 1) * B := Nat.mul_le_mul_right B (by dsimp only [n]; omega)
      _ = (n + 1) * M * W := by dsimp only [B]; ring
  have hfit_capB : Fits w capB := hfit_val.of_le (by
    dsimp only [n, M, W] at hsum_caps_le; omega)
  have hfit_sum : Fits w (capO + capB) := hfit_val.of_le (by
    dsimp only [n, M, W] at hsum_caps_le; exact hsum_caps_le)
  have hcand_le : ∀ mask < 2 ^ (inst.bagAt jFin).length,
      forgetWeight inst.wt (inst.bagAt pFin) (inst.bagAt jFin) mask +
        (tblList jFin).getD mask 0 ≤ capB := fun mask _ => by
    have hfw := forgetWeight_le_mul_maxWeight inst (inst.bagAt pFin) (inst.bagAt jFin) mask
      (inst.bagAt_mem_lt jFin)
    have hfw_B : (inst.bagAt jFin).length * W ≤ B := Nat.mul_le_mul_right W hj_len_le
    have hfc : (tblList jFin).getD mask 0 ≤ (tblList jFin).foldl max 0 := by
      rw [List.getD_eq_getElem?_getD]
      cases hget : (tblList jFin)[mask]? with
      | none => exact Nat.zero_le _
      | some v => exact List.mem_le_foldl_max (List.mem_of_getElem? hget)
    dsimp only [capB, B, W, M] at hfw_B ⊢
    omega
  let cpArgs : ChildPassArgs :=
    ⟨m, 3 + m, 3, t.mem (descBase + 4 * jFin.val), (inst.bagAt jFin).length,
      t.mem (descBase + 4 * jFin.val + 2), 2 ^ (inst.bagAt jFin).length,
      t.mem (descBase + 4 * pFin.val), (inst.bagAt pFin).length, bestPtr⟩
  have hcp_spec := childPassProg_spec (w := w) cpArgs (inst := inst)
    (LB := inst.bagAt jFin) (LP := inst.bagAt pFin)
    (tblB := tblList jFin) (initL := List.replicate tblPLen 0) (cap := capB) (s := t_a)
    hlay_a.adj_holds hlay.adj_holds.1
    hlay_a.wt_holds hlay.wt_holds.1
    rfl
    (hj_bag.mono_frontier hp_a) rfl (hj_blo.trans (le_trans (by omega) hlay.desc_hi))
    (inst.bagAt_mem_lt jFin)
    (hj_tbl.mono_frontier hp_a) hj_tlen (by simpa only [hj_tlen] using hj_tbl.1)
    (hp_bag.mono_frontier hp_a) rfl (hp_blo.trans (le_trans (by omega) hlay.desc_hi))
    hbest_init List.length_replicate
    (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact Nat.zero_le _)
    hcand_le hfit_capB
  obtain ⟨hv_cp, hfr_cp, hp_cp, hbest_cp, hc_cp⟩ := hcp_spec
  let t_c := (Memory.spec 0).clientState t_a (childPassProg cpArgs)
  have hlay_c : NodeLayout inst descBase tblList t_c :=
    hlay.mono_frontier (hp_a.trans hp_cp)
  let bestL := childPassList inst.adj inst.wt (inst.bagAt jFin) (inst.bagAt pFin)
    (tblList jFin) (List.replicate tblPLen 0) (2 ^ (inst.bagAt jFin).length)
  have hbestL_le : ∀ x ∈ bestL, x ≤ capB :=
    mem_childPassList_le
      (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact Nat.zero_le _) hcand_le
  have hbestL_len : bestL.length = tblPLen := by
    rw [length_childPassList, List.length_replicate]
  have hp_mem_c (off : ℕ) (hoff : off < 4) :
      t_c.mem (descBase + 4 * pFin.val + off) = t.mem (descBase + 4 * pFin.val + off) :=
    (hp_a.trans hp_cp).2.2 _ (by have := hlay.desc_hi; have := pFin.isLt; omega)
  have hj_mem_c (off : ℕ) (hoff : off < 4) :
      t_c.mem (descBase + 4 * jFin.val + off) = t.mem (descBase + 4 * jFin.val + off) :=
    (hp_a.trans hp_cp).2.2 _ (by have := hlay.desc_hi; have := jFin.isLt; omega)
  let ppArgs : ParentPassArgs :=
    ⟨t.mem (descBase + 4 * jFin.val), (inst.bagAt jFin).length,
      t.mem (descBase + 4 * pFin.val), (inst.bagAt pFin).length,
      t.mem (descBase + 4 * pFin.val + 2), tblPLen, bestPtr⟩
  have hpp_spec := parentPassProg_spec (w := w) ppArgs
    (LB := inst.bagAt jFin) (LP := inst.bagAt pFin)
    (oldL := tblList pFin) (bestL := bestL) (capO := capO) (capB := capB) (s := t_c)
    (hj_bag.mono_frontier (hp_a.trans hp_cp)) rfl
    (by dsimp only [ppArgs]; rw [hj_val] at *; exact hj_blo.trans (le_trans (by omega) hp_tlo))
    (hp_bag.mono_frontier (hp_a.trans hp_cp)) rfl
    (by dsimp only [ppArgs]; exact hp_blo.trans (le_trans (by omega) hp_tlo))
    (hp_tbl.mono_frontier (hp_a.trans hp_cp)) hp_tlen rfl
    (by simpa only [hp_tlen] using hp_tbl.1)
    hbest_cp hbestL_len
    (fun x hx => List.mem_le_foldl_max hx) hbestL_le hfit_sum
  obtain ⟨hv_pp, hfr_pp, hout_pp, hpfx_pp, hc_pp⟩ := hpp_spec
  let t_p := (Memory.spec 0).clientState t_c (parentPassProg ppArgs)
  obtain ⟨hst_ev, hres_ev⟩ := processNodeStep_eval a (k + 1) t
  have hst_eq : (Memory.spec 0).clientState t (processNodeStep (a, k + 1)) = t_p := by
    rw [hst_ev]
    dsimp only [a, m, n, t_p, t_c, t_a, ppArgs, cpArgs, tblPLen, bestPtr, jFin]
    rw [hp_read, hj_len_m, hj_pow_m, hp_len_m, hp_pow_m]
  have hlay_p : NodeLayout inst descBase
      (Function.update tblList pFin
        (parentPassPrefix (inst.bagAt jFin) (inst.bagAt pFin) (tblList pFin) bestL tblPLen))
      t_p := by
    have hout_p' : ∀ addr,
        (addr < t_c.mem (descBase + 4 * pFin.val + 2) ∨
          t_c.mem (descBase + 4 * pFin.val + 2) + tblPLen ≤ addr) →
        t_p.mem addr = t_c.mem addr := by
      rw [hp_mem_c 2 (by decide)]
      exact hout_pp
    have hholdP' : HoldsIn (t_c.mem (descBase + 4 * pFin.val + 2))
        (parentPassPrefix (inst.bagAt jFin) (inst.bagAt pFin) (tblList pFin) bestL tblPLen)
        t_p := by
      rw [hp_mem_c 2 (by decide)]
      exact hpfx_pp
    exact hlay_c.update_table pFin _ (by rw [length_parentPassPrefix, hp_tlen])
      hfr_pp hout_p' hholdP'
  have hnewP_max :
      (parentPassPrefix (inst.bagAt jFin) (inst.bagAt pFin) (tblList pFin) bestL tblPLen).foldl
        max 0 ≤ (tblList pFin).foldl max 0 + B + (tblList jFin).foldl max 0 := by
    refine (List.foldl_max_le (Nat.zero_le _)
      (mem_parentPassPrefix_le (fun x hx => List.mem_le_foldl_max (a := 0) hx) hbestL_le)).trans ?_
    rw [hcapB_def]
    omega
  have hpfx_next : prefixMaxSum
      (Function.update tblList pFin
        (parentPassPrefix (inst.bagAt jFin) (inst.bagAt pFin) (tblList pFin) bestL tblPLen))
      k ≤ (n - k) * B := by
    have hstep := prefixMaxSum_update_le tblList hk pFin hp_lt _ hnewP_max
    have hsub_n : n - (k + 1) + 1 = n - k := by omega
    calc prefixMaxSum _ k
        ≤ prefixMaxSum tblList (k + 1) + B := hstep
      _ ≤ (n - (k + 1)) * B + B := Nat.add_le_add_right hpfx B
      _ = (n - (k + 1) + 1) * B := by ring
      _ = (n - k) * B := by rw [hsub_n]
  have hv_step : (Memory.spec w).ValidHistory t
      ((Memory.spec w).clientHistory t (processNodeStep (a, k + 1))) := by
    have hpar_lt : a.parPtr + (k + 1) < t.frontier := by
      have := hlay.par_holds.1
      rw [inst.parents_len] at this
      dsimp only [a]; omega
    have hdJ_lt (off : ℕ) (hoff : off < 4) : descBase + 4 * (k + 1) + off < t.frontier := by
      have := hlay.desc_hi; omega
    have hdP_lt (off : ℕ) (hoff : off < 4) : descBase + 4 * pFin.val + off < t.frontier := by
      have := hlay.desc_hi; have := pFin.isLt; omega
    unfold processNodeStep
    dsimp only
    refine validHistory_read_bind hpar_lt ?_
    rw [hp_read]
    refine validHistory_read_bind (by simpa only [Nat.add_zero] using hdJ_lt 0 (by decide)) ?_
    refine validHistory_read_bind (hdJ_lt 1 (by decide)) ?_
    refine validHistory_read_bind (hdJ_lt 2 (by decide)) ?_
    refine validHistory_read_bind (hdJ_lt 3 (by decide)) ?_
    refine validHistory_read_bind (by simpa only [Nat.add_zero] using hdP_lt 0 (by decide)) ?_
    refine validHistory_read_bind (hdP_lt 1 (by decide)) ?_
    refine validHistory_read_bind (hdP_lt 2 (by decide)) ?_
    refine validHistory_read_bind (hdP_lt 3 (by decide)) ?_
    rw [hj_len_m, hj_pow_m, hp_len_m, hp_pow_m]
    refine validHistory_bind_step hv_alloc ?_
    have ha_st : (Memory.spec 0).clientState t (Memory.alloc tblPLen) = t_a := rfl
    have ha_res : (Memory.spec 0).clientResult t (Memory.alloc tblPLen) = bestPtr := rfl
    rw [ha_st, ha_res]
    refine validHistory_bind_step hv_cp ?_
    exact validHistory_bind_step hv_pp (validHistory_pure w _ _)
  have hc_step : memoryCost (processNodeStep (a, k + 1)) t ≤
      10 + 2 ^ M * (5 * M ^ 2 + 5 * M + 7) := by
    have hr_s (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
    have hr_r (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
    unfold processNodeStep
    dsimp only
    iterate 9 rw [memoryCost_bind', memoryCost_read, hr_s, hr_r]
    rw [hp_read, hj_len_m, hj_pow_m, hp_len_m, hp_pow_m]
    have ha_st : (Memory.spec 0).clientState t (Memory.alloc tblPLen) = t_a := rfl
    have ha_res : (Memory.spec 0).clientResult t (Memory.alloc tblPLen) = bestPtr := rfl
    rw [memoryCost_bind', memoryCost_alloc, ha_st, ha_res,
      memoryCost_bind', memoryCost_bind', memoryCost_pure, Nat.add_zero]
    dsimp only [cpArgs] at hc_cp
    dsimp only [ppArgs] at hc_pp
    have hc_cp_M : memoryCost (childPassProg cpArgs) t_a ≤
        2 ^ M * (4 * M ^ 2 + 4 * M + 3) :=
      hc_cp.trans (Nat.mul_le_mul hj_pow_le (cp_cost_poly_le hj_len_le hp_len_le))
    have hc_pp_M : memoryCost (parentPassProg ppArgs) t_c ≤
        2 ^ M * (M ^ 2 + M + 3) :=
      hc_pp.trans (Nat.mul_le_mul hp_pow_le (pp_cost_poly_le hj_len_le hp_len_le))
    have hsum_pow : 2 ^ M * (4 * M ^ 2 + 4 * M + 3) + 2 ^ M * (M ^ 2 + M + 3) + tblPLen ≤
        2 ^ M * (5 * M ^ 2 + 5 * M + 7) :=
      step_pow_sum_le hp_pow_le M
    change 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + ((tblPLen + 1) +
      (memoryCost (childPassProg cpArgs) t_a +
        memoryCost (parentPassProg ppArgs) t_c)))))))))) ≤ _
    omega
  refine ⟨hv_step, ?_, ?_, ?_, hpfx_next, hc_step⟩
  · rw [hres_ev]; omega
  · rw [hst_eq, hfr_pp, hfr_cp]
    change t.frontier + tblPLen ≤ t.frontier + 2 ^ M
    omega
  · rwa [hst_eq]

private theorem processNodesProg_spec {w : ℕ} (inst : MWISInstance) (descBase : ℕ)
    {s₁ : Memory.State}
    (hlay₁ : NodeLayout inst descBase
      (fun i => List.replicate (2 ^ (inst.bagAt i).length) 0) s₁)
    (hfit_peak : Fits w (s₁.frontier + inst.numNodes * 2 ^ inst.maxBagLen))
    (hfit_val : Fits w ((inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight)) :
    let m := inst.numVerts
    let n := inst.numNodes
    let M := inst.maxBagLen
    let args : ProcessNodesArgs := ⟨m, 3 + m, 3, 3 + m + m * m, descBase, n⟩
    let s₂ := (Memory.spec 0).clientState s₁ (processNodesProg args)
    (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (processNodesProg args)) ∧
    s₂.frontier ≤ s₁.frontier + n * 2 ^ M ∧
    (∃ tblFinal : Fin (n + 1) → List ℕ,
      NodeLayout inst descBase tblFinal s₂ ∧
      prefixMaxSum tblFinal 0 ≤ n * (M * inst.maxWeight) ∧
      (∀ i : Fin (n + 1), ∀ s < 2 ^ (inst.bagAt i).length,
        (tblFinal i).getD s 0 =
          (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt n)[i].getD s 0)) ∧
    memoryCost (processNodesProg args) s₁ ≤
      n * (10 + 2 ^ M * (5 * M ^ 2 + 5 * M + 7)) := by
  let m := inst.numVerts
  let n := inst.numNodes
  let M := inst.maxBagLen
  let B := M * inst.maxWeight
  let args : ProcessNodesArgs := ⟨m, 3 + m, 3, 3 + m + m * m, descBase, n⟩
  let stepCost := 10 + 2 ^ M * (5 * M ^ 2 + 5 * M + 7)
  have hm_def : m = inst.numVerts := rfl
  have hn_def : n = inst.numNodes := rfl
  have hM_def : M = inst.maxBagLen := rfl
  have hB_def : B = M * inst.maxWeight := rfl
  have hstepCost_def : stepCost = 10 + 2 ^ M * (5 * M ^ 2 + 5 * M + 7) := rfl
  suffices ∀ k st (tblList : Fin (n + 1) → List ℕ),
      k ≤ n →
      st.frontier ≤ s₁.frontier + (n - k) * 2 ^ M →
      NodeLayout inst descBase tblList st →
      prefixMaxSum tblList k ≤ (n - k) * B →
      (∀ i : Fin (n + 1), ∀ s < 2 ^ (inst.bagAt i).length,
        (tblList i).getD s 0 =
          (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt (n - k))[i].getD s 0) →
      (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (iterate processNodeStep args k k)) ∧
      (let sEnd := (Memory.spec 0).clientState st (iterate processNodeStep args k k)
       sEnd.frontier ≤ s₁.frontier + n * 2 ^ M ∧
       ∃ tblFinal : Fin (n + 1) → List ℕ,
         NodeLayout inst descBase tblFinal sEnd ∧
         prefixMaxSum tblFinal 0 ≤ n * B ∧
         (∀ i : Fin (n + 1), ∀ s < 2 ^ (inst.bagAt i).length,
           (tblFinal i).getD s 0 =
             (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt n)[i].getD s 0)) ∧
      memoryCost (iterate processNodeStep args k k) st ≤ k * stepCost by
    have hrun := this n s₁ (fun i => List.replicate (2 ^ (inst.bagAt i).length) 0) le_rfl
      (by simp) hlay₁
      (by rw [prefixMaxSum_replicate_zero]; simp)
      (fun i s hs => by
        simp [tablesInst, List.getD_eq_getElem?_getD,
          Array.getD_eq_getD_getElem?, hs])
    obtain ⟨hv_l, ⟨hfr_l, hfin_l⟩, hc_l⟩ := hrun
    unfold processNodesProg
    refine ⟨validHistory_bind_step hv_l (validHistory_pure w _ ()), ?_, ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind]; exact hfr_l
    · rw [StateTransitionSpec.clientState_bind]; exact hfin_l
    · rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]; exact hc_l
  intro k
  induction k with
  | zero =>
    intro st tblList _ hfr hlay hpfx hagree
    have h0 : iterate processNodeStep args 0 0 = pure 0 := rfl
    rw [h0]
    simp only [Nat.sub_zero] at hfr hpfx hagree
    exact ⟨validHistory_pure w st 0, ⟨hfr, tblList, hlay, hpfx, hagree⟩,
      by simp [memoryCost_pure]⟩
  | succ k ih =>
    intro st tblList hk hfr hlay hpfx hagree
    have hfr_sub : st.frontier + 2 ^ M ≤ s₁.frontier + (n - k) * 2 ^ M := by
      have hsub : n - (k + 1) + 1 = n - k := by omega
      calc st.frontier + 2 ^ M
          ≤ (s₁.frontier + (n - (k + 1)) * 2 ^ M) + 2 ^ M := Nat.add_le_add_right hfr _
        _ = s₁.frontier + (n - (k + 1) + 1) * 2 ^ M := by ring
        _ = s₁.frontier + (n - k) * 2 ^ M := by rw [hsub]
    have hfit_fr : Fits w (st.frontier + 2 ^ M) := hfit_peak.of_le (by
      have hmul : (n - k) * 2 ^ M ≤ n * 2 ^ M := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      dsimp only [n, M] at hfr_sub hmul ⊢
      omega)
    obtain ⟨hv_step, hres_step, hfr_step, hlay_next, hpfx_next, hc_step⟩ :=
      processNodeStep_full (w := w) inst descBase rfl hk hlay hpfx hfit_fr hfit_val
    let jFin : Fin (n + 1) := ⟨k + 1, by omega⟩
    let pFin := inst.parFin jFin
    let bestL := childPassList inst.adj inst.wt (inst.bagAt jFin) (inst.bagAt pFin)
      (tblList jFin) (List.replicate (2 ^ (inst.bagAt pFin).length) 0)
      (2 ^ (inst.bagAt jFin).length)
    let newTblP := parentPassPrefix (inst.bagAt jFin) (inst.bagAt pFin)
      (tblList pFin) bestL (2 ^ (inst.bagAt pFin).length)
    let tblList' := Function.update tblList pFin newTblP
    have hagree_next : ∀ i : Fin (n + 1), ∀ s < 2 ^ (inst.bagAt i).length,
        (tblList' i).getD s 0 =
          (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt (n - k))[i].getD s 0 := by
      intro i s hs
      have hsub_t : n - k = (n - (k + 1)) + 1 := by omega
      have hj_ofNat : Fin.ofNat (n + 1) (n - (n - (k + 1))) = jFin := by
        apply Fin.ext
        rw [Fin.val_ofNat]
        have h1 : n - (n - (k + 1)) = k + 1 := by omega
        rw [h1, Nat.mod_eq_of_lt (by omega)]
      rw [hsub_t]
      simp only [tablesInst, hj_ofNat, processInstNode]
      by_cases hip : i = pFin
      · subst hip
        dsimp only [tblList']
        rw [Function.update_self, Fin.getElem_fin, Vector.getElem_set_self,
          getD_parentPass_raw _ _ _ _ hs]
        have hp_len : (tblList pFin).length = 2 ^ (inst.bagAt pFin).length :=
          (hlay.tbl_holds pFin).1
        have hs_lt_old : s < (tblList pFin).length := by omega
        have hpfx_get : newTblP.getD s 0 =
            (tblList pFin)[s] +
              bestL.getD (restrictMask (inst.bagAt jFin) (inst.bagAt pFin) s) 0 := by
          have hs_pfx : s < newTblP.length := by
            dsimp only [newTblP]
            rw [length_parentPassPrefix]; exact hs_lt_old
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs_pfx, Option.getD_some]
          dsimp only [newTblP]
          simp only [parentPassPrefix, List.getElem_ofFn, hs, ↓reduceIte, Fin.getElem_fin]
        rw [hpfx_get]
        have hold_eq : (tblList pFin)[s] =
            (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt
              (n - (k + 1)))[pFin].getD s 0 := by
          rw [← hagree pFin s hs, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hs_lt_old, Option.getD_some]
        have hrk_lt : restrictMask (inst.bagAt jFin) (inst.bagAt pFin) s <
            2 ^ (inst.bagAt pFin).length := restrictMask_lt_two_pow _ _ s
        have hbest_eq : bestL.getD (restrictMask (inst.bagAt jFin) (inst.bagAt pFin) s) 0 =
            (childPassInst inst.adj inst.wt (inst.bagAt jFin) (inst.bagAt pFin)
              (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt (n - (k + 1)))[jFin]
              (Array.replicate (2 ^ (inst.bagAt pFin).length) 0)
              (2 ^ (inst.bagAt jFin).length)).getD
              (restrictMask (inst.bagAt jFin) (inst.bagAt pFin) s) 0 :=
          getD_childPassList_eq inst.adj inst.wt (inst.bagAt jFin) (inst.bagAt pFin)
            (tblList jFin) _ (2 ^ (inst.bagAt jFin).length) (hagree jFin) _ hrk_lt
        rw [hold_eq, hbest_eq]
      · dsimp only [tblList']
        rw [Function.update_of_ne hip, Fin.getElem_fin,
          Vector.getElem_set_ne _ _ (fun h => hip (Fin.ext h).symm)]
        exact hagree i s hs
    let st₁ := (Memory.spec 0).clientState st (processNodeStep (args, k + 1))
    obtain ⟨hv_rem, hprops_rem, hc_rem⟩ :=
      ih st₁ tblList' (by omega) (hfr_step.trans hfr_sub) hlay_next hpfx_next hagree_next
    have hiter_eq : iterate processNodeStep args (k + 1) (k + 1) =
        (processNodeStep (args, k + 1) >>= iterate processNodeStep args k) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hres_step]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind, hres_step]; exact hprops_rem
    · rw [memoryCost_bind', hres_step]
      calc memoryCost (processNodeStep (args, k + 1)) st +
            memoryCost (iterate processNodeStep args k k) st₁
          ≤ stepCost + k * stepCost := Nat.add_le_add hc_step hc_rem
        _ = (k + 1) * stepCost := by ring

private theorem processNodesProg_realizes :
    Realizes .exact processNodesProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 4 ∧
        ∃ (inst : MWISInstance) (tblList : Fin (inst.numNodes + 1) → List ℕ),
          args.numVerts = inst.numVerts ∧
          args.adjPtr = 3 + inst.numVerts ∧
          args.wtPtr = 3 ∧
          args.parPtr = 3 + inst.numVerts + inst.numVerts * inst.numVerts ∧
          args.numNodes = inst.numNodes ∧
          NodeLayout inst args.descBase tblList s ∧
          prefixMaxSum tblList inst.numNodes = 0 ∧
          Fits w (s.frontier + inst.numNodes * 2 ^ inst.maxBagLen) ∧
          Fits w ((inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight))
      (fun _ _ => 0) := by
  unfold processNodesProg
  realize [childPassProg_realizes, parentPassProg_realizes]
  obtain ⟨h4, inst, tblInit, hnv, hadjP, hwtP, hparP, hnn, hlay₀, hpfx₀, hfit_peak, hfit_val⟩ := h
  have h1 : Fits w 1 := h4.of_le (by decide)
  have h2 : Fits w 2 := h4.of_le (by decide)
  have h3 : Fits w 3 := h4.of_le (by decide)
  have hd_eq : d = ⟨inst.numVerts, 3 + inst.numVerts, 3,
      3 + inst.numVerts + inst.numVerts * inst.numVerts, d.descBase, inst.numNodes⟩ := by
    cases d
    dsimp only at hnv hadjP hwtP hparP hnn
    subst hnv hadjP hwtP hparP hnn
    rfl
  let M := inst.maxBagLen
  let B := M * inst.maxWeight
  have hM_def : M = inst.maxBagLen := rfl
  have hB_def : B = M * inst.maxWeight := rfl
  refine iterationSafe_of_stepInv _ _ w d
    (fun (j : ℕ) (curNode : ℕ) (t : Memory.State) =>
      j ≤ inst.numNodes ∧ curNode = j ∧
      t.frontier ≤ s.frontier + (inst.numNodes - j) * 2 ^ M ∧
      ∃ tblList : Fin (inst.numNodes + 1) → List ℕ,
        NodeLayout inst d.descBase tblList t ∧
        prefixMaxSum tblList j ≤ (inst.numNodes - j) * B)
    (fun j curNode t ⟨hj_le, hcur_eq, hfr_t, tblList, hlay_t, hpfx_t⟩ => ?_)
    ⟨by rw [hnn], rfl, by rw [hnn]; simp, tblInit, hlay₀, by rw [hnn, hpfx₀]; simp⟩
  subst hcur_eq
  have hfr_sub : t.frontier + 2 ^ M ≤ s.frontier + (inst.numNodes - j) * 2 ^ M := by
    have hsub : inst.numNodes - (j + 1) + 1 = inst.numNodes - j := by omega
    calc t.frontier + 2 ^ M
        ≤ (s.frontier + (inst.numNodes - (j + 1)) * 2 ^ M) + 2 ^ M := Nat.add_le_add_right hfr_t _
      _ = s.frontier + (inst.numNodes - (j + 1) + 1) * 2 ^ M := by ring
      _ = s.frontier + (inst.numNodes - j) * 2 ^ M := by rw [hsub]
  have hfit_fr : Fits w (t.frontier + 2 ^ M) := hfit_peak.of_le (by
    have hmul : (inst.numNodes - j) * 2 ^ M ≤ inst.numNodes * 2 ^ M :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    dsimp only [M] at hfr_sub hmul ⊢
    omega)
  obtain ⟨_, hres_s, hfr_s, hlay_s, hpfx_s, _⟩ :=
    processNodeStep_full (w := w) inst d.descBase hd_eq hj_le hlay_t hpfx_t hfit_fr hfit_val
  let jFin : Fin (inst.numNodes + 1) := ⟨j + 1, by omega⟩
  have hj_val : jFin.val = j + 1 := rfl
  let pFin := inst.parFin jFin
  have hp_idx : j + 1 < inst.parents.length := by rw [inst.parents_len]; omega
  have hp_read : t.mem (d.parPtr + (j + 1)) = pFin.val := by
    rw [hparP]
    dsimp only [pFin, MWISInstance.parFin, jFin]
    rw [dite_eq_left (by omega), hlay_t.par_holds.get (j + 1) hp_idx]
    rfl
  obtain ⟨hj_len_m, hj_pow_m, hj_blo, hj_bag⟩ := hlay_t.bags_holds jFin
  obtain ⟨hj_tlen, _, hj_tbl⟩ := hlay_t.tbl_holds jFin
  rw [hj_val] at hj_len_m hj_pow_m hj_blo hj_bag hj_tbl
  obtain ⟨hp_len_m, hp_pow_m, hp_blo, hp_bag⟩ := hlay_t.bags_holds pFin
  obtain ⟨hp_tlen, _, hp_tbl⟩ := hlay_t.tbl_holds pFin
  have hj_len_le : (inst.bagAt jFin).length ≤ M := inst.bagAt_length_le jFin
  have hp_len_le : (inst.bagAt pFin).length ≤ M := inst.bagAt_length_le pFin
  have hj_pow_le : 2 ^ (inst.bagAt jFin).length ≤ 2 ^ M :=
    Nat.pow_le_pow_right (by decide) hj_len_le
  have hp_pow_le : 2 ^ (inst.bagAt pFin).length ≤ 2 ^ M :=
    Nat.pow_le_pow_right (by decide) hp_len_le
  let tblPLen := 2 ^ (inst.bagAt pFin).length
  let bestPtr := t.frontier
  have htblPLen_def : tblPLen = 2 ^ (inst.bagAt pFin).length := rfl
  have hbestPtr_def : bestPtr = t.frontier := rfl
  let t_a := (Memory.spec 0).clientState t (Memory.alloc tblPLen)
  have ht_a_fr : t_a.frontier = t.frontier + tblPLen := rfl
  have hp_a : PreservesBelow t.frontier t t_a := preservesBelow_alloc t tblPLen
  have hlay_a : NodeLayout inst d.descBase tblList t_a := hlay_t.mono_frontier hp_a
  let capB := B + (tblList jFin).foldl max 0
  let capO := (tblList pFin).foldl max 0
  have hcapB_def : capB = B + (tblList jFin).foldl max 0 := rfl
  have hcapO_def : capO = (tblList pFin).foldl max 0 := rfl
  have hp_lt : pFin.val < j + 1 := by
    dsimp only [pFin, MWISInstance.parFin, jFin]
    rw [dite_eq_left (by omega)]
    exact inst.parents_lt ⟨j + 1, hp_idx⟩ (by omega)
  have hsum_split : prefixMaxSum tblList (j + 1) =
      prefixMaxSum tblList j + (tblList jFin).foldl max 0 := by
    unfold prefixMaxSum
    rw [Finset.sum_range_succ]
    unfold nodeMax
    rw [dite_eq_left jFin.isLt]
  have hcapO_le : capO ≤ prefixMaxSum tblList j :=
    foldl_max_le_prefixMaxSum tblList pFin (by omega)
  have hsum_caps_le : capO + capB ≤ (inst.numNodes + 1) * M * inst.maxWeight := by
    have hcb : capO + capB ≤ prefixMaxSum tblList (j + 1) + B := by
      dsimp only [capO, capB] at hcapO_le ⊢; omega
    calc capO + capB
        ≤ prefixMaxSum tblList (j + 1) + B := hcb
      _ ≤ (inst.numNodes - (j + 1)) * B + B := Nat.add_le_add_right hpfx_t B
      _ = (inst.numNodes - (j + 1) + 1) * B := by ring
      _ ≤ (inst.numNodes + 1) * B := Nat.mul_le_mul_right B (by omega)
      _ = (inst.numNodes + 1) * M * inst.maxWeight := by dsimp only [B]; ring
  have hfit_capB : Fits w capB := hfit_val.of_le (by
    dsimp only [M] at hsum_caps_le; omega)
  have hfit_sum : Fits w (capO + capB) := hfit_val.of_le (by
    dsimp only [M] at hsum_caps_le; exact hsum_caps_le)
  have hcand_le : ∀ mask < 2 ^ (inst.bagAt jFin).length,
      forgetWeight inst.wt (inst.bagAt pFin) (inst.bagAt jFin) mask +
        (tblList jFin).getD mask 0 ≤ capB := fun mask _ => by
    have hfw := forgetWeight_le_mul_maxWeight inst (inst.bagAt pFin) (inst.bagAt jFin) mask
      (inst.bagAt_mem_lt jFin)
    have hfw_B : (inst.bagAt jFin).length * inst.maxWeight ≤ B :=
      Nat.mul_le_mul_right _ hj_len_le
    have hfc : (tblList jFin).getD mask 0 ≤ (tblList jFin).foldl max 0 := by
      rw [List.getD_eq_getElem?_getD]
      cases hget : (tblList jFin)[mask]? with
      | none => exact Nat.zero_le _
      | some v => exact List.mem_le_foldl_max (List.mem_of_getElem? hget)
    dsimp only [capB]; omega
  let cpArgs : ChildPassArgs :=
    ⟨d.numVerts, d.adjPtr, d.wtPtr,
      t.mem (d.descBase + 4 * (j + 1)), t.mem (d.descBase + 4 * (j + 1) + 1),
      t.mem (d.descBase + 4 * (j + 1) + 2), t.mem (d.descBase + 4 * (j + 1) + 3),
      t.mem (d.descBase + 4 * t.mem (d.parPtr + (j + 1))),
      t.mem (d.descBase + 4 * t.mem (d.parPtr + (j + 1)) + 1), bestPtr⟩
  have hcp_safe : Fits w 2 ∧ ∃ m' adjL wtL LB LP tblB initL cap,
      adjL.length = m' * m' ∧ wtL.length = m' ∧ cpArgs.numVerts = m' ∧
      HoldsIn cpArgs.adjPtr adjL t_a ∧ cpArgs.adjPtr + adjL.length ≤ cpArgs.bestPtr ∧
      HoldsIn cpArgs.wtPtr wtL t_a ∧ cpArgs.wtPtr + wtL.length ≤ cpArgs.bestPtr ∧
      HoldsIn cpArgs.bagBPtr LB t_a ∧ LB.length = cpArgs.bagBLen ∧
      cpArgs.bagBPtr + cpArgs.bagBLen ≤ cpArgs.bestPtr ∧ (∀ u ∈ LB, u < m') ∧
      HoldsIn cpArgs.tblBPtr tblB t_a ∧ tblB.length = cpArgs.tblBLen ∧
      cpArgs.tblBPtr + cpArgs.tblBLen ≤ cpArgs.bestPtr ∧
      HoldsIn cpArgs.bagPPtr LP t_a ∧ LP.length = cpArgs.bagPLen ∧
      cpArgs.bagPPtr + cpArgs.bagPLen ≤ cpArgs.bestPtr ∧
      HoldsIn cpArgs.bestPtr initL t_a ∧ initL.length = 2 ^ cpArgs.bagPLen ∧
      cpArgs.bagBLen * wtL.foldl max 0 + tblB.foldl max 0 ≤ cap ∧
      Fits w (cpArgs.adjPtr + m' * m') ∧ Fits w (cpArgs.wtPtr + m') ∧
      Fits w (cpArgs.bagBPtr + cpArgs.bagBLen) ∧ Fits w (cpArgs.tblBPtr + cpArgs.tblBLen) ∧
      Fits w (cpArgs.bagPPtr + cpArgs.bagPLen) ∧ Fits w (2 ^ cpArgs.bagPLen) ∧
      Fits w (cpArgs.bestPtr + 2 ^ cpArgs.bagPLen) ∧ Fits w cap := by
    refine ⟨h2, inst.numVerts, inst.adjMatrix, inst.weights,
      inst.bagAt jFin, inst.bagAt pFin, tblList jFin, List.replicate tblPLen 0, capB,
      inst.adjMatrix_len, inst.weights_len, hnv, ?_⟩
    dsimp only [cpArgs]
    simp only [hp_read, hj_len_m, hj_pow_m, hp_len_m, hadjP, hwtP]
    refine ⟨hlay_a.adj_holds, hlay_t.adj_holds.1,
      hlay_a.wt_holds, hlay_t.wt_holds.1,
      hj_bag.mono_frontier hp_a, trivial, hj_blo.trans (le_trans (by omega) hlay_t.desc_hi),
      inst.bagAt_mem_lt jFin,
      hj_tbl.mono_frontier hp_a, hj_tlen, by simpa only [hj_tlen] using hj_tbl.1,
      hp_bag.mono_frontier hp_a, trivial, hp_blo.trans (le_trans (by omega) hlay_t.desc_hi),
      holdsIn_alloc_zero t tblPLen, List.length_replicate,
      by have : (inst.bagAt jFin).length * inst.maxWeight ≤ B :=
           Nat.mul_le_mul_right _ hj_len_le
         dsimp only [capB, MWISInstance.maxWeight] at *; omega,
      hfit_fr.of_le (by have := hlay_t.adj_holds.1; rw [inst.adjMatrix_len] at this; omega),
      hfit_fr.of_le (by have := hlay_t.wt_holds.1; rw [inst.weights_len] at this; omega),
      hfit_fr.of_le (by have := hj_bag.1; omega),
      hfit_fr.of_le (by have := hj_tbl.1; rw [hj_tlen] at this; omega),
      hfit_fr.of_le (by have := hp_bag.1; omega),
      hfit_fr.of_le (by omega),
      hfit_fr.of_le (by omega),
      hfit_capB⟩
  have hcp_spec := childPassProg_spec (w := w) cpArgs (inst := inst)
    (LB := inst.bagAt jFin) (LP := inst.bagAt pFin)
    (tblB := tblList jFin) (initL := List.replicate tblPLen 0) (cap := capB) (s := t_a)
    (by dsimp only [cpArgs]; rw [hadjP]; exact hlay_a.adj_holds)
    (by dsimp only [cpArgs]; rw [hadjP]; exact hlay_t.adj_holds.1)
    (by dsimp only [cpArgs]; rw [hwtP]; exact hlay_a.wt_holds)
    (by dsimp only [cpArgs]; rw [hwtP]; exact hlay_t.wt_holds.1)
    hnv
    (by dsimp only [cpArgs]; exact hj_bag.mono_frontier hp_a)
    (by dsimp only [cpArgs]; exact hj_len_m.symm)
    (by dsimp only [cpArgs]; rw [hj_len_m]
        exact hj_blo.trans (le_trans (by omega) hlay_t.desc_hi))
    (inst.bagAt_mem_lt jFin)
    (by dsimp only [cpArgs]; exact hj_tbl.mono_frontier hp_a)
    (by dsimp only [cpArgs]; rw [hj_pow_m]; exact hj_tlen)
    (by dsimp only [cpArgs]; rw [hj_pow_m]; simpa only [hj_tlen] using hj_tbl.1)
    (by dsimp only [cpArgs]; rw [hp_read]; exact hp_bag.mono_frontier hp_a)
    (by dsimp only [cpArgs]; rw [hp_read, hp_len_m])
    (by dsimp only [cpArgs]; rw [hp_read, hp_len_m]
        exact hp_blo.trans (le_trans (by omega) hlay_t.desc_hi))
    (holdsIn_alloc_zero t tblPLen) List.length_replicate
    (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact Nat.zero_le _)
    (by dsimp only [cpArgs]; rw [hj_pow_m]; exact hcand_le)
    hfit_capB
  obtain ⟨_, hfr_cp, hp_cp, hbest_cp, _⟩ := hcp_spec
  let t_c := (Memory.spec 0).clientState t_a (childPassProg cpArgs)
  let bestL := childPassList inst.adj inst.wt (inst.bagAt jFin) (inst.bagAt pFin)
    (tblList jFin) (List.replicate tblPLen 0) (cpArgs.tblBLen)
  have hbestL_len : bestL.length = tblPLen := by
    rw [length_childPassList, List.length_replicate]
  have hbestL_max : bestL.foldl max 0 ≤ capB := by
    refine List.foldl_max_le (Nat.zero_le _) ?_
    refine mem_childPassList_le
      (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact Nat.zero_le _) ?_
    dsimp only [cpArgs]; rw [hj_pow_m]; exact hcand_le
  let ppArgs : ParentPassArgs :=
    ⟨t.mem (d.descBase + 4 * (j + 1)), t.mem (d.descBase + 4 * (j + 1) + 1),
      t.mem (d.descBase + 4 * t.mem (d.parPtr + (j + 1))),
      t.mem (d.descBase + 4 * t.mem (d.parPtr + (j + 1)) + 1),
      t.mem (d.descBase + 4 * t.mem (d.parPtr + (j + 1)) + 2),
      t.mem (d.descBase + 4 * t.mem (d.parPtr + (j + 1)) + 3), bestPtr⟩
  have hpp_safe : Fits w 2 ∧ ∃ LB LP oldL bestL' capO' capB',
      HoldsIn ppArgs.bagBPtr LB t_c ∧ LB.length = ppArgs.bagBLen ∧
      ppArgs.bagBPtr + ppArgs.bagBLen ≤ ppArgs.tblPPtr ∧
      HoldsIn ppArgs.bagPPtr LP t_c ∧ LP.length = ppArgs.bagPLen ∧
      ppArgs.bagPPtr + ppArgs.bagPLen ≤ ppArgs.tblPPtr ∧
      HoldsIn ppArgs.tblPPtr oldL t_c ∧ oldL.length = ppArgs.tblPLen ∧
      ppArgs.tblPLen = 2 ^ ppArgs.bagPLen ∧
      ppArgs.tblPPtr + ppArgs.tblPLen ≤ ppArgs.bestPtr ∧
      HoldsIn ppArgs.bestPtr bestL' t_c ∧ bestL'.length = 2 ^ ppArgs.bagPLen ∧
      oldL.foldl max 0 ≤ capO' ∧ bestL'.foldl max 0 ≤ capB' ∧
      Fits w (ppArgs.bagBPtr + ppArgs.bagBLen) ∧ Fits w (ppArgs.bagPPtr + ppArgs.bagPLen) ∧
      Fits w (ppArgs.tblPPtr + ppArgs.tblPLen) ∧ Fits w (2 ^ ppArgs.bagPLen) ∧
      Fits w (ppArgs.bestPtr + 2 ^ ppArgs.bagPLen) ∧ Fits w (capO' + capB') := by
    refine ⟨h2, inst.bagAt jFin, inst.bagAt pFin, tblList pFin, bestL, capO, capB, ?_⟩
    dsimp only [ppArgs]
    simp only [hp_read, hj_len_m, hp_len_m, hp_pow_m]
    refine ⟨hj_bag.mono_frontier (hp_a.trans hp_cp), trivial,
      hj_blo.trans (le_trans (by omega) (hlay_t.tbl_holds pFin).2.1),
      hp_bag.mono_frontier (hp_a.trans hp_cp), trivial,
      hp_blo.trans (le_trans (by omega) (hlay_t.tbl_holds pFin).2.1),
      hp_tbl.mono_frontier (hp_a.trans hp_cp), hp_tlen, trivial,
      by simpa only [hp_tlen] using hp_tbl.1,
      hbest_cp, hbestL_len, le_rfl, hbestL_max,
      hfit_fr.of_le (by have := hj_bag.1; omega),
      hfit_fr.of_le (by have := hp_bag.1; omega),
      hfit_fr.of_le (by have := hp_tbl.1; rw [hp_tlen] at this; omega),
      hfit_fr.of_le (by omega),
      hfit_fr.of_le (by omega),
      hfit_sum⟩
  have hdesc_hi := hlay_t.desc_hi
  have hpar_hi := hlay_t.par_holds.1
  rw [inst.parents_len] at hpar_hi
  have hp_isLt := pFin.isLt
  have hfit_par_j : Fits w (d.parPtr + (j + 1)) := by
    rw [hparP]; exact hfit_fr.of_le (by omega)
  have hfit_dJ0 : Fits w (d.descBase + 4 * (j + 1)) := hfit_fr.of_le (by omega)
  have hfit_dJ1 : Fits w (d.descBase + 4 * (j + 1) + 1) := hfit_fr.of_le (by omega)
  have hfit_dJ2 : Fits w (d.descBase + 4 * (j + 1) + 2) := hfit_fr.of_le (by omega)
  have hfit_dJ3 : Fits w (d.descBase + 4 * (j + 1) + 3) := hfit_fr.of_le (by omega)
  have hfit_dP0 : Fits w (d.descBase + 4 * t.mem (d.parPtr + (j + 1))) := by
    rw [hp_read]; exact hfit_fr.of_le (by omega)
  have hfit_dP1 : Fits w (d.descBase + 4 * t.mem (d.parPtr + (j + 1)) + 1) := by
    rw [hp_read]; exact hfit_fr.of_le (by omega)
  have hfit_dP2 : Fits w (d.descBase + 4 * t.mem (d.parPtr + (j + 1)) + 2) := by
    rw [hp_read]; exact hfit_fr.of_le (by omega)
  have hfit_dP3 : Fits w (d.descBase + 4 * t.mem (d.parPtr + (j + 1)) + 3) := by
    rw [hp_read]; exact hfit_fr.of_le (by omega)
  have h1_le_j1 : 1 ≤ j + 1 := by omega
  refine ⟨?_, Nat.le_of_succ_le hj_le, hres_s, hfr_s.trans hfr_sub, _, hlay_s, hpfx_s⟩
  dsimp only [processNodeStep]
  have ht_a_eq :
      ({ mem := clear t.mem t.frontier (t.mem (d.descBase + 4 * t.mem (d.parPtr + (j + 1)) + 3)),
         frontier := t.frontier + t.mem (d.descBase + 4 * t.mem (d.parPtr + (j + 1)) + 3) } :
        Memory.State) = t_a := by
    dsimp only [t_a, tblPLen]
    rw [hp_read, hp_pow_m]
    rfl
  rw [ht_a_eq]
  exact ⟨hfit_par_j,
    ⟨hfit_dJ0, h4⟩, ⟨hfit_dJ1, h4⟩, ⟨hfit_dJ2, h4⟩, ⟨hfit_dJ3, h4⟩,
    ⟨hfit_dP0, h4⟩, ⟨hfit_dP1, h4⟩, ⟨hfit_dP2, h4⟩, ⟨hfit_dP3, h4⟩,
    hcp_safe, hpp_safe, h1_le_j1⟩

private def runMWISProg (_ : Unit) : Memory.Prog ℕ := do
  let m ← Memory.read 1
  let n ← Memory.read 2
  let wtPtr := 3
  let adjPtr := 3 + m
  let parPtr := adjPtr + m * m
  let rawBagsPtr := parPtr + (n + 1)
  let descBase ← initNodesProg (rawBagsPtr, n + 1)
  let _ ← processNodesProg ⟨m, adjPtr, wtPtr, parPtr, descBase, n⟩
  let bag0Ptr ← Memory.read descBase
  let bag0Len ← Memory.read (descBase + 1)
  let tbl0Ptr ← Memory.read (descBase + 2)
  let tbl0Len ← Memory.read (descBase + 3)
  rootPassProg ⟨m, adjPtr, wtPtr, bag0Ptr, bag0Len, tbl0Ptr, tbl0Len⟩

private theorem init_decode (inst : MWISInstance) :
    (Memory.State.init inst.encode).frontier = inst.encode.length + 1 ∧
    3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1) +
      (inst.bags.flatMap encodeBag).length = (Memory.State.init inst.encode).frontier ∧
    (Memory.State.init inst.encode).mem 1 = inst.numVerts ∧
    (Memory.State.init inst.encode).mem 2 = inst.numNodes ∧
    HoldsIn 3 inst.weights (Memory.State.init inst.encode) ∧
    HoldsIn (3 + inst.numVerts) inst.adjMatrix (Memory.State.init inst.encode) ∧
    HoldsIn (3 + inst.numVerts + inst.numVerts * inst.numVerts) inst.parents
      (Memory.State.init inst.encode) ∧
    HoldsIn (3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1))
      (inst.bags.flatMap encodeBag) (Memory.State.init inst.encode) := by
  let s₀ := Memory.State.init inst.encode
  have hfr : s₀.frontier = inst.encode.length + 1 := by
    simp [s₀, Memory.State.init, Nat.add_comm]
  have hall : HoldsIn 1 inst.encode s₀ := holdsIn_init inst.encode
  unfold MWISInstance.encode at hall
  have hhead : ([inst.numVerts, inst.numNodes] ++ inst.weights ++ inst.adjMatrix ++
      inst.parents ++ inst.bags.flatMap encodeBag) =
      inst.numVerts :: inst.numNodes ::
        (inst.weights ++ (inst.adjMatrix ++ (inst.parents ++ inst.bags.flatMap encodeBag))) := by
    simp [List.append_assoc]
  rw [hhead, HoldsIn.cons_iff] at hall
  obtain ⟨_, hm1, hall1⟩ := hall
  rw [HoldsIn.cons_iff] at hall1
  obtain ⟨_, hm2, hall2⟩ := hall1
  rw [HoldsIn.append_iff] at hall2
  obtain ⟨hwt, hall3⟩ := hall2
  rw [inst.weights_len, HoldsIn.append_iff] at hall3
  obtain ⟨hadj, hall4⟩ := hall3
  rw [inst.adjMatrix_len, HoldsIn.append_iff] at hall4
  obtain ⟨hpar, hbags⟩ := hall4
  rw [inst.parents_len] at hbags
  have hlen_eq : 3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1) +
      (inst.bags.flatMap encodeBag).length = s₀.frontier := by
    rw [hfr]
    unfold MWISInstance.encode
    simp only [List.length_append, List.length_cons, List.length_nil,
      inst.weights_len, inst.adjMatrix_len, inst.parents_len]
    omega
  exact ⟨hfr, hlen_eq, hm1, hm2, hwt, hadj, hpar, hbags⟩

private theorem runMWISProg_spec {w : ℕ} (inst : MWISInstance)
    (hw : Fits w inst.wordBound) :
    let s₀ := Memory.State.init inst.encode
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (runMWISProg ())) ∧
    (Memory.spec 0).clientResult s₀ (runMWISProg ()) = inst.result ∧
    memoryCost (runMWISProg ()) s₀ ≤ inst.stepBound := by
  let s₀ := Memory.State.init inst.encode
  let m := inst.numVerts
  let n := inst.numNodes
  let M := inst.maxBagLen
  obtain ⟨hfr₀, hlen_eq, hm1, hm2, hwt₀, hadj₀, hpar₀, hbags₀⟩ := init_decode inst
  have hpow_12 : (inst.numNodes + 1) * 2 ^ inst.maxBagLen ≤
      (2 * inst.numNodes + 1) * 2 ^ inst.maxBagLen :=
    Nat.mul_le_mul_right _ (by omega)
  have hfit_init_peak : Fits w (s₀.frontier + 4 * (n + 1) + (n + 1) * 2 ^ M) := hw.of_le (by
    dsimp only [s₀, n, M]
    rw [hfr₀]
    unfold MWISInstance.wordBound
    dsimp only
    omega)
  have hfit_raw : Fits w s₀.frontier := hfit_init_peak.of_le (by omega)
  obtain ⟨hv_init, hdesc_eq, hfr₁, hlay₁, hc_init⟩ :=
    initNodesProg_spec (w := w) inst hwt₀ hadj₀ hpar₀ hbags₀ hfit_init_peak hfit_raw
  let rawBagsPtr := 3 + m + m * m + (n + 1)
  let s₁ := (Memory.spec 0).clientState s₀ (initNodesProg (rawBagsPtr, n + 1))
  let descBase := (Memory.spec 0).clientResult s₀ (initNodesProg (rawBagsPtr, n + 1))
  have hfr₁' : s₁.frontier ≤ inst.encode.length + 1 + 4 * (n + 1) + (n + 1) * 2 ^ M := by
    dsimp only [s₁, rawBagsPtr, m, n, M, s₀] at hfr₁ ⊢
    omega
  have hfit_proc_peak : Fits w (s₁.frontier + n * 2 ^ M) := hw.of_le (by
    have hsum : s₁.frontier + n * 2 ^ M ≤
        inst.encode.length + 1 + 4 * (n + 1) + (2 * n + 1) * 2 ^ M := by
      have : (n + 1) * 2 ^ M + n * 2 ^ M = (2 * n + 1) * 2 ^ M := by ring
      omega
    dsimp only [n, M] at hsum ⊢
    exact hsum.trans (by unfold MWISInstance.wordBound; dsimp only; omega))
  have hfit_val : Fits w ((n + 1) * M * inst.maxWeight) := hw.of_le (by
    dsimp only [n, M]; unfold MWISInstance.wordBound; dsimp only; omega)
  obtain ⟨hv_proc, hfr₂, ⟨tblFinal, hlay₂, hpfx₂, hagree₂⟩, hc_proc⟩ :=
    processNodesProg_spec (w := w) inst descBase hlay₁ hfit_proc_peak hfit_val
  let procArgs : ProcessNodesArgs := ⟨m, 3 + m, 3, 3 + m + m * m, descBase, n⟩
  let s₂ := (Memory.spec 0).clientState s₁ (processNodesProg procArgs)
  let zeroFin : Fin (n + 1) := 0
  obtain ⟨h0_len, h0_pow, _, h0_bag⟩ := hlay₂.bags_holds zeroFin
  obtain ⟨h0_tlen, _, h0_tbl⟩ := hlay₂.tbl_holds zeroFin
  dsimp only [zeroFin] at h0_len h0_pow h0_bag h0_tlen h0_tbl
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at h0_len h0_pow h0_bag h0_tlen h0_tbl
  change s₂.mem (descBase + 1) = (inst.bagAt zeroFin).length at h0_len
  change s₂.mem (descBase + 3) = 2 ^ (inst.bagAt zeroFin).length at h0_pow
  change HoldsIn (s₂.mem descBase) (inst.bagAt zeroFin) s₂ at h0_bag
  change HoldsIn (s₂.mem (descBase + 2)) (tblFinal zeroFin) s₂ at h0_tbl
  let rpArgs : RootPassArgs :=
    ⟨m, 3 + m, 3, s₂.mem descBase, s₂.mem (descBase + 1),
      s₂.mem (descBase + 2), s₂.mem (descBase + 3)⟩
  have hrp_spec := rootPassProg_spec (w := w) rpArgs (inst := inst)
    (L0 := inst.bagAt zeroFin) (tbl0 := tblFinal zeroFin)
    (arr0 := (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt n)[zeroFin]) (s := s₂)
    hlay₂.adj_holds hlay₂.wt_holds rfl
    h0_bag h0_len.symm (inst.bagAt_mem_lt zeroFin)
    h0_tbl (by dsimp only [rpArgs]; rw [h0_pow]; exact h0_tlen)
    (by dsimp only [rpArgs]; rw [h0_pow]; exact hagree₂ zeroFin)
  obtain ⟨hv_rp, _, hr_rp, hc_rp⟩ := hrp_spec
  have h1_lt : 1 < s₀.frontier := by dsimp only [s₀]; omega
  have h2_lt : 2 < s₀.frontier := by dsimp only [s₀]; omega
  have hd_lt (off : ℕ) (hoff : off < 4) : descBase + off < s₂.frontier := by
    have hd_hi : descBase + 4 * (n + 1) ≤ s₂.frontier := hlay₂.desc_hi
    omega
  have hr0_st (a : ℕ) : (Memory.spec 0).clientState s₀ (Memory.read a) = s₀ := rfl
  have hr0_res (a : ℕ) : (Memory.spec 0).clientResult s₀ (Memory.read a) = s₀.mem a := rfl
  have hr2_st (a : ℕ) : (Memory.spec 0).clientState s₂ (Memory.read a) = s₂ := rfl
  have hr2_res (a : ℕ) : (Memory.spec 0).clientResult s₂ (Memory.read a) = s₂.mem a := rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold runMWISProg
    dsimp only
    refine validHistory_read_bind h1_lt ?_
    rw [show s₀.mem 1 = m from hm1]
    refine validHistory_read_bind h2_lt ?_
    rw [show s₀.mem 2 = n from hm2]
    refine validHistory_bind_step hv_init ?_
    change (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (processNodesProg procArgs >>= _))
    refine validHistory_bind_step hv_proc ?_
    change (Memory.spec w).ValidHistory s₂
      ((Memory.spec w).clientHistory s₂
        (Memory.read descBase >>= fun bag0Ptr =>
          Memory.read (descBase + 1) >>= fun bag0Len =>
          Memory.read (descBase + 2) >>= fun tbl0Ptr =>
          Memory.read (descBase + 3) >>= fun tbl0Len =>
          rootPassProg ⟨m, 3 + m, 3, bag0Ptr, bag0Len, tbl0Ptr, tbl0Len⟩))
    refine validHistory_read_bind (by simpa only [Nat.add_zero] using hd_lt 0 (by decide)) ?_
    refine validHistory_read_bind (hd_lt 1 (by decide)) ?_
    refine validHistory_read_bind (hd_lt 2 (by decide)) ?_
    exact validHistory_read_bind (hd_lt 3 (by decide)) hv_rp
  · unfold runMWISProg
    dsimp only
    rw [StateTransitionSpec.clientResult_bind, hr0_st, hr0_res, show s₀.mem 1 = m from hm1,
      StateTransitionSpec.clientResult_bind, hr0_st, hr0_res, show s₀.mem 2 = n from hm2,
      StateTransitionSpec.clientResult_bind]
    change (Memory.spec 0).clientResult s₁ (processNodesProg procArgs >>= _) = inst.result
    rw [StateTransitionSpec.clientResult_bind]
    change (Memory.spec 0).clientResult s₂
      (Memory.read descBase >>= _) = inst.result
    iterate 4 rw [StateTransitionSpec.clientResult_bind, hr2_st, hr2_res]
    rw [hr_rp]
    dsimp only [rpArgs, MWISInstance.result]
    rw [h0_pow]
  · unfold runMWISProg
    dsimp only
    rw [memoryCost_bind', memoryCost_read, hr0_st, hr0_res, show s₀.mem 1 = m from hm1,
      memoryCost_bind', memoryCost_read, hr0_st, hr0_res, show s₀.mem 2 = n from hm2,
      memoryCost_bind']
    change 1 + (1 + (memoryCost (initNodesProg (rawBagsPtr, n + 1)) s₀ +
      memoryCost (processNodesProg procArgs >>= _) s₁)) ≤ inst.stepBound
    rw [memoryCost_bind']
    change 1 + (1 + (memoryCost (initNodesProg (rawBagsPtr, n + 1)) s₀ +
      (memoryCost (processNodesProg procArgs) s₁ +
        memoryCost (Memory.read descBase >>= _) s₂))) ≤ inst.stepBound
    iterate 4 rw [memoryCost_bind', memoryCost_read, hr2_st, hr2_res]
    have h0_len_le : (inst.bagAt zeroFin).length ≤ M := inst.bagAt_length_le zeroFin
    have h0_pow_le : 2 ^ (inst.bagAt zeroFin).length ≤ 2 ^ M :=
      Nat.pow_le_pow_right (by decide) h0_len_le
    have hc_rp_M : memoryCost (rootPassProg rpArgs) s₂ ≤
        2 ^ M * (5 * M ^ 2 + 5 * M + 17) := by
      have hrhs : rpArgs.tbl0Len *
          (rpArgs.bag0Len * (2 * rpArgs.bag0Len + 1) + rpArgs.bag0Len * 2 + 1) =
          2 ^ (inst.bagAt zeroFin).length *
            ((inst.bagAt zeroFin).length * (2 * (inst.bagAt zeroFin).length + 1) +
              (inst.bagAt zeroFin).length * 2 + 1) := by
        dsimp only [rpArgs]
        rw [h0_len, h0_pow]
      exact (hc_rp.trans_eq hrhs).trans (Nat.mul_le_mul h0_pow_le (rp_cost_poly_le h0_len_le))
    have h1_pow : 1 ≤ 2 ^ M := Nat.one_le_pow M 2 (by decide)
    dsimp only [s₀, s₁, descBase, rawBagsPtr, procArgs, rpArgs, m, n, M,
      MWISInstance.stepBound] at hc_init hc_proc hc_rp_M ⊢
    exact total_stepBound_le h1_pow hc_init hc_proc hc_rp_M

private theorem runMWISProg_init_helper {w : ℕ} (inst : MWISInstance)
    (hw : Fits w inst.wordBound) :
    let descBase := 3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1)
    let prog := initNodesProg (descBase, inst.numNodes + 1)
    let s₀ := Memory.State.init inst.encode
    let s₁ := (Memory.spec 0).clientState s₀ prog
    let descRes := (Memory.spec 0).clientResult s₀ prog
    descRes = s₀.frontier ∧
    s₁.frontier ≤ inst.encode.length + 1 + 4 * (inst.numNodes + 1) +
      (inst.numNodes + 1) * 2 ^ inst.maxBagLen ∧
    NodeLayout inst descRes
      (fun i => List.replicate (2 ^ (inst.bagAt i).length) 0) s₁ := by
  obtain ⟨hfr₀, _, hm1, hm2, hwt₀, hadj₀, hpar₀, hbags₀⟩ := init_decode inst
  have hpow_12 : (inst.numNodes + 1) * 2 ^ inst.maxBagLen ≤
      (2 * inst.numNodes + 1) * 2 ^ inst.maxBagLen :=
    Nat.mul_le_mul_right _ (by omega)
  have hfit_init_peak : Fits w ((Memory.State.init inst.encode).frontier +
      4 * (inst.numNodes + 1) + (inst.numNodes + 1) * 2 ^ inst.maxBagLen) := hw.of_le (by
    rw [hfr₀]; unfold MWISInstance.wordBound; dsimp only; omega)
  obtain ⟨_, hdesc_eq, hfr₁, hlay₁, _⟩ :=
    initNodesProg_spec (w := w) inst hwt₀ hadj₀ hpar₀ hbags₀ hfit_init_peak
      (hfit_init_peak.of_le (by omega))
  refine ⟨hdesc_eq, ?_, hlay₁⟩
  simpa only [hfr₀] using hfr₁

private theorem runMWISProg_realizes :
    Realizes .exact runMWISProg WordEncoding.encode WordEncoding.encode
      (fun w _ s =>
        ∃ inst : MWISInstance,
          s = Memory.State.init inst.encode ∧
          Fits w inst.wordBound)
      (fun _ _ => 0) := by
  unfold runMWISProg
  realize [initNodesProg_realizes, processNodesProg_realizes, rootPassProg_realizes]
  · obtain ⟨inst, rfl, hw⟩ := h
    exact hw.of_le (by unfold MWISInstance.wordBound; dsimp only; omega)
  · obtain ⟨inst, rfl, hw⟩ := h
    exact hw.of_le (by unfold MWISInstance.wordBound; dsimp only; omega)
  · obtain ⟨inst, rfl, hw⟩ := h
    obtain ⟨_, _, hm1, hm2, _, _, _, _⟩ := init_decode inst
    rw [hm1, hm2]
    exact hw.of_le (by unfold MWISInstance.wordBound; dsimp only; omega)
  · obtain ⟨inst, rfl, hw⟩ := h
    obtain ⟨_, _, _, hm2, _, _, _, _⟩ := init_decode inst
    rw [hm2]
    exact hw.of_le (by unfold MWISInstance.wordBound; dsimp only; omega)
  · obtain ⟨inst, rfl, hw⟩ := h
    exact hw.of_le (by unfold MWISInstance.wordBound; dsimp only; omega)
  · obtain ⟨inst, rfl, hw⟩ := h
    obtain ⟨hfr₀, _, hm1, hm2, _, _, _, hbags₀⟩ := init_decode inst
    rw [hm1, hm2]
    have hpow_12 : (inst.numNodes + 1) * 2 ^ inst.maxBagLen ≤
        (2 * inst.numNodes + 1) * 2 ^ inst.maxBagLen :=
      Nat.mul_le_mul_right _ (by omega)
    exact ⟨inst.bags, inst.maxBagLen, inst.bags_len,
      fun B hB => List.mem_le_foldl_max (List.mem_map_of_mem hB),
      hbags₀,
      hw.of_le (by rw [hfr₀]; unfold MWISInstance.wordBound; dsimp only; omega)⟩
  · obtain ⟨inst, rfl, hw⟩ := h
    obtain ⟨_, _, hm1, _, _, _, _, _⟩ := init_decode inst
    rw [hm1]
    exact hw.of_le (by unfold MWISInstance.wordBound; dsimp only; omega)
  · obtain ⟨inst, rfl, hw⟩ := h
    exact hw.of_le (by unfold MWISInstance.wordBound; dsimp only; omega)
  · obtain ⟨inst, rfl, hw⟩ := h
    obtain ⟨_, _, hm1, _, _, _, _, _⟩ := init_decode inst
    rw [hm1]
    exact hw.of_le (by unfold MWISInstance.wordBound; dsimp only; omega)
  · obtain ⟨inst, rfl, hw⟩ := h
    obtain ⟨_, _, hm1, hm2, _, _, _, _⟩ := init_decode inst
    obtain ⟨_, hfr₁', hlay₁⟩ := runMWISProg_init_helper inst hw
    rw [hm1, hm2]
    refine ⟨inst, fun i => List.replicate (2 ^ (inst.bagAt i).length) 0,
      rfl, rfl, rfl, rfl, hlay₁,
      prefixMaxSum_replicate_zero _ _,
      hw.of_le ?_,
      hw.of_le (by unfold MWISInstance.wordBound; dsimp only; omega)⟩
    have : (inst.numNodes + 1) * 2 ^ inst.maxBagLen + inst.numNodes * 2 ^ inst.maxBagLen =
        (2 * inst.numNodes + 1) * 2 ^ inst.maxBagLen := by ring
    unfold MWISInstance.wordBound; dsimp only; omega
  all_goals
    obtain ⟨inst, rfl, hw⟩ := h
    obtain ⟨hfr₀, _, hm1, hm2, _, _, _, _⟩ := init_decode inst
    obtain ⟨hdesc_eq, hfr₁', hlay₁⟩ := runMWISProg_init_helper inst hw
    rw [hm1, hm2]
  all_goals try
    (change (Memory.spec 0).clientResult _ _ = _ at hdesc_eq
     rw [hdesc_eq, hfr₀]
     exact hw.of_le (by unfold MWISInstance.wordBound; dsimp only; omega))
  · have hfit_proc_peak : Fits w (((Memory.spec 0).clientState (Memory.State.init inst.encode)
        (initNodesProg (3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1),
          inst.numNodes + 1))).frontier + inst.numNodes * 2 ^ inst.maxBagLen) := hw.of_le (by
      have : (inst.numNodes + 1) * 2 ^ inst.maxBagLen + inst.numNodes * 2 ^ inst.maxBagLen =
          (2 * inst.numNodes + 1) * 2 ^ inst.maxBagLen := by ring
      unfold MWISInstance.wordBound; dsimp only; omega)
    have hfit_val : Fits w ((inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight) := hw.of_le (by
      unfold MWISInstance.wordBound; dsimp only; omega)
    let descRes := (Memory.spec 0).clientResult (Memory.State.init inst.encode)
      (initNodesProg (3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1),
        inst.numNodes + 1))
    obtain ⟨_, hfr₂, ⟨tblFinal, hlay₂, hpfx₂, _⟩, _⟩ :=
      processNodesProg_spec (w := w) inst descRes hlay₁ hfit_proc_peak hfit_val
    have hfr₂_bound : ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState (Memory.State.init inst.encode)
          (initNodesProg (3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1),
            inst.numNodes + 1)))
        (processNodesProg ⟨inst.numVerts, 3 + inst.numVerts, 3,
          3 + inst.numVerts + inst.numVerts * inst.numVerts, descRes, inst.numNodes⟩)).frontier ≤
        inst.wordBound := by
      have hfr₂' : ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState (Memory.State.init inst.encode)
            (initNodesProg (3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1),
              inst.numNodes + 1)))
          (processNodesProg ⟨inst.numVerts, 3 + inst.numVerts, 3,
            3 + inst.numVerts + inst.numVerts * inst.numVerts, descRes,
            inst.numNodes⟩)).frontier ≤
          ((Memory.spec 0).clientState (Memory.State.init inst.encode)
            (initNodesProg (3 + inst.numVerts + inst.numVerts * inst.numVerts + (inst.numNodes + 1),
              inst.numNodes + 1))).frontier + inst.numNodes * 2 ^ inst.maxBagLen := hfr₂
      have : (inst.numNodes + 1) * 2 ^ inst.maxBagLen + inst.numNodes * 2 ^ inst.maxBagLen =
          (2 * inst.numNodes + 1) * 2 ^ inst.maxBagLen := by ring
      dsimp only [descRes] at hfr₂' ⊢
      unfold MWISInstance.wordBound; dsimp only; omega
    dsimp only [descRes] at hfr₂_bound hlay₂
    let zeroFin : Fin (inst.numNodes + 1) := 0
    obtain ⟨h0_len, h0_pow, _, h0_bag⟩ := hlay₂.bags_holds zeroFin
    obtain ⟨h0_tlen, _, h0_tbl⟩ := hlay₂.tbl_holds zeroFin
    dsimp only [zeroFin] at h0_len h0_pow h0_bag h0_tlen h0_tbl
    simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at h0_len h0_pow h0_bag h0_tlen h0_tbl
    have hmax0 : (tblFinal zeroFin).foldl max 0 ≤
        inst.numNodes * (inst.maxBagLen * inst.maxWeight) :=
      (foldl_max_le_prefixMaxSum tblFinal zeroFin (Nat.zero_le _)).trans hpfx₂
    have h0_len_le : (inst.bagAt zeroFin).length ≤ inst.maxBagLen := inst.bagAt_length_le zeroFin
    have hcap_root : (inst.bagAt zeroFin).length * inst.weights.foldl max 0 +
        (tblFinal zeroFin).foldl max 0 ≤
        (inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight := by
      have hbw : (inst.bagAt zeroFin).length * inst.weights.foldl max 0 ≤
          inst.maxBagLen * inst.maxWeight := Nat.mul_le_mul_right _ h0_len_le
      calc (inst.bagAt zeroFin).length * inst.weights.foldl max 0 + (tblFinal zeroFin).foldl max 0
          ≤ inst.maxBagLen * inst.maxWeight +
              inst.numNodes * (inst.maxBagLen * inst.maxWeight) := Nat.add_le_add hbw hmax0
        _ = (inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight := by ring
    exact ⟨inst.numVerts, inst.adjMatrix, inst.weights, inst.bagAt zeroFin, tblFinal zeroFin,
      (inst.numNodes + 1) * inst.maxBagLen * inst.maxWeight,
      inst.adjMatrix_len, inst.weights_len, rfl,
      hlay₂.adj_holds, hlay₂.wt_holds,
      h0_bag, h0_len.symm, inst.bagAt_mem_lt zeroFin,
      h0_tbl, by rw [h0_pow]; exact h0_tlen,
      by rw [h0_len]; exact hcap_root,
      hw.of_le (by have := hlay₂.adj_holds.1; rw [inst.adjMatrix_len] at this; omega),
      hw.of_le (by have := hlay₂.wt_holds.1; rw [inst.weights_len] at this; omega),
      hw.of_le (by have := h0_bag.1; rw [h0_len]; omega),
      hw.of_le (by have := h0_tbl.1; rw [h0_pow, ← h0_tlen]; omega),
      hfit_val⟩

/-- One fixed exact-basis Word-RAM program computes maximum-weight independent set
`MWISInstance.result` in `≤ C * (inst.stepBound + 1) + 1` instructions for every word width `w`
satisfying `Fits w inst.wordBound` and `InputFits w inst.encode`. -/
theorem exists_program_mwis_treeDecomposition :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      prog.ComputesInTime
        (fun _ inst => inst.encode)
        (fun inst _ => C * (inst.stepBound + 1) + 1)
        (fun inst w => Fits w inst.wordBound)
        MWISInstance.result := by
  obtain ⟨r, C, pc, prog, _, _, hexec⟩ :=
    runMWISProg_realizes.exists_standard_init_program_state_from_words (0 : Fin 1)
  refine ⟨r, C, prog, fun inst w hw hin => ?_⟩
  have hf_len : Fits w (inst.encode.length + 1) :=
    hw.of_le (by unfold MWISInstance.wordBound; dsimp only; omega)
  obtain ⟨hval, hres, hcost⟩ := runMWISProg_spec inst hw
  obtain ⟨y, n, hruns, hhalt, _, _, hn_le⟩ :=
    hexec w () inst.encode (fun i => Fin.elim0 i) (Nat.zero_le _) hf_len hin
      ⟨inst, rfl, hw⟩ hval
  rw [clientResult_width, hres] at hhalt
  refine ⟨n + 1, ⟨⟨pc, y⟩, n, hruns, hhalt, rfl⟩, ?_⟩
  have hmul : C * (memoryCost (runMWISProg ()) (Memory.State.init inst.encode) + 0 + 1) + 1 ≤
      C * (inst.stepBound + 1) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left C (by omega)) 1
  exact hn_le.trans hmul

/-- Uniform exact-basis Word-RAM computability certificate for `MWISInstance.result`. -/
theorem uniformComputableInTime_mwis_treeDecomposition :
    ∃ C : ℕ,
      UniformComputableInTime .exact
        MWISInstance.result
        (fun _ inst => inst.encode)
        (fun inst _ => C * (inst.stepBound + 1) + 1)
        (fun inst w => Fits w inst.wordBound) := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_mwis_treeDecomposition
  refine ⟨C, r, prog, hcomp, fun inst => ?_⟩
  obtain ⟨w, hw_le, hin⟩ := InputFits.exists_width inst.encode inst.wordBound
  exact ⟨w, (fits_self inst.wordBound).mono hw_le, hin⟩

/-- **FPT Word-RAM Maximum-Weight Independent Set.** One fixed exact-basis Word-RAM program
computes `mwisValue R wt` on any graph `G` (`e : V ≃ Fin m`), rooted tree decomposition
`R : G.RootedTreeDecomposition n` of width `R.width ≤ k`, vertex weights `wt : V → ℕ`, and bag
orderings `L` (`IsBagOrder R L`) within `C * (mwisFPTBound n k + 1) + 1` instructions
(`O((n + 1) · 2 ^ (k + 1) · (k + 1) ^ 2)`). -/
theorem exists_program_mwis_rooted :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ {V : Type*} {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
        {m n k : ℕ} (e : V ≃ Fin m) (R : G.RootedTreeDecomposition n) (wt : V → ℕ)
        (L : Fin (n + 1) → List V),
        IsBagOrder R L →
        R.width ≤ k →
        ∀ w : ℕ,
          let inst := MWISInstance.ofRooted e R wt L
          Fits w inst.wordBound →
          InputFits w inst.encode →
          ∃ steps,
            Executes w prog (.init inst.encode) (mwisValue R wt) steps ∧
            steps ≤ C * (mwisFPTBound n k + 1) + 1 := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_mwis_treeDecomposition
  refine ⟨r, C, prog, fun {V G _ _ m n k} e R wt L hL hk w hw hin => ?_⟩
  let inst := MWISInstance.ofRooted e R wt L
  obtain ⟨steps, hexec, hsteps⟩ := hcomp inst w hw hin
  rw [MWISInstance.result_ofRooted e R wt hL] at hexec
  have hbound := MWISInstance.stepBound_ofRooted_le e R wt hL hk
  exact ⟨steps, hexec, hsteps.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left C (Nat.add_le_add_right hbound 1)) 1)⟩

end Cslib.Algorithms.WordRAM.TreeDecomposition
