/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSetFPT
import CslibFrontier.Foundations.Data.List.FoldMax
import Mathlib.Data.List.OfFn

/-!
# Serialized MWIS instance model, `ℕ`-table dynamic program, and rooted-decomposition bridge

This module defines the pure serialized instance bundle `MWISInstance`, flat word encoding,
`ℕ`-indexed dynamic-programming passes (`noAdjInst`, `indepInst`, `childPassInst`, `rootPassInst`,
`tablesInst`), FPT step/word bounds, and equivalence bridge to `mwisFPT` and `mwisValue` shared by
the Word-RAM maximum-weight independent set modules.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.encodeBag`: length-prefixed bag word list.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance`: flat word-serializable instance bundle
  with `MWISInstance.encode`, `MWISInstance.result`, `MWISInstance.maxBagLen`,
  `MWISInstance.maxWeight`, `MWISInstance.wordBound`, `MWISInstance.stepBound`, and
  `MWISInstance.ofRooted`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.mwisFPTBound`: closed-form width-`k` step bound
  `6 + (n + 1) * (2 ^ (k + 1) * (5 * (k + 1) ^ 2 + 6 * (k + 1) + 32))`.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.result_ofRooted_eq_mwisFPT`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.result_ofRooted`:
  `MWISInstance.ofRooted` agrees with `mwisFPT R w L`, and equals `mwisValue R w` under
  `IsBagOrder R L`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.maxBagLen_ofRooted_le`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.stepBound_ofRooted_le`: width-`k`
  bounds on `maxBagLen` and `stepBound`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Algorithms.Lean.TreeDecomposition

/-! ### Instance bundle, flat encoding, and `ℕ`-indexed DP passes -/

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

/-- Test whether `x` is non-adjacent under `adj` to every selected vertex of `L` under mask `m`. -/
@[expose] def noAdjInst (adj : ℕ → ℕ → Bool) (x : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | u :: L, m => noAdjInst adj x L (m / 2) && !(decide (m % 2 = 1) && adj x u)

/-- Test whether the vertices of `L` selected by mask `m` are pairwise non-adjacent under `adj`. -/
@[expose] def indepInst (adj : ℕ → ℕ → Bool) : List ℕ → ℕ → Bool
  | [], _ => true
  | u :: L, m => indepInst adj L (m / 2) && (!decide (m % 2 = 1) || noAdjInst adj u L (m / 2))

/-- Child-to-parent projection pass over `ℕ` vertex indices and Boolean relation `adj`. -/
@[expose] def childPassInst (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (LB LP : List ℕ)
    (f init : Array ℕ) : ℕ → Array ℕ
  | 0 => init
  | c + 1 =>
    let best := childPassInst adj wt LB LP f init c
    if indepInst adj LB c then
      let key := keyMask LB LP c
      best.setIfInBounds key (max (best.getD key 0) (forgetWeight wt LP LB c + f.getD c 0))
    else
      best

/-- `childPassInst` preserves the size of `init`. -/
theorem size_childPassInst (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ)
    (LB LP : List ℕ) (f init : Array ℕ) (c : ℕ) :
    (childPassInst adj wt LB LP f init c).size = init.size := by
  induction c with
  | zero => rfl
  | succ c ih =>
    dsimp only [childPassInst]
    split_ifs
    · rw [Array.size_setIfInBounds, ih]
    · exact ih

/-- Final maximization pass at the root bag over `ℕ` vertex indices and Boolean relation `adj`. -/
@[expose] def rootPassInst (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (L : List ℕ) (tbl : Array ℕ) :
    ℕ → ℕ
  | 0 => 0
  | c + 1 =>
    let best := rootPassInst adj wt L tbl c
    if indepInst adj L c then max best (forgetWeight wt [] L c + tbl.getD c 0) else best

/-- Single bottom-up node transition updating `par j`'s DP table from child node `j`. -/
@[expose] def processInstNode (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (n : ℕ)
    (par : Fin (n + 1) → Fin (n + 1)) (bags : Fin (n + 1) → List ℕ)
    (st : Vector (Array ℕ) (n + 1)) (j : Fin (n + 1)) : Vector (Array ℕ) (n + 1) :=
  let p := par j
  let init := Array.replicate (2 ^ (bags p).length) 0
  let best := childPassInst adj wt (bags j) (bags p) st[j] init (2 ^ (bags j).length)
  let tp := parentPass (bags j) (bags p) st[p] best (2 ^ (bags p).length)
  st.set p tp p.isLt

/-- Bottom-up node table state after processing `t` nonroot nodes `n, n - 1, …, n + 1 - t`. -/
@[expose] def tablesInst (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (n : ℕ)
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

/-- Bounded parent node index of `i` (`0` at the root `i = 0`). -/
@[expose] def parFin (inst : MWISInstance) (i : Fin (inst.numNodes + 1)) :
    Fin (inst.numNodes + 1) :=
  if hi : 1 ≤ i.val then
    let idx : Fin inst.parents.length := ⟨i.val, by rw [inst.parents_len]; exact i.isLt⟩
    ⟨inst.parents[idx], (inst.parents_lt idx hi).trans i.isLt⟩
  else
    ⟨0, Nat.succ_pos _⟩

/-- Ordered vertex list of node `i`. -/
@[expose] def bagAt (inst : MWISInstance) (i : Fin (inst.numNodes + 1)) : List ℕ :=
  inst.bags[i.val]'(by rw [inst.bags_len]; exact i.isLt)

/-- Pure dynamic-programming value computed on `inst`. -/
@[expose] def result (inst : MWISInstance) : ℕ :=
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

/-- Every node's bag length is at most `inst.maxBagLen`. -/
theorem bagAt_length_le (inst : MWISInstance)
    (i : Fin (inst.numNodes + 1)) : (inst.bagAt i).length ≤ inst.maxBagLen := by
  have hmem : inst.bagAt i ∈ inst.bags := List.getElem_mem _
  exact List.mem_le_foldl_max (List.mem_map_of_mem hmem)

/-- Every vertex in `inst.bagAt i` is `< inst.numVerts`. -/
theorem bagAt_mem_lt (inst : MWISInstance)
    (i : Fin (inst.numNodes + 1)) : ∀ u ∈ inst.bagAt i, u < inst.numVerts :=
  inst.bags_lt (inst.bagAt i) (List.getElem_mem _)

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
        _ = ((e x).val + 1) * m := by rw [Nat.succ_mul]
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

/-- Under `IsBagOrder R L` and `R.width ≤ k`, every bag has length at most `k + 1`. -/
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

/-- Under `IsBagOrder R L` and `R.width ≤ k`, `stepBound` is bounded by `mwisFPTBound n k`. -/
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
  have hpoly :
      5 * (MWISInstance.ofRooted e R w L).maxBagLen ^ 2 +
          6 * (MWISInstance.ofRooted e R w L).maxBagLen + 32 ≤
        5 * (k + 1) ^ 2 + 6 * (k + 1) + 32 :=
    Nat.add_le_add_right
      (Nat.add_le_add (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left hM 2))
        (Nat.mul_le_mul_left 6 hM)) 32
  exact Nat.add_le_add_left (Nat.mul_le_mul_left (n + 1) (Nat.mul_le_mul hpow hpoly)) 6

end RootedBridge

end Cslib.Algorithms.WordRAM.TreeDecomposition
