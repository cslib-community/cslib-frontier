/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.Instance
import CslibFrontier.Foundations.Data.List.FoldMax

/-!
# Internal `ℕ`-indexed dynamic-programming helpers for `MWISInstance`

Internal helper definitions and bag/parent indexing lemmas consumed privately by `Model` and the
Word-RAM pass submodules (`IndepScan`, `ChildPass`, `NodeLayout`, `RootPass`, `ProcessNodes`,
`Runner`); never re-exported through `IndependentSet` or `IndependentSet.Model`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.noAdjInst`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.indepInst`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.childPassInst`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.rootPassInst`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.tablesInst`: pure `ℕ`-indexed DP passes.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.parFin`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.bagAt`: bounded node accessors.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.size_childPassInst`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.tablesInst_zero`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.tablesInst_succ`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.bagAt_length_le`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.bagAt_mem_lt`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.Algorithms.Lean.TreeDecomposition

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

private def processInstNode (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (n : ℕ)
    (par : Fin (n + 1) → Fin (n + 1)) (bags : Fin (n + 1) → List ℕ)
    (st : Vector (Array ℕ) (n + 1)) (j : Fin (n + 1)) : Vector (Array ℕ) (n + 1) :=
  let p := par j
  let init := Array.replicate (2 ^ (bags p).length) 0
  let best := childPassInst adj wt (bags j) (bags p) st[j] init (2 ^ (bags j).length)
  let tp := parentPass (bags j) (bags p) st[p] best (2 ^ (bags p).length)
  st.set p tp p.isLt

/-- Bottom-up node table state after processing `t` nonroot nodes `n, n - 1, …, n + 1 - t`. -/
def tablesInst (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (n : ℕ)
    (par : Fin (n + 1) → Fin (n + 1)) (bags : Fin (n + 1) → List ℕ) :
    ℕ → Vector (Array ℕ) (n + 1)
  | 0 => Vector.replicate (n + 1) #[]
  | t + 1 =>
    processInstNode adj wt n par bags (tablesInst adj wt n par bags t)
      (Fin.ofNat (n + 1) (n - t))

/-- Initial replicate state of `tablesInst` before processing nonroot nodes. -/
theorem tablesInst_zero (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (n : ℕ)
    (par : Fin (n + 1) → Fin (n + 1)) (bags : Fin (n + 1) → List ℕ) :
    tablesInst adj wt n par bags 0 = Vector.replicate (n + 1) #[] := by rfl

/-- Step equation of `tablesInst` processing nonroot node `Fin.ofNat (n + 1) (n - t)`. -/
theorem tablesInst_succ (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (n : ℕ)
    (par : Fin (n + 1) → Fin (n + 1)) (bags : Fin (n + 1) → List ℕ) (t : ℕ) :
    tablesInst adj wt n par bags (t + 1) =
      let prev := tablesInst adj wt n par bags t
      let j := Fin.ofNat (n + 1) (n - t)
      let p := par j
      let init := Array.replicate (2 ^ (bags p).length) 0
      let best := childPassInst adj wt (bags j) (bags p) prev[j] init (2 ^ (bags j).length)
      let tp := parentPass (bags j) (bags p) prev[p] best (2 ^ (bags p).length)
      prev.set p tp p.isLt := by rfl

namespace MWISInstance

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

/-- Every node's bag length is at most `inst.maxBagLen`. -/
theorem bagAt_length_le (inst : MWISInstance)
    (i : Fin (inst.numNodes + 1)) : (inst.bagAt i).length ≤ inst.maxBagLen := by
  have hmem : inst.bagAt i ∈ inst.bags := List.getElem_mem _
  exact List.mem_le_foldl_max (List.mem_map_of_mem hmem)

/-- Every vertex in `inst.bagAt i` is `< inst.numVerts`. -/
theorem bagAt_mem_lt (inst : MWISInstance)
    (i : Fin (inst.numNodes + 1)) : ∀ u ∈ inst.bagAt i, u < inst.numVerts :=
  inst.bags_lt (inst.bagAt i) (List.getElem_mem _)

end MWISInstance

end Cslib.Algorithms.WordRAM.TreeDecomposition
