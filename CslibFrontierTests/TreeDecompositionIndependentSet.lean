/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSetFPT
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.VecNotation
meta import CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSetFPT
meta import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet
meta import Mathlib.Combinatorics.SimpleGraph.Hasse
meta import Mathlib.Data.Fin.VecNotation

/-! # Maximum-weight independent sets over tree decompositions on small graphs

Kernel-checked runs of the pure tree-decomposition dynamic program (`mwisFPT`) and Word-RAM
realization (`exists_program_mwis_rooted`), with no `native_decide`:

1. the weighted path `0 - 1 - 2 - 3` with weights `3, 5, 4, 1` and a width-one decomposition:
   the value `7` (attained by `{0, 2}`) and the independence number `2` read off the unit-weight
   run;
2. the five-cycle with a width-two fan decomposition: the independence number `2` and a weighted
   value in which the best set avoids the heaviest vertex's neighbours;
3. a one-node decomposition of the edgeless graph on three vertices, where every vertex is chosen;
4. the star `K_{1,3}` with a root bag `{0}` and three children, which exercises the sum of
   several child messages: the independence number `3` and two weighted values;
5. the pure executable program `mwisFPT` on the same decompositions, a bag ordering that
   `IsBagOrder` rejects, and a compiled run on the orderings built by `sortedBags`;
6. a family of path decompositions of every depth `N`, evaluated by `decide +kernel` at depth `40`
   and by `#guard` at depth `2000`;
7. checked Word-RAM `MWISInstance` encodings and non-vacuous `Fits` / `InputFits` witnesses for
   `exists_program_mwis_rooted` (including width invariance `w = 8` vs `w = 16`, edgeless single-bag
   `n = 0`, and `starDecomposition`).
-/

-- The `#guard` checks of sections 5–7 evaluate compiled definitions (`deepPath 2000`, `sortedBags`,
-- and `MWISInstance.result`) beyond the practical unrolling reach of `decide`.
set_option linter.hashCommand false

public section

namespace Cslib.Tests.TreeDecompositionIndependentSet

open SimpleGraph Cslib.Algorithms.Lean Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.Algorithms.WordRAM.TreeDecomposition Cslib.WordRAM

/-! ### 1. A weighted path -/

/-- The path `0 - 1 - 2 - 3` with bags `{0, 1}`, `{1, 2}`, `{2, 3}` along the node path
`0 - 1 - 2`. -/
def pathDecomposition : (pathGraph 4).RootedTreeDecomposition 2 where
  parent := ![0, 0, 1]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0, 1}, {1, 2}, {2, 3}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

/-- Vertex weights `3, 5, 4, 1`. -/
def pathWeight : Fin 4 → ℕ := ![3, 5, 4, 1]

/-- The program returns `7`, the weight of `{0, 2}`. -/
example : mwisValue pathDecomposition pathWeight = 7 := by decide

/-- So no independent set of the weighted path weighs more than `7`, and `{0, 2}` attains it. -/
example : IsGreatest {x | ∃ I : Finset (Fin 4), (pathGraph 4).IsIndepSet (↑I : Set (Fin 4)) ∧
    ∑ v ∈ I, pathWeight v = x} 7 := by
  have h := isGreatest_mwisValue pathDecomposition pathWeight
  rwa [show mwisValue pathDecomposition pathWeight = 7 by decide] at h

/-- The unit-weight run computes the independence number of the path. -/
example : (pathGraph 4).indepNum = 2 := by
  rw [← mwisValue_one_eq_indepNum pathDecomposition]
  decide

/-! ### 2. The five-cycle -/

/-- The five-cycle `0 - 1 - 2 - 3 - 4 - 0`. -/
def cycle5 : SimpleGraph (Fin 5) where
  Adj i j := j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i h => by omega⟩

instance : DecidableRel cycle5.Adj := fun i j =>
  inferInstanceAs (Decidable (j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5))

/-- The fan decomposition of the five-cycle: bags `{0, 1, 2}`, `{0, 2, 3}`, `{0, 3, 4}` along
the node path `0 - 1 - 2`. -/
def cycleDecomposition : cycle5.RootedTreeDecomposition 2 where
  parent := ![0, 0, 1]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0, 1, 2}, {0, 2, 3}, {0, 3, 4}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

/-- The five-cycle has independence number two. -/
example : cycle5.indepNum = 2 := by
  rw [← mwisValue_one_eq_indepNum cycleDecomposition]
  decide

/-- With weights `1, 1, 10, 1, 1` the best independent set is `{0, 2}` or `{2, 4}`, of weight
`11`. -/
example : mwisValue cycleDecomposition ![1, 1, 10, 1, 1] = 11 := by decide

/-! ### 3. An edgeless graph with one bag -/

/-- The edgeless graph on three vertices with a single bag. -/
def bagDecomposition : (⊥ : SimpleGraph (Fin 3)).RootedTreeDecomposition 0 where
  parent := ![0]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0, 1, 2}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

/-- Every vertex is chosen. -/
example : mwisValue bagDecomposition ![2, 3, 4] = 9 := by decide

/-! ### 4. A star with three children -/

/-- The star `K_{1,3}` with centre `0` and leaves `1, 2, 3`. -/
def star : SimpleGraph (Fin 4) where
  Adj i j := i ≠ j ∧ (i = 0 ∨ j = 0)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel star.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ (i = 0 ∨ j = 0)))

/-- The star decomposition: root bag `{0}` and three children with bags `{0, ℓ}`, so the root
table is the sum of three child messages. -/
def starDecomposition : star.RootedTreeDecomposition 3 where
  parent := ![0, 0, 0, 0]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0}, {0, 1}, {0, 2}, {0, 3}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

/-- The unit-weight run sums the three leaf messages: the independence number is `3`. -/
example : star.indepNum = 3 := by
  rw [← mwisValue_one_eq_indepNum starDecomposition]
  decide

/-- With weights `2, 1, 1, 1` the three leaves (total `3`) beat the centre; with weights
`5, 1, 1, 1` the centre wins. -/
example : mwisValue starDecomposition ![2, 1, 1, 1] = 3 ∧
    mwisValue starDecomposition ![5, 1, 1, 1] = 5 := by
  decide

/-! ### 5. The executable program -/

/-- The bags of `pathDecomposition`, in increasing order. -/
def pathBags : Fin 3 → List (Fin 4) := ![[0, 1], [1, 2], [2, 3]]

example : IsBagOrder pathDecomposition pathBags := by decide

/-- A list with a repeated vertex is not a bag ordering. -/
example : ¬IsBagOrder pathDecomposition ![[0, 1, 0], [1, 2], [2, 3]] := by decide

example : mwisFPT pathDecomposition pathWeight pathBags = 7 := by decide

example : mwisFPT cycleDecomposition ![1, 1, 10, 1, 1]
    ![[0, 1, 2], [0, 2, 3], [0, 3, 4]] = 11 := by
  decide

example : mwisFPT bagDecomposition ![2, 3, 4] ![[0, 1, 2]] = 9 := by decide

example : mwisFPT starDecomposition ![2, 1, 1, 1] ![[0], [0, 1], [0, 2], [0, 3]] = 3 ∧
    mwisFPT starDecomposition ![5, 1, 1, 1] ![[0], [0, 1], [0, 2], [0, 3]] = 5 := by
  decide

/-- The independence number of the star, from the executable program. -/
example : star.indepNum = 3 := by
  rw [← mwisFPT_one_eq_indepNum starDecomposition
    (L := ![[0], [0, 1], [0, 2], [0, 3]]) (by decide)]
  decide

/-! ### 6. Deep path decompositions -/

/-- The path decomposition of the path on `N + 2` vertices: node `i` has bag `{i, i + 1}` and
parent `i - 1`, so the decomposition is a path of depth `N`. -/
def deepPath (N : ℕ) : (pathGraph (N + 2)).RootedTreeDecomposition N where
  parent i := ⟨i.val - 1, by omega⟩
  parent_zero := rfl
  parent_lt i hi := by
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    rw [Fin.lt_def]
    simp only
    omega
  bag i := {⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩}
  exists_mem_bag v := ⟨⟨v.val - 1, by omega⟩, by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega⟩
  exists_adj_mem_bag u v h := by
    rw [pathGraph_adj] at h
    refine ⟨⟨min u.val v.val, by omega⟩, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  top_unique v i j hi hi' hj hj' := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_zero] at hi hi' hj hj'
    ext
    omega

/-- The bags of `deepPath N` in increasing order. -/
def deepBags (N : ℕ) : Fin (N + 1) → List (Fin (N + 2)) :=
  fun i => [⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩]

theorem isBagOrder_deepBags (N : ℕ) : IsBagOrder (deepPath N) (deepBags N) := fun i =>
  ⟨by simp [deepBags, Fin.ext_iff], by simp [deepBags, deepPath]⟩

/-- With unit weights it returns the independence number `21` of the path on `42` vertices. -/
example : mwisFPT (deepPath 40) (fun _ => 1) (deepBags 40) = 21 := by decide +kernel

example : (pathGraph 42).indepNum = 21 := by
  rw [← mwisFPT_one_eq_indepNum (deepPath 40) (isBagOrder_deepBags 40)]
  decide +kernel

/- Compiled evaluation at depth `2000`. -/
#guard mwisFPT (deepPath 2000) (fun _ => 1) (deepBags 2000) == 1001

/-- `sortedBags` orders the bags of a decomposition of a linearly ordered vertex type, so
`mwisFPT_eq_mwisValue` applies to it. -/
example : mwisFPT pathDecomposition pathWeight (sortedBags pathDecomposition) = 7 := by
  rw [mwisFPT_eq_mwisValue _ _ (isBagOrder_sortedBags _)]
  decide

/- The compiled program on the orderings built by `sortedBags`, which `decide` cannot unfold. -/
#guard mwisFPT pathDecomposition pathWeight (sortedBags pathDecomposition) == 7
#guard mwisFPT cycleDecomposition ![1, 1, 10, 1, 1] (sortedBags cycleDecomposition) == 11

/-! ### 7. Word-RAM FPT execution witnesses -/

/-- Encoded Word-RAM instance for `pathDecomposition`. -/
def pathInst : MWISInstance :=
  MWISInstance.ofRooted (Equiv.refl (Fin 4)) pathDecomposition pathWeight pathBags

/-- Encoded Word-RAM instance for the single-bag edgeless graph `bagDecomposition`. -/
def bagInst : MWISInstance :=
  MWISInstance.ofRooted (Equiv.refl (Fin 3)) bagDecomposition ![2, 3, 4] ![[0, 1, 2]]

/-- Encoded Word-RAM instances for `starDecomposition`. -/
def starInstLow : MWISInstance :=
  MWISInstance.ofRooted (Equiv.refl (Fin 4)) starDecomposition ![2, 1, 1, 1]
    ![[0], [0, 1], [0, 2], [0, 3]]

def starInstHigh : MWISInstance :=
  MWISInstance.ofRooted (Equiv.refl (Fin 4)) starDecomposition ![5, 1, 1, 1]
    ![[0], [0, 1], [0, 2], [0, 3]]

#guard pathInst.result == 7
#guard bagInst.result == 9
#guard starInstLow.result == 3
#guard starInstHigh.result == 5

example : ∃ r C : ℕ, ∃ prog : Program .exact r,
    (∀ w ∈ ([8, 16] : List ℕ), Fits w pathInst.wordBound ∧ InputFits w pathInst.encode ∧
      ∃ steps, Executes w prog (.init pathInst.encode) 7 steps ∧
        steps ≤ C * (mwisFPTBound 2 1 + 1) + 1) ∧
    (∃ steps, Executes 8 prog (.init bagInst.encode) 9 steps ∧
      steps ≤ C * (mwisFPTBound 0 2 + 1) + 1) ∧
    (∃ steps, Executes 9 prog (.init starInstLow.encode) 3 steps ∧
      steps ≤ C * (mwisFPTBound 3 1 + 1) + 1) := by
  obtain ⟨r, C, prog, hprog⟩ := exists_program_mwis_rooted
  refine ⟨r, C, prog, ?_, ?_, ?_⟩
  · intro w hw
    have hw816 : w = 8 ∨ w = 16 := by simpa using hw
    have hfit : Fits w pathInst.wordBound := by
      rcases hw816 with rfl | rfl <;> decide
    have hin : InputFits w pathInst.encode := by
      rcases hw816 with rfl | rfl <;> decide
    obtain ⟨steps, hex, hle⟩ := hprog (k := 1) (Equiv.refl (Fin 4)) pathDecomposition pathWeight
      pathBags (by decide) (pathDecomposition.width_le_iff.2 (by decide)) w hfit hin
    rw [show mwisValue pathDecomposition pathWeight = 7 by decide] at hex
    exact ⟨hfit, hin, steps, hex, hle⟩
  · obtain ⟨steps, hex, hle⟩ := hprog (k := 2) (Equiv.refl (Fin 3)) bagDecomposition ![2, 3, 4]
      ![[0, 1, 2]] (by decide) (bagDecomposition.width_le_iff.2 (by decide)) 8
      (by decide) (by decide)
    rw [show mwisValue bagDecomposition ![2, 3, 4] = 9 by decide] at hex
    exact ⟨steps, hex, hle⟩
  · obtain ⟨steps, hex, hle⟩ := hprog (k := 1) (Equiv.refl (Fin 4)) starDecomposition ![2, 1, 1, 1]
      ![[0], [0, 1], [0, 2], [0, 3]] (by decide) (starDecomposition.width_le_iff.2 (by decide)) 9
      (by decide) (by decide)
    rw [show mwisValue starDecomposition ![2, 1, 1, 1] = 3 by decide] at hex
    exact ⟨steps, hex, hle⟩

end Cslib.Tests.TreeDecompositionIndependentSet
