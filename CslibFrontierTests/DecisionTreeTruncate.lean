/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.DecisionTree.Truncate
import Mathlib.Tactic.NormNum

/-! # Tests for truncating decision trees

`andTree` computes the conjunction of two bits with three leaves: it queries `x₀`, and if it is
`true` queries `x₁`. Its paths never repeat a query; cutting them at length `1` keeps the short
path and cuts the long ones, which are followed with probability `1 / 2 ≤ 3 / 2 ^ 2`, so the
truncation errs on exactly half the inputs (Exercise 3.22 at `ε = 3 / 2`, where
`⌊log₂ (3 / (3 / 2))⌋ = 1`). Read as signs, the conjunction has weight exactly `1 / 4` above
degree `1`, within the bound `3 / 2 ^ 2` for three leaves, and within the `ε = 3 / 2` of
Proposition 3.17, whose degree is `log₂ (3 / (3 / 2)) = 1`. At `ε = 4 > 3` the degree
`log₂ (3 / 4)` is negative, so Proposition 3.17 bounds the whole weight.

`chain` queries `x₀` four times and has five leaves, yet follows a path of length more than `3`
with probability `1 / 2 > 5 / 2 ^ 4`: the bound on long paths needs distinct queries. Pruning it
leaves two leaves and no repeated query. It computes `¬x₀`, whose weight above degree `0` is
exactly `1`, which meets the bound `2 / 2 ^ 1` for the pruned tree. -/

public section

namespace CslibFrontierTests.DecisionTreeTruncate

open Cslib Cslib.DecisionTree Cslib.BitString Finset

/-- The conjunction of two bits as a decision tree with three leaves. -/
def andTree : DecisionTree (Fin 2) Bool :=
  .node 0 (.leaf false) (.node 1 (.leaf false) (.leaf true))

/-- `andTree` never repeats a query. -/
theorem andTree_queriesDistinct : andTree.QueriesDistinct := by
  simp [andTree, QueriesDistinctFrom]

/-- The tree that outputs `x₀`. -/
def rootTree : DecisionTree (Fin 2) Bool := .node 0 (.leaf false) (.leaf true)

/-- A tree that avoids `{1}` never queries `x₁`. -/
example : rootTree.QueriesDistinctFrom {1} ∧ ∀ x, 1 ∉ rootTree.queries x := by
  have h : rootTree.QueriesDistinctFrom {1} := by simp [rootTree, QueriesDistinctFrom]
  exact ⟨h, fun x hx => h.notMem_queries x hx (mem_singleton_self 1)⟩

/-- Cutting at length `1` keeps the short path and cuts the long ones, as `eval_truncate`
predicts from the path lengths. -/
example : (andTree.truncate 1).eval ![false, true] = some false ∧
    (andTree.truncate 1).eval ![true, true] = none ∧
    (andTree.truncate 1).depth ≤ 1 := by
  refine ⟨?_, ?_, depth_truncate_le 1 andTree⟩
  · rw [eval_truncate]
    decide
  · rw [eval_truncate]
    decide

/-- The inputs `00` and `01` agree on the only coordinate queried for `00`, so they follow the
same path. -/
example : andTree.path ![false, true] = andTree.path ![false, false] :=
  andTree.path_eq_of_forall_mem_queries fun i hi => by
    have : andTree.queries ![false, false] = {0} := by decide
    rw [this, mem_singleton] at hi
    subst hi
    rfl

/-- A tree querying `x₀` twice on a path does not have distinct queries. -/
example : ¬(DecisionTree.node 0 (.leaf false) (.node 0 (.leaf false) (.leaf true)) :
    DecisionTree (Fin 2) Bool).QueriesDistinct := by
  simp [QueriesDistinctFrom]

/-- Paths of length more than `1` are followed with probability `1 / 2`, within the bound
`3 / 2 ^ 2`. -/
example : (dens {x : Fin 2 → Bool | 1 < (andTree.path x).length} : ℝ) = 1 / 2 ∧
    (dens {x : Fin 2 → Bool | 1 < (andTree.path x).length} : ℝ) ≤
      andTree.leafCount / 2 ^ (1 + 1) := by
  refine ⟨?_, dens_lt_length_path_le andTree_queriesDistinct 1⟩
  rw [dens_eq_card_div_card,
    show #{x : Fin 2 → Bool | 1 < (andTree.path x).length} = 2 by decide]
  norm_num

/-- The truncation at length `1` errs on exactly half the inputs, within the bound `3 / 2 ^ 2`. -/
example : (dens {x : Fin 2 → Bool | (andTree.truncate 1).eval x ≠ some (andTree.eval x)} : ℝ) =
      1 / 2 ∧
    (dens {x : Fin 2 → Bool | (andTree.truncate 1).eval x ≠ some (andTree.eval x)} : ℝ) ≤
      andTree.leafCount / 2 ^ (1 + 1) := by
  refine ⟨?_, dens_eval_truncate_ne_le andTree_queriesDistinct 1⟩
  simp_rw [eval_truncate]
  rw [dens_eq_card_div_card, show #{x : Fin 2 → Bool | (if (andTree.path x).length ≤ 1 then
    some (andTree.eval x) else none) ≠ some (andTree.eval x)} = 2 by decide]
  norm_num

/-- Exercise 3.22 at `ε = 3 / 2`: the cut is at `⌊log₂ (3 / (3 / 2))⌋ = 1`, and the truncation
errs on at most a `3 / 2` fraction of inputs. -/
example : ⌊Real.logb 2 (andTree.leafCount / (3 / 2))⌋₊ = 1 ∧
    (dens {x : Fin 2 → Bool | (andTree.truncate ⌊Real.logb 2 (andTree.leafCount / (3 / 2))⌋₊).eval
      x ≠ some (andTree.eval x)} : ℝ) ≤ 3 / 2 := by
  refine ⟨?_, dens_eval_truncate_floor_logb_ne_le andTree_queriesDistinct (by norm_num)⟩
  rw [show (andTree.leafCount : ℝ) / (3 / 2) = 2 by norm_num [andTree, leafCount],
    Real.logb_self_eq_one one_lt_two, Nat.floor_one]

/-- The conjunction of two bits, read as signs, has Fourier weight `1 / 4` above degree `1`. -/
theorem sum_fourierCoeff_sq_andTree :
    ∑ S with 1 < #S, fourierCoeff (fun x => signVal (andTree.eval x)) S ^ 2 = 1 / 4 := by
  have : ({S : Finset (Fin 2) | 1 < #S} : Finset _) = {univ} := by decide
  rw [this, sum_singleton, fourierCoeff_eq_sum]
  rw [← Equiv.sum_comp (piFinTwoEquiv (fun _ => Bool)).symm]
  simp [piFinTwoEquiv, Fintype.sum_prod_type, andTree, chi, Fin.prod_univ_two]
  norm_num

/-- The weight `1 / 4` is within the bound `3 / 2 ^ 2 = 3 / 4` for a tree with three leaves. -/
example : (1 : ℝ) / 4 ≤ 3 / 4 :=
  calc (1 : ℝ) / 4
      = ∑ S with 1 < #S, fourierCoeff (fun x => signVal (andTree.eval x)) S ^ 2 :=
        sum_fourierCoeff_sq_andTree.symm
    _ ≤ andTree.leafCount / 2 ^ (1 + 1) :=
        sum_fourierCoeff_sq_le_leafCount_div (fun b => signVal b) (fun b => by simp) andTree 1
    _ = 3 / 4 := by norm_num [andTree, leafCount]

/-- Proposition 3.17 at `ε = 3 / 2`: the degree is `log₂ (3 / (3 / 2)) = 1`, and the weight
`1 / 4` above it is at most `3 / 2`. -/
example : Real.logb 2 (andTree.leafCount / (3 / 2)) = 1 ∧
    ∑ S with Real.logb 2 (andTree.leafCount / (3 / 2)) < #S,
      fourierCoeff (fun x => signVal (andTree.eval x)) S ^ 2 ≤ 3 / 2 := by
  have h : Real.logb 2 (andTree.leafCount / (3 / 2)) = 1 := by
    rw [show (andTree.leafCount : ℝ) / (3 / 2) = 2 by norm_num [andTree, leafCount]]
    exact Real.logb_self_eq_one one_lt_two
  refine ⟨h, sum_fourierCoeff_sq_logb_lt_card_le (fun b => signVal b) (fun b => by simp) andTree
    (by norm_num)⟩

/-- Proposition 3.17 at `ε = 4`, more than the three leaves: the degree `log₂ (3 / 4)` is
negative, so every set counts, and the whole weight is at most `4`. -/
example : Real.logb 2 (andTree.leafCount / 4) < 0 ∧
    ∑ S with Real.logb 2 (andTree.leafCount / 4) < #S,
      fourierCoeff (fun x => signVal (andTree.eval x)) S ^ 2 ≤ 4 := by
  refine ⟨Real.logb_neg one_lt_two (by norm_num [andTree, leafCount])
    (by norm_num [andTree, leafCount]), sum_fourierCoeff_sq_logb_lt_card_le (fun b => signVal b)
    (fun b => by simp) andTree (by norm_num)⟩

/-- A chain querying `x₀` four times, with five leaves. -/
def chain : DecisionTree (Fin 1) Bool :=
  .node 0 (.node 0 (.node 0 (.node 0 (.leaf true) (.leaf false)) (.leaf false)) (.leaf false))
    (.leaf false)

/-- The chain repeats queries, and its long paths are more frequent than `5 / 2 ^ 4`. -/
example : ¬chain.QueriesDistinct ∧
    (chain.leafCount : ℝ) / 2 ^ (3 + 1) <
      dens {x : Fin 1 → Bool | 3 < (chain.path x).length} := by
  refine ⟨by simp [chain, QueriesDistinctFrom], ?_⟩
  rw [dens_eq_card_div_card,
    show #{x : Fin 1 → Bool | 3 < (chain.path x).length} = 1 by decide]
  norm_num [chain, leafCount]

/-- Pruning the chain leaves a tree with two leaves and no repeated query. -/
example : (chain.prune PartialAssignment.empty).QueriesDistinct ∧
    (chain.prune PartialAssignment.empty).leafCount = 2 ∧
    (chain.prune PartialAssignment.empty).leafCount ≤ chain.leafCount :=
  ⟨queriesDistinctFrom_prune (by simp) chain, by decide, leafCount_prune_le chain _⟩

/-- The chain computes `¬x₀`, read as signs `-χ_{0}`. -/
theorem signVal_eval_chain (x : Fin 1 → Bool) : signVal (chain.eval x) = -chi ℝ {0} x := by
  rcases Bool.eq_false_or_eq_true (x 0) with h | h <;> simp [chain, chi, h]

/-- The chain has weight exactly `1` above degree `0`, which meets the bound `2 / 2 ^ 1` for its
pruned tree. -/
example : ∑ S with 0 < #S, fourierCoeff (fun x => signVal (chain.eval x)) S ^ 2 = 1 ∧
    ∑ S with 0 < #S, fourierCoeff (fun x => signVal (chain.eval x)) S ^ 2 ≤
      (chain.prune PartialAssignment.empty).leafCount / 2 ^ (0 + 1) := by
  have h1 : ∑ S with 0 < #S, fourierCoeff (fun x => signVal (chain.eval x)) S ^ 2 = 1 := by
    have : ({S : Finset (Fin 1) | 0 < #S} : Finset _) = {{0}} := by decide
    simp_rw [this, sum_singleton, signVal_eval_chain]
    rw [show (fun x : Fin 1 → Bool => -chi ℝ {0} x) = fun x => (-1) * chi ℝ {0} x by
      funext x; ring, fourierCoeff_const_mul, fourierCoeff_chi]
    norm_num
  refine ⟨h1, ?_⟩
  have h := sum_fourierCoeff_sq_le_leafCount_div (fun b => signVal b) (fun b => by simp)
    (chain.prune PartialAssignment.empty) 0
  simp only [eval_prune_empty] at h
  exact h

end CslibFrontierTests.DecisionTreeTruncate
