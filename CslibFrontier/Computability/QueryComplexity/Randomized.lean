/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Probability.Minimax
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
import CslibFrontier.Foundations.Data.ENat.IInf
import Mathlib.Tactic.NormNum

/-!
# Randomized decision trees

A randomized decision tree tosses coins, uses them to pick a deterministic decision tree, and runs
it. We represent it by the distribution over decision trees that it draws from, a finitely
supported probability distribution `Convexity.StdSimplex ℝ (DecisionTree ι β)`
(`RandomizedDecisionTree`). Its depth is the largest depth of a tree it can draw: the number of
queries it makes in the worst case over the inputs and the coins (`RandomizedDecisionTree.depth`).
It computes `f` with error `ε` when on every input the tree it draws outputs a wrong value with
probability at most `ε` (`RandomizedDecisionTree.errorProb`, `RandomizedDecisionTree.Computes`).
The randomized decision tree complexity `R_ε(f)` is the least depth of a randomized decision tree
computing `f` with error `ε` (`QueryComplexity.randomizedComplexity`) [BuhrmanDeWolf2002]; the
bounded-error complexity `R(f)` of the literature is `R_{1/3}(f)`.

Deterministic trees are randomized trees that draw one tree, so `R_ε(f) ≤ D(f)` for `ε ≥ 0`
(`DecisionTree.randomizedComplexity_le_complexity`). With error `0` every tree that can be drawn
computes `f`, so `R_0(f) = D(f)` (`QueryComplexity.randomizedComplexity_zero`); zero-error
complexity in the literature usually counts the expected number of queries instead, which can be
smaller. A fair coin guesses a Boolean value correctly with probability `1/2`, so `R_ε(f) = 0` for
Boolean-valued `f` and `ε ≥ 1/2` (`QueryComplexity.randomizedComplexity_eq_zero_of_le`).

If a randomized tree computes `f` with error `ε`, then for every distribution `ν` on the inputs
some tree that it can draw errs with probability at most `ε` on inputs drawn from `ν`
(`RandomizedDecisionTree.Computes.exists_distributionalError_le`, from
`Convexity.StdSimplex.exists_mem_support_le_sum_mul` in `CslibFrontier.Probability.Minimax`). This
averaging argument is the easy direction of Yao's principle [Yao1977]; the converse follows from
the minimax theorem (`QueryComplexity.exists_computes_of_forall_exists_distributionalError_le`).

Post-processing the output with a function `g` (`RandomizedDecisionTree.mapOutput`) makes no
further queries and errs against `g ∘ f` at most as often as the original tree errs against `f`
(`RandomizedDecisionTree.errorProb_mapOutput_le`); so lower bounds for computing `g ∘ f` are lower
bounds for computing `f`. More generally, a transformation `φ` of the drawn tree
(`RandomizedDecisionTree.mapTree`), such as appending a verification to every leaf, adds the
queries that `φ` adds (`RandomizedDecisionTree.depth_mapTree_le`) and no error when `φ` preserves
correctness (`RandomizedDecisionTree.errorProb_mapTree_le`).

## Main definitions

* `Cslib.RandomizedDecisionTree`: randomized decision trees, as finitely supported distributions
  over decision trees, with `RandomizedDecisionTree.depth`, `RandomizedDecisionTree.errorProb` and
  `RandomizedDecisionTree.Computes`.
* `Cslib.RandomizedDecisionTree.mapTree`: transforming the drawn tree.
* `Cslib.RandomizedDecisionTree.mapOutput`: post-processing the output.
* `Cslib.DecisionTree.distributionalError`: the error of a decision tree on inputs drawn from a
  distribution.
* `Cslib.QueryComplexity.randomizedComplexity`: the randomized decision tree complexity `R_ε(f)`.

## Main results

* `Cslib.RandomizedDecisionTree.Computes.exists_distributionalError_le`: the averaging argument.
* `Cslib.RandomizedDecisionTree.depth_mapTree_le`,
  `Cslib.RandomizedDecisionTree.errorProb_mapTree_le`: transforming the drawn tree adds the queries
  of the transformation and no error when it preserves correctness.
* `Cslib.RandomizedDecisionTree.depth_mapOutput_le`,
  `Cslib.RandomizedDecisionTree.errorProb_mapOutput_le`: post-processing adds no queries and no
  error.
* `Cslib.DecisionTree.randomizedComplexity_le_complexity`: `R_ε(f) ≤ D(f)` for `ε ≥ 0`.
* `Cslib.QueryComplexity.randomizedComplexity_zero`: `R_0(f) = D(f)`.
* `Cslib.QueryComplexity.randomizedComplexity_antitone`: `R_ε(f)` decreases as `ε` grows.
* `Cslib.QueryComplexity.randomizedComplexity_eq_zero_of_le`: `R_ε(f) = 0` for Boolean-valued `f`
  and `ε ≥ 1/2`.

## References

* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
-/

@[expose] public section

open scoped NNReal

namespace Cslib

open Convexity

/-- A randomized decision tree over Boolean variables indexed by `ι`, with outputs in `β`: a
finitely supported probability distribution over decision trees. It draws a tree from this
distribution and runs it. -/
abbrev RandomizedDecisionTree (ι β : Type*) : Type _ :=
  StdSimplex ℝ (DecisionTree ι β)

namespace DecisionTree

variable {ι β : Type*}

open Classical in
/-- The error of a decision tree `t` on inputs drawn from `ν`: the probability that on an input `x`
drawn from `ν` it outputs a value other than `f x`. -/
noncomputable def distributionalError (t : DecisionTree ι β) (ν : StdSimplex ℝ (ι → Bool))
    (f : (ι → Bool) → β) : ℝ :=
  ν.errorProb fun x => t.eval x = f x

/-- `distributionalError` with any decidable equality on the outputs. -/
theorem distributionalError_eq_sum [DecidableEq β] (t : DecisionTree ι β)
    (ν : StdSimplex ℝ (ι → Bool)) (f : (ι → Bool) → β) :
    t.distributionalError ν f = ν.weights.sum fun x w => w * if t.eval x = f x then 0 else 1 :=
  StdSimplex.errorProb_eq_sum (fun x => t.eval x = f x) ν

variable {t : DecisionTree ι β} {ν : StdSimplex ℝ (ι → Bool)} {f : (ι → Bool) → β}

theorem distributionalError_nonneg : 0 ≤ t.distributionalError ν f :=
  StdSimplex.errorProb_nonneg

/-- A decision tree computing `f` has error `0` on every distribution. -/
theorem Computes.distributionalError_eq_zero (ht : t.Computes f) :
    t.distributionalError ν f = 0 :=
  StdSimplex.errorProb_eq_zero_iff.mpr fun x _ => ht x

end DecisionTree

namespace RandomizedDecisionTree

variable {ι β : Type*}

/-- The depth of a randomized decision tree: the largest depth of a tree that it can draw, so the
number of queries it makes in the worst case over the inputs and the coins. -/
def depth (μ : RandomizedDecisionTree ι β) : ℕ :=
  StdSimplex.maxCost DecisionTree.depth μ

open Classical in
/-- The probability that the tree drawn from `μ` outputs on `x` a value other than `f x`. -/
noncomputable def errorProb (μ : RandomizedDecisionTree ι β) (f : (ι → Bool) → β)
    (x : ι → Bool) : ℝ :=
  StdSimplex.errorProb (fun t : DecisionTree ι β => t.eval x = f x) μ

/-- A randomized decision tree `μ` computes `f` with error `ε` when on every input the tree drawn
from `μ` outputs a wrong value with probability at most `ε`. -/
def Computes (μ : RandomizedDecisionTree ι β) (ε : ℝ) (f : (ι → Bool) → β) : Prop :=
  ∀ x, μ.errorProb f x ≤ ε

/-- `errorProb` with any decidable equality on the outputs. -/
theorem errorProb_eq_sum [DecidableEq β] (μ : RandomizedDecisionTree ι β) (f : (ι → Bool) → β)
    (x : ι → Bool) :
    μ.errorProb f x = μ.weights.sum fun t w => w * if t.eval x = f x then 0 else 1 :=
  StdSimplex.errorProb_eq_sum (fun t : DecisionTree ι β => t.eval x = f x) μ

variable {μ : RandomizedDecisionTree ι β} {f : (ι → Bool) → β} {t : DecisionTree ι β}
  {ε ε' : ℝ} {d : ℕ} {x : ι → Bool}

theorem depth_le_iff : μ.depth ≤ d ↔ ∀ t ∈ μ.weights.support, t.depth ≤ d :=
  StdSimplex.maxCost_le_iff

theorem depth_le_depth (ht : t ∈ μ.weights.support) : t.depth ≤ μ.depth :=
  StdSimplex.le_maxCost ht

@[simp] theorem depth_single (t : DecisionTree ι β) :
    depth (StdSimplex.single t : RandomizedDecisionTree ι β) = t.depth :=
  StdSimplex.maxCost_single DecisionTree.depth t

theorem errorProb_nonneg : 0 ≤ μ.errorProb f x :=
  StdSimplex.errorProb_nonneg

theorem errorProb_le_one : μ.errorProb f x ≤ 1 :=
  StdSimplex.errorProb_le_one

theorem errorProb_eq_zero_iff :
    μ.errorProb f x = 0 ↔ ∀ t ∈ μ.weights.support, t.eval x = f x :=
  StdSimplex.errorProb_eq_zero_iff

private theorem errorProb_single_of_eq (h : t.eval x = f x) :
    errorProb (StdSimplex.single t : RandomizedDecisionTree ι β) f x = 0 :=
  StdSimplex.errorProb_single_of_pos h

private theorem errorProb_single_of_ne (h : t.eval x ≠ f x) :
    errorProb (StdSimplex.single t : RandomizedDecisionTree ι β) f x = 1 :=
  StdSimplex.errorProb_single_of_neg h

theorem Computes.mono (h : μ.Computes ε f) (hε : ε ≤ ε') : μ.Computes ε' f :=
  fun x => (h x).trans hε

/-- A randomized decision tree can only compute with nonnegative error. -/
theorem Computes.nonneg (h : μ.Computes ε f) : 0 ≤ ε :=
  errorProb_nonneg.trans (h fun _ => false)

/-- A deterministic decision tree computing `f` computes it with any nonnegative error. -/
theorem computes_single (ht : t.Computes f) (hε : 0 ≤ ε) :
    Computes (StdSimplex.single t : RandomizedDecisionTree ι β) ε f :=
  fun x => (errorProb_single_of_eq (ht x)).trans_le hε

/-- A randomized decision tree computes `f` with error `0` exactly when every tree it can draw
computes `f`. -/
theorem computes_zero_iff : μ.Computes 0 f ↔ ∀ t ∈ μ.weights.support, t.Computes f :=
  ⟨fun h t ht x => errorProb_eq_zero_iff.mp ((h x).antisymm errorProb_nonneg) t ht,
    fun h x => (errorProb_eq_zero_iff.mpr fun t ht => h t ht x).le⟩

/-- **The averaging argument**, the easy direction of Yao's principle: if `μ` computes `f` with
error `ε`, then for every distribution `ν` on the inputs some tree that `μ` can draw errs with
probability at most `ε` on inputs drawn from `ν`. -/
theorem Computes.exists_distributionalError_le (h : μ.Computes ε f)
    (ν : StdSimplex ℝ (ι → Bool)) : ∃ t ∈ μ.weights.support, t.distributionalError ν f ≤ ε :=
  StdSimplex.exists_errorProb_le (fun (t : DecisionTree ι β) x => t.eval x = f x) μ ν h

/-! ### Transforming the drawn tree -/

/-- Transform the tree drawn from `μ` by `φ`: draw a tree `t` from `μ` and run `φ t`. -/
noncomputable def mapTree {γ : Type*} (φ : DecisionTree ι β → DecisionTree ι γ)
    (μ : RandomizedDecisionTree ι β) : RandomizedDecisionTree ι γ :=
  StdSimplex.map φ μ

/-- Every tree that `mapTree φ μ` can draw is `φ t` for a tree `t` that `μ` can draw. -/
theorem exists_of_mem_support_mapTree {γ : Type*} {φ : DecisionTree ι β → DecisionTree ι γ}
    {u : DecisionTree ι γ} (hu : u ∈ (mapTree φ μ).weights.support) :
    ∃ t ∈ μ.weights.support, φ t = u :=
  StdSimplex.exists_of_mem_support_map hu

/-- If `φ` adds at most `d` queries to every tree, then so does `mapTree φ`. -/
theorem depth_mapTree_le {γ : Type*} (φ : DecisionTree ι β → DecisionTree ι γ)
    (μ : RandomizedDecisionTree ι β) {d : ℕ} (hφ : ∀ t, (φ t).depth ≤ t.depth + d) :
    (mapTree φ μ).depth ≤ μ.depth + d :=
  StdSimplex.maxCost_map_le DecisionTree.depth DecisionTree.depth φ μ hφ

/-- If `φ` turns every tree that outputs `f x` on `x` into one that outputs `g x` on `x`, then
`mapTree φ μ` errs against `g` on `x` at most as often as `μ` errs against `f`. -/
theorem errorProb_mapTree_le {γ : Type*} (φ : DecisionTree ι β → DecisionTree ι γ)
    (μ : RandomizedDecisionTree ι β) (f : (ι → Bool) → β) (g : (ι → Bool) → γ) (x : ι → Bool)
    (hφ : ∀ t : DecisionTree ι β, t.eval x = f x → (φ t).eval x = g x) :
    (mapTree φ μ).errorProb g x ≤ μ.errorProb f x :=
  StdSimplex.errorProb_map_le (fun (t : DecisionTree ι β) => t.eval x = f x)
    (fun (t : DecisionTree ι γ) => t.eval x = g x) φ μ hφ

/-- If `φ` turns every tree into one that outputs `g x` on `x`, then `mapTree φ μ` never errs
against `g` on `x`. -/
theorem errorProb_mapTree_eq_zero {γ : Type*} (φ : DecisionTree ι β → DecisionTree ι γ)
    (μ : RandomizedDecisionTree ι β) (g : (ι → Bool) → γ) (x : ι → Bool)
    (hφ : ∀ t : DecisionTree ι β, (φ t).eval x = g x) : (mapTree φ μ).errorProb g x = 0 :=
  errorProb_eq_zero_iff.mpr fun u hu => by
    obtain ⟨t, -, rfl⟩ := exists_of_mem_support_mapTree hu
    exact hφ t

/-! ### Post-processing the output -/

/-- Post-process the output of a randomized decision tree with `g`: draw a tree from `μ` and
relabel its leaves with `g` (`DecisionTree.map`). -/
noncomputable def mapOutput {γ : Type*} (g : β → γ) (μ : RandomizedDecisionTree ι β) :
    RandomizedDecisionTree ι γ :=
  mapTree (DecisionTree.map g) μ

/-- Post-processing makes no further queries. -/
theorem depth_mapOutput_le {γ : Type*} (g : β → γ) (μ : RandomizedDecisionTree ι β) :
    (mapOutput g μ).depth ≤ μ.depth := by
  simpa [mapOutput] using depth_mapTree_le (DecisionTree.map g) μ (d := 0) fun t => by simp

/-- **Post-processing does not increase the error**: the tree drawn from `mapOutput g μ` errs
against `g ∘ f` at most as often as the tree drawn from `μ` errs against `f`. -/
theorem errorProb_mapOutput_le {γ : Type*} (g : β → γ) (μ : RandomizedDecisionTree ι β)
    (f : (ι → Bool) → β) (x : ι → Bool) :
    (mapOutput g μ).errorProb (g ∘ f) x ≤ μ.errorProb f x :=
  errorProb_mapTree_le _ μ f _ x fun t ht => by simp [ht]

end RandomizedDecisionTree

namespace QueryComplexity

open RandomizedDecisionTree

variable {ι β : Type*} {f : (ι → Bool) → β} {μ : RandomizedDecisionTree ι β}
  {ε ε' : ℝ≥0} {d : ℕ}

/-- The randomized decision tree complexity `R_ε(f)`: the least depth of a randomized decision tree
computing `f` with nonnegative error budget `ε` over finitely many variables. These restrictions
ensure that a feasible tree exists. -/
-- Finiteness restricts the public domain; `sInf` itself does not require it.
@[nolint unusedArguments]
noncomputable def randomizedComplexity [Finite ι] (ε : ℝ≥0) (f : (ι → Bool) → β) : ℕ :=
  sInf {d | ∃ μ : RandomizedDecisionTree ι β, μ.Computes ε f ∧ μ.depth ≤ d}

variable [Finite ι]

theorem randomizedComplexity_le_depth (h : μ.Computes ε f) : randomizedComplexity ε f ≤ μ.depth :=
  Nat.sInf_le_of_le h

/-- For `ε ≥ 0` the randomized complexity is attained: some randomized decision tree of depth
`R_ε(f)` computes `f` with error `ε`. -/
theorem exists_computes_depth_eq_randomizedComplexity (f : (ι → Bool) → β) :
    ∃ μ : RandomizedDecisionTree ι β, μ.Computes ε f ∧ μ.depth = randomizedComplexity ε f :=
  Nat.exists_eq_sInf_of_exists depth
    ⟨StdSimplex.single (DecisionTree.exists_computes_depth_eq_complexity f).choose,
      computes_single (DecisionTree.exists_computes_depth_eq_complexity f).choose_spec.1
        ε.coe_nonneg⟩

theorem randomizedComplexity_le_iff :
    randomizedComplexity ε f ≤ d ↔ ∃ μ : RandomizedDecisionTree ι β, μ.Computes ε f ∧ μ.depth ≤ d :=
  Nat.sInf_le_iff_of_exists (exists_computes_depth_eq_randomizedComplexity (ε := ε) f)

/-- Lower bounds on `R_ε(f)` are lower bounds on the depth of every randomized decision tree
computing `f` with error `ε`. -/
theorem le_randomizedComplexity_iff :
    d ≤ randomizedComplexity ε f ↔ ∀ μ : RandomizedDecisionTree ι β, μ.Computes ε f → d ≤ μ.depth :=
  Nat.le_sInf_iff_of_exists (exists_computes_depth_eq_randomizedComplexity (ε := ε) f)

/-- `R_ε(f)` decreases as `ε` grows. -/
theorem randomizedComplexity_antitone (hεε' : ε ≤ ε') :
    randomizedComplexity ε' f ≤ randomizedComplexity ε f :=
  Nat.sInf_mono_of_exists (exists_computes_depth_eq_randomizedComplexity (ε := ε) f)
    fun _ hμ => hμ.mono hεε'

/-- With error `0` randomness does not help: `R_0(f) = D(f)`. The cost here is the worst case over
the coins, unlike the expected number of queries of zero-error (Las Vegas) complexity. -/
theorem randomizedComplexity_zero (f : (ι → Bool) → β) :
    randomizedComplexity 0 f = DecisionTree.complexity f := by
  obtain ⟨t, ht, hd⟩ := DecisionTree.exists_computes_depth_eq_complexity f
  obtain ⟨μ, hμ, hμd⟩ := exists_computes_depth_eq_randomizedComplexity (ε := 0) f
  obtain ⟨s, hs⟩ := μ.support_weights_nonempty
  refine le_antisymm ((randomizedComplexity_le_depth (computes_single ht le_rfl)).trans_eq
    (by rw [depth_single, hd])) ?_
  rw [← hμd]
  exact (DecisionTree.complexity_le_depth (computes_zero_iff.mp hμ s hs)).trans (depth_le_depth hs)

omit [Finite ι] in
/-- A fair coin computes any Boolean-valued function with error at most `1/2`, without a query.
This witness is available even for infinitely many coordinates. -/
theorem exists_computes_depth_zero_of_le {ε : ℝ} (hε : 1 / 2 ≤ ε)
    (f : (ι → Bool) → Bool) :
    ∃ μ : RandomizedDecisionTree ι Bool, μ.Computes ε f ∧ μ.depth = 0 := by
  classical
  set μ : RandomizedDecisionTree ι Bool := StdSimplex.duple (.leaf false) (.leaf true)
    (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hsupp : μ.weights.support ⊆ {DecisionTree.leaf false, DecisionTree.leaf true} := by
    simp only [μ, StdSimplex.weights_duple]
    exact Finsupp.support_add.trans (Finset.union_subset_union Finsupp.support_single_subset
      Finsupp.support_single_subset)
  have hdepth : μ.depth = 0 := Nat.le_zero.mp <| depth_le_iff.mpr fun t ht => by
    rcases Finset.mem_insert.mp (hsupp ht) with rfl | ht
    · rfl
    · rw [Finset.mem_singleton.mp ht]
      rfl
  refine ⟨μ, fun x => ?_, hdepth⟩
  refine le_trans (le_of_eq ?_) hε
  simp only [errorProb, StdSimplex.errorProb, μ, StdSimplex.weights_duple]
  rw [Finsupp.sum_add_index' (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _,
    Finsupp.sum_single_index (zero_mul _), Finsupp.sum_single_index (zero_mul _)]
  cases f x <;> simp

/-- From `ε = 1/2` on, a fair coin computes every Boolean-valued function: `R_ε(f) = 0`. -/
theorem randomizedComplexity_eq_zero_of_le (hε : (1 / 2 : ℝ) ≤ ε) (f : (ι → Bool) → Bool) :
    randomizedComplexity ε f = 0 := by
  obtain ⟨μ, hμ, hd⟩ := exists_computes_depth_zero_of_le hε f
  exact Nat.le_zero.mp ((randomizedComplexity_le_depth hμ).trans_eq hd)

end QueryComplexity

namespace DecisionTree

/-- Randomness does not hurt: `R_ε(f) ≤ D(f)` for `ε ≥ 0`. -/
theorem randomizedComplexity_le_complexity {ι β : Type*} [Finite ι] {ε : ℝ≥0}
    (f : (ι → Bool) → β) : QueryComplexity.randomizedComplexity ε f ≤ complexity f :=
  QueryComplexity.randomizedComplexity_zero f ▸
    QueryComplexity.randomizedComplexity_antitone zero_le

/-- `R_ε(f)` is at most the number of variables for `ε ≥ 0`. -/
theorem randomizedComplexity_le_card {ι β : Type*} [Fintype ι] {ε : ℝ≥0}
    (f : (ι → Bool) → β) : QueryComplexity.randomizedComplexity ε f ≤ Fintype.card ι :=
  (randomizedComplexity_le_complexity f).trans (complexity_le_card f)

end DecisionTree

end Cslib
