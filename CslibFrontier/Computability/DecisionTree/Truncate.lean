/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Prune
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Computability.DecisionTree.Fourier
import CslibFrontier.Foundations.BooleanAnalysis.SpectralConcentration
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Tactic.Linarith

/-!
# Truncating decision trees and the spectrum of small trees

Cutting every path of a decision tree at length `k` gives a tree of depth at most `k`
(`DecisionTree.truncate`, `DecisionTree.depth_truncate_le`) that agrees with the original on the
inputs whose path has length at most `k`, and outputs `none` on the others
(`DecisionTree.eval_truncate`). When no path queries a coordinate twice
(`DecisionTree.QueriesDistinct`), as the book insists for decision trees
[O'Donnell, Definition 3.13][ODonnell2014], a uniformly random input follows a path of length more
than `k` with probability at most `s / 2 ^ (k + 1)`, for `s` the number of leaves
(`DecisionTree.dens_lt_length_path_le`): each node at depth `k + 1` is reached with probability
`2 ^ (-(k + 1))`, and there are at most `s` of them. So the truncation differs from the tree on at
most that fraction of inputs (`DecisionTree.dens_eval_truncate_ne_le`), and on at most an `ε`
fraction when `k = ⌊log₂ (s / ε)⌋` (`DecisionTree.dens_eval_truncate_floor_logb_ne_le`,
[O'Donnell, Exercise 3.22][ODonnell2014]). Without distinct queries the bound fails, but pruning
(`DecisionTree.prune`) turns any tree into one with no repeated query
(`DecisionTree.queriesDistinctFrom_prune`) and no more leaves (`DecisionTree.leafCount_prune_le`)
that computes the same function. So for any tree `t` with `s = t.leafCount`, the bounds hold for
`(t.prune PartialAssignment.empty).truncate k` against `t.eval`; they need not hold for
`t.truncate k` itself, which can err on more inputs when `t` repeats a query.

Giving the new leaves the value `0`, a function of a decision tree with `s` leaves and values in
`[-1, 1]` is within squared `L²` distance `s / 2 ^ (k + 1)` of a function of degree at most `k`,
so its Fourier weight above degree `k` is at most `s / 2 ^ (k + 1)`
(`DecisionTree.sum_fourierCoeff_sq_le_leafCount_div`), for any decision tree, by pruning first.
Hence it is `ε`-concentrated on degree up to `log₂ (s / ε)`
(`DecisionTree.sum_fourierCoeff_sq_logb_lt_card_le`)
[O'Donnell, Proposition 3.17 and Exercise 3.22][ODonnell2014].

Deviations from the book. The book's functions are `{-1, 1}`-valued and its trees never repeat a
query, so its size is the number of reachable leaves; here the values lie in `[-1, 1]`, any tree is
allowed, `s` is the structural leaf count `DecisionTree.leafCount`, which also counts unreachable
leaves, and any `ε > 0` is allowed rather than `ε ∈ (0, 1]`. Exercise 3.22 labels the new leaves
`±1`; here they are `none`, so closeness says the truncation outputs `some (t.eval x)`, and any
`±1` labelling errs on at most the same inputs. For the Fourier bound the new leaves are valued `0`
rather than `±1`, which saves a factor `4` in the squared `L²` distance.

## Usage

Open `Cslib.DecisionTree`. The hypothesis `QueriesDistinct t` of the truncation bounds is
`QueriesDistinctFrom ∅ t`, a conjunction over the nodes that `simp [QueriesDistinctFrom]` decides
for a concrete tree. For any tree `t`, `queriesDistinctFrom_prune` gives it for the pruned tree
`t' = t.prune PartialAssignment.empty`. The bounds then concern `t'.truncate k`:
`DecisionTree.eval_prune_empty` replaces `t'.eval` by the original `t.eval`, and
`leafCount_prune_le` replaces `t'.leafCount` by the original `t.leafCount` in the upper bound, so
`t'.truncate k` fails to output `some (t.eval x)` on at most a `t.leafCount / 2 ^ (k + 1)` fraction
of inputs. This says nothing about `t.truncate k`: the repeated-query chain in the tests below
has five leaves, yet its truncation at length `3` errs on half the inputs, more than `5 / 2 ^ 4`.
The Fourier bounds need no such hypothesis. A Boolean tree `t : DecisionTree ι Bool` enters them
with `g = signVal`, as `fun x => signVal (t.eval x)`, and `|signVal b| ≤ 1` is `by simp`. With
`s = t.leafCount`, the weight above degree `k` is at most `s / 2 ^ (k + 1)`
(`DecisionTree.sum_fourierCoeff_sq_le_leafCount_div`), which is the form the low-degree algorithm
uses (`UniformLearning.lowDegreeLearner_learns_decisionTreeClass`). The checked client
[`CslibFrontierTests/DecisionTreeTruncate.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/DecisionTreeTruncate.lean)
works the conjunction of two bits, a tree with three leaves whose truncation at length one errs on
exactly half the inputs and whose weight above degree one is exactly `1 / 4`; the conjunction of
three bits at `ε = 3 / 4`, where Exercise 3.22 cuts at length `2` with error `1 / 4` and
Proposition 3.17 counts only the degree-`3` weight `1 / 16`; and a chain that repeats one query,
whose long paths and truncation break the bounds while its pruned tree meets them.

## Main definitions

* `Cslib.DecisionTree.truncate`: cut every path at length `k`.

## Main results

* `Cslib.DecisionTree.eval_truncate`: the truncation agrees with the tree on short paths.
* `Cslib.DecisionTree.dens_lt_length_path_le`: long paths are rare.
* `Cslib.DecisionTree.dens_eval_truncate_ne_le`: the truncation at length `k` errs on at most a
  `s / 2 ^ (k + 1)` fraction of inputs, the general-`k` bound behind Exercise 3.22.
* `Cslib.DecisionTree.dens_eval_truncate_floor_logb_ne_le`: Exercise 3.22, the truncation at
  `⌊log₂ (s / ε)⌋` is `ε`-close to the tree.
* `Cslib.DecisionTree.sum_fourierCoeff_sq_le_leafCount_div`,
  `Cslib.DecisionTree.sum_fourierCoeff_sq_logb_lt_card_le`: small decision trees have spectra
  concentrated on low degree.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.DecisionTree

open Finset BitString
open scoped BigOperators

variable {ι β : Type*}

/-- Cut every path of a decision tree at length `k`: the nodes at depth `k` become leaves labelled
`none`, and the original leaves `b` above them become `some b`. -/
def truncate : ℕ → DecisionTree ι β → DecisionTree ι (Option β)
  | _, leaf b => leaf (some b)
  | 0, node _ _ _ => leaf none
  | k + 1, node i t₀ t₁ => node i (truncate k t₀) (truncate k t₁)

/-- A truncated tree has depth at most the cut. -/
theorem depth_truncate_le (k : ℕ) (t : DecisionTree ι β) : (t.truncate k).depth ≤ k := by
  induction t generalizing k with
  | leaf b => cases k <;> simp [truncate]
  | node i t₀ t₁ ih₀ ih₁ => cases k <;> simp [truncate, ih₀, ih₁]

/-- **A truncated tree agrees with the original on short paths**: it outputs `some (t.eval x)`
when the path of `x` has length at most `k`, and `none` otherwise. -/
theorem eval_truncate (k : ℕ) (t : DecisionTree ι β) (x : ι → Bool) :
    (t.truncate k).eval x = if (t.path x).length ≤ k then some (t.eval x) else none := by
  induction t generalizing k with
  | leaf b => simp [truncate, path]
  | node i t₀ t₁ ih₀ ih₁ =>
    cases k with
    | zero => simp [truncate, path]
    | succ k => cases hx : x i <;> simp [truncate, path, hx, ih₀, ih₁]

/-- Cutting at `k = ⌊log₂ (s / ε)⌋` makes `s / 2 ^ (k + 1)` at most `ε`. -/
private theorem div_two_pow_floor_logb_add_one_le {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    s / 2 ^ (⌊Real.logb 2 (s / ε)⌋₊ + 1) ≤ ε := by
  have hpow : s / ε < 2 ^ (⌊Real.logb 2 (s / ε)⌋₊ + 1) := by
    rw [← Real.rpow_natCast, ← Real.logb_lt_iff_lt_rpow one_lt_two (div_pos hs hε)]
    exact_mod_cast Nat.lt_floor_add_one _
  rw [div_lt_iff₀ hε] at hpow
  rw [div_le_iff₀ (by positivity)]
  linarith

variable [DecidableEq ι] [Fintype ι]

/-- **Long paths are rare**: in a decision tree with `s` leaves whose paths never repeat a query,
a uniformly random input follows a path of length more than `k` with probability at most
`s / 2 ^ (k + 1)`. -/
theorem dens_lt_length_path_le {A : Finset ι} {t : DecisionTree ι β}
    (h : t.QueriesDistinctFrom A) (k : ℕ) :
    (dens {x : ι → Bool | k < (t.path x).length} : ℝ) ≤ t.leafCount / 2 ^ (k + 1) := by
  induction t generalizing A k with
  | leaf b => simp only [path, List.length_nil, Nat.not_lt_zero, filter_false, dens_empty,
      NNRat.cast_zero]; positivity
  | node i t₀ t₁ ih₀ ih₁ =>
    obtain ⟨hi, h₀, h₁⟩ := h
    simp only [leafCount, Nat.cast_add]
    cases k with
    | zero =>
      have : (dens {x : ι → Bool | 0 < ((node i t₀ t₁).path x).length} : ℝ) ≤ 1 := by
        exact_mod_cast dens_le_one
      have := t₀.leafCount_pos; have := t₁.leafCount_pos
      have : (2 : ℝ) ≤ t₀.leafCount + t₁.leafCount := by norm_cast; omega
      linarith
    | succ k =>
      -- The subtrees never query `i`, so their paths do not depend on bit `i`.
      have hindep {t' : DecisionTree ι β} (ht' : t'.QueriesDistinctFrom (insert i A))
          (x : ι → Bool) (b : Bool) : t'.path (Function.update x i b) = t'.path x :=
        t'.path_eq_of_forall_mem_queries fun j hj => Function.update_of_ne
          (fun (e : j = i) => ht'.notMem_queries x hj (by subst e; exact mem_insert_self j A)) _ _
      have hstep (s : ι → Bool) :
          𝔼 a, (if k + 1 < ((node i t₀ t₁).path (Function.update s i a)).length then (1 : ℝ)
            else 0) =
          ((if k < (t₀.path s).length then 1 else 0) +
            (if k < (t₁.path s).length then 1 else 0)) / 2 := by
        rw [Fintype.expect_bool]
        simp [path, hindep h₀, hindep h₁]
      rw [← Fintype.expect_boole, ← Fintype.expect_expect_update _ i]
      simp_rw [hstep]
      rw [← expect_div, expect_add_distrib, Fintype.expect_boole, Fintype.expect_boole]
      have : ((t₀.leafCount : ℝ) + t₁.leafCount) / 2 ^ (k + 1 + 1) =
          (t₀.leafCount / 2 ^ (k + 1) + t₁.leafCount / 2 ^ (k + 1)) / 2 := by ring
      linarith [ih₀ h₀ k, ih₁ h₁ k]

/-- **A truncated tree is close to the original**: in a decision tree with `s` leaves whose paths
never repeat a query, the truncation at length `k` fails to output `some (t.eval x)` on at most a
`s / 2 ^ (k + 1)` fraction of inputs. This is the general-`k` bound behind
[O'Donnell, Exercise 3.22][ODonnell2014], which is the case `k = ⌊log₂ (s / ε)⌋`
(`DecisionTree.dens_eval_truncate_floor_logb_ne_le`). -/
theorem dens_eval_truncate_ne_le [DecidableEq β] {A : Finset ι} {t : DecisionTree ι β}
    (h : t.QueriesDistinctFrom A) (k : ℕ) :
    (dens {x : ι → Bool | (t.truncate k).eval x ≠ some (t.eval x)} : ℝ) ≤
      t.leafCount / 2 ^ (k + 1) := by
  refine le_trans ?_ (dens_lt_length_path_le h k)
  exact_mod_cast dens_le_dens (monotone_filter_right _ fun x => by simp [eval_truncate])

/-- **Exercise 3.22**: in a decision tree with `s` leaves whose paths never repeat a query,
cutting the paths at length `⌊log₂ (s / ε)⌋` gives a tree that outputs `some (t.eval x)` on all
but an `ε` fraction of inputs, for any `ε > 0` [O'Donnell, Exercise 3.22][ODonnell2014]. The book
labels the new leaves `±1` and takes `ε ∈ (0, 1]`. A tree `t` that repeats queries enters through
its pruned tree `t.prune PartialAssignment.empty`, which computes `t.eval` with at most
`t.leafCount` leaves: the conclusion is then about the truncation of the pruned tree, compared
against `t.eval`, and does not hold in general for the truncation of `t` itself. -/
theorem dens_eval_truncate_floor_logb_ne_le [DecidableEq β] {A : Finset ι}
    {t : DecisionTree ι β} (h : t.QueriesDistinctFrom A) {ε : ℝ} (hε : 0 < ε) :
    (dens {x : ι → Bool |
      (t.truncate ⌊Real.logb 2 (t.leafCount / ε)⌋₊).eval x ≠ some (t.eval x)} : ℝ) ≤ ε := by
  exact (dens_eval_truncate_ne_le h _).trans
    (div_two_pow_floor_logb_add_one_le (by exact_mod_cast t.leafCount_pos) hε)

/-- The high-degree weight of a tree without repeated queries. -/
private theorem sum_fourierCoeff_sq_le_leafCount_div_aux (g : β → ℝ) (hg : ∀ b, |g b| ≤ 1)
    {t : DecisionTree ι β} (ht : t.QueriesDistinct) (k : ℕ) :
    ∑ S with k < #S, fourierCoeff (fun x => g (t.eval x)) S ^ 2 ≤ t.leafCount / 2 ^ (k + 1) := by
  classical
  set G : Option β → ℝ := fun o => o.elim 0 g
  have hdeg := sum_fourierCoeff_sq_le_expect_sub_sq (T := {S : Finset ι | k < #S})
    (f := fun x => g (t.eval x)) (g := fun x => G ((t.truncate k).eval x))
    fun S hS => fourierCoeff_eq_zero_of_depth_lt G _
      ((depth_truncate_le k t).trans_lt (mem_filter.1 hS).2)
  refine hdeg.trans ((expect_le_expect (g := fun x =>
    if (t.truncate k).eval x ≠ some (t.eval x) then (1 : ℝ) else 0) fun x _ => ?_).trans ?_)
  · by_cases h : (t.truncate k).eval x = some (t.eval x)
    · simp [G, h]
    · have hnone : (t.truncate k).eval x = none := by
        rw [eval_truncate] at h ⊢
        split_ifs at h ⊢ <;> simp_all
      simpa [G, h, hnone, sq_le_one_iff_abs_le_one] using hg (t.eval x)
  · rw [Fintype.expect_boole]
    exact dens_eval_truncate_ne_le ht k

/-- **Small decision trees have little high-degree weight**: a function of a decision tree with
`s` leaves, with values in `[-1, 1]`, has Fourier weight at most `s / 2 ^ (k + 1)` above
degree `k`. Here `s = t.leafCount`, which also counts unreachable leaves, and the tree may repeat
queries. -/
theorem sum_fourierCoeff_sq_le_leafCount_div (g : β → ℝ) (hg : ∀ b, |g b| ≤ 1)
    (t : DecisionTree ι β) (k : ℕ) :
    ∑ S with k < #S, fourierCoeff (fun x => g (t.eval x)) S ^ 2 ≤ t.leafCount / 2 ^ (k + 1) := by
  have h := sum_fourierCoeff_sq_le_leafCount_div_aux g hg
    (queriesDistinctFrom_prune (ρ := PartialAssignment.empty) (A := ∅) (by simp) t) k
  simp only [eval_prune_empty] at h
  exact h.trans (by gcongr; exact leafCount_prune_le t _)

/-- **A small decision tree is concentrated on low degree**: a function of a decision tree with
`s` leaves, with values in `[-1, 1]`, is `ε`-concentrated on degree up to `log₂ (s / ε)`, for any
`ε > 0` [O'Donnell, Proposition 3.17][ODonnell2014]. Here `s = t.leafCount`, which also counts
unreachable leaves. The book takes `{-1, 1}` values, trees without repeated queries and
`ε ∈ (0, 1]`. -/
theorem sum_fourierCoeff_sq_logb_lt_card_le (g : β → ℝ) (hg : ∀ b, |g b| ≤ 1)
    (t : DecisionTree ι β) {ε : ℝ} (hε : 0 < ε) :
    ∑ S with Real.logb 2 (t.leafCount / ε) < #S,
      fourierCoeff (fun x => g (t.eval x)) S ^ 2 ≤ ε := by
  set L := Real.logb 2 (t.leafCount / ε)
  have hs : (0 : ℝ) < t.leafCount / ε := div_pos (by exact_mod_cast t.leafCount_pos) hε
  rcases le_or_gt 0 L with hL | hL
  · simp_rw [← Nat.floor_lt hL]
    exact (sum_fourierCoeff_sq_le_leafCount_div g hg t _).trans
      (div_two_pow_floor_logb_add_one_le (by exact_mod_cast t.leafCount_pos) hε)
  · -- Here `s < ε`, and the whole weight is at most `1 ≤ s`.
    have hsε := (Real.logb_neg_iff one_lt_two hs).1 hL
    rw [div_lt_one hε] at hsε
    have hone : (1 : ℝ) ≤ t.leafCount := by exact_mod_cast t.leafCount_pos
    calc ∑ S with L < #S, fourierCoeff (fun x => g (t.eval x)) S ^ 2
        ≤ 𝔼 x, g (t.eval x) ^ 2 := sum_fourierCoeff_sq_le_expect_sq _ _
      _ ≤ 1 := expect_le univ_nonempty fun x _ => (sq_le_one_iff_abs_le_one _).2 (hg _)
      _ ≤ ε := by linarith

end Cslib.DecisionTree
