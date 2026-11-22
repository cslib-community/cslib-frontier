/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Randomized
public import CslibFrontier.Probability.Minimax
import CslibFrontier.Foundations.Data.ENat.IInf

/-!
# Yao's minimax principle for decision trees

The distributional complexity `D^ν_ε(f)` of `f` for a distribution `ν` on the inputs is the least
depth of a deterministic decision tree that errs with probability at most `ε` on inputs drawn from
`ν` (`QueryComplexity.distributionalComplexity`). **Yao's minimax principle** [Yao1977] says that
the randomized complexity is the distributional complexity of a hardest distribution:
`R_ε(f) = max_ν D^ν_ε(f)` (`QueryComplexity.randomizedComplexity_eq_iSup_distributionalComplexity`,
`QueryComplexity.exists_distributionalComplexity_eq_randomizedComplexity`).

One inequality is the averaging argument: some tree that an optimal randomized tree can draw does
as well as the randomized tree on inputs drawn from `ν`
(`RandomizedDecisionTree.Computes.exists_distributionalError_le`). This is the direction used for
lower bounds: a distribution on which every shallow tree errs often bounds `R_ε(f)` below
(`QueryComplexity.distributionalComplexity_le_randomizedComplexity`).

The other inequality is the minimax theorem for a finite two-player zero-sum game
(`Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le`, in
`CslibFrontier.Probability.Minimax`) [vonNeumann1928], proved there by linear-programming
duality. The algorithm player picks the set of inputs on which a tree of depth at most `d` errs,
of which there are finitely many, the input player picks an input, and the payoff is `1` when the
tree errs. If every distribution on the inputs has a tree of depth at
most `d` erring with probability at most `ε`, the minimax theorem gives a distribution over such
trees erring with probability at most `ε` on every input
(`QueryComplexity.exists_computes_of_forall_exists_distributionalError_le`).

## Main definitions

* `Cslib.QueryComplexity.distributionalComplexity`: the distributional complexity `D^ν_ε(f)`.

## Main results

* `Cslib.QueryComplexity.distributionalComplexity_le_randomizedComplexity`: `D^ν_ε(f) ≤ R_ε(f)`.
* `Cslib.QueryComplexity.exists_computes_of_forall_exists_distributionalError_le`: the converse
  for a fixed depth.
* `Cslib.QueryComplexity.randomizedComplexity_eq_iSup_distributionalComplexity`: **Yao's minimax
  principle**, `R_ε(f) = ⨆ ν, D^ν_ε(f)`.
* `Cslib.QueryComplexity.exists_distributionalComplexity_eq_randomizedComplexity`: some
  distribution is hardest.

## References

* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
* [J. von Neumann, *Zur Theorie der Gesellschaftsspiele*][vonNeumann1928]
-/

@[expose] public section

open scoped NNReal

namespace Cslib

open Convexity RandomizedDecisionTree

namespace QueryComplexity

variable {ι β : Type*} {f : (ι → Bool) → β} {ν : StdSimplex ℝ (ι → Bool)} {ε : ℝ≥0} {d : ℕ}
  {t : DecisionTree ι β}

/-- The distributional complexity `D^ν_ε(f)`: the least depth of a decision tree that errs with
probability at most the nonnegative budget `ε` on inputs drawn from `ν`. The finite coordinate
space ensures that the feasible set is nonempty. -/
-- Finiteness restricts the public domain; `sInf` itself does not require it.
@[nolint unusedArguments]
noncomputable def distributionalComplexity [Finite ι] (ε : ℝ≥0) (ν : StdSimplex ℝ (ι → Bool))
    (f : (ι → Bool) → β) : ℕ :=
  sInf {d | ∃ t : DecisionTree ι β, t.distributionalError ν f ≤ ε ∧ t.depth ≤ d}

variable [Finite ι]

theorem distributionalComplexity_le_depth (h : t.distributionalError ν f ≤ ε) :
    distributionalComplexity ε ν f ≤ t.depth :=
  Nat.sInf_le_of_le h

/-- For `ε ≥ 0` the distributional complexity is attained: some decision tree of depth
`D^ν_ε(f)` errs with probability at most `ε` on inputs drawn from `ν`. -/
theorem exists_distributionalError_le_depth_eq_distributionalComplexity
    (ν : StdSimplex ℝ (ι → Bool)) (f : (ι → Bool) → β) : ∃ t : DecisionTree ι β,
      t.distributionalError ν f ≤ ε ∧ t.depth = distributionalComplexity ε ν f :=
  let h := DecisionTree.exists_computes_depth_eq_complexity f
  Nat.exists_eq_sInf_of_exists DecisionTree.depth
    ⟨h.choose, h.choose_spec.1.distributionalError_eq_zero.trans_le ε.coe_nonneg⟩

/-- **The easy direction of Yao's principle**: `D^ν_ε(f) ≤ R_ε(f)` for every distribution `ν` on
the inputs. To bound `R_ε(f)` below, it suffices to find a distribution on which every shallow
decision tree errs often. -/
theorem distributionalComplexity_le_randomizedComplexity (ε : ℝ≥0) (ν : StdSimplex ℝ (ι → Bool))
    (f : (ι → Bool) → β) : distributionalComplexity ε ν f ≤ randomizedComplexity ε f := by
  obtain ⟨μ, hμ, hd⟩ := exists_computes_depth_eq_randomizedComplexity (ε := ε) f
  obtain ⟨t, ht, hνt⟩ := hμ.exists_distributionalError_le ν
  exact (distributionalComplexity_le_depth hνt).trans ((depth_le_depth ht).trans_eq hd)

/-- **The hard direction of Yao's principle**, by the minimax theorem: if for every distribution
`ν` on the inputs some decision tree of depth at most `d` errs with probability at most `ε` on
inputs drawn from `ν`, then some randomized decision tree of depth at most `d` computes `f` with
error `ε`. -/
theorem exists_computes_of_forall_exists_distributionalError_le {ε : ℝ}
    (h : ∀ ν : StdSimplex ℝ (ι → Bool), ∃ t : DecisionTree ι β,
      t.depth ≤ d ∧ t.distributionalError ν f ≤ ε) :
    ∃ μ : RandomizedDecisionTree ι β, μ.Computes ε f ∧ μ.depth ≤ d :=
  StdSimplex.exists_maxCost_le_and_forall_errorProb_le DecisionTree.depth
    (fun t x => t.eval x = f x) h

/-- `R_ε(f) ≤ d` exactly when `D^ν_ε(f) ≤ d` for every distribution `ν` on the inputs. -/
theorem randomizedComplexity_le_iff_forall_distributionalComplexity_le :
    randomizedComplexity ε f ≤ d ↔
      ∀ ν : StdSimplex ℝ (ι → Bool), distributionalComplexity ε ν f ≤ d := by
  refine ⟨fun h ν => (distributionalComplexity_le_randomizedComplexity ε ν f).trans h,
    fun h => ?_⟩
  obtain ⟨μ, hμ, hd⟩ := exists_computes_of_forall_exists_distributionalError_le fun ν =>
    let ⟨t, ht, hd⟩ := exists_distributionalError_le_depth_eq_distributionalComplexity (ε := ε) ν f
    ⟨t, hd.trans_le (h ν), ht⟩
  exact (randomizedComplexity_le_depth hμ).trans hd

/-- **Yao's minimax principle**: the randomized decision tree complexity is the largest
distributional complexity over the distributions on the inputs, `R_ε(f) = ⨆ ν, D^ν_ε(f)`. -/
theorem randomizedComplexity_eq_iSup_distributionalComplexity (ε : ℝ≥0) (f : (ι → Bool) → β) :
    randomizedComplexity ε f = ⨆ ν : StdSimplex ℝ (ι → Bool), distributionalComplexity ε ν f :=
  Nat.eq_ciSup_of_le_iff fun _ => randomizedComplexity_le_iff_forall_distributionalComplexity_le

/-- **Yao's minimax principle**, with a hardest distribution: some distribution `ν` on the inputs
has `D^ν_ε(f) = R_ε(f)`. -/
theorem exists_distributionalComplexity_eq_randomizedComplexity (ε : ℝ≥0) (f : (ι → Bool) → β) :
    ∃ ν : StdSimplex ℝ (ι → Bool), distributionalComplexity ε ν f = randomizedComplexity ε f :=
  Nat.exists_eq_of_le_iff fun _ => randomizedComplexity_le_iff_forall_distributionalComplexity_le

end QueryComplexity

end Cslib
