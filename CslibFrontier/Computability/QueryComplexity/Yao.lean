/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Randomized

/-!
# Yao's minimax principle for decision trees

The distributional complexity `D^ν_ε(f)` of `f` for a distribution `ν` on the inputs is the least
depth of a deterministic decision tree that errs with probability at most `ε` on inputs drawn from
`ν` (`QueryComplexity.distributionalComplexity`), specializing
`Cslib.RandomizedCost.simplexDistributionalComplexity` to `DecisionTree.randomizedCost`.
**Yao's minimax principle** [Yao1977, vonNeumann1928] says that the randomized complexity is the
distributional complexity of a hardest distribution: `R_ε(f) = max_ν D^ν_ε(f)`
(`QueryComplexity.randomizedComplexity_eq_iSup_distributionalComplexity`,
`QueryComplexity.exists_distributionalComplexity_eq_randomizedComplexity`). Both the averaging
direction (`QueryComplexity.distributionalComplexity_le_randomizedComplexity`) and the minimax
direction (`QueryComplexity.exists_computes_of_forall_exists_distributionalError_le`) instantiate
the `StdSimplex` layer of `Cslib.RandomizedCost`.

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
  (DecisionTree.randomizedCost ι β).simplexDistributionalComplexity ε ν (fun x z => z = f x)

variable [Finite ι]

private theorem exists_exact_tree (f : (ι → Bool) → β) :
    ∃ t : DecisionTree ι β, ∀ x, (DecisionTree.randomizedCost ι β).eval t x = f x :=
  let ⟨t, ht, _⟩ := DecisionTree.exists_computes_depth_eq_complexity f
  ⟨t, ht⟩

theorem distributionalComplexity_le_depth (h : t.distributionalError ν f ≤ ε) :
    distributionalComplexity ε ν f ≤ t.depth :=
  RandomizedCost.simplexDistributionalComplexity_le_cost h

/-- For `ε ≥ 0` the distributional complexity is attained: some decision tree of depth
`D^ν_ε(f)` errs with probability at most `ε` on inputs drawn from `ν`. -/
theorem exists_distributionalError_le_depth_eq_distributionalComplexity
    (ν : StdSimplex ℝ (ι → Bool)) (f : (ι → Bool) → β) : ∃ t : DecisionTree ι β,
      t.distributionalError ν f ≤ ε ∧ t.depth = distributionalComplexity ε ν f :=
  RandomizedCost.exists_simplexDistributionalComplexity_eq
    (C := DecisionTree.randomizedCost ι β) (R := fun x z => z = f x) (ε := ε) ν
    (exists_exact_tree f)

/-- **The easy direction of Yao's principle**: `D^ν_ε(f) ≤ R_ε(f)` for every distribution `ν` on
the inputs. To bound `R_ε(f)` below, it suffices to find a distribution on which every shallow
decision tree errs often. -/
theorem distributionalComplexity_le_randomizedComplexity (ε : ℝ≥0) (ν : StdSimplex ℝ (ι → Bool))
    (f : (ι → Bool) → β) : distributionalComplexity ε ν f ≤ randomizedComplexity ε f :=
  RandomizedCost.simplexDistributionalComplexity_le_simplexComplexity
    (C := DecisionTree.randomizedCost ι β) (R := fun x z => z = f x) (ε := ε) ν
    (exists_exact_tree f)

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
      ∀ ν : StdSimplex ℝ (ι → Bool), distributionalComplexity ε ν f ≤ d :=
  RandomizedCost.simplexComplexity_le_iff_forall_simplexDistributionalComplexity_le
    (C := DecisionTree.randomizedCost ι β) (R := fun x z => z = f x) (ε := ε) (d := d)
    (exists_exact_tree f)

/-- **Yao's minimax principle**: the randomized decision tree complexity is the largest
distributional complexity over the distributions on the inputs, `R_ε(f) = ⨆ ν, D^ν_ε(f)`. -/
theorem randomizedComplexity_eq_iSup_distributionalComplexity (ε : ℝ≥0) (f : (ι → Bool) → β) :
    randomizedComplexity ε f = ⨆ ν : StdSimplex ℝ (ι → Bool), distributionalComplexity ε ν f :=
  RandomizedCost.simplexComplexity_eq_iSup_simplexDistributionalComplexity
    (C := DecisionTree.randomizedCost ι β) (R := fun x z => z = f x) (ε := ε)
    (exists_exact_tree f)

/-- **Yao's minimax principle**, with a hardest distribution: some distribution `ν` on the inputs
has `D^ν_ε(f) = R_ε(f)`. -/
theorem exists_distributionalComplexity_eq_randomizedComplexity (ε : ℝ≥0) (f : (ι → Bool) → β) :
    ∃ ν : StdSimplex ℝ (ι → Bool), distributionalComplexity ε ν f = randomizedComplexity ε f :=
  RandomizedCost.exists_simplexDistributionalComplexity_eq_simplexComplexity
    (C := DecisionTree.randomizedCost ι β) (R := fun x z => z = f x) (ε := ε)
    (exists_exact_tree f)

end QueryComplexity

end Cslib
