/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Simplex.LinearProgram
public import CslibFrontier.Probability.Minimax.Value
import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Solving finite zero-sum games with the simplex method

This module computes the value and optimal mixed strategies of a finite zero-sum game with the
simplex method of `CslibFrontier.Algorithms.Lean.Simplex.LinearProgram`, and proves the output
correct: the returned value is the value of the game (`Cslib.Probability.IsMinimaxValue`) and
the returned strategies witness it.

## Algorithm

The game has the loss matrix `M : Fin m → Fin n → K` over a linearly ordered field `K`: the row
player picks `i`, the column player picks `j`, and the row player pays `M i j`. With the shift
`s = 1 - min (0, min_{i,j} M i j)` (`gameShift`), every entry of `M i j + s` is at least `1`.
`solveGame` runs the simplex method with Bland's rule on the slack dictionary of the canonical
program

  `max ∑ i, x i` subject to `x ≥ 0` and `∑ i, x i * (M i j + s) ≤ 1` for every column `j`,

whose right-hand side `1 ≥ 0` makes the slack dictionary feasible, so no phase I is needed. The
program is bounded, since `∑ i, x i ≤ ∑ i, x i * (M i j + s) ≤ 1` for any column `j`, so the
simplex method stops at an optimal dictionary `D` with optimum `V = D.objConst > 0`. The primal
optimum `x` (the first `m` coordinates of the basic solution of `D`) and the dual optimum `y`
read off the reduced costs of the slack variables (`Dictionary.slackDual`) are normalized to the
strategies `x / V` and `y / V`, and the value is `1 / V - s`, by
`Cslib.Probability.strategies_of_canonical_pair`. This is the reduction of
`Cslib.Probability.exists_isMinimaxValue` ([MatousekGartner2007], Section 8.1), with the existence
of an optimal primal-dual pair replaced by the run of the simplex method.

## Main definitions

* `Cslib.Algorithms.Lean.Simplex.GameSolution`: a value with a row and a column strategy.
* `Cslib.Algorithms.Lean.Simplex.gameShift`: the shift making every entry of the loss matrix at
  least `1`, exposed so that `solveGame` reduces in the kernel.
* `Cslib.Algorithms.Lean.Simplex.solveGame`: the value and optimal strategies of a game with at
  least one row and one column, computed with the simplex method.

## Main results

* `Cslib.Algorithms.Lean.Simplex.solveGame_spec`: for a game with at least one row and one
  column, the strategies returned by `solveGame` are mixed strategies (nonnegative weights summing
  to `1`), the row strategy pays at most the returned value against every column, and the column
  strategy collects at least the returned value against every row.
* `Cslib.Algorithms.Lean.Simplex.isMinimaxValue_solveGame`: the returned value is the value of
  the game.

## References

* [J. Matoušek and B. Gärtner, *Understanding and Using Linear Programming*][MatousekGartner2007]
* [V. Chvátal, *Linear Programming*][Chvatal1983]
-/

public section

namespace Cslib.Algorithms.Lean.Simplex

open Finset Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}

/-- A **solution of a zero-sum game** with `m` rows and `n` columns: a value together with the
weight vectors of a row strategy and a column strategy. -/
structure GameSolution (K : Type*) (m n : ℕ) where
  /-- The value of the game. -/
  value : K
  /-- The weights of the row player's mixed strategy. -/
  row : Fin m → K
  /-- The weights of the column player's mixed strategy. -/
  col : Fin n → K

/-- The shift `1 - min (0, min_{i,j} M i j)`, after which every entry `M i j + gameShift M` of the
loss matrix is at least `1`. It is public and exposed because its client is the body of
`solveGame`, which the kernel must be able to unfold to evaluate the solver (as in `decide +kernel`
checks); an exposed definition cannot refer to a private one. -/
@[expose] def gameShift (M : Fin m → Fin n → K) : K :=
  1 - (univ : Finset (Fin m × Fin n)).fold min 0 fun ij => M ij.1 ij.2

/-- **The value and optimal strategies of a zero-sum game with at least one row and one column
(`0 < m` and `0 < n`), computed with the simplex method.** When `m = 0` or `n = 0` the game has
no mixed strategies and the result is a junk value with no guarantee; `solveGame_spec` and
`isMinimaxValue_solveGame` assume `[NeZero m] [NeZero n]`.

With `s = gameShift M`, the simplex method with Bland's rule maximizes `∑ i, x i` subject to
`x ≥ 0` and `∑ i, x i * (M i j + s) ≤ 1`, from its slack dictionary; with optimum `V`, the row
strategy is the primal optimum divided by `V`, the column strategy is the dual optimum
`Dictionary.slackDual` divided by `V`, and the value is `1 / V - s`. For a nonempty game the
outcomes other than `optimal` do not occur. -/
@[expose] def solveGame (M : Fin m → Fin n → K) : GameSolution K m n :=
  match (slackDictionary (Matrix.of fun j i => M i j + gameShift M) 1 1).simplex with
  | .optimal D =>
    { value := 1 / D.objConst - gameShift M
      row := fun i => D.basicSolution (Fin.castAdd n i) / D.objConst
      col := fun j => D.slackDual j / D.objConst }
  | _ => ⟨0, 0, 0⟩

private theorem one_le_add_gameShift (M : Fin m → Fin n → K) (i : Fin m) (j : Fin n) :
    1 ≤ M i j + gameShift M := by
  have : (univ : Finset (Fin m × Fin n)).fold min 0 (fun ij => M ij.1 ij.2) ≤ M i j :=
    (fold_min_le _).2 (.inr ⟨(i, j), mem_univ _, le_rfl⟩)
  rw [gameShift]
  linarith

/-- **The output of `solveGame` is correct**: for a game with at least one row and one column, the
returned row and column strategies have nonnegative weights summing to `1`, the row strategy pays
at most the returned value against every column, and the column strategy collects at least the
returned value against every row. -/
theorem solveGame_spec [NeZero m] [NeZero n] (M : Fin m → Fin n → K) :
    (∀ i, 0 ≤ (solveGame M).row i) ∧ ∑ i, (solveGame M).row i = 1 ∧
      (∀ j, ∑ i, (solveGame M).row i * M i j ≤ (solveGame M).value) ∧
      (∀ j, 0 ≤ (solveGame M).col j) ∧ ∑ j, (solveGame M).col j = 1 ∧
      ∀ i, (solveGame M).value ≤ ∑ j, (solveGame M).col j * M i j := by
  have hb : (0 : Fin n → K) ≤ 1 := fun _ => zero_le_one
  rcases simplex_slackDictionary_spec (Matrix.of fun j i => M i j + gameShift M) 1 1 hb with
    ⟨D, hD, -, hx0, hAx, hval⟩ | ⟨-, hunb⟩
  swap
  -- the column `0` of the game bounds the program: `y = Pi.single 0 1` is dual feasible
  · refine absurd ⟨1, ?_⟩ hunb
    rintro _ ⟨x, ⟨hx, hAx⟩, rfl⟩
    simpa only [single_dotProduct, Pi.one_apply, one_mul] using
      dotProduct_le_dotProduct_of_nonneg_of_mulVec_le hx hAx
        (Pi.single_nonneg.2 zero_le_one) fun i => by
          simpa only [Pi.one_apply, single_one_vecMul, row_apply, Matrix.of_apply] using
            one_le_add_gameShift M i 0
  simp only [solveGame, hD]
  have hyV := slackDual_dotProduct _ 1 1 hb hD
  rw [dotProduct_one] at hyV
  rw [one_dotProduct] at hval
  refine Probability.strategies_of_canonical_pair hx0 (fun j => ?_)
    (slackDual_nonneg _ 1 1 hb hD) (fun i => ?_) hval hyV
  · simpa only [mulVec, dotProduct, Matrix.of_apply, Pi.one_apply, mul_comm] using hAx j
  · simpa only [vecMul, dotProduct, Matrix.of_apply, Pi.one_apply] using
      le_slackDual_vecMul _ 1 1 hb hD i

/-- **The simplex method computes the value of a finite zero-sum game** over a linearly ordered
field: `(solveGame M).value` is the value of the game `M`, witnessed by the strategies
`(solveGame M).row` and `(solveGame M).col` (`solveGame_spec`). -/
theorem isMinimaxValue_solveGame [NeZero m] [NeZero n] (M : Fin m → Fin n → K) :
    Probability.IsMinimaxValue M (solveGame M).value :=
  let ⟨hp0, hp1, hp, hq0, hq1, hq⟩ := solveGame_spec M
  .of_weights hp0 hp1 hp hq0 hq1 hq

end Cslib.Algorithms.Lean.Simplex
