/-
Copyright (c) 2026 Samuel Schlesinger, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# The value of a finite zero-sum game

In the finite zero-sum game with loss matrix `M : I → J → K` over a linearly ordered field `K`,
the row player picks `i`, the column player picks `j`, and the row player pays `M i j` to the
column player. An element `v : K` is the *value* of the game (`IsMinimaxValue M v`) if the row
player has a mixed strategy `p` paying at most `v` against every column and the column player has
a mixed strategy `q` collecting at least `v` against every row. By von Neumann's minimax theorem
[vonNeumann1928] every game with finitely many rows and columns has a value
(`exists_isMinimaxValue`), and it is unique (`IsMinimaxValue.unique`):
`min_p max_j ∑ i, p i M i j = max_q min_i ∑ j, q j M i j = v`.

Existence is proved by linear-programming duality over `K`
(`Matrix.exists_isGreatest_isLeast_dotProduct_of_nonneg`, by Fourier–Motzkin elimination), with no
topology. The LP-duality argument is that of [MatousekGartner2007], Theorem 8.1.3 and its proof
(Section 8.1, pp. 136–138), for real games: there the row and column players' problems are the
linear programs (8.2) and (8.4), over strategies summing to `1` with a free variable for the value.
The formulation here is different: after shifting `M` by a constant, the row player's problem,
normalized by its value, is the canonical program `max {∑ i, x i | 0 ≤ x, ∑ i, x i * M i j ≤ 1}`
and the column player's is its dual, and the argument runs over every linearly ordered field. So a
game with entries in `ℚ` has a rational value and rational optimal strategies. The theorem proves
that optimal strategies exist; the source's clause that they can be computed efficiently is not
formalized here. `Cslib.Algorithms.Lean.Simplex.solveGame` computes the value and optimal
strategies with the simplex method (Bland's rule), with no bound on its running time. The
hypothesis form of the minimax theorem used by Yao's principle,
`Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le`, is derived from it in
`CslibFrontier.Probability.Minimax`.

The open Mathlib pull request
[mathlib4#39393](https://github.com/leanprover-community/mathlib4/pull/39393) proves the
existence of a saddle point of a finite real matrix game (`Matrix.exists_saddle_point`,
`Matrix.exists_mixedNash`) from Sion's theorem on `stdSimplex`. The proof here does not depend on
it and holds over every linearly ordered field; over `ℝ`, the payoff at such a saddle point is the
value (`IsMinimaxValue.unique`).

## Main definitions

* `Cslib.Probability.IsMinimaxValue`: `v` is the value of a finite zero-sum game.

## Main results

* `Cslib.Probability.exists_isMinimaxValue`: every finite zero-sum game over a linearly ordered
  field has a value, with optimal mixed strategies over the same field.
* `Cslib.Probability.IsMinimaxValue.unique`: the value is unique.
* `Cslib.Probability.IsMinimaxValue.exists_le`, `Cslib.Probability.IsMinimaxValue.exists_ge`:
  against any mixed strategy, the opponent has a pure strategy doing at least as well as the value.

## References

* [J. von Neumann, *Zur Theorie der Gesellschaftsspiele*][vonNeumann1928]
* [J. Matoušek and B. Gärtner, *Understanding and Using Linear Programming*][MatousekGartner2007]
-/

public section

namespace Cslib.Probability

open Finset Convexity

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {I J : Type*} [Fintype I] [Fintype J]

/-- `v` is the *value* of the finite zero-sum game with loss matrix `M` (the row player pays
`M i j`): some mixed row strategy pays at most `v` against every column, and some mixed column
strategy collects at least `v` against every row. This is a value predicate, not a saddle-point
existence theorem; see the module documentation for its relation to mathlib4#39393. -/
@[expose] def IsMinimaxValue (M : I → J → K) (v : K) : Prop :=
  (∃ p : StdSimplex K I, ∀ j, ∑ i, p.weights i * M i j ≤ v) ∧
    ∃ q : StdSimplex K J, ∀ i, v ≤ ∑ j, q.weights j * M i j

omit [IsStrictOrderedRing K] in
/-- A point of the standard simplex given by its weight vector. -/
private theorem exists_stdSimplex_weights_eq {ι : Type*} [Fintype ι] {w : ι → K}
    (hw0 : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) : ∃ p : StdSimplex K ι, ⇑p.weights = w := by
  have : w ∈ Set.range fun p : StdSimplex K ι => (p.weights : ι → K) := by
    rw [StdSimplex.range_toFun_comp_weights]
    exact ⟨Set.mem_iInter.2 hw0, hw1⟩
  exact this

omit [IsStrictOrderedRing K] in
/-- Weight vectors `p` and `q` of mixed strategies, with `p` paying at most `v` against every
column and `q` collecting at least `v` against every row, witness that `v` is the value. -/
theorem IsMinimaxValue.of_weights {M : I → J → K} {v : K} {p : I → K} {q : J → K}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (hp : ∀ j, ∑ i, p i * M i j ≤ v)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) (hq : ∀ i, v ≤ ∑ j, q j * M i j) :
    IsMinimaxValue M v := by
  obtain ⟨p', rfl⟩ := exists_stdSimplex_weights_eq hp0 hp1
  obtain ⟨q', rfl⟩ := exists_stdSimplex_weights_eq hq0 hq1
  exact ⟨⟨p', hp⟩, q', hq⟩

/-- If `p` pays at most `c` against every column, it pays at most `c` against every mixed column
strategy. -/
private theorem sum_mul_sum_le {M : I → J → K} {c : K} {p : I → K} (q : J → K)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) (hp : ∀ j, ∑ i, p i * M i j ≤ c) :
    ∑ i, p i * ∑ j, q j * M i j ≤ c := by
  calc ∑ i, p i * ∑ j, q j * M i j = ∑ j, q j * ∑ i, p i * M i j := by
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring
    _ ≤ ∑ j, q j * c := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hp j) (hq0 j)
    _ = c := by rw [← sum_mul, hq1, one_mul]

/-- If `q` collects at least `c` against every row, it collects at least `c` against every mixed
row strategy. -/
private theorem le_sum_mul_sum {M : I → J → K} {c : K} (p : I → K) {q : J → K}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (hq : ∀ i, c ≤ ∑ j, q j * M i j) :
    c ≤ ∑ i, p i * ∑ j, q j * M i j :=
  calc c = ∑ i, p i * c := by rw [← sum_mul, hp1, one_mul]
    _ ≤ _ := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hq i) (hp0 i)

/-- Some column does at least as well against `p` as the mixed column strategy `q`. -/
private theorem exists_sum_mul_sum_le [Nonempty J] (M : I → J → K) (p : I → K) {q : J → K}
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) :
    ∃ j, ∑ i, p i * ∑ j', q j' * M i j' ≤ ∑ i, p i * M i j := by
  obtain ⟨j, hj⟩ := Finite.exists_max fun j => ∑ i, p i * M i j
  exact ⟨j, sum_mul_sum_le q hq0 hq1 hj⟩

/-- The value of a game is unique. -/
theorem IsMinimaxValue.unique {M : I → J → K} {v w : K} (hv : IsMinimaxValue M v)
    (hw : IsMinimaxValue M w) : v = w := by
  obtain ⟨⟨p, hp⟩, q, hq⟩ := hv
  obtain ⟨⟨p', hp'⟩, q', hq'⟩ := hw
  have h₁ := sum_mul_sum_le _ q'.weights_nonneg q'.total_of_fintype hp
  have h₂ := le_sum_mul_sum _ p.weights_nonneg p.total_of_fintype hq'
  have h₃ := sum_mul_sum_le _ q.weights_nonneg q.total_of_fintype hp'
  have h₄ := le_sum_mul_sum _ p'.weights_nonneg p'.total_of_fintype hq
  linarith

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Dividing a vector `w` with sum `V ≠ 0` by `V` turns the shifted payoff
`∑ k, w k * (a k + s)` into `(∑ k, w k * (a k + s)) / V - s`. -/
private theorem sum_div_mul_eq {ι : Type*} [Fintype ι] (w a : ι → K) {V : K} (hV : V ≠ 0)
    (hw : ∑ k, w k = V) (s : K) :
    ∑ k, w k / V * a k = (∑ k, w k * (a k + s)) / V - s := by
  simp only [mul_add, sum_add_distrib, ← sum_mul, hw, add_div, div_mul_eq_mul_div, ← sum_div]
  rw [mul_div_cancel_left₀ _ hV, add_sub_cancel_right]

/-- **Optimal strategies from the canonical pair of a game.** Let `x ≥ 0` be feasible for
`max {∑ i, x i | 0 ≤ x, ∑ i, x i * (M i j + s) ≤ 1}` and `y ≥ 0` for its dual
`min {∑ j, y j | 0 ≤ y, 1 ≤ ∑ j, y j * (M i j + s)}`, with the same objective value `V`. Then
`V > 0` (as `y = 0` violates the dual constraint of any row), `x / V` and `y / V` are mixed
strategies, `x / V` pays at most `1 / V - s` against every column and `y / V` collects at least
`1 / V - s` against every row; so `1 / V - s` is the value (`IsMinimaxValue.of_weights`). This is
the read-off step of `exists_isMinimaxValue`, also used by the simplex solver
`Cslib.Algorithms.Lean.Simplex.solveGame`. -/
theorem strategies_of_canonical_pair [Nonempty I] {M : I → J → K} {s V : K} {x : I → K}
    {y : J → K} (hx : 0 ≤ x) (hxM : ∀ j, ∑ i, x i * (M i j + s) ≤ 1) (hy : 0 ≤ y)
    (hyM : ∀ i, 1 ≤ ∑ j, y j * (M i j + s)) (hxV : ∑ i, x i = V) (hyV : ∑ j, y j = V) :
    (∀ i, 0 ≤ x i / V) ∧ ∑ i, x i / V = 1 ∧ (∀ j, ∑ i, x i / V * M i j ≤ 1 / V - s) ∧
      (∀ j, 0 ≤ y j / V) ∧ ∑ j, y j / V = 1 ∧ ∀ i, 1 / V - s ≤ ∑ j, y j / V * M i j := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  -- the common optimum `V` is positive, since `y = 0` violates the constraint of row `i₀`
  have hV : 0 < V := by
    refine hyV ▸ (sum_nonneg fun j _ => hy j).lt_of_ne fun h => ?_
    have := hyM i₀
    rw [sum_eq_zero fun j _ => by rw [(sum_eq_zero_iff_of_nonneg fun j _ => hy j).1 h.symm j
      (mem_univ j), zero_mul]] at this
    exact zero_lt_one.not_ge this
  refine ⟨fun i => div_nonneg (hx i) hV.le, by rw [← sum_div, hxV, div_self hV.ne'], fun j => ?_,
    fun j => div_nonneg (hy j) hV.le, by rw [← sum_div, hyV, div_self hV.ne'], fun i => ?_⟩
  · rw [sum_div_mul_eq x (M · j) hV.ne' hxV s]
    gcongr
    exact hxM j
  · rw [sum_div_mul_eq y (M i) hV.ne' hyV s]
    gcongr
    exact hyM i

/-- **Every finite zero-sum game has a value**, over every linearly ordered field [vonNeumann1928]:
there are mixed strategies `p`, `q` and `v : K` with `∑ i, p i * M i j ≤ v` for every column `j`
and `v ≤ ∑ j, q j * M i j` for every row `i`. This is the existence part of
[MatousekGartner2007], Theorem 8.1.3, extended from real games to every linearly ordered field;
the source's efficient-computation clause is not formalized. The proof follows the source's
LP-duality argument (pp. 136–138), but with the canonical pair in place of its programs (8.2) and
(8.4): shifting `M` by `s` so that some column pays at least `1` against every row, the programs
`max {∑ i, x i | 0 ≤ x, ∑ i, x i * (M i j + s) ≤ 1}` and
`min {∑ j, y j | 0 ≤ y, 1 ≤ ∑ j, y j * (M i j + s)}` are feasible, and their common optimum `V` is
positive; `x / V` and `y / V` are optimal strategies and `1 / V - s` is the value. -/
theorem exists_isMinimaxValue [Nonempty I] [Nonempty J] (M : I → J → K) :
    ∃ v, IsMinimaxValue M v := by
  classical
  obtain ⟨j₀⟩ := ‹Nonempty J›
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min fun i => M i j₀
  -- after the shift by `s`, the column `j₀` pays at least `1` against every row
  set s := 1 - M i₀ j₀
  obtain ⟨-, ⟨⟨x, ⟨hx, hAx⟩, rfl⟩, -⟩, ⟨y, ⟨hy, hyA⟩, hxy⟩, -⟩ :=
    Matrix.exists_isGreatest_isLeast_dotProduct_of_nonneg (Matrix.of fun j i => M i j + s) 1 1
      ⟨0, le_rfl, by rw [Matrix.mulVec_zero]; exact zero_le_one⟩
      ⟨Pi.single j₀ 1, Pi.single_nonneg.2 zero_le_one, fun i => by
        simp only [Pi.one_apply, Matrix.single_one_vecMul, Matrix.row_apply, Matrix.of_apply, s]
        linarith [hi₀ i]⟩
  simp only [dotProduct_one, one_dotProduct] at hxy
  replace hAx (j : J) : ∑ i, x i * (M i j + s) ≤ 1 := by
    simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.one_apply, mul_comm] using hAx j
  replace hyA (i : I) : 1 ≤ ∑ j, y j * (M i j + s) := hyA i
  obtain ⟨hp0, hp1, hp, hq0, hq1, hq⟩ := strategies_of_canonical_pair hx hAx hy hyA hxy.symm rfl
  exact ⟨_, .of_weights hp0 hp1 hp hq0 hq1 hq⟩

/-- Against any mixed row strategy `p`, some column collects at least the value. -/
theorem IsMinimaxValue.exists_le {M : I → J → K} {v : K} (hv : IsMinimaxValue M v) {p : I → K}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) : ∃ j, v ≤ ∑ i, p i * M i j := by
  obtain ⟨-, q, hq⟩ := hv
  have := q.nonempty
  obtain ⟨j, hj⟩ := exists_sum_mul_sum_le M p q.weights_nonneg q.total_of_fintype
  exact ⟨j, (le_sum_mul_sum p hp0 hp1 hq).trans hj⟩

/-- Against any mixed column strategy `q`, some row pays at most the value. -/
theorem IsMinimaxValue.exists_ge {M : I → J → K} {v : K} (hv : IsMinimaxValue M v) {q : J → K}
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) : ∃ i, ∑ j, q j * M i j ≤ v := by
  obtain ⟨⟨p, hp⟩, -⟩ := hv
  have := p.nonempty
  obtain ⟨i, hi⟩ := Finite.exists_min fun i => ∑ j, q j * M i j
  refine ⟨i, ?_⟩
  calc ∑ j, q j * M i j = ∑ i', p.weights i' * ∑ j, q j * M i j := by
        rw [← sum_mul, p.total_of_fintype, one_mul]
    _ ≤ ∑ i', p.weights i' * ∑ j, q j * M i' j :=
        sum_le_sum fun i' _ => mul_le_mul_of_nonneg_left (hi i') (p.weights_nonneg i')
    _ ≤ v := sum_mul_sum_le q hq0 hq1 hp

end Cslib.Probability
