/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Probability.Minimax
import CslibFrontier.Probability.Minimax.Value

/-!
# Finite zero-sum games over `ℚ`

The minimax theorem holds over every linearly ordered field, so a game with rational losses has a
rational value with rational optimal strategies (`Cslib.Probability.exists_isMinimaxValue`). These
checks compute the value and optimal strategies of three games over `ℚ`, with the row player
paying `M i j`:

* matching pennies, value `1 / 2` with uniform strategies; the hypothesis form of the minimax
  theorem (`Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le`) recovers the
  row player's guarantee over `ℚ`;
* rock–paper–scissors, value `0` with uniform strategies;
* a `2 × 3` game with value `2 / 3`, optimal row strategy `(4 / 9, 5 / 9)` and optimal column
  strategy `(1 / 3, 2 / 3, 0)`, whose third column is never played; the value returned by
  `exists_isMinimaxValue` is identified with `2 / 3` by uniqueness.

Uniqueness of the value (`Cslib.Probability.IsMinimaxValue.unique`) rules out every other value.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.ZeroSum

open Finset Convexity Cslib.Probability

/-- The point of the standard simplex with weight vector `w`. -/
private noncomputable def ofVec {ι : Type*} [Fintype ι] (w : ι → ℚ) (h0 : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) : StdSimplex ℚ ι where
  weights := Finsupp.equivFunOnFinite.symm w
  nonneg := h0
  total := by rwa [Finsupp.sum_fintype _ _ (by simp), Finsupp.coe_equivFunOnFinite_symm]

@[simp] private theorem weights_ofVec {ι : Type*} [Fintype ι] (w : ι → ℚ) (h0 h1) (i : ι) :
    (ofVec w h0 h1).weights i = w i :=
  rfl

/-! ### Matching pennies -/

/-- Matching pennies: the row player pays `1` when the coins match. -/
private def pennies (i j : Bool) : ℚ := if i = j then 1 else 0

/-- The uniform distribution on `Bool`. -/
private noncomputable def uniform₂ : StdSimplex ℚ Bool :=
  ofVec (fun _ => 1 / 2) (fun _ => by norm_num) (by norm_num [Fintype.sum_bool])

private theorem isMinimaxValue_pennies : IsMinimaxValue pennies (1 / 2) := by
  refine ⟨⟨uniform₂, fun j => ?_⟩, uniform₂, fun i => ?_⟩
  · cases j <;> norm_num [uniform₂, pennies, Fintype.sum_bool]
  · cases i <;> norm_num [uniform₂, pennies, Fintype.sum_bool]

/-- The value of matching pennies is `1 / 2` and nothing else. -/
example (v : ℚ) : IsMinimaxValue pennies v ↔ v = 1 / 2 :=
  ⟨fun h => h.unique isMinimaxValue_pennies, fun h => h ▸ isMinimaxValue_pennies⟩

/-- The hypothesis form of the minimax theorem over `ℚ`: against every mixed strategy `q` of the
column player, the row player matching the less likely coin pays at most `1 / 2`, so some mixed
row strategy pays at most `1 / 2` against both columns. -/
example : ∃ p : StdSimplex ℚ Bool, ∀ j, ∑ i, p.weights i * pennies i j ≤ 1 / 2 :=
  StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le pennies fun q => by
    have h := q.total_of_fintype
    simp only [Fintype.sum_bool] at h
    by_cases hq : q.weights true ≤ 1 / 2
    · exact ⟨true, by simpa [pennies] using hq⟩
    · exact ⟨false, by simp only [pennies, Fintype.sum_bool]; norm_num; linarith⟩

/-! ### Rock–paper–scissors -/

/-- Rock–paper–scissors on `Fin 3`, where `i + 1` beats `i`: the row player pays `1` when the
column's move beats its own, receives `1` when its move beats the column's, and pays `0` on a
draw. -/
private def rps (i j : Fin 3) : ℚ := if j = i + 1 then 1 else if i = j + 1 then -1 else 0

/-- The uniform distribution on `Fin 3`. -/
private noncomputable def uniform₃ : StdSimplex ℚ (Fin 3) :=
  ofVec (fun _ => 1 / 3) (fun _ => by norm_num) (by norm_num [Fin.sum_univ_three])

private theorem isMinimaxValue_rps : IsMinimaxValue rps 0 := by
  refine ⟨⟨uniform₃, fun j => ?_⟩, uniform₃, fun i => ?_⟩
  · fin_cases j <;> norm_num [uniform₃, rps, Fin.sum_univ_three]
  · fin_cases i <;> norm_num [uniform₃, rps, Fin.sum_univ_three]

/-- The value of rock–paper–scissors is `0` and nothing else. -/
example (v : ℚ) : IsMinimaxValue rps v ↔ v = 0 :=
  ⟨fun h => h.unique isMinimaxValue_rps, fun h => h ▸ isMinimaxValue_rps⟩

/-- Every pure strategy can be exploited: against rock (`0`), the column player wins with
paper (`1`). So no pure row strategy guarantees the value `0`. -/
example (i : Fin 3) : ∃ j, 0 < rps i j :=
  ⟨i + 1, by fin_cases i <;> decide⟩

/-! ### A `2 × 3` game -/

/-- A `2 × 3` game. Against the row strategy `(a, 1 - a)` the columns collect `6 a - 2`,
`2 - 3 a` and `a`; the first two balance at `a = 4 / 9`, where they collect `2 / 3` and the third
column collects only `4 / 9`. -/
private def game (i : Fin 2) (j : Fin 3) : ℚ := ![![4, -1, 1], ![-2, 2, 0]] i j

/-- The optimal row strategy `(4 / 9, 5 / 9)`. -/
private noncomputable def rowOpt : StdSimplex ℚ (Fin 2) :=
  ofVec ![4 / 9, 5 / 9] (fun i => by fin_cases i <;> norm_num) (by norm_num [Fin.sum_univ_two])

/-- The optimal column strategy `(1 / 3, 2 / 3, 0)`, which never plays the third column. -/
private noncomputable def colOpt : StdSimplex ℚ (Fin 3) :=
  ofVec ![1 / 3, 2 / 3, 0] (fun j => by fin_cases j <;> norm_num)
    (by norm_num [Fin.sum_univ_three])

private theorem isMinimaxValue_game : IsMinimaxValue game (2 / 3) := by
  refine ⟨⟨rowOpt, fun j => ?_⟩, colOpt, fun i => ?_⟩
  · fin_cases j <;> norm_num [rowOpt, game, Fin.sum_univ_two]
  · fin_cases i <;> norm_num [colOpt, game, Fin.sum_univ_three]

/-- The value that the minimax theorem over `ℚ` returns for the `2 × 3` game is `2 / 3`, by
uniqueness of the value. -/
example : (exists_isMinimaxValue game).choose = 2 / 3 :=
  (exists_isMinimaxValue game).choose_spec.unique isMinimaxValue_game

/-- The value of the `2 × 3` game is `2 / 3` and nothing else. -/
example (v : ℚ) : IsMinimaxValue game v ↔ v = 2 / 3 :=
  ⟨fun h => h.unique isMinimaxValue_game, fun h => h ▸ isMinimaxValue_game⟩

/-- The uniform row strategy is not optimal: the first column collects `1` from it, more than the
value `2 / 3`. -/
example : 2 / 3 < ∑ i : Fin 2, 1 / 2 * game i 0 := by
  norm_num [game, Fin.sum_univ_two]

end CslibFrontierTests.GameTheory.ZeroSum
