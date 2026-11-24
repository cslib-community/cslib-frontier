/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Interactive.Debate
import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import Mathlib.Data.ZMod.Basic

/-!
# Tests for the stochastic debate protocol

Boundary witnesses for `CslibFrontier/Computability/Interactive/Debate.lean`:
* the coin step on the grid `4`: with a uniform coin from either side the bit of a round is
  `true` with probability `3 / 4` for the claim `3`, never for the claim `0` and always for the
  claim `4`, so the comparison in `coinBit` is strict and the claim `k` means exactly `k / N`;
* the Lipschitz hypothesis of the soundness statement is satisfiable: the output of a
  `(T + 1)`-step computation is `(T + 1)`-Lipschitz in every step law.
-/

public section

namespace CslibFrontierTests.Debate

open Cslib Cslib.Interactive.Debate Cslib.ProbOracleComp Cslib.Probability
open scoped ENNReal NNReal

/-- A uniform coin from the challenger's copy: the claim `3` on the grid `4`. -/
example (z : ZMod 4) :
    (PMF.uniformOfFintype (ZMod 4)).map (fun w => coinBit (3 : Fin 5) w z) true = 3 / 4 := by
  simpa using map_coinBit_uniformOfFintype_left (N := 4) 3 z

/-- A uniform coin from the proposer's copy: the claim `3` on the grid `4`. -/
example (z : ZMod 4) :
    (PMF.uniformOfFintype (ZMod 4)).map (fun w => coinBit (3 : Fin 5) z w) true = 3 / 4 := by
  simpa using map_coinBit_uniformOfFintype_right (N := 4) 3 z

/-- The claim `0` never gives the bit `true`. -/
example (z : ZMod 4) :
    (PMF.uniformOfFintype (ZMod 4)).map (fun w => coinBit (0 : Fin 5) w z) true = 0 := by
  simpa using map_coinBit_uniformOfFintype_left (N := 4) 0 z

/-- The claim `4`, that is probability `1`, always gives the bit `true`. -/
example (z : ZMod 4) :
    (PMF.uniformOfFintype (ZMod 4)).map (fun w => coinBit (4 : Fin 5) w z) true = 1 := by
  have h := map_coinBit_uniformOfFintype_left (N := 4) 4 z
  rw [h]
  exact ENNReal.div_self (by simp) (by simp)

/-- The transcript of `n` steps makes `n` queries. -/
theorem isQueryBounded_transcript (n : ℕ) : (transcript n).IsQueryBounded n := by
  induction n with
  | zero => exact .pure _ 0
  | succ n ih =>
    exact ih.bind fun bits => by
      simpa using (IsQueryBounded.query (spec := StepSpec) bits).bind fun bit =>
        .pure (bit :: bits) 0

/-- The Lipschitz hypothesis of the soundness statement holds with the trivial constant: the
output of a `(T + 1)`-step computation is `(T + 1)`-Lipschitz in every step law. -/
example (T : ℕ) (law : List Bool → PMF Bool) :
    LipschitzAt ((T + 1 : ℕ) : ℝ≥0) law (output (T + 1)) :=
  (LipschitzAt.of_isQueryBounded (isQueryBounded_transcript (T + 1)) law).map _

end CslibFrontierTests.Debate
