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
  `(T + 1)`-step computation is `(T + 1)`-Lipschitz in every step law;
* the two correctness statements applied to concrete step laws: under the step law that always
  writes `true` the honest proposer is accepted with probability at least `3 / 5` against every
  challenger, and under the step law that always writes `false`, with the trivial Lipschitz
  constant, every proposer is accepted with probability at most `2 / 5` against the honest
  challenger.
-/

public section

namespace CslibFrontierTests.Debate

open Cslib Cslib.Interactive.Debate Cslib.ProbOracleComp Cslib.Probability
open OracleComp (sumHandler)
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

/-- Under a constant step law every step writes the same bit. -/
theorem evalWith_transcript_const (b : Bool) :
    ∀ n, OracleComp.evalWith (sumHandler ProbComp.unifOracle fun _ => PMF.pure b) (transcript n) =
      PMF.pure (List.replicate n b)
  | 0 => rfl
  | n + 1 => by
    have hquery (bits : List Bool) :
        OracleComp.evalWith (sumHandler ProbComp.unifOracle fun _ => PMF.pure b)
          (ProbOracleComp.query (spec := StepSpec) bits) = PMF.pure b :=
      OracleComp.evalWith_query _ _
    simp only [transcript, OracleComp.evalWith_bind, OracleComp.evalWith_pure, hquery,
      evalWith_transcript_const b n, PMF.pure_bind, List.replicate_succ]

/-- Under a constant step law the output of a computation of at least one step is that bit. -/
theorem evalWith_output_const (b : Bool) (n : ℕ) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle fun _ => PMF.pure b) (output (n + 1)) =
      PMF.pure b := by
  rw [output, OracleComp.evalWith_map, evalWith_transcript_const, PMF.pure_map]
  rfl

/-- Completeness applied: under the step law that always writes `true`, the honest proposer is
accepted with probability at least `3 / 5` against every challenger. -/
example {K : ℝ≥0} (hK : 0 < K) (T : ℕ) (B : Challenger (Params.default K T).grid) :
    3 / 5 ≤ OracleComp.evalWith (sumHandler ProbComp.unifOracle fun _ => PMF.pure true)
      (run (Params.default K T) (honestProposer (Params.default K T)) B) true :=
  completeness_stepLaw hK T (by
    rw [evalWith_output_const, PMF.pure_apply_self]
    exact ENNReal.div_le_of_le_mul (by norm_num)) B

/-- Soundness applied: under the step law that always writes `false`, with the trivial Lipschitz
constant `T + 1`, every proposer is accepted with probability at most `2 / 5` against the honest
challenger. -/
example (T : ℕ) (A : Proposer (Params.default ((T + 1 : ℕ) : ℝ≥0) T).grid) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle fun _ => PMF.pure false)
      (run (Params.default ((T + 1 : ℕ) : ℝ≥0) T) A
        (honestChallenger (Params.default ((T + 1 : ℕ) : ℝ≥0) T))) true ≤ 2 / 5 :=
  soundness_of_lipschitzAt_stepLaw (by positivity) T
    ((LipschitzAt.of_isQueryBounded (isQueryBounded_transcript (T + 1)) _).map _)
    (by simp [evalWith_output_const]) A

end CslibFrontierTests.Debate
