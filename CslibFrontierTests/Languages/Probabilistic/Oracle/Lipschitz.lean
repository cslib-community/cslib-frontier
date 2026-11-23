/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Languages.Probabilistic.Oracle.Lipschitz
import CslibFrontier.Probability.PMF.Event

/-!
# Tests for Lipschitz oracle programs

Boundary witnesses for `Cslib.ProbOracleComp.LipschitzAt`:
* a single query is not `K`-Lipschitz for `K < 1`, so the definition can fail;
* a program that queries `T + 1` times and returns its first reply is `1`-Lipschitz, so the
  constant can sit below the query count.
-/

public section

namespace CslibFrontierTests.Lipschitz

open Cslib Cslib.ProbOracleComp Cslib.Probability
open OracleComp (sumHandler)
open scoped ENNReal NNReal

/-- One external query of a `Bool` oracle. -/
abbrev ask : ProbOracleComp (fun _ : Unit => Bool) Bool := query ()

/-- Where the definition fails: a single query is not `K`-Lipschitz for `K < 1`. Moving the reply
from always `true` to always `false` (tolerance `1`) moves the output by `1`. -/
example {K : ℝ≥0} (hK : K < 1) : ¬ LipschitzAt K (fun _ => PMF.pure true) ask := by
  intro h
  have hclose := h (fun _ => PMF.pure false) 1
    (fun _ event => (PMF.toOuterMeasure_le_one _ event).trans le_add_self) {true}
  simp only [ask, query, OracleComp.evalWith_query, PMF.toOuterMeasure_pure_apply,
    Set.mem_singleton_iff, Bool.false_eq_true, ite_true, ite_false, zero_add, mul_one] at hclose
  exact absurd hK (not_lt.2 (by exact_mod_cast hclose))

/-- Where the constant is below the query count: querying `T + 1` times and returning the first
reply is `1`-Lipschitz at every oracle. -/
example (T : ℕ) (oracle : Unit → PMF Bool) :
    LipschitzAt 1 oracle
      (ask >>= fun b => discard ((List.range T).mapM fun _ => ask) *> pure b) := by
  have hfirst : LipschitzAt 1 oracle ask := by
    simpa only [Nat.cast_one] using LipschitzAt.of_isQueryBounded (IsQueryBounded.query ()) oracle
  have hrest (b : Bool) : LipschitzAt 0 oracle
      (discard ((List.range T).mapM fun _ => ask) *> pure b) := by
    intro oracle' ε _
    have hlaw (o : Unit → PMF Bool) : OracleComp.evalWith (sumHandler ProbComp.unifOracle o)
        (discard ((List.range T).mapM fun _ => ask) *> pure b) = PMF.pure b := by
      rw [seqRight_eq_bind, OracleComp.evalWith_bind]
      simp only [OracleComp.evalWith_pure, PMF.bind_const]
    rw [hlaw, hlaw]
    exact (CloseTo.refl _).mono zero_le
  simpa only [add_zero] using hfirst.bind hrest

end CslibFrontierTests.Lipschitz
