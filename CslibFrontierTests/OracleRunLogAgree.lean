/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.RunLogAgree

/-!
# Tests for `Oracle.RunLogAgree`

Checks `Cslib.ProbOracleComp.eval_runLog_apply_eq_of_agree` (positive agreement away from `bad`,
and necessity of the good-log hypothesis) and `Cslib.ProbOracleComp.map_fst_eval_runLog`.
-/

public section

namespace CslibFrontierTests.OracleRunLogAgree

open Cslib

/-- Agreement away from `bad := (· = true)` equates the logged run probabilities on a log
naming only `false`. -/
example :
    ProbComp.eval
        ((ProbOracleComp.query (spec := fun _ : Bool => Bool) false).runLog fun q => pure q)
        (false, [(false, false)]) =
      ProbComp.eval
        ((ProbOracleComp.query (spec := fun _ : Bool => Bool) false).runLog fun _ => pure false)
        (false, [(false, false)]) :=
  ProbOracleComp.eval_runLog_apply_eq_of_agree
    (bad := fun q : Bool => q = true)
    (fun q hq => by cases q <;> simp_all)
    (ProbOracleComp.query false)
    (by simp)

/-- Necessity of the good-log hypothesis: one `bad` query distinguishes two constant oracles. -/
example :
    ProbComp.eval ((ProbOracleComp.query (spec := fun _ : Unit => Bool) ()).runLog
        fun _ => pure true) (true, [((), true)]) ≠
      ProbComp.eval ((ProbOracleComp.query (spec := fun _ : Unit => Bool) ()).runLog
        fun _ => pure false) (true, [((), true)]) := by
  simp [ProbOracleComp.runLog, StateT.run]

/-- Projecting away the log of `runLog` recovers the unlogged `run` law. -/
example :
    (ProbComp.eval
        ((ProbOracleComp.query (spec := fun _ : Bool => Bool) false).runLog
          fun q => pure q)).map Prod.fst =
      PMF.pure false := by
  rw [ProbOracleComp.map_fst_eval_runLog]
  simp [ProbOracleComp.run_query]

end CslibFrontierTests.OracleRunLogAgree
