/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Interactive.Debate.Machine

/-!
# Tests for machines with an external stochastic oracle

One-step machines of each kind, for
`CslibFrontier/Computability/Interactive/Debate/Machine.lean`: a deterministic step writes its
bit, a coin step writes a fair coin, and a query step writes the oracle's reply, both for the
machine's run and, through the bridge, for the output of its step law.
-/

public section

namespace CslibFrontierTests.DebateMachine

open Cslib Cslib.Interactive.Debate
open OracleComp (sumHandler)

variable {Query : Type}

/-- One step of a machine has the law of its first step. -/
theorem evalWith_run_one (M : Machine Query) (O : Query → PMF Bool) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle O) (M.run 1) = M.stepLaw O [] := by
  simp only [Machine.run, Machine.transcript, OracleComp.evalWith_map, OracleComp.evalWith_bind,
    OracleComp.evalWith_pure, Machine.evalWith_next, PMF.pure_bind, PMF.map_bind, PMF.pure_map,
    List.headD_cons, PMF.bind_pure]

/-- A deterministic step writes its bit. -/
example (O : Query → PMF Bool) (bit : Bool) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle O)
      ((⟨fun _ => .det bit⟩ : Machine Query).run 1) = PMF.pure bit :=
  evalWith_run_one _ O

/-- A coin step writes a fair coin, whatever the oracle. -/
example (O : Query → PMF Bool) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle O)
      ((⟨fun _ => .coin⟩ : Machine Query).run 1) = Probability.PMF.uniformOfFintype Bool :=
  evalWith_run_one _ O

/-- A query step writes the oracle's reply. -/
example (O : Query → PMF Bool) (query : Query) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle O)
      ((⟨fun _ => .ask query⟩ : Machine Query).run 1) = O query :=
  evalWith_run_one _ O

/-- The bridge on a query step: the output of the step law is the oracle's reply. -/
example (O : Query → PMF Bool) (query : Query) :
    OracleComp.evalWith
      (sumHandler ProbComp.unifOracle ((⟨fun _ => .ask query⟩ : Machine Query).stepLaw O))
      (output 1) = O query :=
  (Machine.evalWith_output_stepLaw _ O 1).trans (evalWith_run_one _ O)

end CslibFrontierTests.DebateMachine
