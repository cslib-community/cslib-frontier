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

For machines that query the whole transcript: with the identity encoding the machine is the
output program of `Debate.lean`. With the encoding `Option.some`, which is injective but not
surjective, the trivial Lipschitz constant of the run gives the step-law hypothesis, and the
soundness statement applies to an oracle that always answers `false`.
-/

public section

namespace CslibFrontierTests.DebateMachine

open Cslib Cslib.Interactive.Debate
open OracleComp (sumHandler)
open ProbOracleComp (LipschitzAt)
open scoped NNReal

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

/-- One step of the machine that queries the whole transcript asks the encoding of the empty
transcript. -/
example (enc : List Bool → Query) (O : Query → PMF Bool) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle O) ((prefixMachine enc).run 1) =
      O (enc []) :=
  evalWith_run_one _ O

/-- With the identity encoding, the run of the machine against `O` has the law of the output
program against the step law `O`. -/
example (O : List Bool → PMF Bool) (n : ℕ) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle O)
      ((prefixMachine (id : List Bool → List Bool)).run n) =
        OracleComp.evalWith (sumHandler ProbComp.unifOracle O) (output n) := by
  rw [run_prefixMachine_id]

/-- Definition 6.1 with the trivial constant gives the step-law hypothesis of the soundness step,
for an encoding that is injective but not surjective: the oracle is also defined at `none`, which
no transcript asks. -/
example (O : Option (List Bool) → PMF Bool) (n : ℕ) :
    LipschitzAt (n : ℝ≥0) ((prefixMachine Option.some).stepLaw O) (output n) :=
  lipschitzAt_stepLaw_of_lipschitzAt_run (Option.some_injective _)
    ((prefixMachine Option.some).lipschitzAt_run O n)

/-- The soundness statement applies: against the oracle that always answers `false`, no
proposer is accepted with probability above `2 / 5`. -/
example (T : ℕ) (A : Proposer (Params.default ((T + 1 : ℕ) : ℝ≥0) T).grid) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle fun _ : List Bool => PMF.pure false)
      (run (Params.default ((T + 1 : ℕ) : ℝ≥0) T) A
        (honestChallenger (Params.default ((T + 1 : ℕ) : ℝ≥0) T))) true ≤ 2 / 5 := by
  have h := soundness_of_lipschitzAt_run_prefixMachine (Option.some_injective _)
    (K := ((T + 1 : ℕ) : ℝ≥0)) (by positivity) T
    ((prefixMachine Option.some).lipschitzAt_run (fun _ => PMF.pure false) (T + 1)) ?_ A
  · exact h
  · simp [Machine.run, Machine.transcript, OracleComp.evalWith_bind, Machine.evalWith_next,
      stepLaw_prefixMachine]

end CslibFrontierTests.DebateMachine
