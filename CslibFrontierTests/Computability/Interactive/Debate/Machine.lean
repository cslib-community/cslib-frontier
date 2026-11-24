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
output program of `Debate.lean`, its run is Lipschitz in the external oracle with the trivial
constant, and the soundness statement applies to an oracle that always answers `false`.
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

/-- The run of the machine that queries the whole transcript makes one query per step, so it is
Lipschitz in the external oracle with the number of steps as constant. -/
theorem lipschitzAt_run_prefixMachine_id (O : List Bool → PMF Bool) (n : ℕ) :
    LipschitzAt (n : ℝ≥0) O ((prefixMachine (id : List Bool → List Bool)).run n) := by
  rw [run_prefixMachine_id]
  refine (ProbOracleComp.LipschitzAt.of_isQueryBounded (n := n) ?_ O).map _
  induction n with
  | zero => exact .pure _ 0
  | succ n ih =>
    exact ih.bind fun bits => by
      simpa using (ProbOracleComp.IsQueryBounded.query (spec := StepSpec) bits).bind fun bit =>
        .pure (bit :: bits) 0

/-- Definition 6.1 then gives the step-law hypothesis of the soundness step. -/
example (O : List Bool → PMF Bool) (n : ℕ) :
    LipschitzAt (n : ℝ≥0) O (output n) :=
  lipschitzAt_stepLaw_of_lipschitzAt_run (enc := id) Function.injective_id
    (lipschitzAt_run_prefixMachine_id O n)

/-- The soundness statement applies: against the oracle that always answers `false`, no
proposer is accepted with probability above `2 / 5`. -/
example (T : ℕ) (A : Proposer (Params.default ((T + 1 : ℕ) : ℝ≥0) T).grid) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle fun _ : List Bool => PMF.pure false)
      (run (Params.default ((T + 1 : ℕ) : ℝ≥0) T) A
        (honestChallenger (Params.default ((T + 1 : ℕ) : ℝ≥0) T))) true ≤ 2 / 5 := by
  have h := soundness_of_lipschitzAt_run_prefixMachine (enc := id) Function.injective_id
    (K := ((T + 1 : ℕ) : ℝ≥0)) (by positivity) T
    (lipschitzAt_run_prefixMachine_id (fun _ => PMF.pure false) (T + 1)) ?_ A
  · exact h
  · simp [Machine.run, Machine.transcript, OracleComp.evalWith_bind, Machine.evalWith_next,
      stepLaw_prefixMachine]

end CslibFrontierTests.DebateMachine
