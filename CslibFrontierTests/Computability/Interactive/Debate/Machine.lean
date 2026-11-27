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

At the constants printed in Figure 1 (`Params.figure1`), with `K = 1` and one step: completeness
applied to the step law that always writes `true`, soundness applied to the step law that always
writes `false`, and the prefix-machine corollary applied to the oracle that always answers
`false`.
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

/-- Completeness at the constants of Figure 1, with `K = 1` and one step: under the step law that
always writes `true`, the honest proposer is accepted with probability at least `3 / 5` against
every challenger. -/
example (B : Challenger (Params.figure1 1 1).grid) :
    3 / 5 ≤ OracleComp.evalWith (sumHandler ProbComp.unifOracle fun _ => PMF.pure true)
      (run (Params.figure1 1 1) (honestProposer (Params.figure1 1 1)) B) true := by
  refine completeness_figure1_stepLaw one_pos 1 ?_ B
  rw [← run_prefixMachine_id, evalWith_run_one]
  simp only [stepLaw_prefixMachine, PMF.pure_apply_self]
  exact ENNReal.div_le_of_le_mul (by norm_num)

/-- Soundness at the constants of Figure 1, with `K = 1` and one step: under the step law that
always writes `false`, which is `1`-Lipschitz since the output of one step makes one query, every
proposer is accepted with probability at most `2 / 5` against the honest challenger. -/
example (A : Proposer (Params.figure1 1 1).grid) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle fun _ => PMF.pure false)
      (run (Params.figure1 1 1) A (honestChallenger (Params.figure1 1 1))) true ≤ 2 / 5 := by
  refine soundness_figure1_of_lipschitzAt_stepLaw one_pos 1 ?_ ?_ A
  · have h := lipschitzAt_stepLaw_of_lipschitzAt_run (enc := id) Function.injective_id
      ((prefixMachine id).lipschitzAt_run (fun _ => PMF.pure false) 1)
    rw [Nat.cast_one] at h
    exact h
  · rw [← run_prefixMachine_id, evalWith_run_one]
    simp

/-- The prefix-machine corollary at the constants of Figure 1, with `K = 1` and one step: against
the oracle that always answers `false`, through the encoding `Option.some`, no proposer is
accepted with probability above `2 / 5`. -/
example (A : Proposer (Params.figure1 1 1).grid) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle
        ((prefixMachine Option.some).stepLaw fun _ : Option (List Bool) => PMF.pure false))
      (run (Params.figure1 1 1) A (honestChallenger (Params.figure1 1 1))) true ≤ 2 / 5 := by
  refine soundness_figure1_of_lipschitzAt_run_prefixMachine (Option.some_injective _) one_pos 1
    ?_ ?_ A
  · simpa using (prefixMachine Option.some).lipschitzAt_run (fun _ => PMF.pure false) 1
  · rw [evalWith_run_one]
    simp

end CslibFrontierTests.DebateMachine
