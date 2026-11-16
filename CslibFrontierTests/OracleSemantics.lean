/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
public import CslibFrontier.Languages.Probabilistic.Oracle.Support

/-! # One semantics for oracle programs -/

set_option linter.privateModule false

namespace CslibFrontierTests.OracleSemantics

open Cslib OracleComp

/-- Two calls to a Boolean interface. -/
private def twoCalls : OracleComp (fun _ : Unit => Bool) Bool := do
  let a ← query ()
  let b ← query ()
  return a && !b

-- A deterministic handler gives a point distribution.
example : evalWith (fun _ => PMF.pure true) twoCalls = PMF.pure false := by
  simp [twoCalls]

-- When every call must answer `true`, the only possible result is `false`.
example : supportWith (fun _ => {true}) twoCalls = {false} := by
  ext b
  simp [twoCalls, eq_comm]

-- With fair answers, `true` has positive probability: evaluation and support agree.
example : true ∈ (evalWith (fun _ => Probability.PMF.uniformOfFintype Bool) twoCalls).support := by
  rw [support_evalWith]
  simp [twoCalls, PMF.mem_support_iff]

-- A stateful oracle counting its calls.
private noncomputable def counter : (q : Unit) → StateT ℕ PMF Bool :=
  fun _ s => PMF.pure (true, s + 1)

example : runWith counter twoCalls 0 = PMF.pure (false, 2) := by
  simp [twoCalls, counter]

-- Every result of the counting run is reached along a `true` reply.
example {result : Bool} {final : ℕ} (h : (result, final) ∈ (runWith counter twoCalls 0).support) :
    result ∈ supportWith (fun _ => {true}) twoCalls :=
  mem_supportWith_of_mem_support_runWith counter
    (fun _ _ _ _ h => by
      simp only [counter, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
      exact h.1) h

-- A memoryless oracle run with state keeps the state.
example (s : ℕ) :
    runWith (fun _ => StateT.lift (PMF.pure true)) twoCalls s =
      PMF.pure (false, s) := by
  rw [runWith_lift]
  simp [twoCalls]

-- Closed probabilistic programs are the instance with uniform answers.
example (program : ProbComp Bool) :
    ProbComp.eval program = evalWith ProbComp.unifOracle program :=
  ProbComp.eval_eq_evalWith program

example : (ProbComp.eval (ProbComp.unifFin 1)).support = Set.univ := by
  rw [ProbComp.support_eval]
  exact supportWith_query _ 1

/-- A program with a private coin and one external call. -/
private noncomputable def coinThenQuery : ProbOracleComp (fun _ : Unit => Bool) Bool := do
  let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let reply ← ProbOracleComp.query ()
  return coin && reply

-- Its possible results are those for any coin and any reply.
example : true ∈ support coinThenQuery := by
  simp [coinThenQuery, PMF.mem_support_iff]

-- Its run is, by definition, the generic run of the sum handler.
example (oracle : (q : Unit) → StateT ℕ PMF Bool) (s : ℕ) :
    ProbOracleComp.runWith oracle coinThenQuery s =
      runWith (sumHandler (m := fun α => ℕ → PMF (α × ℕ))
        (fun n state => (ProbComp.unifOracle n).map (·, state)) oracle) coinThenQuery s :=
  rfl

-- Against a reply that is always `false`, it never accepts.
example (s : ℕ) :
    ProbOracleComp.acceptProbWith (fun _ => StateT.lift (PMF.pure false)) coinThenQuery s = 0 := by
  rw [ProbOracleComp.acceptProbWith_lift]
  simp [coinThenQuery, ProbOracleComp.sample_eq_liftLeft, ProbOracleComp.query]

/-! The two universe regressions are intentionally separate. Generic oracle computations support
higher response, result, and state carriers. `ProbOracleComp` supports higher query, result, and
state carriers, but its external responses remain in `Type 0` because they share the response
universe of `unifSpec` in the sum interface. -/

universe u v w s

private abbrev lowReplySpec : Unit → Type := fun _ => Bool

private def highReplyProgram : OracleComp lowReplySpec (ULift.{w} Bool) :=
  PFunctor.FreeM.bind (query ()) fun reply => pure (ULift.up reply)

private def highResultProgram : OracleComp lowReplySpec (ULift.{w} Bool) := do
  let reply ← highReplyProgram
  return ULift.up !reply.down

-- Ordinary monadic notation sequences high-universe results over a low-reply program.
example : evalWith (fun _ => PMF.pure true) highResultProgram = PMF.pure (ULift.up false) := by
  simp [highResultProgram, highReplyProgram]

private def highClosedProgram : ProbComp (ULift.{w} Bool) :=
  PFunctor.FreeM.bind (ProbComp.unifFin 1) fun _ => pure (ULift.up true)

-- Closed-program support semantics also retain an independently chosen result universe.
example : (ProbComp.eval highClosedProgram).support = {ULift.up true} := by
  rw [ProbComp.support_eval]
  ext result
  simp [highClosedProgram]

-- The generalized nonemptiness theorem applies to a genuinely high-result program.
example : ∃ result : ULift.{w} Bool, result ∈ (ProbComp.eval highClosedProgram).support := by
  rw [ProbComp.support_eval]
  exact ProbComp.support_nonempty highClosedProgram

private abbrev highSpec : OracleSpec.{u + 1, v + 1} (Type u) := fun _ => Type v

private def highProgram : OracleComp highSpec (ULift.{w} Bool) :=
  PFunctor.FreeM.bind (query (spec := highSpec) PUnit) fun _ => pure (ULift.up true)

private noncomputable def highOracle :
    (q : Type u) → Type s → PMF (highSpec q × Type s) :=
  fun _ state => PMF.pure (PUnit, state)

-- Generic syntax and raw state semantics genuinely separate reply, result, and state universes.
example (state : Type s) :
    runWith highOracle highProgram state = PMF.pure (ULift.up true, state) := by
  rw [show highOracle = (fun _ state => (PMF.pure PUnit).map (·, state)) by
      funext q state
      simp only [highOracle, PMF.pure_map],
    runWith_memoryless]
  simp [highProgram]

private abbrev highQuerySpec : Type u → Type := fun _ => Bool

private def highProbProgram : ProbOracleComp highQuerySpec (ULift.{w} Bool) :=
  PFunctor.FreeM.bind (ProbOracleComp.query PUnit) fun reply => pure (ULift.up reply)

private def highSimHandler (_ : Type u) : ProbOracleComp lowReplySpec Bool :=
  pure true

-- Substitution changes the external interface while preserving a high-universe result.
example :
    ProbOracleComp.simulate highSimHandler highProbProgram =
      (pure (ULift.up true) : ProbOracleComp lowReplySpec (ULift.{w} Bool)) := by
  change OracleComp.substitute
    (OracleComp.sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n)) highSimHandler)
      highProbProgram = _
  simp [highProbProgram, highSimHandler, ProbOracleComp.query, OracleComp.sumHandler]

private noncomputable def highProbOracle :
    (q : Type u) → Type s → PMF (highQuerySpec q × Type s) :=
  fun _ state => PMF.pure (true, state)

-- The combined private-randomness interface separates query, result, and state universes.
example (state : Type s) :
    ProbOracleComp.runWith highProbOracle highProbProgram state =
      PMF.pure (ULift.up true, state) := by
  rw [show highProbOracle = (fun _ state => (PMF.pure true).map (·, state)) by
      funext q state
      simp only [highProbOracle, PMF.pure_map],
    ProbOracleComp.runWith_memoryless]
  simp [highProbProgram, ProbOracleComp.query, OracleComp.sumHandler]

private def highAcceptProgram : ProbOracleComp highQuerySpec Bool := do
  let reply ← ProbOracleComp.query PUnit
  return !reply

-- Acceptance permits high-universe queries and raw state while replies remain small.
example (state : Type s) :
    ProbOracleComp.acceptProbWith highProbOracle highAcceptProgram state = 0 := by
  rw [highAcceptProgram, ProbOracleComp.acceptProbWith_query_bind]
  simp [highProbOracle, ProbOracleComp.acceptProbWith_pure]

end CslibFrontierTests.OracleSemantics
