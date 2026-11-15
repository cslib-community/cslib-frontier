/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Languages.Probabilistic.Oracle.Support

/-! # One semantics for oracle programs -/

namespace CslibFrontierTests.OracleSemantics

open Cslib OracleComp

/-- Two calls to a Boolean interface. -/
private def twoCalls : OracleComp (fun _ : Unit => Bool) Bool := do
  let a ← query ()
  let b ← query ()
  return a && !b

-- A deterministic handler gives a point distribution.
example : evalWith (fun _ => PMF.pure true) twoCalls = PMF.pure false := by
  simp only [twoCalls, ← PFunctor.FreeM.bind_eq_bind, evalWith_bind, evalWith_query,
    PMF.pure_bind, evalWith_pure, Bool.not_true, Bool.and_false]

-- When every call must answer `true`, the only possible result is `false`.
example : supportWith (fun _ => {true}) twoCalls = {false} := by
  ext b
  simp only [twoCalls, ← PFunctor.FreeM.bind_eq_bind, mem_supportWith_bind_iff,
    supportWith_query, supportWith_pure, Set.mem_singleton_iff]
  simp

-- With fair answers, `true` has positive probability: evaluation and support agree.
example : true ∈ (evalWith (fun _ => Probability.PMF.uniformOfFintype Bool) twoCalls).support := by
  rw [support_evalWith]
  simp only [twoCalls, ← PFunctor.FreeM.bind_eq_bind, mem_supportWith_bind_iff,
    supportWith_query, supportWith_pure, Set.mem_singleton_iff]
  simp [PMF.mem_support_iff]

-- A stateful oracle counting its calls.
private noncomputable def counter : (q : Unit) → StateT ℕ PMF Bool :=
  fun _ s => PMF.pure (true, s + 1)

example : runWith counter twoCalls 0 = PMF.pure (false, 2) := by
  simp only [twoCalls, ← PFunctor.FreeM.bind_eq_bind, runWith_bind, runWith_query, counter,
    PMF.pure_bind, runWith_pure, Bool.not_true, Bool.and_false]

-- Every result of the counting run is reached along a `true` reply.
example {result : Bool} {final : ℕ} (h : (result, final) ∈ (runWith counter twoCalls 0).support) :
    result ∈ supportWith (fun _ => {true}) twoCalls :=
  mem_supportWith_of_mem_support_runWith counter
    (fun _ _ _ _ h => by
      simp only [counter, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
      exact h.1) h

-- A memoryless oracle run with state keeps the state.
example (s : ℕ) :
    runWith (fun _ state => (PMF.pure true).map (·, state)) twoCalls s =
      PMF.pure (false, s) := by
  rw [runWith_lift]
  simp only [twoCalls, ← PFunctor.FreeM.bind_eq_bind, evalWith_bind, evalWith_query,
    PMF.pure_bind, evalWith_pure, PMF.pure_map, Bool.not_true, Bool.and_false]

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
  simp only [coinThenQuery, ← PFunctor.FreeM.bind_eq_bind, mem_supportWith_bind_iff,
    ProbOracleComp.support_sample, ProbComp.eval_uniform, ProbOracleComp.supportWith_query,
    supportWith_pure, Set.mem_singleton_iff]
  simp [PMF.mem_support_iff]

-- Its run is, by definition, the generic run of the sum handler.
example (oracle : (q : Unit) → StateT ℕ PMF Bool) (s : ℕ) :
    ProbOracleComp.runWith oracle coinThenQuery s =
      runWith (sumHandler (m := fun α => ℕ → PMF (α × ℕ))
        (fun n state => (ProbComp.unifOracle n).map (·, state)) oracle) coinThenQuery s :=
  rfl

-- Against a reply that is always `false`, it never accepts.
example (s : ℕ) :
    ProbOracleComp.acceptProbWith
        (fun _ state => (PMF.pure false).map (·, state)) coinThenQuery s = 0 := by
  rw [ProbOracleComp.acceptProbWith_lift]
  simp only [coinThenQuery, ← PFunctor.FreeM.bind_eq_bind, evalWith_bind,
    ProbOracleComp.sample_eq_liftLeft, evalWith_sumHandler_liftLeft, ProbOracleComp.query,
    evalWith_query, evalWith_pure]
  simp

/-! The two universe regressions are intentionally separate. Generic oracle computations support
higher response, result, and state carriers. `ProbOracleComp` supports higher query, result, and
state carriers, but its external responses remain in `Type 0` because they share the response
universe of `unifSpec` in the sum interface. -/

universe u v w s

private abbrev highSpec : OracleSpec.{u + 1, v + 1} (Type u) := fun _ => Type v

private def highProgram : OracleComp highSpec (Type w) :=
  PFunctor.FreeM.bind (query (spec := highSpec) PUnit) fun _ => pure PUnit

private noncomputable def highOracle :
    (q : Type u) → Type s → PMF (highSpec q × Type s) :=
  fun _ state => PMF.pure (PUnit, state)

-- Generic syntax and raw state semantics genuinely separate reply, result, and state universes.
example (state : Type s) :
    runWith highOracle highProgram state = PMF.pure (PUnit, state) := by
  simp [highProgram, highOracle]

private abbrev highQuerySpec : Type u → Type := fun _ => Bool

private def highProbProgram : ProbOracleComp highQuerySpec (Type w) :=
  PFunctor.FreeM.bind (ProbOracleComp.query PUnit) fun _ => pure PUnit

private noncomputable def highProbOracle :
    (q : Type u) → Type s → PMF (highQuerySpec q × Type s) :=
  fun _ state => PMF.pure (true, state)

-- The combined private-randomness interface separates query, result, and state universes.
example (state : Type s) :
    ProbOracleComp.runWith highProbOracle highProbProgram state =
      PMF.pure (PUnit, state) := by
  simp [highProbProgram, highProbOracle]

end CslibFrontierTests.OracleSemantics
