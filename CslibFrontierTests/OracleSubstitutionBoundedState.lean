/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Probabilistic.Oracle.SubstitutionGrowth
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Tactic.PPT

/-! Checked clients for the bounded-state, `ProbOracleComp.run`, and empty-oracle wrappers in
`CslibFrontier.Computability.Probabilistic.Oracle.SubstitutionGrowth`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.OracleSubstitutionBoundedState

open Cslib Cslib.Probability Turing.MultiTapeTM

private noncomputable def twoQueries : ℕ → List Bool → WordOracleComp Unit Bool := fun n aux => do
  let a ← List.take n <$> ProbOracleComp.query ((), aux)
  let b ← List.take n <$> ProbOracleComp.query ((), a)
  return (a == b)

private theorem isOraclePPT_twoQueries : IsOraclePPT encBool twoQueries := by ppt [twoQueries]

example : IsOraclePPTOn (encPair encUnary encBits) (encPair encBool encBool)
    (fun caller : ℕ × List Bool => (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        fun (req : Unit × List Bool) (used : Bool) =>
          if !used then (·, true) <$> (List.take caller.1 <$> ProbOracleComp.query ((), req.2))
          else pure ([], true)) (twoQueries caller.1 caller.2)).run false) :=
  isOraclePPT_twoQueries.run_interpret_preprocess_open_of_state_le
    (operationEncoding := encFinEnum Unit) (by fun_prop) (by ppt) (.const false)
    (.const 1) fun _ b => by cases b <;> rfl

example : IsPPTOn (encPair encUnary encBits) (encPair encBool encBool)
    (fun caller : ℕ × List Bool => (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        fun (req : Unit × List Bool) (used : Bool) =>
          if !used then (fun b => (b :: req.2, true)) <$> ProbComp.uniform Bool
          else pure ([], true))
      (twoQueries caller.1 caller.2)).run false) :=
  isOraclePPT_twoQueries.run_interpret_preprocess_of_state_le
    (operationEncoding := encFinEnum Unit) (by fun_prop) (by ppt) (.const false)
    (.const 1) fun _ b => by cases b <;> rfl

example : IsPPTOn (encPair encUnary encBits) encBool
    (fun c : ℕ × List Bool =>
      (twoQueries c.1 c.2).run fun r => (· :: r.2) <$> ProbComp.uniform Bool) :=
  isOraclePPT_twoQueries.isPPTOn_run (operationEncoding := encFinEnum Unit) (by fun_prop) (by ppt)

example : IsPPTOn (encPair encUnary encBits) encBool
    (fun c : ℕ × List Bool => (twoQueries c.1 c.2).run fun _ => pure []) :=
  isOraclePPT_twoQueries.on.isPPTOn_runEmptyOracle

end CslibFrontierTests.OracleSubstitutionBoundedState
