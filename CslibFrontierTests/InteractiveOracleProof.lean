/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Classes.IOP

set_option linter.privateModule false

namespace CslibFrontierTests.InteractiveOracleProof

open Cslib Cslib.Complexity Cslib.Probability
open Cslib.Complexity.InteractiveOracleProof

private noncomputable def prover : Prover Unit where
  State := Bool
  init := false
  respond _ seen := PMF.pure (if seen then [false, true] else [true], true)

private def verifier : WordOracleComp Request Bool := do
  let premature ← ProbOracleComp.query (.read, encAddress (0, 0))
  let first ← ProbOracleComp.query (.challenge, [])
  let second ← ProbOracleComp.query (.challenge, [])
  let oldProof ← ProbOracleComp.query (.read, encAddress (0, 0))
  let newProof ← ProbOracleComp.query (.read, encAddress (1, 1))
  pure (premature == [false] && first.isEmpty && second.isEmpty &&
    oldProof == [true] && newProof == [true])

/-- Queries return a bit only after commitment. The first word survives the second round. -/
example : InteractiveOracleProof.acceptProb [(0, 1), (0, 2 ^ 100)] verifier prover = 1 := by
  simp only [InteractiveOracleProof.acceptProb, verifier, Prover.run_bind, Prover.run_pure,
    Prover.run_query, proverOracle, prover, StateT.run, PMF.pure_bind, PMF.pure_map,
    decodeAddress_encAddress]
  change PMF.pure true true = 1
  exact PMF.pure_apply_self _

end CslibFrontierTests.InteractiveOracleProof
