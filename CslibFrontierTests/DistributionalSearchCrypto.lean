/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Game.DistributionalSearch

/-!
# Cryptographic clients of distributional search

Inversion accepts a different preimage when the function is noninjective. The generic search
experiment also agrees with evaluation of the existing program experiment, and the prediction
adapter reuses the existing independent-hidden-bit theorem.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.DistributionalSearchCrypto

open Cslib Cslib.Crypto Cslib.Probability

/-- The sampled input is `true`, but returning `false` also inverts the constant function. -/
example : (inversionSearchProblem (PMF.pure true) (fun _ : Bool => ())).experiment
    (fun _ => PMF.pure false) = PMF.pure true := by
  rw [experiment_inversionSearchProblem]
  simp [inversionExperiment]

/-- The search semantics can use `ProbComp`'s evaluator without changing the inversion game. -/
example {α β : Type} [BEq β] [LawfulBEq β] (sample : ProbComp α) (f : α → β)
    (inverter : β → ProbComp α) :
    (inversionSearchProblem (ProbComp.eval sample) f).experiment
        (fun image => ProbComp.eval (inverter image)) =
      ProbComp.eval (inversionExperiment sample f inverter) := by
  rw [experiment_inversionSearchProblem, ProbComp.eval_inversionExperiment]

/-- The existing cryptographic independence bound applies directly to the search problem. -/
example {O : Type} (view : O) (predictor : O → PMF Bool) :
    (predictionSearchProblem ((PMF.uniformOfFintype Bool).map (view, ·))
        Prod.fst Prod.snd).experiment predictor = PMF.uniformOfFintype Bool := by
  rw [experiment_predictionSearchProblem]
  exact predictionExperiment_uniform_bit view predictor

end CslibFrontierTests.DistributionalSearchCrypto
