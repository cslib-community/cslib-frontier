/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: local-only (test suite)

import CslibFrontier.Crypto.Primitives.UHF.Finite
import CslibFrontier.Crypto.Primitives.UHF.PairwiseUnpredictability
import CslibFrontier.Languages.Probabilistic.Semantics
import Mathlib.Algebra.Field.ZMod

set_option linter.privateModule false

/-!
# Single-pair universal hash games

The collision and difference experiments reject repeated messages, and the exhaustive search
examines all distinct pairs. A nonzero difference checks the order of the two hashes.
The prediction game reveals one digest and rejects a prediction for the queried message.
-/

namespace Cslib.Crypto.UHF.Tests

private def hash (_ : Unit) (m : Fin 3) : Bool := decide (m = 0)

example :
    (bestCollisionGuess hash [0, 1, 2]).map (fun guess => (guess.first, guess.second)) =
      some (1, 2) := by
  decide

example : (bestCollisionGuess hash [0, 0]).isNone := by
  decide

example : ProbComp.eval (collisionExperiment hash (pure ⟨0, 0⟩)) true = 0 := by
  simp [collisionExperiment, ProbComp.eval_uniform]

example :
    ProbComp.eval (differenceExperiment (fun (_ : Unit) (m : ZMod 3) => m)
      (pure ⟨⟨0, 1⟩, 1⟩)) true = 1 := by
  simp [differenceExperiment, ProbComp.eval_uniform]

example :
    ProbComp.eval (differenceExperiment (fun (_ : Unit) (m : ZMod 3) => m)
      (pure ⟨⟨0, 0⟩, 0⟩)) true = 0 := by
  simp [differenceExperiment, ProbComp.eval_uniform]

private def echoGuess (target : Bool) : PredictionAdversary Bool Bool Unit where
  choose _ := pure (false, ())
  guess _ digest := pure ⟨target, digest⟩

example : ProbComp.eval (predictionExperiment (fun k : Bool => fun _ => k) (echoGuess true))
    true = 1 := by
  simp [predictionExperiment, echoGuess, ProbComp.eval_uniform, ENNReal.mul_inv_cancel]

example : ProbComp.eval (predictionExperiment (fun k : Bool => fun _ => k) (echoGuess false))
    true = 0 := by
  simp [predictionExperiment, echoGuess, ProbComp.eval_uniform]

end Cslib.Crypto.UHF.Tests
