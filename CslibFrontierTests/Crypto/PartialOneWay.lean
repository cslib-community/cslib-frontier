/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PartialOneWay

/-! # Tests for partial one-wayness reductions -/

namespace CslibTests.Crypto.PartialOneWay

open Cslib Cslib.Crypto

/-- A first validation call is retained even though the local handler answers false. -/
example : ProbComp.eval
    (partialGuessingToDomainAt false 1 0
      (fun (_ _ : Unit) => do
        let _ ← ProbOracleComp.query true
        pure false) () ()) = PMF.pure true := by
  rfl

/-- With no validation slots, the reduction returns the separately checked final output. -/
example : ProbComp.eval
    (partialGuessingToDomainAt false 0 0
      (fun (_ _ : Unit) => pure true) () ()) = PMF.pure true := by
  rfl

/-- The final-output slot remains separate after unsuccessful validation calls. -/
example : ProbComp.eval
    (partialGuessingToDomainAt false 2 2
      (fun (_ _ : Unit) => do
        let _ ← ProbOracleComp.query false
        let _ ← ProbOracleComp.query false
        pure true) () ()) = PMF.pure true := by
  rfl

/-- Terminating before the selected validation slot returns the declared fallback. -/
example : ProbComp.eval
    (partialGuessingToDomainAt true 2 1
      (fun (_ _ : Unit) => pure false) () ()) = PMF.pure true := by
  rfl

/-- Wrong and repeated candidates still consume slots before the selected correct candidate. -/
example : ProbComp.eval
    (partialGuessingToDomainAt false 3 2
      (fun (_ _ : Unit) => do
        let _ ← ProbOracleComp.query false
        let _ ← ProbOracleComp.query false
        let _ ← ProbOracleComp.query true
        pure false) () ()) = PMF.pure true := by
  rfl

/-- The strict sampler for three source slots has four slots, so its loss differs from the
paper's exact uniform loss. -/
example : Probability.dyadicSize 2 = 4 := by decide

end CslibTests.Crypto.PartialOneWay
