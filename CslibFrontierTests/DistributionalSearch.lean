/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Probability.Distributional.Search
import CslibFrontier.Probability.PMF.Bool

/-!
# Hidden information in distributional search

Every randomized solver given only the unit observation guesses a uniform hidden bit correctly
with probability exactly one half. The same bit, when revealed as an ordinary relation-search
input, is recovered without error. These examples check that the scoring relation's access to
hidden state does not grant that access to the solver.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.DistributionalSearch

open Cslib.Probability DistributionalSearchProblem
open scoped ENNReal

private noncomputable def hiddenBit : DistributionalSearchProblem Bool Unit Bool where
  distribution := PMF.uniformOfFintype Bool
  observe := fun _ => ()
  accepts := fun state answer => answer = state

/-- Randomized guesses cannot recover an independent, unobserved uniform bit better than chance. -/
example (solver : Unit → PMF Bool) : hiddenBit.experiment solver true = (2 : ℝ≥0∞)⁻¹ := by
  classical
  simp only [hiddenBit, experiment, PMF.bind_apply, PMF.map_apply,
    PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, tsum_bool]
  simp only [Bool.false_eq_true, Bool.true_eq_false, decide_true, decide_false,
    ite_true, ite_false, zero_add, add_zero]
  rw [← mul_add, add_comm, PMF.apply_true_add_apply_false, mul_one]

/-- Revealing the bit makes exact recovery possible with zero failure probability. -/
example : (ofRelation (PMF.uniformOfFintype Bool) (fun state answer => answer = state)).experiment
    PMF.pure = PMF.pure true := by
  classical
  simp [experiment, ofRelation, PMF.bind_const]

end CslibFrontierTests.DistributionalSearch
