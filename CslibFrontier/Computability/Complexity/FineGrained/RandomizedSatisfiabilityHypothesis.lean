/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.RandomizedPowerTime
public import CslibFrontier.Computability.Complexity.FineGrained.SatisfiabilityHypothesis

/-!
# The randomized Satisfiability Hypothesis

The bounded-error decision hypothesis of [MITHardnessGroup2026SH, v2, §7] implies its deterministic
counterpart. The randomized fixed-width equivalences and transfers are tracked in #8457.

## Main definitions

* `Cslib.Complexity.rSH`: the bounded-error decision Satisfiability Hypothesis.

## Main results

* `Cslib.Complexity.rSH.sh`: randomized SH implies deterministic SH.

## References

* [MIT Hardness Group, *ETH is Dead, Long Live SH*][MITHardnessGroup2026SH], v2, §7.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL PromiseProblem

/-- The randomized Satisfiability Hypothesis [MITHardnessGroup2026SH, v2, §7, p. 10].
It rules out any fixed power saving for unrestricted CNF satisfiability with two-sided error
at most `1 / 3`. The bound holds for every seed and measures occurring variables, clauses
and literal occurrences, with polynomial overhead in the native binary input length. -/
@[expose] def rSH : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 →
    ¬SolvesWithErrorInPowerExpTime (ofSet SAT) encCNF ErrorModel.bounded
      (fun φ => φ.numVars + φ.length + φ.vars.length) p

/-- The randomized Satisfiability Hypothesis implies SH. -/
theorem rSH.sh (h : rSH) : SH :=
  fun p hp hp₁ hdet =>
    h p hp hp₁ (solvesWithErrorInPowerExpTime_deterministic_iff.mpr hdet
      |>.mono_error (ErrorModel.deterministic_le ErrorModel.bounded))

end Cslib.Complexity
