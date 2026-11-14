/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeOracleProgram
public import CslibFrontier.Computability.Probabilistic.Oracle.Tidy

/-!
# Forgetting named native oracle programs

This bridge packages a retained `NativeOracleProgram` into the existing existential clean-phase
calculus when its explicit clock is polynomially bounded. The low-level named witness therefore
does not need to import the higher-level polynomial API.

## Main definitions

This bridge introduces no new data type.

## Main results

* `Turing.MultiTapePTM.Internal.NativeOracleProgram.isTidyOraclePPTOn`: the forward forgetful
  theorem. It does not extract construction data from an existential certificate.

## References

The bridge is original to this module.
-/

public section

namespace Turing.MultiTapePTM.Internal.NativeOracleProgram

open Cslib Cslib.Probability

variable {r : ℕ} {Alpha Beta : Type}
  {program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
  {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}

/-- Forget a named witness into the existing existential clean-phase calculus when its recorded
clock is polynomially bounded. This direction packages `witness.machine`; it does not extract a
machine from `IsTidyOraclePPTOn`. -/
theorem isTidyOraclePPTOn (witness : NativeOracleProgram r program encIn encOut)
    (htime : PolyBounded (fun input => (encIn input).length) witness.time) :
    IsTidyOraclePPTOn encIn encOut program := by
  letI := witness.stateFintype
  exact IsTidyOraclePPTOn.of_polyBounded witness.machine htime witness.computes

end Turing.MultiTapePTM.Internal.NativeOracleProgram
