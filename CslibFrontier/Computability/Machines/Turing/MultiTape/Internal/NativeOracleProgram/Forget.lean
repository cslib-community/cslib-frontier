/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeOracleProgram
public import CslibFrontier.Computability.Probabilistic.Oracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.Oracle.Phase

/-!
# Forgetting named native oracle programs

A retained `NativeOracleProgram` whose recorded clock is polynomially bounded gives the existential
oracle-machine predicate `IsOraclePPTOn`. The theorem lives in its own module so that the witness
module imports only the machine layer.

## Main results

* `Turing.MultiTapePTM.Internal.NativeOracleProgram.isOraclePPTOn`: a witness with a polynomially
  bounded clock gives `IsOraclePPTOn`.

## References

The bridge is original to this module.
-/

public section

namespace Turing.MultiTapePTM.Internal.NativeOracleProgram

open Cslib Cslib.Probability

variable {r : ℕ} {Alpha Beta : Type}
  {program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
  {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}

/-- A named witness whose recorded clock is polynomially bounded in the length of the encoded
input gives `IsOraclePPTOn`; the machine it packages is `witness.machine`. -/
theorem isOraclePPTOn (witness : NativeOracleProgram r program encIn encOut)
    (htime : Turing.MultiTapeTM.PolyBounded
      (fun input => (encIn input).length) witness.time) :
    IsOraclePPTOn encIn encOut program := by
  let _ := witness.stateFintype
  exact (Oracle.IsTidyOraclePPTOn.of_polyBounded
    witness.machine htime witness.computes).isOraclePPTOn

end Turing.MultiTapePTM.Internal.NativeOracleProgram
