/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Probabilistic.Oracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.Oracle.Normalization

/-!
# Polynomially clocked oracle runs

The public numerical certificate for a clocked oracle run is compiled by the internal
finite-configuration normalization implementation. Arbitrary stateful replies are truncated
by the machine clock; no global reply-length hypothesis is imposed.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

variable {Operation : Type} [DecidableEq Operation]

/-- Every clocked run of a finite-control oracle machine under a polynomial-time computable clock
`clock : List Bool → ℕ` is `IsOraclePPTOn`. -/
theorem IsOraclePPTOn.runOracle_of_clock {k : ℕ} {Control : Type}
    [Finite Operation] [Finite Control]
    (machine : _root_.Turing.MultiTapePTM k Bool Control Operation)
    {clock : List Bool → ℕ} (hclock : ComputableInPolyTime clock encBits encUnary) :
    IsOraclePPTOn encBits encBits
      (fun word : List Bool => machine.runOracle (clock word) word) :=
  (Turing.MultiTapePTM.Internal.Oracle.IsTidyOraclePPTOn.runOracle_of_clock
    machine hclock).isOraclePPTOn

end Cslib.Probability
