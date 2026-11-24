/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.Oracle.Time
import CslibFrontier.Computability.Probabilistic.PPT.AuxClock
import CslibFrontier.Computability.Probabilistic.ExponentialIterate
import CslibFrontier.Computability.Complexity.Classes.Oracle.Exponential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Ordinary-module clients use numerical oracle certificates without the phase compiler API. -/

public section

namespace CslibFrontierTests.OraclePhaseFacade

open Cslib Cslib.Probability Turing Turing.MultiTapeTM

/-- info: Unknown identifier `Cslib.Probability.IsTidyOraclePPTOn` -/
#guard_msgs in
#check_failure Cslib.Probability.IsTidyOraclePPTOn
/-- info: Unknown constant `Turing.MultiTapePTM.Internal.Oracle.IsTidyOraclePPTOn` -/
#guard_msgs in
#check_failure Turing.MultiTapePTM.Internal.Oracle.IsTidyOraclePPTOn

example := @IsOraclePPTOn.runOracle_of_clock
example := @isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn
example := @IsOraclePPTWithAux.exists_run_interpret_take
example := @IsPPTOn.exists_multiTapePTM_iterate_binary
example := @IsOraclePPTOn.preprocess_exp

example : IsOraclePPTOn (Operation := Unit) encBits encBits (fun w : List Bool => pure w) :=
  ComputableInPolyTime.id'.isOraclePPTOn

example : IsOraclePPTOn (Operation := Unit) encBits encBool
    (fun _ : List Bool => (!·) <$> ProbOracleComp.sample (ProbComp.uniform Bool)) :=
  (isPPTOn_uniform_bool encBits).isOraclePPTOn.map ComputableInPolyTime.bool_not

example : IsOraclePPTOn (Operation := Unit) encBits encBool
    (fun w : List Bool => if w.headD false then
      ProbOracleComp.sample (ProbComp.uniform Bool) else pure false) :=
  IsOraclePPTOn.cond (by fun_prop) (isPPTOn_uniform_bool encBits).isOraclePPTOn
    (ComputableInPolyTime.const false).isOraclePPTOn

example : IsOraclePPTOn (Operation := Unit) encBits encBool
    (fun w : List Bool => OracleComp.iterate w.length
      (fun _ => ProbOracleComp.sample (ProbComp.uniform Bool)) false) :=
  (IsOraclePPTOn.iterate_spec (stateEncoding := encBool) (by fun_prop) (.const false)
    (isPPTOn_uniform_bool encBool).isOraclePPTOn (fun _ _ _ => True) (fun _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) (size := fun _ => 1) (.const 1)
    (fun _ _ _ _ _ => by simp)).1

end CslibFrontierTests.OraclePhaseFacade
