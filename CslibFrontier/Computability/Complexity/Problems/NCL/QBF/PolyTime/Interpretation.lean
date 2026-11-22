/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Interpretation
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.PolyTime.Emit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time interpreted source emission

Every fixed interpretation compiles the shared source instruction stream in polynomial time.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.Target.computableInPolyTime_compile_source`:
  interpreted graph emission.
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit.Interpretation

open _root_.Turing.MultiTapeTM

/-- Every fixed interpretation emits its source graph data in polynomial time. -/
@[fun_prop]
theorem Target.computableInPolyTime_compile_source (T : Target) :
    ComputableInPolyTime (fun x => T.language.compile (source x)) encPrenexCNF encAndOrGraph :=
  T.language.computableInPolyTime_compile.comp computableInPolyTime_source

end Cslib.Complexity.NCL.QBF.Emit.Interpretation
