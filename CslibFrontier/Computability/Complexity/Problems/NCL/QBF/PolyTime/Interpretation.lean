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

Distinguishing the two swap colors adds one finite instruction tag. The source emitter and any
fixed interpretation compile in polynomial time.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.encProgram`: colored source instruction encoding.
* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.source`: emit a normalized source instance.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.computableInPolyTime_source`: instruction emission.
* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.Target.computableInPolyTime_compile_source`:
  interpreted graph emission.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit.Interpretation

open _root_.Turing.MultiTapeTM

/-- Encode colored instruction tags by their finite enumeration rank. -/
@[expose] def encOpcode : Option Opcode ↪ List Bool := encFinEnum (Option Opcode)

/-- Encode colored instruction lists with unary offsets. -/
@[expose] def encProgram : Program ↪ List Bool := encList (encPair encUnary encOpcode)

/-- Lift ordinary source instructions into the colored instruction table in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_lift : ComputableInPolyTime lift Emit.encProgram encProgram := by
  have ht : ComputableInPolyTime (some : Opcode → Option Opcode) Emit.encOpcode encOpcode :=
    ComputableInPolyTime.of_finite _
  have he : ComputableInPolyTime (fun p : Emit.Program × (ℕ × Opcode) => (p.2.1, some p.2.2))
      (encPair Emit.encProgram (encPair encUnary Emit.encOpcode))
      (encPair encUnary encOpcode) := by fun_prop
  unfold lift encProgram
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.of_eq (fun _ => rfl)) he

/-- Emit a circuit retaining swap colors in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_circuit :
    ComputableInPolyTime (fun p : List Quantifier × List (List Bool) => circuit p.1 p.2)
      Source.encPrepared encProgram := by
  have hc := computableInPolyTime_lift.comp (Emit.computableInPolyTime_chain.comp
    ((ComputableInPolyTime.const 0).prod
      (ComputableInPolyTime.fst (encList Source.encQuantifier) (encList (encList encBool)))))
  have ht : ComputableInPolyTime (fun p : List Quantifier × List (List Bool) =>
      terminal 0 p.1.length p.2) Source.encPrepared encProgram := by
    unfold terminal Source.encPrepared encProgram
    fun_prop
  exact ((ComputableInPolyTime.const (lift [(0, Opcode.output)])).listAppend' hc).listAppend' ht

/-- Emit the normalized source with both swap colors retained. -/
@[expose]
def source (x : Source.Input) : Program := circuit (Source.prepare x).1 (Source.prepare x).2

/-- Colored instruction emission is polynomial-time in the upstream source encoding. -/
@[fun_prop]
theorem computableInPolyTime_source :
    ComputableInPolyTime source encPrenexCNF encProgram :=
  computableInPolyTime_circuit.comp Source.computableInPolyTime_prepare

/-- Every fixed interpretation emits its source graph data in polynomial time. -/
@[fun_prop]
theorem Target.computableInPolyTime_compile_source (T : Target) :
    ComputableInPolyTime (fun x => T.language.compile (source x)) encPrenexCNF encAndOrGraph :=
  T.language.computableInPolyTime_compile.comp computableInPolyTime_source

end Cslib.Complexity.NCL.QBF.Emit.Interpretation
