/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Interpretation.Bits
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.PolyTime.Interpretation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time interpreted configuration emission

Each fixed fragment contributes a fixed canonical bit list. Selecting those lists by finite tags
and concatenating them gives a polynomial-time configuration emitter for any fixed bit map.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.sourceConfiguration`: canonical source bits.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.computableInPolyTime_sourceConfiguration`:
  polynomial-time configuration emission.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit.Interpretation

open _root_.Turing.MultiTapeTM

/-- Concatenating a fixed finite table of fragment configurations is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_configurationBits (B : Diagram.BitMap Gate) (recorded : Bool) :
    ComputableInPolyTime (configurationBits B recorded) encProgram (encList encBool) := by
  have hb : ComputableInPolyTime (opcodeBits B recorded) encOpcode (encList encBool) :=
    ComputableInPolyTime.of_finite _
  have hi : ComputableInPolyTime (fun p : Program × (ℕ × Opcode) => p.2.2)
      (encPair encProgram (encPair encUnary encOpcode)) encOpcode := by fun_prop
  have hl : ComputableInPolyTime (id : Program → Program) encProgram
      (encList (encPair encUnary encOpcode)) := ComputableInPolyTime.of_eq (fun _ => rfl)
  unfold configurationBits
  exact ComputableInPolyTime.flatMapWithInput
    (f := fun (_ : Program) (i : ℕ × Opcode) => opcodeBits B recorded i.2) hl (hb.comp hi)

/-- Emit the normalized source's canonical configuration through a fixed bit map. -/
@[expose] def sourceConfiguration (B : Diagram.BitMap Gate) (recorded : Bool)
    (x : PrenexCNF) : List Bool :=
  configurationBits B recorded (source x)

/-- Emit the normalized source's initial or target bit list in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_sourceConfiguration (B : Diagram.BitMap Gate) (recorded : Bool) :
    ComputableInPolyTime (sourceConfiguration B recorded) encPrenexCNF (encList encBool) :=
  (computableInPolyTime_configurationBits B recorded).comp computableInPolyTime_source

end Cslib.Complexity.NCL.QBF.Emit.Interpretation
