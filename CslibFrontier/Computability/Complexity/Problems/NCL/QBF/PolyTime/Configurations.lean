/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Bits
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Source
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.PolyTime.InterpretationBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Canonical source configurations in polynomial time

The output latch contributes the chosen record bit. Concatenating the canonical configurations
of the emitted fragments gives exactly the numbered source initial or target configuration.
The finite fragment table and list concatenation make this a polynomial-time map.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.sourceConfiguration`: emit a normalized source configuration.

## Main results

* `Cslib.Complexity.NCL.QBF.Numbered.computableInPolyTime_initial`,
  `Cslib.Complexity.NCL.QBF.Numbered.computableInPolyTime_target`: configuration emission.
* `Cslib.Complexity.NCL.QBF.Reduction.computableInPolyTime_toConfig`,
  `Cslib.Complexity.NCL.QBF.Reduction.computableInPolyTime_toEdge`: standard reduction maps.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit

open _root_.Turing.MultiTapeTM

/-- The complete circuit's instruction bits agree with its canonical expanded configuration. -/
theorem configurationBits_circuit (recorded : Bool) (qs : List Quantifier)
    (ms : List (List Bool)) :
    configurationBits recorded (circuit qs ms) =
      Gate.extendedBits (Circuit.diagram qs ms) (Circuit.configuration recorded qs ms).orient :=
  Interpretation.configurationBits_circuit Gate.bitMap recorded qs ms

/-- Emit the source's canonical configuration with its chosen output record. -/
@[expose] def sourceConfiguration (recorded : Bool) (x : PrenexCNF) : List Bool :=
  configurationBits recorded (source x)

/-- Clearing the output record gives exactly the numbered source initial configuration. -/
theorem sourceConfiguration_false (x : PrenexCNF) :
    sourceConfiguration false x = Numbered.initial x := by
  rw [Numbered.initial, Diagram.bits_closed]
  exact configurationBits_circuit false _ _

/-- Setting the output record gives exactly the numbered fixed target configuration. -/
theorem sourceConfiguration_true (x : PrenexCNF) :
    sourceConfiguration true x = Numbered.target x := by
  rw [Numbered.target, Diagram.bits_closed]
  exact configurationBits_circuit true _ _

/-- Concatenating a fixed finite table of fragment configurations is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_configurationBits (recorded : Bool) :
    ComputableInPolyTime (configurationBits recorded) encProgram (encList encBool) :=
  Interpretation.computableInPolyTime_configurationBits Gate.bitMap recorded

/-- Emit the normalized source's initial or target bit list in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_sourceConfiguration (recorded : Bool) :
    ComputableInPolyTime (sourceConfiguration recorded) encPrenexCNF (encList encBool) :=
  (computableInPolyTime_configurationBits recorded).comp computableInPolyTime_source

end Cslib.Complexity.NCL.QBF.Emit

namespace Cslib.Complexity.NCL.QBF.Numbered

open _root_.Turing.MultiTapeTM

/-- The canonical source initial bit list is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_initial :
    ComputableInPolyTime initial encPrenexCNF (encList encBool) :=
  funext Emit.sourceConfiguration_false ▸ Emit.computableInPolyTime_sourceConfiguration false

/-- The source's fixed target bit list is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_target :
    ComputableInPolyTime target encPrenexCNF (encList encBool) :=
  funext Emit.sourceConfiguration_true ▸ Emit.computableInPolyTime_sourceConfiguration true

end Cslib.Complexity.NCL.QBF.Numbered

namespace Cslib.Complexity.NCL.QBF.Reduction

open _root_.Turing.MultiTapeTM

/-- Emit the graph and both explicit configurations in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toConfig :
    ComputableInPolyTime toConfig encPrenexCNF encAndOrNCL :=
  encAndOrNCL_mk_polyTime computableInPolyTime_graphData
    Numbered.computableInPolyTime_initial Numbered.computableInPolyTime_target

/-- Emit the graph, initial bit list and output-memory edge in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toEdge :
    ComputableInPolyTime toEdge encPrenexCNF encAndOrNCLEdge :=
  encAndOrNCLEdge_mk_polyTime computableInPolyTime_graphData
    Numbered.computableInPolyTime_initial (ComputableInPolyTime.const 4)

end Cslib.Complexity.NCL.QBF.Reduction
