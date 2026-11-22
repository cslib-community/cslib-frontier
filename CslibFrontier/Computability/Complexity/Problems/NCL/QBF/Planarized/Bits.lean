/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Planarized.Emit
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Bits
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.PolyTime.InterpretationBits

/-!
# Canonical planar source configurations in polynomial time

Serialize the source initial and target configurations after planarization. Their bits agree
with concatenating the canonical configurations of the emitted fixed fragments.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Planarized.initialBits`,
  `Cslib.Complexity.NCL.QBF.Planarized.targetBits`: numbered canonical planar configurations.

## Main results

* `Cslib.Complexity.NCL.QBF.Planarized.computableInPolyTime_initialBits`,
  `Cslib.Complexity.NCL.QBF.Planarized.computableInPolyTime_targetBits`: polynomial-time emission.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Planarized

open Diagram _root_.Turing.MultiTapeTM

/-- The canonical initial configuration, numbered in edge-creation order. -/
@[expose] def initialBits (x : PrenexCNF) : List Bool := (diagram x).bits (initial x).orient

/-- The fixed target configuration, numbered in edge-creation order. -/
@[expose] def targetBits (x : PrenexCNF) : List Bool := (diagram x).bits (target x).orient

/-- Emitting canonical inactive fragment configurations gives exactly the planar initial bits. -/
private theorem sourceConfiguration_false (x : PrenexCNF) :
    Emit.Interpretation.sourceConfiguration Planar.Circuit.bitMap false x = initialBits x := by
  unfold initialBits
  rw [Diagram.bits_closed]
  exact Emit.Interpretation.configurationBits_circuit Planar.Circuit.bitMap false _ _

/-- Emitting canonical recorded fragment configurations gives exactly the planar target bits. -/
private theorem sourceConfiguration_true (x : PrenexCNF) :
    Emit.Interpretation.sourceConfiguration Planar.Circuit.bitMap true x = targetBits x := by
  unfold targetBits
  rw [Diagram.bits_closed]
  exact Emit.Interpretation.configurationBits_circuit Planar.Circuit.bitMap true _ _

/-- Emit the canonical planar initial bit list in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_initialBits :
    ComputableInPolyTime initialBits encPrenexCNF (encList encBool) := by
  rw [← funext sourceConfiguration_false]
  exact Emit.Interpretation.computableInPolyTime_sourceConfiguration Planar.Circuit.bitMap false

/-- Emit the fixed planar target bit list in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_targetBits :
    ComputableInPolyTime targetBits encPrenexCNF (encList encBool) := by
  rw [← funext sourceConfiguration_true]
  exact Emit.Interpretation.computableInPolyTime_sourceConfiguration Planar.Circuit.bitMap true

end Cslib.Complexity.NCL.QBF.Planarized
