/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Planarized
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.PolyTime.Interpretation

/-!
# Polynomial-time planar source graph emission

Instantiate the fixed instruction compiler with circuit planarization. The emitted word equals
the planar source diagram's word, including the order of vertices and edges.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Planarized.graphData`: the explicit planar source graph.

## Main results

* `Cslib.Complexity.NCL.QBF.Planarized.computableInPolyTime_graphData`: polynomial-time
  source graph generation.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Planarized

open Diagram _root_.Turing.MultiTapeTM

/-- Interpret source fragments by replacing gates and swaps with their planar implementations. -/
private def interpretation : Emit.Interpretation.Target where
  map D := Planar.planarizeAlong Gate.expand D
  map_id _ := rfl
  map_comp _ _ := rfl
  map_tensor _ _ := rfl

/-- The colored source instructions expand to the plane source word in its exact edge order. -/
private theorem expand_source (x : PrenexCNF) :
    interpretation.language.expand (Emit.source x) = word x :=
  Emit.Interpretation.expand_circuit interpretation _ _

/-- Emit the exact plane source word in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_word : ComputableInPolyTime word encPrenexCNF encWord := by
  have h := interpretation.language.computableInPolyTime_expand.comp
    Emit.computableInPolyTime_source
  change ComputableInPolyTime (fun x =>
    interpretation.language.expand (Emit.source x)) _ _ at h
  simpa only [expand_source] using h

/-- Explicit vertex data and edge count of the planar source graph. -/
@[expose] def graphData (x : PrenexCNF) : AndOrGraph := Word.compile (word x)

/-- Generate the explicit planar source graph in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_graphData :
    ComputableInPolyTime graphData encPrenexCNF encAndOrGraph :=
  Word.computableInPolyTime_compile.comp computableInPolyTime_word

end Cslib.Complexity.NCL.QBF.Planarized
