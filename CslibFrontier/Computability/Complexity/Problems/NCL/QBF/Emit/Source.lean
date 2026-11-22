/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.PolyTime.Compile
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Instances

/-!
# Source emission agrees with numbered circuit semantics

The polynomial-time instruction emitter expands to the numbered source word. Its compilation
therefore gives the graph used by all three reachability reductions.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.expand_source`: exact agreement of primitive words.
* `Cslib.Complexity.NCL.QBF.Emit.compile_source`: exact agreement of graph data.
* `Cslib.Complexity.NCL.QBF.Reduction.computableInPolyTime_graphData`: polynomial-time
  source graph generation.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit

/-- Expanding the emitted instructions gives the numbered source word, with the same edge order. -/
theorem expand_source (x : PrenexCNF) : expand (source x) = Numbered.word x :=
  expand_circuit _ _

/-- Compiling emitted source instructions gives exactly the reduction's graph data. -/
theorem compile_source (x : PrenexCNF) :
    language.compile (source x) = Reduction.graphData x :=
  (language.compile_eq_expand _).trans
    ((congrArg Word.compile (expand_source x)).trans (Reduction.graphData_eq_compile x).symm)

end Cslib.Complexity.NCL.QBF.Emit

namespace Cslib.Complexity.NCL.QBF.Reduction

open _root_.Turing.MultiTapeTM

/-- Generate the explicit source graph in polynomial time using the instruction compiler. -/
@[fun_prop]
theorem computableInPolyTime_graphData :
    ComputableInPolyTime graphData encPrenexCNF encAndOrGraph := by
  have h := Emit.language.computableInPolyTime_compile.comp Emit.computableInPolyTime_source
  change ComputableInPolyTime (fun x => Emit.language.compile (Emit.source x)) _ _ at h
  simpa only [Emit.compile_source] using h

/-- The directional edge-to-edge reduction is polynomial-time in the standard encodings. -/
@[fun_prop]
theorem computableInPolyTime_toEdgeToEdge :
    ComputableInPolyTime toEdgeToEdge encPrenexCNF encAndOrNCLEdgeToEdge := by
  unfold toEdgeToEdge
  fun_prop

end Cslib.Complexity.NCL.QBF.Reduction
