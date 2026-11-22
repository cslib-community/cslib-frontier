/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Circuit
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Expansion
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.RealizationSimulation

/-!
# Planar source circuits

Apply circuit planarization to the normalized QBF reduction. The canonical initial and target
configurations and the three distinguished edges are transported by its simulation. All three
reachability questions agree with the truth of the source QBF, for every source input.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Planarized.diagram`: the planar primitive circuit.
* `Cslib.Complexity.NCL.QBF.Planarized.initial`, `Cslib.Complexity.NCL.QBF.Planarized.target`:
  canonical configurations.
* `Cslib.Complexity.NCL.QBF.Planarized.output`, `Cslib.Complexity.NCL.QBF.Planarized.tryIn`,
  `Cslib.Complexity.NCL.QBF.Planarized.satOut`: tracked decision edges.

## Main results

* `Cslib.Complexity.NCL.QBF.Planarized.planar`, `Cslib.Complexity.NCL.QBF.Planarized.isAndOr`,
  `Cslib.Complexity.NCL.QBF.Planarized.loopFree`, `Cslib.Complexity.NCL.QBF.Planarized.wellFormed`:
  output graph properties.
* `Cslib.Complexity.NCL.QBF.Planarized.reachable_iff_mem_TQBFCNF`,
  `Cslib.Complexity.NCL.QBF.Planarized.canReverse_iff_mem_TQBFCNF`,
  `Cslib.Complexity.NCL.QBF.Planarized.exists_reachable_sat_iff_mem_TQBFCNF`: semantic correctness.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Planarized

open Diagram

/-- The normalized source circuit expanded and planarized. -/
@[expose]
def diagram (x : PrenexCNF) : Diagram Prim [] [] := Planar.Circuit.diagram (Reduction.circuit x)

/-- The plane primitive word emitted from the source circuit. -/
@[expose] def word (x : PrenexCNF) : Word := (diagram x).toWord Prim.interp 0

/-- The emitted word checks from the empty boundary to the empty boundary. -/
theorem wellTyped_word (x : PrenexCNF) : (word x).WellTyped [] [] :=
  wellTyped_toWord Prim.interp (diagram x)

/-- Every emitted layer is one standard AND/OR vertex. -/
theorem checkPlane_word (x : PrenexCNF) : (word x).checkPlane = true :=
  Planar.Circuit.checkPlane_word _ (Expanded.checkGens_circuit _ _)

/-- The simulation of the source circuit by its planar expansion. -/
@[expose] def simulation (x : PrenexCNF) :
    ConstraintGraph.Simulation ((Reduction.circuit x).graph Gate.interp)
      ((diagram x).graph Prim.interp) := Planar.Circuit.simulation (Reduction.circuit x)

/-- The canonical initial configuration of the planar circuit. -/
@[expose] def initial (x : PrenexCNF) : Realization Prim.interp (diagram x) [] [] :=
  (Reduction.initial x).mapClosed (simulation x)

/-- The canonical fixed target of the planar circuit. -/
@[expose] def target (x : PrenexCNF) : Realization Prim.interp (diagram x) [] [] :=
  (Reduction.target x).mapClosed (simulation x)

/-- The tracked output memory. -/
@[expose] def output (x : PrenexCNF) : (diagram x).Edge :=
  Planar.Circuit.edge (Reduction.circuit x) (Reduction.output x)

/-- The tracked inactive try input. -/
@[expose] def tryIn (x : PrenexCNF) : (diagram x).Edge :=
  Planar.Circuit.edge (Reduction.circuit x) (Reduction.tryIn x)

/-- The tracked satisfied output. -/
@[expose] def satOut (x : PrenexCNF) : (diagram x).Edge :=
  Planar.Circuit.edge (Reduction.circuit x) (Reduction.satOut x)

/-- The source drawing contains no swaps after planarization. -/
theorem planar (x : PrenexCNF) : (diagram x).Planar := Planar.Circuit.planar _

/-- Every resulting vertex is AND or OR. -/
theorem isAndOr (x : PrenexCNF) : ((diagram x).graph Prim.interp).IsAndOr :=
  Planar.Circuit.andOr _ (Expanded.checkGens_circuit _ _)

/-- No vertex contains both endpoints of an edge. -/
theorem loopFree (x : PrenexCNF) : ((diagram x).graph Prim.interp).LoopFree :=
  Planar.Circuit.loopFree _ (Expanded.checkGens_circuit _ _)

/-- Every edge has opposite endpoints of equal weight. -/
theorem wellFormed (x : PrenexCNF) : ((diagram x).graph Prim.interp).WellFormed :=
  Planar.Circuit.wellFormed _ (Expanded.checkGens_circuit _ _)

/-- Fixed-target reachability in the planar circuit agrees with source truth. -/
theorem reachable_iff_mem_TQBFCNF (x : PrenexCNF) :
    ((diagram x).graph Prim.interp).Reachable (initial x).orient (target x).orient ↔ x ∈ TQBFCNF :=
  (simulation x).reachable_enc_iff.trans (Reduction.reachable_iff_mem_TQBFCNF x)

/-- The planar output edge can reverse exactly for true source inputs. -/
theorem canReverse_iff_mem_TQBFCNF (x : PrenexCNF) :
    ((diagram x).graph Prim.interp).CanReverse (initial x).orient (output x) ↔ x ∈ TQBFCNF :=
  ((simulation x).canReverse_enc_iff
    (fun t => Planar.Circuit.simulation_abs _ t _)).trans (Reduction.canReverse_iff_mem_TQBFCNF x)

/-- Directional edge-to-edge reachability in the planar circuit agrees with source truth. -/
theorem exists_reachable_sat_iff_mem_TQBFCNF (x : PrenexCNF) :
    (∃ s t, ((diagram x).graph Prim.interp).Legal s ∧ s (tryIn x) = false ∧
      t (satOut x) = false ∧ ((diagram x).graph Prim.interp).Reachable s t) ↔ x ∈ TQBFCNF :=
  ((simulation x).exists_legal_reachable_iff
    (fun t => Planar.Circuit.simulation_abs _ t _)
    (fun t => Planar.Circuit.simulation_abs _ t _) false false).trans
      (Reduction.exists_reachable_sat_iff_mem_TQBFCNF x)

end Cslib.Complexity.NCL.QBF.Planarized
