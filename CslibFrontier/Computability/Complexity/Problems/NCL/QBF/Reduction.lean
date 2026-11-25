/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Normalize
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Circuit

/-!
# Total source-to-circuit correctness

Normalize an arbitrary upstream alternating prenex CNF input and emit its closed NCL circuit.
The explicit initial and target configurations are legal for every input. The three reachability
questions agree with membership in `TQBFCNF`, including malformed source conditions such as
free variables. Word emission, AND/OR expansion and their polynomial-time bounds are handled
after this circuit-level semantic interface.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Reduction.circuit`: the normalized closed circuit for an input.
* `Cslib.Complexity.NCL.QBF.Reduction.initial`, `Cslib.Complexity.NCL.QBF.Reduction.target`:
  legal configurations independent of the source truth.

## Main results

* `Cslib.Complexity.NCL.QBF.Reduction.reachable_iff_mem_TQBFCNF`: fixed-target correctness.
* `Cslib.Complexity.NCL.QBF.Reduction.canReverse_iff_mem_TQBFCNF`: configuration-to-edge
  correctness.
* `Cslib.Complexity.NCL.QBF.Reduction.exists_reachable_sat_iff_mem_TQBFCNF`: directional
  edge-to-edge correctness.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Reduction

open Diagram Source Cslib.Logic.PL Cslib.Logic.PL.QBF

/-- Emit a closed circuit after regularizing the source. -/
@[expose] def circuit (x : PrenexCNF) : Diagram Gate [] [] :=
  Circuit.diagram (quantifiers (normalize x).rounds)
    (masks (normalize x).rounds (normalize x).matrix)

/-- The circuit's explicit legal initial configuration. -/
@[expose] def initial (x : PrenexCNF) : Realization Gate.interp (circuit x) [] [] :=
  Circuit.initial (quantifiers (normalize x).rounds)
    (masks (normalize x).rounds (normalize x).matrix)

/-- The fixed target, with the initial body and a set output record. -/
@[expose] def target (x : PrenexCNF) : Realization Gate.interp (circuit x) [] [] :=
  Circuit.target (quantifiers (normalize x).rounds)
    (masks (normalize x).rounds (normalize x).matrix)

/-- The output memory used by the configuration-to-edge question. -/
@[expose] def output (x : PrenexCNF) : (circuit x).Edge :=
  Circuit.output (quantifiers (normalize x).rounds)
    (masks (normalize x).rounds (normalize x).matrix)

/-- The try wire, initially inactive in the edge-to-edge question. -/
@[expose] def tryIn (x : PrenexCNF) : (circuit x).Edge :=
  Circuit.tryIn (quantifiers (normalize x).rounds)
    (masks (normalize x).rounds (normalize x).matrix)

/-- The body sat wire, pointing up at the target of the edge-to-edge question. -/
@[expose] def satOut (x : PrenexCNF) : (circuit x).Edge :=
  Circuit.satOut (quantifiers (normalize x).rounds)
    (masks (normalize x).rounds (normalize x).matrix)

private theorem truth_iff_mem (x : PrenexCNF) :
    Chain.Truth (Matrix.Satisfies (masks (normalize x).rounds (normalize x).matrix))
      (quantifiers (normalize x).rounds) [] ↔ x ∈ TQBFCNF := by
  let n := normalize x
  have hc : (rounds n.rounds (ofCNF n.matrix)).Closed := normalize_closed x
  have hm : n ∈ TQBFCNF ↔ (rounds n.rounds (ofCNF n.matrix)).eval (fun _ => false) = true :=
    mem_TQBFCNF.trans (mem_TQBF_iff_of_closed hc (fun _ => false))
  exact (truth_iff_eval n.rounds n.matrix hc (fun _ => false)).trans
    (hm.symm.trans (normalize_mem_iff x))

/-- **Fixed-target correctness for every upstream input.** Open formulas are replaced by a
fixed false instance before the closed circuit is constructed. -/
theorem reachable_iff_mem_TQBFCNF (x : PrenexCNF) :
    ((circuit x).graph Gate.interp).Reachable (initial x).orient (target x).orient ↔
      x ∈ TQBFCNF :=
  (Circuit.reachable_target_iff_truth _ _).trans (truth_iff_mem x)

/-- **Configuration-to-edge correctness for every upstream input.** -/
theorem canReverse_iff_mem_TQBFCNF (x : PrenexCNF) :
    ((circuit x).graph Gate.interp).CanReverse (initial x).orient (output x) ↔ x ∈ TQBFCNF :=
  (Circuit.canReverse_initial_iff_truth _ _).trans (truth_iff_mem x)

/-- **Directional edge-to-edge correctness for every upstream input.** -/
theorem exists_reachable_sat_iff_mem_TQBFCNF (x : PrenexCNF) :
    (∃ s t, ((circuit x).graph Gate.interp).Legal s ∧ s (tryIn x) = false ∧
      t (satOut x) = false ∧ ((circuit x).graph Gate.interp).Reachable s t) ↔ x ∈ TQBFCNF :=
  (Circuit.exists_reachable_sat_iff_truth _ _).trans (truth_iff_mem x)

end Cslib.Complexity.NCL.QBF.Reduction
