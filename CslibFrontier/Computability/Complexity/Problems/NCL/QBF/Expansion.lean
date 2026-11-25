/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Reduction
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Expansion
import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Layout

/-!
# AND/OR expansion of source circuits

Expand every circuit generator by its open implementation. The source circuits pass a
compositional shape check, including empty matrices and clauses, so their expanded graphs
consist entirely of AND/OR vertices. The open simulation transports the explicit configurations
and distinguished edges, preserving the three source-language equivalences.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Expanded.diagram`: the primitive expansion of a normalized circuit.
* `Cslib.Complexity.NCL.QBF.Expanded.initial`, `Cslib.Complexity.NCL.QBF.Expanded.target`:
  legal canonical extensions of its source configurations.

## Main results

* `Cslib.Complexity.NCL.QBF.Expanded.isAndOr`: every expanded vertex is AND or OR.
* `Cslib.Complexity.NCL.QBF.Expanded.loopFree`: no expanded vertex repeats an incident edge.
* `Cslib.Complexity.NCL.QBF.Expanded.wellFormed`: each edge has consistent opposite endpoints.
* `Cslib.Complexity.NCL.QBF.Expanded.reachable_iff_mem_TQBFCNF`,
  `Cslib.Complexity.NCL.QBF.Expanded.canReverse_iff_mem_TQBFCNF`,
  `Cslib.Complexity.NCL.QBF.Expanded.exists_reachable_sat_iff_mem_TQBFCNF`: expanded correctness.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Expanded

open Diagram Network

private theorem checkGens_layout {a b : List Color} {D : Diagram Gate a b}
    {s : D.Edge → Bool} {k : ℕ} {p : Emit.Program} {recorded : Bool}
    (h : Emit.Layout recorded D s k p) : D.checkGens Gate.checkStandard = true := by
  induction h with
  | id => rfl
  | cell op _ => cases op <;> decide +kernel
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ => exact congrArg₂ Bool.and ih₁ ih₂

/-- All cells of the closed QBF circuit pass the standard expansion checks. -/
theorem checkGens_circuit (qs : List Quantifier) (ms : List (List Bool)) :
    (Circuit.diagram qs ms).checkGens Gate.checkStandard = true :=
  checkGens_layout (Emit.Layout.circuit false qs ms)

/-- Expand a normalized source circuit into primitive AND/OR gadgets. -/
@[expose]
def diagram (x : PrenexCNF) : Diagram Prim [] [] := (Reduction.circuit x).subst Gate.expand

/-- The open simulation fixes the source edges within the expanded circuit. -/
@[expose] def openSim (x : PrenexCNF) :
    OpenSim Gate.interp Prim.interp (Reduction.circuit x) (diagram x) :=
  openSimSubst Gate.expandOpenSim (Reduction.circuit x)

/-- The canonical extension of the source initial configuration. -/
@[expose] def initial (x : PrenexCNF) : Realization Prim.interp (diagram x) [] [] where
  orient := (openSim x).enc (Reduction.initial x).orient
  legal := (openSim x).legal_enc (Reduction.initial x).legal
  top_eq := rfl
  bot_eq := rfl

/-- The canonical extension of the source's fixed target. -/
@[expose] def target (x : PrenexCNF) : Realization Prim.interp (diagram x) [] [] where
  orient := (openSim x).enc (Reduction.target x).orient
  legal := (openSim x).legal_enc (Reduction.target x).legal
  top_eq := rfl
  bot_eq := rfl

/-- The tracked output-memory edge in the expansion. -/
@[expose] def output (x : PrenexCNF) : (diagram x).Edge := (openSim x).ι (Reduction.output x)

/-- The tracked inactive try edge for edge-to-edge reachability. -/
@[expose] def tryIn (x : PrenexCNF) : (diagram x).Edge := (openSim x).ι (Reduction.tryIn x)

/-- The tracked satisfied edge for edge-to-edge reachability. -/
@[expose] def satOut (x : PrenexCNF) : (diagram x).Edge := (openSim x).ι (Reduction.satOut x)

/-- Every vertex of an expanded source circuit is an AND or OR vertex. -/
theorem isAndOr (x : PrenexCNF) : ((diagram x).graph Prim.interp).IsAndOr :=
  Gate.expand_isAndOr_of_check _ (checkGens_circuit _ _)

/-- No expanded vertex contains both endpoints of any edge. -/
theorem loopFree (x : PrenexCNF) : ((diagram x).graph Prim.interp).LoopFree :=
  Gate.expand_loopFree_of_check _ (checkGens_circuit _ _)

/-- Every edge has two opposite ports of equal weight. -/
theorem wellFormed (x : PrenexCNF) : ((diagram x).graph Prim.interp).WellFormed :=
  Gate.expand_wellFormed_of_check _ (checkGens_circuit _ _)

/-- Fixed-target correctness survives expansion of all circuit generators. -/
theorem reachable_iff_mem_TQBFCNF (x : PrenexCNF) :
    ((diagram x).graph Prim.interp).Reachable (initial x).orient (target x).orient ↔ x ∈ TQBFCNF :=
  (Gate.expandSimulation (Reduction.circuit x)).reachable_enc_iff.trans
    (Reduction.reachable_iff_mem_TQBFCNF x)

/-- The tracked output edge is reversible exactly for true closed source inputs. -/
theorem canReverse_iff_mem_TQBFCNF (x : PrenexCNF) :
    ((diagram x).graph Prim.interp).CanReverse (initial x).orient (output x) ↔ x ∈ TQBFCNF :=
  ((Gate.expandSimulation (Reduction.circuit x)).canReverse_enc_iff (fun _ => rfl)).trans
    (Reduction.canReverse_iff_mem_TQBFCNF x)

/-- Directional edge-to-edge correctness survives expansion, including arbitrary legal starts. -/
theorem exists_reachable_sat_iff_mem_TQBFCNF (x : PrenexCNF) :
    (∃ s t, ((diagram x).graph Prim.interp).Legal s ∧ s (tryIn x) = false ∧
      t (satOut x) = false ∧ ((diagram x).graph Prim.interp).Reachable s t) ↔ x ∈ TQBFCNF :=
  ((Gate.expandSimulation (Reduction.circuit x)).exists_legal_reachable_iff
    (fun _ => rfl) (fun _ => rfl) false false).trans
      (Reduction.exists_reachable_sat_iff_mem_TQBFCNF x)

end Cslib.Complexity.NCL.QBF.Expanded
