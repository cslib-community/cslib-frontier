/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.PSPACE
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# Configuration-to-edge NCL is in PSPACE

A target bit list witnesses reversal of the requested edge. Its width is the supplied initial
list's length, so polynomially bounded existential quantification applies to the existing
configuration reachability decider. This gives the AND/OR case of the upper bound in
[HearnDemaine2005, Theorem 5].

## Main results

* `Cslib.Complexity.NCL.AndOrNCLEdge_mem_PSPACE`: configuration-to-edge membership in PSPACE.

## References

* [Hearn and Demaine][HearnDemaine2005, Theorem 5]
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM

private abbrev EdgeInput := AndOrNCLEdge.Instance
private abbrev WitnessInput := EdgeInput × List Bool
private abbrev witnessEncoding := encPair encAndOrNCLEdge encBits

private def edgeToConfig (q : WitnessInput) : AndOrNCL.Instance :=
  ⟨q.1.graph, q.1.initial, q.2⟩

private def changed (q : WitnessInput) : Bool :=
  decide (q.1.edge < q.1.graph.edgeCount) &&
    decide (q.2.getD q.1.edge false ≠ q.1.initial.getD q.1.edge false)

private def witness : Set WitnessInput := {q | edgeToConfig q ∈ AndOrNCL ∧ changed q = true}

private theorem edge_witness_iff (x : EdgeInput) : x ∈ AndOrNCLEdge ↔
    ∃ t : List Bool, t.length = x.initial.length ∧ ⟨x.graph, x.initial, t⟩ ∈ AndOrNCL ∧
      x.edge < x.graph.edgeCount ∧ t.getD x.edge false ≠ x.initial.getD x.edge false := by
  constructor
  · rintro ⟨he, hv, hs, hl, u, hu, hd⟩
    let e : Fin x.graph.edgeCount := ⟨x.edge, he⟩
    have hread : (List.ofFn u).getD x.edge false = u e :=
      congrFun (AndOrGraph.config_ofFn x.graph u) e
    refine ⟨List.ofFn u, by simp [hs], ⟨hv, hs, List.length_ofFn, hl, ?_⟩, he, ?_⟩
    · simpa only [AndOrGraph.config_ofFn] using hu
    · rw [hread]
      exact hd
  · rintro ⟨t, _, ⟨hv, hs, _, hl, hr⟩, he, hd⟩
    exact ⟨he, hv, hs, hl, x.graph.config t, hr, hd⟩

private theorem computableInPolyTime_witnessStart :
    ComputableInPolyTime (fun q : WitnessInput => q.1.initial)
      witnessEncoding (encList encBool) := by
  fun_prop [witnessEncoding]

private theorem computableInPolyTime_witnessTarget :
    ComputableInPolyTime (fun q : WitnessInput => q.2) witnessEncoding encBits := by
  fun_prop [witnessEncoding]

private theorem computableInPolyTime_edgeToConfig :
    ComputableInPolyTime edgeToConfig witnessEncoding encAndOrNCL :=
  encAndOrNCL_mk_polyTime (by fun_prop [witnessEncoding]) computableInPolyTime_witnessStart
    ((bits_encList_polyTime encBool).1.comp computableInPolyTime_witnessTarget)

private theorem computableInPolyTime_changed :
    ComputableInPolyTime changed witnessEncoding encBool := by
  have he : ComputableInPolyTime (fun q : WitnessInput => q.1.edge)
      witnessEncoding encNat := by fun_prop [witnessEncoding]
  have hw : ComputableInPolyTime (fun q : WitnessInput => q.1.graph.edgeCount)
      witnessEncoding encNat := by fun_prop [witnessEncoding]
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.binary_lt' he hw)
    (ComputableInPolyTime.decide_ne
      (ComputableInPolyTime.listGetD_binary (encA := encBool) false
        computableInPolyTime_witnessTarget he)
      (ComputableInPolyTime.listGetD_binary (encA := encBool) false
        computableInPolyTime_witnessStart he))

private theorem witness_mem_PSPACE : witness ∈ PSPACE witnessEncoding := by
  have hred : PolyTimeReducible witnessEncoding encAndOrNCL (edgeToConfig ⁻¹' AndOrNCL) AndOrNCL :=
    ⟨edgeToConfig, computableInPolyTime_edgeToConfig, fun _ => Iff.rfl⟩
  have hgoal : {q | changed q = true} ∈ PSPACE witnessEncoding :=
    ⟨_, .of_polyTime computableInPolyTime_changed, fun _ => Iff.rfl⟩
  exact inter_mem_PSPACE (hred.mem_PSPACE AndOrNCL_mem_PSPACE) hgoal

/-- Configuration-to-edge reachability on AND/OR multigraphs is in PSPACE,
including graphs with loops. -/
theorem AndOrNCLEdge_mem_PSPACE : AndOrNCLEdge ∈ PSPACE encAndOrNCLEdge := by
  have hh := setOf_exists_mem_PSPACE witness_mem_PSPACE
    (by fun_prop : ComputableInPolyTime (fun x : EdgeInput => x.initial.length)
      encAndOrNCLEdge encUnary)
  convert hh using 1
  ext x
  simpa only [witness, edgeToConfig, changed, Set.mem_ofPred_eq, Bool.and_eq_true,
    decide_eq_true_eq] using edge_witness_iff x

end Cslib.Complexity.NCL
