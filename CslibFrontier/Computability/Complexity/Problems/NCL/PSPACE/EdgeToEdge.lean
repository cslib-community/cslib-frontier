/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.PSPACE.Edge
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# Directional edge-to-edge NCL is in PSPACE

A single witness concatenates the initial and final configurations. In a valid graph its
length equals the number of ports, since each edge has two ends. A fixed-target reachability
test on the two halves verifies validity, width, legality and reachability together.

The witness width is the number of explicitly listed ports on every input, including a
malformed binary edge count. This proves the AND/OR case of the directional edge-to-edge upper
bound in [HearnDemaine2005, Corollary 6].

## Main results

* `Cslib.Complexity.NCL.AndOrNCLEdgeToEdge_mem_PSPACE`: directional edge-to-edge membership.

## References

* [Hearn and Demaine][HearnDemaine2005, Corollary 6]
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM

private abbrev EdgeInput := AndOrNCLEdgeToEdge.Instance
private abbrev WitnessInput := EdgeInput × List Bool
private abbrev witnessEncoding := encPair encAndOrNCLEdgeToEdge encBits

private def configWitness (q : WitnessInput) : AndOrNCL.Instance :=
  let n := q.2.length / 2
  ⟨q.1.graph, q.2.take n, q.2.drop n⟩

private def checkPort (g : AndOrGraph) (p : Port ℕ) (s : List Bool) : Bool :=
  decide (p.edge < g.edgeCount) && decide (s.getD p.edge false = p.dir)

private def guard (q : WitnessInput) : Bool :=
  checkPort q.1.graph q.1.first (configWitness q).initial &&
    checkPort q.1.graph q.1.second (configWitness q).target

private def witness : Set WitnessInput := {q | configWitness q ∈ AndOrNCL ∧ guard q = true}

private theorem witness_iff (x : EdgeInput) : x ∈ AndOrNCLEdgeToEdge ↔
    ∃ w : List Bool, w.length = (x.graph.vertices.flatMap Vertex.ports).length ∧
      (x, w) ∈ witness := by
  constructor
  · rintro ⟨ha, hb, hv, s, t, hs, hA, hB, hr⟩
    let w := List.ofFn s ++ List.ofFn t
    have hw : w.length = 2 * x.graph.edgeCount := by simp [w, two_mul]
    have he : configWitness (x, w) = ⟨x.graph, List.ofFn s, List.ofFn t⟩ := by
      have half : w.length / 2 = (List.ofFn s).length := by rw [List.length_ofFn]; omega
      simp only [configWitness, half, w, List.take_left, List.drop_left]
    refine ⟨w, hw.trans (AndOrGraph.portCount_eq_two_mul _ hv.1 hv.2.2).symm, ?_⟩
    change configWitness (x, w) ∈ AndOrNCL ∧ guard (x, w) = true
    simp only [guard, he, checkPort, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hv, List.length_ofFn, List.length_ofFn, ?_, ?_⟩, ⟨ha, ?_⟩, hb, ?_⟩
    · simpa only [AndOrGraph.config_ofFn] using hs
    · simpa only [AndOrGraph.config_ofFn] using hr
    · exact (congrFun (AndOrGraph.config_ofFn x.graph s) ⟨_, ha⟩).trans hA
    · exact (congrFun (AndOrGraph.config_ofFn x.graph t) ⟨_, hb⟩).trans hB
  · rintro ⟨w, _, ⟨hv, _, _, hs, hr⟩, hg⟩
    simp only [guard, checkPort, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact ⟨hg.1.1, hg.2.1, hv, _, _, hs, hg.1.2, hg.2.2, hr⟩

private theorem computableInPolyTime_configWitness :
    ComputableInPolyTime configWitness witnessEncoding encAndOrNCL := by
  have hw := (bits_encList_polyTime encBool).1.comp
    (ComputableInPolyTime.snd encAndOrNCLEdgeToEdge encBits)
  have hn : ComputableInPolyTime (fun q : WitnessInput => q.2.length / 2)
      witnessEncoding encUnary := by
    unfold witnessEncoding
    fun_prop
  exact encAndOrNCL_mk_polyTime (by unfold witnessEncoding; fun_prop)
    (ComputableInPolyTime.listTakeWithInput hw hn) (ComputableInPolyTime.listDropWithInput hw hn)

private theorem computableInPolyTime_checkPort {α : Type} {enc : α ↪ List Bool}
    {g : α → AndOrGraph} {p : α → Port ℕ} {s : α → List Bool}
    (hg : ComputableInPolyTime g enc encAndOrGraph)
    (hp : ComputableInPolyTime p enc (encPort encNat))
    (hs : ComputableInPolyTime s enc (encList encBool)) :
    ComputableInPolyTime (fun x => checkPort (g x) (p x) (s x)) enc encBool := by
  have he : ComputableInPolyTime (fun x => (p x).edge) enc encNat := by fun_prop
  exact (ComputableInPolyTime.binary_lt' he (by fun_prop)).bool_and'
    ((ComputableInPolyTime.listGetD_binary (encA := encBool) false hs he).decide_eq' (by fun_prop))

/-- Directional edge-to-edge reachability on AND/OR multigraphs is in PSPACE,
including graphs with loops. -/
theorem AndOrNCLEdgeToEdge_mem_PSPACE : AndOrNCLEdgeToEdge ∈ PSPACE encAndOrNCLEdgeToEdge := by
  have hc := computableInPolyTime_configWitness
  have hred : PolyTimeReducible witnessEncoding encAndOrNCL (configWitness ⁻¹' AndOrNCL) AndOrNCL :=
    ⟨configWitness, hc, fun _ => Iff.rfl⟩
  have hg : ComputableInPolyTime guard witnessEncoding encBool := by
    unfold guard
    apply ComputableInPolyTime.bool_and' <;> apply computableInPolyTime_checkPort <;>
      unfold witnessEncoding at * <;> fun_prop
  have hgSpace : {q | guard q = true} ∈ PSPACE witnessEncoding :=
    ⟨_, .of_polyTime hg, fun _ => Iff.rfl⟩
  have hw : witness ∈ PSPACE witnessEncoding :=
    inter_mem_PSPACE (hred.mem_PSPACE AndOrNCL_mem_PSPACE) hgSpace
  have hlen : ComputableInPolyTime
      (fun x : EdgeInput => (x.graph.vertices.flatMap Vertex.ports).length)
      encAndOrNCLEdgeToEdge encUnary := by fun_prop
  have heq : AndOrNCLEdgeToEdge = {x | ∃ w,
      w.length = (x.graph.vertices.flatMap Vertex.ports).length ∧ (x, w) ∈ witness} :=
    Set.ext witness_iff
  rw [heq]
  exact setOf_exists_mem_PSPACE hw hlen

end Cslib.Complexity.NCL
