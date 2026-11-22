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

/-!
# Directional edge-to-edge NCL is in PSPACE

Quantify an initial bit list of polynomially computed width. If its second distinguished edge
already has the requested direction, the empty path suffices. Otherwise configuration-to-edge
reachability supplies the requested reversal.

The witness encodes one bit per edge of a valid graph. Its width is bounded by the number
of explicitly listed ports on every input, including a malformed binary edge count. This
proves the AND/OR case of the directional edge-to-edge upper bound in
[HearnDemaine2005, Corollary 6].

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
private def boundedWidth (g : AndOrGraph) : ℕ :=
  min (g.vertices.flatMap Vertex.ports).length g.edgeCount

private theorem boundedWidth_eq (g : AndOrGraph) (hv : g.Valid) : boundedWidth g = g.edgeCount := by
  rw [boundedWidth, AndOrGraph.portCount_eq_two_mul g hv.1 hv.2.2]
  exact Nat.min_eq_right (by omega)

private theorem computableInPolyTime_boundedWidth :
    ComputableInPolyTime boundedWidth encAndOrGraph encUnary := by
  have hp : ComputableInPolyTime (fun g : AndOrGraph => g.vertices.flatMap Vertex.ports)
      encAndOrGraph (encWeightedPorts encNat) := by fun_prop
  exact ComputableInPolyTime.binary_min_unary' ((ComputableInPolyTime.length_list _).comp hp)
    (by fun_prop)

private def toEdge (q : WitnessInput) : AndOrNCLEdge.Instance :=
  ⟨q.1.graph, q.2, q.1.second.edge⟩

private def common (q : WitnessInput) : Bool :=
  q.1.graph.checkValid &&
    ((decide (q.2.length = q.1.graph.edgeCount) && q.1.graph.checkLegal q.2) &&
      (decide (q.1.first.edge < q.1.graph.edgeCount) &&
        (decide (q.1.second.edge < q.1.graph.edgeCount) &&
          decide (q.2.getD q.1.first.edge false = q.1.first.dir))))

private def desired (q : WitnessInput) : Bool :=
  decide (q.2.getD q.1.second.edge false = q.1.second.dir)

private def witness : Set WitnessInput :=
  {q | common q = true ∧ (desired q = true ∨ toEdge q ∈ AndOrNCLEdge)}

private theorem exists_goal_iff {V E : Type*} [DecidableEq E]
    (G : ConstraintGraph V E) (s : E → Bool) (e : E) (d : Bool) :
    (∃ t, G.Reachable s t ∧ t e = d) ↔ s e = d ∨ G.CanReverse s e := by
  constructor
  · rintro ⟨t, hr, hd⟩
    by_cases hs : s e = d
    · exact .inl hs
    · exact .inr ⟨t, hr, fun h => hs (h.symm.trans hd)⟩
  · rintro (hs | ⟨t, hr, hd⟩)
    · exact ⟨s, .refl, hs⟩
    · by_cases hs : s e = d
      · exact ⟨s, .refl, hs⟩
      · refine ⟨t, hr, ?_⟩
        cases hS : s e <;> cases hT : t e <;> cases d <;> simp_all

private theorem edgeToEdge_witness_iff (x : EdgeInput) : x ∈ AndOrNCLEdgeToEdge ↔
    ∃ s : List Bool, s.length = boundedWidth x.graph ∧ (x, s) ∈ witness := by
  constructor
  · rintro ⟨hA, hB, hv, s, t, hl, hAeq, hBeq, hr⟩
    let eA : Fin x.graph.edgeCount := ⟨x.first.edge, hA⟩
    let eB : Fin x.graph.edgeCount := ⟨x.second.edge, hB⟩
    let bits := List.ofFn s
    have hread (e : Fin x.graph.edgeCount) : bits.getD e false = s e :=
      congrFun (AndOrGraph.config_ofFn x.graph s) e
    refine ⟨bits, by rw [boundedWidth_eq _ hv]; exact List.length_ofFn, ?_, ?_⟩
    · simp only [common, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨(AndOrGraph.checkValid_eq_true_iff _).2 hv,
        ⟨List.length_ofFn, ?_⟩, hA, hB, ?_⟩
      · apply (AndOrGraph.checkLegal_eq_true_iff _ hv.1 _).2
        simpa only [bits, AndOrGraph.config_ofFn] using hl
      · rw [show bits.getD x.first.edge false = s eA from hread eA]
        exact hAeq
    · have hg := (exists_goal_iff x.graph.graph s eB x.second.dir).1 ⟨t, hr, hBeq⟩
      rcases hg with hg | hg
      · left
        simp only [desired, decide_eq_true_eq]
        rw [show bits.getD x.second.edge false = s eB from hread eB]
        exact hg
      · right
        refine ⟨hB, hv, List.length_ofFn, ?_, ?_⟩
        · change x.graph.graph.Legal (x.graph.config bits)
          simpa only [bits, AndOrGraph.config_ofFn] using hl
        · change x.graph.graph.CanReverse (x.graph.config bits) eB
          simpa only [bits, AndOrGraph.config_ofFn] using hg
  · rintro ⟨s, _, hc, hd⟩
    simp only [common, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hv, ⟨hs, hl⟩, hA, hB, hAdir⟩ := hc
    have hv := (AndOrGraph.checkValid_eq_true_iff _).1 hv
    have hl := (AndOrGraph.checkLegal_eq_true_iff _ hv.1 _).1 hl
    rcases hd with hd | hd
    · exact ⟨hA, hB, hv, x.graph.config s, x.graph.config s, hl, hAdir,
        of_decide_eq_true hd, .refl⟩
    · obtain ⟨_, _, _, _, hreverse⟩ := hd
      obtain ⟨t, hr, ht⟩ := (exists_goal_iff x.graph.graph (x.graph.config s)
        (⟨x.second.edge, hB⟩ : Fin x.graph.edgeCount) x.second.dir).2 (.inr hreverse)
      exact ⟨hA, hB, hv, x.graph.config s, t, hl, hAdir, ht, hr⟩

private theorem computableInPolyTime_descriptor :
    ComputableInPolyTime (fun q : WitnessInput => q.1)
      witnessEncoding encAndOrNCLEdgeToEdge := by
  unfold witnessEncoding
  fun_prop

private theorem computableInPolyTime_state :
    ComputableInPolyTime (fun q : WitnessInput => q.2) witnessEncoding encBits := by
  unfold witnessEncoding
  fun_prop

private theorem computableInPolyTime_toEdge :
    ComputableInPolyTime toEdge witnessEncoding encAndOrNCLEdge := by
  have hd := computableInPolyTime_descriptor
  have hg : ComputableInPolyTime (fun q : WitnessInput => q.1.graph)
      witnessEncoding encAndOrGraph := by fun_prop
  have he : ComputableInPolyTime (fun q : WitnessInput => q.1.second.edge)
      witnessEncoding encNat := by fun_prop
  exact encAndOrNCLEdge_mk_polyTime hg
    ((bits_encList_polyTime encBool).1.comp computableInPolyTime_state) he

private theorem computableInPolyTime_common :
    ComputableInPolyTime common witnessEncoding encBool := by
  have hd := computableInPolyTime_descriptor
  have hs := computableInPolyTime_state
  have hg : ComputableInPolyTime (fun q : WitnessInput => q.1.graph)
      witnessEncoding encAndOrGraph := by fun_prop
  have hw : ComputableInPolyTime (fun q : WitnessInput => q.1.graph.edgeCount)
      witnessEncoding encNat := by
    fun_prop
  have hA : ComputableInPolyTime (fun q : WitnessInput => q.1.first.edge)
      witnessEncoding encNat := by fun_prop
  have hB : ComputableInPolyTime (fun q : WitnessInput => q.1.second.edge)
      witnessEncoding encNat := by fun_prop
  have hdA : ComputableInPolyTime (fun q : WitnessInput => q.1.first.dir)
      witnessEncoding encBool := by fun_prop
  have hn : ComputableInPolyTime (fun q : WitnessInput => q.2.length)
      witnessEncoding encUnary := by fun_prop
  have hbn := ComputableInPolyTime.unary_to_binary.comp hn
  have hlen := hbn.decide_eq' hw
  have hr := ComputableInPolyTime.listGetD_binary (encA := encBool) false hs hA
  have hdir := hr.decide_eq' hdA
  have hv := AndOrGraph.computableInPolyTime_checkValid.comp hg
  have hl := AndOrGraph.computableInPolyTime_checkLegal hg hs
  exact ComputableInPolyTime.bool_and' hv
    (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hlen hl)
      (ComputableInPolyTime.bool_and' (ComputableInPolyTime.binary_lt' hA hw)
        (ComputableInPolyTime.bool_and' (ComputableInPolyTime.binary_lt' hB hw) hdir)))

private theorem computableInPolyTime_desired :
    ComputableInPolyTime desired witnessEncoding encBool := by
  have hd := computableInPolyTime_descriptor
  have he : ComputableInPolyTime (fun q : WitnessInput => q.1.second.edge)
      witnessEncoding encNat := by fun_prop
  have hdir : ComputableInPolyTime (fun q : WitnessInput => q.1.second.dir)
      witnessEncoding encBool := by fun_prop
  have hr := ComputableInPolyTime.listGetD_binary (encA := encBool) false
    computableInPolyTime_state he
  exact hr.decide_eq' hdir

private theorem witness_mem_PSPACE : witness ∈ PSPACE witnessEncoding := by
  have hred : PolyTimeReducible witnessEncoding encAndOrNCLEdge
      (toEdge ⁻¹' AndOrNCLEdge) AndOrNCLEdge :=
    ⟨toEdge, computableInPolyTime_toEdge, fun _ => Iff.rfl⟩
  have hc : {q | common q = true} ∈ PSPACE witnessEncoding :=
    ⟨_, .of_polyTime computableInPolyTime_common, fun _ => Iff.rfl⟩
  have hd : {q | desired q = true} ∈ PSPACE witnessEncoding :=
    ⟨_, .of_polyTime computableInPolyTime_desired, fun _ => Iff.rfl⟩
  exact inter_mem_PSPACE hc (union_mem_PSPACE hd (hred.mem_PSPACE AndOrNCLEdge_mem_PSPACE))

/-- Directional edge-to-edge reachability on AND/OR multigraphs is in PSPACE,
including graphs with loops. -/
theorem AndOrNCLEdgeToEdge_mem_PSPACE : AndOrNCLEdgeToEdge ∈ PSPACE encAndOrNCLEdgeToEdge := by
  have hg : ComputableInPolyTime (fun x : EdgeInput => x.graph)
      encAndOrNCLEdgeToEdge encAndOrGraph := by
    fun_prop
  have hh := setOf_exists_mem_PSPACE witness_mem_PSPACE (computableInPolyTime_boundedWidth.comp hg)
  have heq : {x : EdgeInput | ∃ s : List Bool, s.length = boundedWidth x.graph ∧ (x, s) ∈ witness} =
      AndOrNCLEdgeToEdge := Set.ext (fun x => (edgeToEdge_witness_iff x).symm)
  simp only [Function.comp_apply] at hh
  rwa [heq] at hh

end Cslib.Complexity.NCL
