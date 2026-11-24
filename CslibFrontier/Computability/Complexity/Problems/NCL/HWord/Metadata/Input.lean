/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Metadata.PolyTime
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.OfFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.List.GetD

/-!
# Standard explicit AND/OR inputs for H-word instances

Both configurations are emitted at the source length, with the target read by the fixed zero
padding convention. Thus every graph and both direction lists satisfy the generic canonical
planarizer's input conditions, before the final source/target length test.

## Main definitions

* `HWord.Metadata.toAndOr`: the actual explicit standard graph and endpoint directions.
* `HWord.Metadata.toInput`: the same data in the canonical planarizer's restricted input type.

## Main results

* `HWord.Metadata.computableInPolyTime_toInput`: standard encoded input compilation.
* `HWord.Metadata.toAndOr_mem_iff`: exact endpoint reconfiguration semantics.
-/

public section

namespace Cslib.Complexity.NCL.HWord.Metadata

open SelectorNetwork.AndOr _root_.Turing.MultiTapeTM

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- The same numbered standard graph with one canonical bit per actual wire at each endpoint. -/
@[expose] def toAndOr (x : Instance q) : AndOrNCL.Instance where
  graph := AndOrGraph.ofFinite (Planarized.finiteGraph (n := x.source.length) H hq)
  initial := Program.bits (stateBlocks H hq x.source.length x.source)
  target := Program.bits (stateBlocks H hq x.source.length x.target)

private theorem graph_valid (n : ℕ) :
    (AndOrGraph.ofFinite (Planarized.finiteGraph (n := n) H hq)).Valid :=
  AndOrGraph.ofFinite_valid _ (Numbering.isAndOr _ _ _)
    (Numbering.wellFormed _ _ _)

private theorem graph_loopFree (n : ℕ) :
    (AndOrGraph.ofFinite (Planarized.finiteGraph (n := n) H hq)).graph.LoopFree :=
  AndOrGraph.ofFinite_loopFree _ (Numbering.loopFree _ _ _)

private theorem length_bits (n : ℕ) (word : List (Fin q)) :
    (Program.bits (stateBlocks H hq n word)).length = Planarized.width (n := n) H hq := by
  rw [bits_stateBlocks_eq H hq word (fun i : Fin n => word.getD i.val ⟨0, hq⟩) (fun _ => rfl)]
  exact List.length_ofFn

/-- The actual graph data and full direction lists satisfy the generic planarizer's domain. -/
@[expose] def toInput (x : Instance q) : Planar.Embedding.PolyTime.Input :=
  ⟨toAndOr H hq x, by
    exact ⟨graph_valid H hq x.source.length, graph_loopFree H hq x.source.length,
      length_bits H hq x.source.length x.source,
      length_bits H hq x.source.length x.target⟩⟩

/-- Actual explicit AND/OR graph and configuration emission is polynomial-time. -/
theorem computableInPolyTime_toAndOr : ComputableInPolyTime (toAndOr H hq) (encInstance q)
    encAndOrNCL := by
  have hs := encInstance_source_polyTime q
    (ComputableInPolyTime.id' (encIn := encInstance q))
  have ht := encInstance_target_polyTime q
    (ComputableInPolyTime.id' (encIn := encInstance q))
  have hn : ComputableInPolyTime (fun x : Instance q => x.source.length)
      (encInstance q) encUnary := by fun_prop
  have hg := (computableInPolyTime_graph H hq).comp hn
  have hi := (computableInPolyTime_bits H hq).comp (hn.prod hs)
  have hf := (computableInPolyTime_bits H hq).comp (hn.prod ht)
  unfold toAndOr
  fun_prop

/-- The same actual data are polynomial-time under the generic planarizer's restricted encoding. -/
theorem computableInPolyTime_toInput : ComputableInPolyTime (toInput H hq) (encInstance q)
    Planar.Embedding.PolyTime.encInput :=
  (computableInPolyTime_toAndOr H hq).of_enc_eq (fun _ => rfl)

private theorem toAndOr_eq_ofFn (x : Instance q) :
    let S := Numbering.simulation (PortGraph.network H x.source.length) (AndOr.rowSection H hq)
      (PortGraph.bandwidthCertificate H).order
    toAndOr H hq x =
      ⟨AndOrGraph.ofFinite (Planarized.finiteGraph (n := x.source.length) H hq),
        List.ofFn (S.enc (AndOr.orientation H hq x.source.get)),
        List.ofFn (S.enc (AndOr.orientation H hq
          (fun i : Fin x.source.length => x.target.getD i.val ⟨0, hq⟩)))⟩ := by
  dsimp only
  unfold toAndOr
  rw [AndOrNCL.Instance.mk.injEq]
  exact ⟨rfl, bits_stateBlocks_eq H hq x.source x.source.get
    (fun i => List.getD_eq_get x.source ⟨0, hq⟩ i),
    bits_stateBlocks_eq H hq x.target (fun i => x.target.getD i.val ⟨0, hq⟩) (fun _ => rfl)⟩

/-- The actual raw instance preserves and reflects word reconfiguration at the source length. -/
theorem toAndOr_mem_iff (x : Instance q) : toAndOr H hq x ∈ AndOrNCL ↔
    Legal H x.source.get ∧ Reachable H x.source.get
      (fun i : Fin x.source.length => x.target.getD i.val ⟨0, hq⟩) := by
  let s := x.source.get
  let t := fun i : Fin x.source.length => x.target.getD i.val ⟨0, hq⟩
  let S := Numbering.simulation (PortGraph.network H x.source.length) (AndOr.rowSection H hq)
    (PortGraph.bandwidthCertificate H).order
  rw [toAndOr_eq_ofFn, AndOrGraph.ofFinite_mem_AndOrNCL_iff _ (graph_valid H hq _)]
  simp only [List.length_ofFn, Planarized.width, Planarized.finiteGraph, AndOrGraph.ofFinite,
    true_and, AndOrGraph.config_ofFn]
  change (Planarized.finiteGraph (n := x.source.length) H hq).Legal
    (S.enc (AndOr.orientation H hq s)) ∧
    (Planarized.finiteGraph (n := x.source.length) H hq).Reachable
      (S.enc (AndOr.orientation H hq s))
      (S.enc (AndOr.orientation H hq t)) ↔ _
  exact (and_congr S.legal_enc_iff S.reachable_enc_iff).trans
    (and_congr (AndOr.legal_orientation_iff H hq s) (AndOr.reachable_orientation_iff H hq s t))

/-- The generic compiler emits the same actual plane word and endpoint bits as `Planarized`. -/
theorem compile_toInput (x : Instance q) : Planar.Embedding.PolyTime.compile (toInput H hq x) =
    ⟨Planarized.word (n := x.source.length) H hq, Planarized.bits H hq x.source.get,
      Planarized.bits H hq (fun i : Fin x.source.length => x.target.getD i.val ⟨0, hq⟩)⟩ := by
  let s := x.source.get
  let t := fun i : Fin x.source.length => x.target.getD i.val ⟨0, hq⟩
  let S := Numbering.simulation (PortGraph.network H x.source.length) (AndOr.rowSection H hq)
    (PortGraph.bandwidthCertificate H).order
  have hx : toInput H hq x =
      (⟨⟨AndOrGraph.ofFinite (Planarized.finiteGraph (n := x.source.length) H hq),
        List.ofFn (S.enc (AndOr.orientation H hq s)), List.ofFn (S.enc (AndOr.orientation H hq t))⟩,
        (toInput H hq x).property.1, (toInput H hq x).property.2.1,
        List.length_ofFn, List.length_ofFn⟩ :
        Planar.Embedding.PolyTime.Input) := by
    apply Subtype.ext
    change toAndOr H hq x = _
    exact toAndOr_eq_ofFn H hq x
  rw [hx, Planarized.bits_planeSimulation, Planarized.bits_planeSimulation]
  have hc := Planar.Embedding.PolyTime.compile_ofFinite
    (Planarized.finiteGraph (n := x.source.length) H hq)
    (toInput H hq x).property.1 (Planarized.vertices_isAndOr (n := x.source.length) H hq)
    (Planarized.vertices_wellFormed (n := x.source.length) H hq)
    (Planarized.vertices_loopFree (n := x.source.length) H hq)
    (S.enc (AndOr.orientation H hq s)) (S.enc (AndOr.orientation H hq t))
  simp only [Planarized.word, Planarized.diagram, Planarized.vertices, S, s, t] at hc ⊢
  convert hc using 1
  rfl

end Cslib.Complexity.NCL.HWord.Metadata
