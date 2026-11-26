/-
Copyright (c) 2026 Samuel Schlesinger, Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Graph
public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Polynomial-time extraction of NCL incidence multigraphs

Scan the explicit vertex ports and enumerate at most their total count of edges. Binary edge
counts are capped by this unary list-length bound before constructing a range.

## Main results

* `AndOrGraph.computableInPolyTime_incidenceGraph` certifies incidence extraction in polynomial
  time under the binary graph encodings, on every raw input.
-/

public section

namespace Cslib.Complexity.NCL.AndOrGraph

open _root_.Turing.MultiTapeTM

private theorem computableInPolyTime_portVertex {α : Type} {input : α ↪ List Bool}
    {g : α → AndOrGraph} {e : α → ℕ} {d : α → Bool}
    (hg : ComputableInPolyTime g input encAndOrGraph)
    (he : ComputableInPolyTime e input encNat)
    (hd : ComputableInPolyTime d input encBool) :
    ComputableInPolyTime (fun a => (g a).portVertex (e a) (d a)) input encNat := by
  have hz : ComputableInPolyTime (fun a => (g a).vertices.zipIdx)
      input (encList (encPair (encVertex encNat) encUnary)) := by fun_prop
  have ht : ComputableInPolyTime (fun p : α × (Vertex ℕ × ℕ) =>
      p.2.1.ports.any fun q => decide (q.port = ⟨e p.1, d p.1⟩))
      (encPair input (encPair (encVertex encNat) encUnary)) encBool := by fun_prop
  have hf := ComputableInPolyTime.findWithInput
    (test := fun a v => v.1.ports.any fun p => decide (p.port = ⟨e a, d a⟩)) hz ht
  have hu : ComputableInPolyTime (fun a =>
      (((g a).vertices.zipIdx.find? fun v =>
        v.1.ports.any fun p => decide (p.port = ⟨e a, d a⟩)).map Prod.snd).getD 0)
      input encUnary := by fun_prop
  exact ComputableInPolyTime.unary_to_binary.comp hu

/-- Extract the numbered incidence multigraph in polynomial time in the binary graph encoding. -/
@[fun_prop]
theorem computableInPolyTime_incidenceGraph :
    ComputableInPolyTime incidenceGraph encAndOrGraph encGraph := by
  have hn : ComputableInPolyTime (fun g : AndOrGraph =>
      (g.vertices.flatMap Vertex.ports).length) encAndOrGraph encUnary := by fun_prop
  have hn' := ComputableInPolyTime.unary_to_binary.comp hn
  have he : ComputableInPolyTime (fun g : AndOrGraph => g.edgeCount)
      encAndOrGraph encNat := by fun_prop
  have hm : ComputableInPolyTime (fun g : AndOrGraph =>
      if g.edgeCount ≤ (g.vertices.flatMap Vertex.ports).length then
        min (g.vertices.flatMap Vertex.ports).length g.edgeCount else 0)
      encAndOrGraph encUnary := by fun_prop
  have hm' : ComputableInPolyTime (fun g : AndOrGraph =>
      if g.edgeCount ≤ (g.vertices.flatMap Vertex.ports).length then g.edgeCount else 0)
      encAndOrGraph encUnary :=
    hm.of_enc_eq fun g => congrArg encUnary (by split_ifs <;> omega)
  have hr : ComputableInPolyTime (fun g : AndOrGraph =>
      (List.range (g.vertices.flatMap Vertex.ports).length).take
        (if g.edgeCount ≤ (g.vertices.flatMap Vertex.ports).length then g.edgeCount else 0))
      encAndOrGraph (encList encUnary) := by fun_prop
  have hvU : ComputableInPolyTime (fun g : AndOrGraph => List.range g.vertices.length)
      encAndOrGraph (encList encUnary) := by fun_prop
  have hv : ComputableInPolyTime (fun g : AndOrGraph => List.range g.vertices.length)
      encAndOrGraph (encList encNat) := by
    simpa only [Function.comp_def, List.map_id'] using
      (ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary).comp hvU
  have hi : ComputableInPolyTime (fun p : AndOrGraph × ℕ => p.2)
      (encPair encAndOrGraph encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hedges := ComputableInPolyTime.mapWithInput
    (f := fun g e => (g.portVertex e false, g.portVertex e true)) hr
    ((computableInPolyTime_portVertex (g := Prod.fst) (by fun_prop) hi (.const false)).prod
      (computableInPolyTime_portVertex (g := Prod.fst) (by fun_prop) hi (.const true)))
  exact encGraph_mk_polyTime hv hedges

end Cslib.Complexity.NCL.AndOrGraph
