/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Emit
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Bundles
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.RoutingCorrectness
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Emit
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding

/-!
# Exact serialization of finite graph data

Erasing the finite edge bounds recovers the supplied vertex records. The explicit graph-data
emitter consequently uses the same incidence order, colors, and source cells as the canonical
finite incidence drawing.

## Main results

* `expand_emit_program`: the existing canonical plane word.
* `configurationBits_emit_program`: its actual canonical simulation configurations.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding.PolyTime

open Diagram

/-- The finite semantic vertices, with their bounds erased, are the original supplied records. -/
private theorem vertices_map (g : AndOrGraph) (hb : g.Bounded) :
    (List.ofFn g.graph).map (Vertex.map Fin.val) = g.vertices := by
  rw [List.map_ofFn]; change List.ofFn (g.graph.map Fin.val) = _
  rw [g.graph_map_val hb, List.ofFn_get]

/-- The binary natural-edge scan computes the actual finite incidence color. -/
private theorem edgeColor_eq (g : AndOrGraph) (hb : g.Bounded) (e : Fin g.edgeCount) :
    Emit.edgeColor g e.val = color (List.ofFn g.graph) e := by
  unfold Emit.edgeColor color; conv_lhs => rw [← vertices_map g hb]
  simp only [List.flatMap_map, Vertex.map, ← List.map_flatMap, List.any_map]; rfl

/-- The emitted binary port records retain the actual finite incidence identities. -/
private def finiteWire (g : AndOrGraph) (bits : List Bool) (p : Port (Fin g.edgeCount)) : Wire :=
  Emit.wire g bits (p.map Fin.val)

/-- Finite incidence names remain distinct after adding their color and direction data. -/
private theorem finiteWire_injective (g : AndOrGraph) (bits : List Bool) :
    Function.Injective (finiteWire g bits) := fun p q h =>
  congrArg WeightedPort.port <| WeightedPort.map_injective Fin.val_injective
    (show WeightedPort.map Fin.val ⟨p, 0⟩ = WeightedPort.map Fin.val ⟨q, 0⟩ from
      congrArg (fun r => ({ port := r, weight := 0 } : WeightedPort ℕ)) (congrArg Wire.port h))

/-- The finite wire's color agrees with the canonical incidence drawing. -/
private theorem finiteWire_color (g : AndOrGraph) (hb : g.Bounded) (bits : List Bool) :
    (fun p => (finiteWire g bits p).color) = fun p => color (List.ofFn g.graph) p.edge :=
  funext fun p => edgeColor_eq g hb p.edge

private theorem shape_vertices (g : AndOrGraph) (h : g.Valid) :
    ∀ v ∈ List.ofFn g.graph, v.ports.length = 3 ∧ v.minInflow = 2 := by
  intro _ hv; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  rcases h.2.1 i with ⟨_, _, _, hn, hp⟩ | ⟨_, _, _, hn, hp⟩
  · exact ⟨by simpa only [Vertex.and, List.length_cons, List.length_nil] using hp.length_eq, hn⟩
  · exact ⟨by simpa only [Vertex.or, List.length_cons, List.length_nil] using hp.length_eq, hn⟩

/-- Source instructions retain every original vertex's port order and index. -/
private theorem sources_eq (x : AndOrNCL.Instance) (h : x.graph.Valid) (bits : List Bool) :
    Emit.sources x bits = sourceProgram
      ((List.ofFn x.graph.graph).map
        fun v => v.ports.map fun p => finiteWire x.graph bits p.port) 0 := by
  unfold Emit.sources sourceProgram; conv_lhs => rw [← vertices_map x.graph h.1]
  simp only [List.zipIdx_map, List.map_map]
  refine List.map_congr_left fun ⟨v, _⟩ hi => ?_
  obtain ⟨p, q, r, hp⟩ := List.length_eq_three.mp
    (shape_vertices x.graph h v (List.fst_mem_of_mem_zipIdx hi)).1
  cases v with
  | mk ps _ =>
    dsimp only at hp; subst ps
    simp only [Nat.zero_add]; rfl

/-- The explicit available-wire list is precisely the finite source boundary order. -/
private theorem available_eq (g : AndOrGraph) (hb : g.Bounded) (bits : List Bool) :
    Emit.available g bits = (Sources.vertexLabels (List.ofFn g.graph)).map (finiteWire g bits) := by
  unfold Emit.available Sources.vertexLabels; conv_lhs => rw [← vertices_map g hb]
  simp only [List.flatMap_map, Vertex.map, List.map_flatMap, List.map_map]; rfl

/-- The explicit requested-wire list is exactly the finite endpoint-pair order. -/
private theorem requested_eq (x : AndOrNCL.Instance) (hl : x.initial.length = x.graph.edgeCount)
    (bits : List Bool) :
    Emit.requested x bits = (Sinks.pairLabels (List.finRange x.graph.edgeCount)).map
      (finiteWire x.graph bits) := by
  unfold Emit.requested Sinks.pairLabels; rw [hl, ← List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map, List.map_flatMap, List.map_cons, List.map_nil]; rfl

/-- The cap stream retains the original finite edge order and endpoint directions. -/
private theorem caps_eq (x : AndOrNCL.Instance) (h : x.graph.Valid)
    (hl : x.initial.length = x.graph.edgeCount) (bits : List Bool) :
    Emit.caps x bits = capProgram (color (List.ofFn x.graph.graph))
      (fun p => (finiteWire x.graph bits p).bit) (List.finRange x.graph.edgeCount) 0 := by
  unfold Emit.caps capProgram; rw [hl, ← List.map_coe_finRange_eq_range, List.map_map]
  exact List.map_congr_left fun e _ => by rw [Function.comp_apply, edgeColor_eq x.graph h.1 e]; rfl

private theorem word_cast {a b a' b' : List Color} {Label : Type} {xs ys : List Label}
    (D : Wiring Cell a b xs ys) (ha : a = a') (hb : b = b') (k : ℕ) :
    (planarizeAlong Cell.expand (D.cast ha hb).diagram).toWord Prim.interp k =
      (planarizeAlong Cell.expand D.diagram).toWord Prim.interp k := by
  subst ha hb; rfl

/-- The emitted primitive word is the existing canonical planarizer, with identical numbering. -/
theorem expand_emit_program (x : AndOrNCL.Instance) (h : x.graph.Valid)
    (hl : x.initial.length = x.graph.edgeCount) (bits : List Bool) :
    expand (Emit.program x bits) = planarize x.graph h := by
  unfold Emit.program
  rw [expand_append, expand_append, sources_eq x h bits, requested_eq x hl bits,
    available_eq x.graph h.1 bits, caps_eq x h hl bits,
    expand_sourceProgram _ _ (shape_vertices x.graph h),
    expand_program _ (finiteWire_injective x.graph bits) _ _
      (incidencePerm _ (ofFn_wellFormed x.graph.graph h.2.2))
      (vertexLabels_nodup _ (ofFn_wellFormed x.graph.graph h.2.2)),
    expand_capProgram, finiteWire_color x.graph h.1 bits]
  change _ = _ ++ ((planarizeAlong Cell.expand (routing (List.ofFn x.graph.graph)
    (color (List.ofFn x.graph.graph)) _).diagram).toWord Prim.interp 0 ++ _)
  rw [routing, word_cast, List.append_assoc]; rfl

private theorem labelledBits_cast {a b a' b' : List Color} {Label : Type}
    {xs ys : List Label} (D : Wiring Cell a b xs ys) (ha : a = a') (hb : b = b')
    (u : Label → Bool) :
    labelledBits (D.cast ha hb).labeling u = labelledBits D.labeling u := by
  subst ha hb; rfl

/-- The actual subdivision encoding gives opposite downward reference directions at endpoints. -/
private theorem stub_enc {V E : Type} [DecidableEq E] (G : ConstraintGraph V E) (c : E → Color)
    (hc : ∀ v p, p ∈ (G v).ports → p.weight = (c p.port.edge).weight) (hl : G.LoopFree)
    (s : E → Bool) (p : Port E) :
    (Stub.simulation G c hc hl).enc s p = xor (s p.edge) p.dir := by
  change (finTwoEquiv (finTwoEquiv.symm p.dir) ^^ s p.edge) = _
  rw [Equiv.apply_symm_apply, Bool.xor_comm]

/-- Emitted directions are the actual canonical planar simulation bits, in edge creation order. -/
theorem configurationBits_emit_program (x : AndOrNCL.Instance) (h : x.graph.Valid)
    (hf : x.graph.graph.LoopFree)
    (hl : x.initial.length = x.graph.edgeCount) (bits : List Bool) :
    configurationBits (Emit.program x bits) = (planarizeDiagram x.graph h).bits
      ((planarizeDiagramSimulation x.graph h hf).enc (x.graph.config bits)) := by
  let vs := List.ofFn x.graph.graph
  let c := color vs
  let s := (Stub.simulation (fun i : Fin vs.length => vs.get i) c
    (fun i _ hp => port_weight_color (ofFn_andOr x.graph.graph h.2.1)
      (ofFn_wellFormed x.graph.graph h.2.2) (List.get_mem _ i) hp)
    (ofFn_loopFree x.graph.graph hf)).enc (x.graph.config bits)
  have hu : s = fun p => (finiteWire x.graph bits p).bit := funext (stub_enc _ _ _ _ _)
  unfold Emit.program
  rw [configurationBits_append, configurationBits_append, sources_eq x h bits,
    requested_eq x hl bits, available_eq x.graph h.1 bits, caps_eq x h hl bits,
    configurationBits_sourceProgram _ _ (shape_vertices x.graph h),
    configurationBits_program _ (finiteWire_injective x.graph bits) _ _
      (incidencePerm _ (ofFn_wellFormed x.graph.graph h.2.2))
      (vertexLabels_nodup _ (ofFn_wellFormed x.graph.graph h.2.2)),
    configurationBits_capProgram, finiteWire_color x.graph h.1 bits, bits_closed]
  change _ = extendedBits (diagram vs c _) (s ∘ (drawing vs c _).edgeEquiv)
  rw [hu]
  change _ = labelledBits ((sourceBundle vs c).labeling.comp
    ((routing vs c _).labeling.comp (sinkBundle c).labeling)) _
  rw [labelledBits_comp, labelledBits_comp, routing, labelledBits_cast, List.append_assoc]; rfl

end Cslib.Complexity.NCL.Planar.Embedding.PolyTime
