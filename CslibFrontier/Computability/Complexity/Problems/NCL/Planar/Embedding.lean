/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Origin
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CompileEdge

/-!
# Planarizing arbitrary finite AND/OR graph data

`Planar.planarize` accepts any valid `AndOrGraph` and returns a closed plane word in the L1
format. For a loop-free input its compiled finite graph simulates the original graph, with a
representative for every original edge. The source layout is constructed from the incidence list.

## Main definitions

* `Planar.planarize`: the plane word for valid finite graph data.
* `Planar.planarizeSimulation`: the simulation into its compiled finite graph.
* `Planar.planarizeEdge`: the compiled representative of an original edge.

## Main results

* `Planar.planarize_wellTyped`, `Planar.planarize_checkPlane`, `Planar.planarize_compile_valid`:
  the output instance filters.
* `Planar.planarizeSimulation_abs`: representative edges track abstraction.
* `Planar.planarize_reachable_iff`, `Planar.planarize_canReverse_iff`,
  `Planar.planarize_edgeToEdge_iff`: the three reachability questions.
-/

public section

namespace Cslib.Complexity.NCL.Planar

open Diagram

private def vertexEquiv {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m)) :
    Fin (List.ofFn G).length ≃ Fin n := finCongr List.length_ofFn

private theorem listGraph_eq {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m)) :
    (fun i : Fin (List.ofFn G).length => (List.ofFn G).get i) = G ∘ vertexEquiv G :=
  funext (List.get_ofFn G)

private theorem ofFn_wellFormed {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m))
    (h : G.WellFormed) :
    ConstraintGraph.WellFormed (fun i : Fin (List.ofFn G).length => (List.ofFn G).get i) := by
  rw [listGraph_eq]
  exact h.reindex (vertexEquiv G)

private theorem ofFn_loopFree {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m))
    (h : G.LoopFree) :
    ConstraintGraph.LoopFree (fun i : Fin (List.ofFn G).length => (List.ofFn G).get i) := by
  rw [listGraph_eq]
  exact fun i => h (vertexEquiv G i)

private theorem ofFn_andOr {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m))
    (h : G.IsAndOr) : ∀ v ∈ List.ofFn G, v.IsAndOr := by
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
  exact h i

private def ofFnSimulation {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m)) :
    ConstraintGraph.Simulation G (fun i : Fin (List.ofFn G).length => (List.ofFn G).get i) :=
  ConstraintGraph.Simulation.ofLegalEquiv _ _ (Equiv.refl _) fun s => by
    change ConstraintGraph.Legal
      (fun i : Fin (List.ofFn G).length => (List.ofFn G).get i) s ↔ G.Legal s
    rw [listGraph_eq]
    exact ConstraintGraph.legal_comp G (vertexEquiv G).surjective s

/-- Construct a closed plane diagram from arbitrary valid finite AND/OR graph data. -/
@[expose] def planarizeDiagram (g : AndOrGraph) (h : g.Valid) : Diagram Prim [] [] :=
  Embedding.planeDiagram (List.ofFn g.graph) (by exact ofFn_wellFormed g.graph h.2.2)

/-- The plane word representing arbitrary valid finite AND/OR graph data. -/
@[expose] def planarize (g : AndOrGraph) (h : g.Valid) : Word :=
  (planarizeDiagram g h).toWord Prim.interp 0

/-- The canonical plane diagram simulates the input finite graph. -/
def planarizeDiagramSimulation (g : AndOrGraph) (h : g.Valid) (hl : g.graph.LoopFree) :
    ConstraintGraph.Simulation g.graph ((planarizeDiagram g h).graph Prim.interp) :=
  (ofFnSimulation g.graph).trans
    (Embedding.planeSimulation (List.ofFn g.graph) (ofFn_andOr g.graph (by exact h.2.1))
      (by exact ofFn_wellFormed g.graph h.2.2) (ofFn_loopFree g.graph hl))

/-- An original edge's representative in the plane diagram. -/
def planarizeDiagramEdge (g : AndOrGraph) (h : g.Valid) (e : Fin g.edgeCount) :
    (planarizeDiagram g h).Edge :=
  Embedding.planeEdge (List.ofFn g.graph) (by exact ofFn_wellFormed g.graph h.2.2) e

/-- The diagram simulation reads its tracked original edges. -/
theorem planarizeDiagramSimulation_abs (g : AndOrGraph) (h : g.Valid) (hl : g.graph.LoopFree)
    (s : (planarizeDiagram g h).Edge → Bool) (e : Fin g.edgeCount) :
    (planarizeDiagramSimulation g h hl).abs s e = s (planarizeDiagramEdge g h e) := by
  simp only [planarizeDiagramSimulation, ConstraintGraph.Simulation.trans, NCL.Simulation.trans,
    ofFnSimulation, ConstraintGraph.Simulation.ofLegalEquiv, Function.comp_apply,
    Equiv.coe_refl, Function.comp_id, planarizeDiagramEdge]
  exact Embedding.planeSimulation_abs (List.ofFn g.graph) (ofFn_andOr g.graph (by exact h.2.1))
    (ofFn_wellFormed g.graph h.2.2) (ofFn_loopFree g.graph hl) s e

/-- The compiled plane word simulates the original finite graph. -/
def planarizeSimulation (g : AndOrGraph) (h : g.Valid) (hl : g.graph.LoopFree) :
    ConstraintGraph.Simulation g.graph (Word.compile (planarize g h)).graph :=
  (planarizeDiagramSimulation g h hl).trans (compileSimulation Prim.interp (planarizeDiagram g h))

/-- An original edge's creation-order number in the compiled plane graph. -/
def planarizeEdge (g : AndOrGraph) (h : g.Valid) (e : Fin g.edgeCount) :
    Fin (Word.compile (planarize g h)).edgeCount :=
  compileEdgeEquiv Prim.interp (planarizeDiagram g h) (planarizeDiagramEdge g h e)

/-- The finite compiled simulation reads exactly the representative of each original edge. -/
theorem planarizeSimulation_abs (g : AndOrGraph) (h : g.Valid) (hl : g.graph.LoopFree)
    (s : Fin (Word.compile (planarize g h)).edgeCount → Bool) (e : Fin g.edgeCount) :
    (planarizeSimulation g h hl).abs s e = s (planarizeEdge g h e) := by
  change (planarizeDiagramSimulation g h hl).abs
    ((compileSimulation Prim.interp (planarizeDiagram g h)).abs s) e = _
  rw [planarizeDiagramSimulation_abs]
  exact compileSimulation_abs Prim.interp (planarizeDiagram g h) s (planarizeDiagramEdge g h e)

/-- The canonical output diagram has no crossings. -/
theorem planarize_planar (g : AndOrGraph) (h : g.Valid) : (planarizeDiagram g h).Planar :=
  Embedding.plane_planar _ _

/-- Every vertex of the canonical output diagram is AND or OR. -/
theorem planarize_isAndOr (g : AndOrGraph) (h : g.Valid) :
    ((planarizeDiagram g h).graph Prim.interp).IsAndOr :=
  Embedding.plane_isAndOr _ (ofFn_andOr g.graph (by exact h.2.1)) _

/-- The canonical output diagram has no self-loops. -/
theorem planarize_loopFree (g : AndOrGraph) (h : g.Valid) :
    ((planarizeDiagram g h).graph Prim.interp).LoopFree :=
  Embedding.plane_loopFree _ (ofFn_andOr g.graph (by exact h.2.1)) _

/-- The canonical output diagram has consistent two-ended incidences. -/
theorem planarize_wellFormed (g : AndOrGraph) (h : g.Valid) :
    ((planarizeDiagram g h).graph Prim.interp).WellFormed :=
  Embedding.plane_wellFormed _ (ofFn_andOr g.graph (by exact h.2.1)) _

/-- The output word is closed and well typed. -/
theorem planarize_wellTyped (g : AndOrGraph) (h : g.Valid) :
    (planarize g h).WellTyped [] [] := wellTyped_toWord _ _

/-- Every output word layer is a standard single-vertex plane cell. -/
theorem planarize_checkPlane (g : AndOrGraph) (h : g.Valid) :
    (planarize g h).checkPlane = true :=
  Embedding.checkPlane_word _ (ofFn_andOr g.graph (by exact h.2.1)) _

/-- Compiling the output word gives valid finite AND/OR graph data. -/
theorem planarize_compile_valid (g : AndOrGraph) (h : g.Valid) :
    (Word.compile (planarize g h)).Valid :=
  Embedding.compile_valid_word _ (ofFn_andOr g.graph (by exact h.2.1))
    (by exact ofFn_wellFormed g.graph h.2.2)

/-- The compiled output graph has polynomially many vertices. -/
theorem planarize_vertices_le (g : AndOrGraph) (h : g.Valid) :
    (Word.compile (planarize g h)).vertices.length ≤
      g.vertices.length + 16 * g.edgeCount + 286 * (2 * g.edgeCount) ^ 2 := by
  simpa only [planarize, planarizeDiagram, Embedding.word, List.length_ofFn] using
    Embedding.compiled_vertices_le (List.ofFn g.graph)
      (by exact ofFn_wellFormed g.graph h.2.2)

/-- The compiled output graph has polynomially many edges. -/
theorem planarize_edges_le (g : AndOrGraph) (h : g.Valid) :
    (Word.compile (planarize g h)).edgeCount ≤ 25 * g.edgeCount + 429 * (2 * g.edgeCount) ^ 2 :=
  Embedding.compiled_edges_le (List.ofFn g.graph) (by exact ofFn_wellFormed g.graph h.2.2)

/-- The source vertex, edge cap, or routing crossing responsible for each output vertex. -/
def planarizeVertexOrigin (g : AndOrGraph) (h : g.Valid)
    (v : (planarizeDiagram g h).Vtx Prim.interp) :
    Embedding.VertexOrigin g.vertices.length g.edgeCount
      (swapCount (Embedding.routing (List.ofFn g.graph) (Embedding.color (List.ofFn g.graph))
        (by exact ofFn_wellFormed g.graph h.2.2)).diagram) :=
  Embedding.VertexOrigin.mapVertices (vertexEquiv g.graph)
    (Embedding.planeVertexOrigin (List.ofFn g.graph)
      (by exact ofFn_wellFormed g.graph h.2.2) v)

/-- The canonical planarization preserves and reflects configuration reachability. -/
theorem planarize_reachable_iff (g : AndOrGraph) (h : g.Valid) (hl : g.graph.LoopFree)
    (s t : Fin g.edgeCount → Bool) :
    (Word.compile (planarize g h)).graph.Reachable
      ((planarizeSimulation g h hl).enc s) ((planarizeSimulation g h hl).enc t) ↔
        g.graph.Reachable s t :=
  (planarizeSimulation g h hl).reachable_enc_iff

/-- The canonical planarization preserves and reflects edge reversal. -/
theorem planarize_canReverse_iff (g : AndOrGraph) (h : g.Valid) (hl : g.graph.LoopFree)
    (s : Fin g.edgeCount → Bool) (e : Fin g.edgeCount) :
    (Word.compile (planarize g h)).graph.CanReverse
      ((planarizeSimulation g h hl).enc s) (planarizeEdge g h e) ↔ g.graph.CanReverse s e :=
  (planarizeSimulation g h hl).canReverse_enc_iff (fun _ => planarizeSimulation_abs g h hl _ e)

/-- The canonical planarization preserves and reflects directional edge-to-edge reachability. -/
theorem planarize_edgeToEdge_iff (g : AndOrGraph) (h : g.Valid) (hl : g.graph.LoopFree)
    (e f : Fin g.edgeCount) (d b : Bool) :
    (∃ s t, (Word.compile (planarize g h)).graph.Legal s ∧ s (planarizeEdge g h e) = d ∧
      t (planarizeEdge g h f) = b ∧ (Word.compile (planarize g h)).graph.Reachable s t) ↔
      ∃ s t, g.graph.Legal s ∧ s e = d ∧ t f = b ∧ g.graph.Reachable s t :=
  (planarizeSimulation g h hl).exists_legal_reachable_iff
    (fun _ => planarizeSimulation_abs g h hl _ e) (fun _ => planarizeSimulation_abs g h hl _ f) d b

end Cslib.Complexity.NCL.Planar
