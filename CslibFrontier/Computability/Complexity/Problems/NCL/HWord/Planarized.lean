/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.AndOr
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Numbering
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Planarize
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CompileReachability

/-!
# Actual planar words implementing H-word reconfiguration

Number the complete standard graph, draw its incidences, and expand every crossing. The
result is a closed typed planar word, with actual initial and target directions and exact
configuration-to-configuration semantics.

## Main definitions

* `HWord.Planarized.word`: the emitted standard planar word.
* `HWord.Planarized.bits`: the physical configuration of a word, in edge creation order.

## Main results

* `HWord.Planarized.mem_compile_iff`: exact word-reconfiguration semantics of the emitted word.
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner
  Cslib.Complexity.NCL.Diagram.instDecidableEqInner

namespace Cslib.Complexity.NCL.HWord.Planarized

open Diagram

variable {q n : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Exact edge count after explicit finite numbering of the standard network. -/
@[expose] def width : ℕ :=
  (SelectorNetwork.AndOr.Numbering.edgeList (PortGraph.network H n) (AndOr.rowSection H hq)
    (PortGraph.bandwidthCertificate H).order).length

/-- Exact vertex count in source-cell and local creation order. -/
@[expose] def vertexCount : ℕ :=
  (SelectorNetwork.AndOr.Numbering.vertexList (PortGraph.network H n) (AndOr.rowSection H hq)
    (PortGraph.bandwidthCertificate H).order).length

/-- The standard word network on finite vertex and edge intervals. -/
@[expose] def finiteGraph : ConstraintGraph (Fin (vertexCount (n := n) H hq))
    (Fin (width (n := n) H hq)) :=
  SelectorNetwork.AndOr.Numbering.graph (PortGraph.network H n) (AndOr.rowSection H hq)
    (PortGraph.bandwidthCertificate H).order

/-- Every numbered standard vertex, in explicit enumeration order. -/
@[expose] def vertices : List (Vertex (Fin (width (n := n) H hq))) :=
  List.ofFn (finiteGraph H hq)

private def vertexIndex : Fin (vertices (n := n) H hq).length ≃ Fin (vertexCount (n := n) H hq) :=
  finCongr (List.length_ofFn (f := finiteGraph H hq))

private theorem get_vertices (i : Fin (vertices (n := n) H hq).length) :
    (vertices H hq).get i = finiteGraph H hq (vertexIndex H hq i) :=
  List.get_ofFn _ i

/-- The emitted vertex list consists entirely of standard AND/OR vertices. -/
theorem vertices_isAndOr : ∀ v ∈ vertices (n := n) H hq, v.IsAndOr := by
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact SelectorNetwork.AndOr.Numbering.isAndOr _ _ _ i

/-- The emitted finite vertex list has exactly two consistent ports per edge. -/
theorem vertices_wellFormed :
    ConstraintGraph.WellFormed (fun i : Fin (vertices (n := n) H hq).length =>
      (vertices H hq).get i) := by
  have heq : (fun i : Fin (vertices (n := n) H hq).length => (vertices H hq).get i) =
      finiteGraph H hq ∘ vertexIndex H hq := funext (get_vertices H hq)
  rw [heq]
  exact (SelectorNetwork.AndOr.Numbering.wellFormed _ _ _).reindex (vertexIndex H hq)

/-- The emitted finite list has no self-loops. -/
theorem vertices_loopFree :
    ConstraintGraph.LoopFree (fun i : Fin (vertices (n := n) H hq).length =>
      (vertices H hq).get i) := by
  intro i
  change (((vertices H hq).get i).ports.map (fun p => p.port.edge)).Nodup
  rw [get_vertices]
  exact SelectorNetwork.AndOr.Numbering.loopFree _ _ _ _

private def listSimulation : ConstraintGraph.Simulation (AndOr.graph (n := n) H hq)
    (fun i : Fin (vertices (n := n) H hq).length => (vertices H hq).get i) :=
  (SelectorNetwork.AndOr.Numbering.simulation (PortGraph.network H n)
    (AndOr.rowSection H hq) (PortGraph.bandwidthCertificate H).order).trans
      (ConstraintGraph.Simulation.ofLegalEquiv (finiteGraph H hq)
        (fun i : Fin (vertices (n := n) H hq).length => (vertices H hq).get i)
        (Equiv.refl _) (fun s => by
          change ConstraintGraph.Legal
            (fun i : Fin (vertices (n := n) H hq).length => (vertices H hq).get i) s ↔
            (finiteGraph H hq).Legal s
          rw [show (fun i : Fin (vertices (n := n) H hq).length => (vertices H hq).get i) =
            finiteGraph H hq ∘ vertexIndex H hq from funext (get_vertices H hq)]
          exact ConstraintGraph.legal_comp _ (vertexIndex H hq).surjective s))

/-- The actual closed planar diagram for the standard word network. -/
@[expose] def diagram : Diagram Prim [] [] :=
  Planar.Embedding.planeDiagram (vertices (n := n) H hq) (vertices_wellFormed H hq)

/-- The planar diagram preserves and reflects the complete standard network's dynamics. -/
def simulation : ConstraintGraph.Simulation (AndOr.graph (n := n) H hq)
    ((diagram (n := n) H hq).graph Prim.interp) :=
  (listSimulation H hq).trans (Planar.Embedding.planeSimulation (vertices H hq)
    (vertices_isAndOr H hq) (vertices_wellFormed H hq) (vertices_loopFree H hq))

/-- The physical direction of every planar implementation wire for a source word. -/
def orientation (w : Fin n → Fin q) : (diagram (n := n) H hq).Edge → Bool :=
  (simulation H hq).enc (AndOr.orientation H hq w)

/-- The actual planar implementation is legal exactly when the word is compatible. -/
theorem legal_orientation_iff (w : Fin n → Fin q) :
    ((diagram (n := n) H hq).graph Prim.interp).Legal (orientation H hq w) ↔ Legal H w :=
  (simulation H hq).legal_enc_iff.trans (AndOr.legal_orientation_iff H hq w)

/-- The planar implementation's canonical paths are exactly word-reconfiguration paths. -/
theorem reachable_orientation_iff (s t : Fin n → Fin q) :
    ((diagram (n := n) H hq).graph Prim.interp).Reachable
      (orientation H hq s) (orientation H hq t) ↔
      Reachable H s t :=
  ((simulation H hq).reachable_enc_iff).trans (AndOr.reachable_orientation_iff H hq s t)

/-- The emitted standard planar word, independent of the chosen endpoint words. -/
@[expose] def word : Word := (diagram (n := n) H hq).toWord Prim.interp 0

/-- Each source word has one physical direction bit per emitted wire. -/
@[expose] def bits (w : Fin n → Fin q) : List Bool :=
  (diagram (n := n) H hq).bits (orientation H hq w)

/-- Actual planar bits are the canonical extension of the same numbered standard orientation. -/
theorem bits_planeSimulation (w : Fin n → Fin q) : bits H hq w =
    (diagram H hq).bits ((Planar.Embedding.planeSimulation (vertices H hq)
      (vertices_isAndOr H hq) (vertices_wellFormed H hq) (vertices_loopFree H hq)).enc
        ((SelectorNetwork.AndOr.Numbering.simulation (PortGraph.network H n)
          (AndOr.rowSection H hq) (PortGraph.bandwidthCertificate H).order).enc
            (AndOr.orientation H hq w))) := by rfl

/-- The emitted word is closed and well typed. -/
theorem wellTyped_word : (word (n := n) H hq).WellTyped [] [] :=
  wellTyped_toWord Prim.interp (diagram (n := n) H hq)

/-- The emitted word passes the standard single-vertex plane check. -/
theorem checkPlane_word : (word (n := n) H hq).checkPlane = true :=
  Planar.Embedding.checkPlane_word (vertices H hq) (vertices_isAndOr H hq)
    (vertices_wellFormed H hq)

/-- Compiling the emitted word gives valid standard AND/OR graph data. -/
theorem compile_valid : (Word.compile (word (n := n) H hq)).Valid :=
  Planar.Embedding.compile_valid_word (vertices H hq) (vertices_isAndOr H hq)
    (vertices_wellFormed H hq)

/-- The actual compiled planar graph has exactly the intended word-reconfiguration semantics. -/
theorem mem_compile_iff (s t : Fin n → Fin q) :
    ⟨Word.compile (word (n := n) H hq), bits H hq s, bits H hq t⟩ ∈ AndOrNCL ↔
      Legal H s ∧ Reachable H s t :=
  (mem_compile_AndOrNCL_iff Prim.interp (diagram (n := n) H hq) (compile_valid H hq)
    (orientation H hq s) (orientation H hq t)).trans
    (and_congr (legal_orientation_iff H hq s) (reachable_orientation_iff H hq s t))

end Cslib.Complexity.NCL.HWord.Planarized
