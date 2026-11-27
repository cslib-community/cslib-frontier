/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CompileEdge
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Vertices
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.BandwidthTransport

/-!
# Bandwidth certificates for compiled diagrams

The compiler retains the actual list positions of vertices and creation numbers of edges.
Transport along these numberings preserves a supplied bandwidth order.

## Main definitions

* `Diagram.compileVertexEquiv`: actual diagram vertices in compiled list order.
* `Diagram.compileBandwidthCertificate`: retain an order when compiling a closed diagram.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} (I : Interp Γ)

/-- Actual diagram vertices numbered by their positions in the compiled list. -/
@[expose] def compileVertexEquiv (D : Diagram Γ [] []) :
    D.Vtx I ≃ Fin (Word.compile (D.toWord I 0)).vertices.length :=
  (vertexEquiv I D).trans (finCongr (by
    rw [compile_toWord]
    simp only [AndOrGraph.ofFinite, List.length_ofFn]))

/-- Inverting the compiled vertex numbering preserves the actual list index. -/
theorem compileVertexEquiv_symm_val (D : Diagram Γ [] [])
    (v : Fin (Word.compile (D.toWord I 0)).vertices.length) :
    (vertexEquiv I D ((compileVertexEquiv I D).symm v)).val = v.val :=
  congrArg Fin.val ((compileVertexEquiv I D).apply_symm_apply v)

/-- A compiled vertex has the original ports under the actual edge numbering. -/
theorem compile_graph_vertexEquiv (D : Diagram Γ [] []) (v : D.Vtx I) :
    (Word.compile (D.toWord I 0)).graph (compileVertexEquiv I D v) =
      (D.graph I v).map (compileEdgeEquiv I D) := by
  unfold compileVertexEquiv compileEdgeEquiv
  generalize_proofs hv he
  generalize hg : Word.compile (D.toWord I 0) = g at *
  rw [compile_toWord] at hg
  cases hg
  simp only [Equiv.trans_apply, finCongr_apply, AndOrGraph.graph_ofFinite]
  change ((vertexList I D).get (vertexEquiv I D v)).map D.numEquiv = _
  rw [get_vertexEquiv]
  rfl

/-- Compile a closed diagram while retaining its supplied bandwidth order. -/
@[expose] def compileBandwidthCertificate (D : Diagram Γ [] []) {bound : ℕ}
    (C : ConstraintGraph.BandwidthCertificate (D.graph I) bound) :
    ConstraintGraph.BandwidthCertificate (Word.compile (D.toWord I 0)).graph bound :=
  C.ofEquiv (compileVertexEquiv I D) (compileEdgeEquiv I D)
    (compileEdgeEquiv I D).injective (compile_graph_vertexEquiv I D)

end Cslib.Complexity.NCL.Diagram
