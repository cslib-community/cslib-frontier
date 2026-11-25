/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Reindex
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Vertices
public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance

/-!
# Finite numbering of orthogonal drawings

Vertex-list numbering and creation-order edge numbering transport the exact paths and port
incidences to the finite graph used by word compilation.

## Main definitions

* `Cslib.Complexity.NCL.GridDrawing.Closed.finite`: number a diagram drawing.
* `Cslib.Complexity.NCL.GridDrawing.Closed.ofFinite`: retain a drawing under graph serialization.

## Main results

Both transports preserve complete finite paths and all nonintersection conditions.
-/

public section

namespace Cslib.Complexity.NCL.GridDrawing

open Diagram

variable {Γ : List Color → List Color → Type} {I : Interp Γ} {a b : List Color}

/-- Finite graph numbering preserves exactly the listed endpoint ports. -/
theorem hasPort_finiteGraph (D : Diagram Γ a b) (i : Fin (vertexList I D).length)
    (e : Fin (a.length + D.innerCount)) (d : Bool) :
    HasPort (finiteGraph I D) i e d ↔
      HasPort (D.graph I) ((vertexEquiv I D).symm i) (D.numEquiv.symm e) d := by
  rw [finiteGraph, hasPort_map_iff]
  constructor
  · rintro ⟨f, hf, he⟩
    have hfe := congrArg D.numEquiv.symm he
    simp only [Equiv.symm_apply_apply] at hfe
    subst f
    simpa only [HasPort, get_vertexList] using hf
  · intro he
    refine ⟨D.numEquiv.symm e, ?_, D.numEquiv.apply_symm_apply e⟩
    simpa only [HasPort, get_vertexList] using he

/-- Number a closed diagram drawing on the exact finite vertex and edge intervals. -/
@[expose] noncomputable def Closed.finite (D : Diagram Γ a b) (P : Closed (D.graph I)) :
    Closed (finiteGraph I D) :=
  P.reindex (vertexEquiv I D).symm D.numEquiv.symm (hasPort_finiteGraph D)

/-- Serializing a finite graph changes no edge path or port incidence. -/
@[expose]
noncomputable def Closed.ofFinite {n m : ℕ} {G : ConstraintGraph (Fin n) (Fin m)} (P : Closed G) :
    Closed (AndOrGraph.ofFinite G).graph :=
  P.reindex (finCongr (by simp [AndOrGraph.ofFinite])) (Equiv.refl _)
    (fun i _ _ => by rw [HasPort, AndOrGraph.graph_ofFinite]; rfl)

end Cslib.Complexity.NCL.GridDrawing
