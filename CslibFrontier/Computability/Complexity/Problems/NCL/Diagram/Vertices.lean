/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Finite

/-!
# Exact vertex numbering of diagrams

The positions in the vertex list form an explicit equivalence with the diagram's vertex type.
This complements creation-order edge numbering and retains complete vertex data.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.vertexEquiv`: vertex positions in list order.

## Main results

* `Cslib.Complexity.NCL.Diagram.get_vertexEquiv`: list lookup is the diagram's actual vertex.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} (I : Interp Γ)

/-- The diagram's vertices in the order of its flattened vertex list. -/
@[expose]
def vertexEquiv : {a b : List Color} → (D : Diagram Γ a b) → D.Vtx I ≃ Fin (vertexList I D).length
  | _, _, .gen _ => .refl _
  | _, _, .id _ => (show Empty ≃ Fin 0 from Equiv.equivOfIsEmpty _ _)
  | _, _, .swap .. => (show Empty ≃ Fin 0 from Equiv.equivOfIsEmpty _ _)
  | _, _, .comp D₁ D₂ =>
    ((vertexEquiv D₁).sumCongr (vertexEquiv D₂)).trans
      (finSumFinEquiv.trans (finCongr (by simp [vertexList])))
  | _, _, .tensor D₁ D₂ =>
    ((vertexEquiv D₁).sumCongr (vertexEquiv D₂)).trans
      (finSumFinEquiv.trans (finCongr (by simp [vertexList])))

private theorem get_map_append_left {α β γ : Type*} (l : List α) (r : List β)
    (f : α → γ) (g : β → γ) (i : Fin l.length) (j : Fin (l.map f ++ r.map g).length)
    (hj : j.val = i.val) : (l.map f ++ r.map g).get j = f (l.get i) := by
  have hj' : j = ⟨i.val, by
      simp only [List.length_append, List.length_map]; have := i.isLt; omega⟩ :=
    Fin.ext hj
  rw [hj']
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left (by simp), List.getElem_map]

private theorem get_map_append_right {α β γ : Type*} (l : List α) (r : List β)
    (f : α → γ) (g : β → γ) (i : Fin r.length) (j : Fin (l.map f ++ r.map g).length)
    (hj : j.val = l.length + i.val) : (l.map f ++ r.map g).get j = g (r.get i) := by
  have hj' : j = ⟨l.length + i.val, by
      simp only [List.length_append, List.length_map]; have := i.isLt; omega⟩ := Fin.ext hj
  rw [hj']
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.add_sub_cancel_left, List.getElem_map]

/-- Reading the numbered vertex gives exactly its interpreted constraint vertex. -/
theorem get_vertexEquiv {a b : List Color} (D : Diagram Γ a b) (v : D.Vtx I) :
    (vertexList I D).get (vertexEquiv I D v) = D.graph I v := by
  induction D with
  | gen _ => rfl
  | id _ | swap _ _ => exact v.elim
  | comp D₁ D₂ ih₁ ih₂ | tensor D₁ D₂ ih₁ ih₂ =>
    rcases v with v | v
    · exact (get_map_append_left _ _ _ _ (vertexEquiv I D₁ v) _ rfl).trans
        (congrArg (Vertex.map _) (ih₁ v))
    · exact (get_map_append_right _ _ _ _ (vertexEquiv I D₂ v) _ rfl).trans
        (congrArg (Vertex.map _) (ih₂ v))

/-- Arbitrary list positions recover the same vertex after inverse numbering. -/
theorem get_vertexList {a b : List Color} (D : Diagram Γ a b)
    (i : Fin (vertexList I D).length) :
    (vertexList I D).get i = D.graph I ((vertexEquiv I D).symm i) := by
  simpa only [Equiv.apply_symm_apply] using get_vertexEquiv I D ((vertexEquiv I D).symm i)

end Cslib.Complexity.NCL.Diagram
