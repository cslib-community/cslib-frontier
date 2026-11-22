/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word

/-!
# Crossing counts of diagrams

The syntactic crossing count is additive under stacking and juxtaposition. It bounds the number
of crossover implementations introduced by planarization.

## Main definitions

* `Diagram.swapCount`: the number of explicit swaps in a diagram.

## Main results

* `Diagram.swapCount_moveLeft`: moving one wire across a bundle uses one crossing per wire.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type}

/-- The number of syntactic crossings in a drawing. -/
@[expose] def swapCount : {a b : List Color} → Diagram Γ a b → ℕ
  | _, _, .gen _ | _, _, .id _ => 0
  | _, _, .swap .. => 1
  | _, _, .comp D₁ D₂ | _, _, .tensor D₁ D₂ => swapCount D₁ + swapCount D₂

/-- Moving one wire left crosses every wire of the intervening bundle once. -/
theorem swapCount_moveLeft (l : List Color) (c : Color) (r : List Color) :
    swapCount (moveLeft (Γ := Γ) l c r) = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [moveLeft, swapCount, ih]

/-- Stacking diagrams adds their vertex counts. -/
theorem length_vertexList_comp (I : Interp Γ) {a b c : List Color}
    (D : Diagram Γ a b) (D' : Diagram Γ b c) :
    (vertexList I (D.comp D')).length = (vertexList I D).length + (vertexList I D').length := by
  simp only [vertexList, List.length_append, List.length_map]

/-- Juxtaposing diagrams adds their vertex counts. -/
theorem length_vertexList_tensor (I : Interp Γ) {a b c d : List Color}
    (D : Diagram Γ a b) (D' : Diagram Γ c d) :
    (vertexList I (D.tensor D')).length = (vertexList I D).length + (vertexList I D').length := by
  simp only [vertexList, List.length_append, List.length_map]

end Cslib.Complexity.NCL.Diagram
